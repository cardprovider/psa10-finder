#!/usr/bin/env python3
"""
PSA 10 Pokemon Deal Finder (UK)
================================
Finds UK eBay PSA 10 Pokemon cards listed below what they have recently sold for.

For every card it works out, using ONLY data from the last N days (default 28):
  * Value              = average of the 5 most recent UK sales
  * Avg cheapest 5     = average of the 5 cheapest current UK listings
  * Cheapest listed    = cheapest current UK listing (with link)
  * Cheapest sold      = lowest UK sale in the window
  * Sales in window    = how many sold (popularity / how easy it is to resell)
and gives each card a Price score, a Popularity score and an Overall score.

Data sources
  * Current listings : eBay Browse API (official, free)      -> EBAY_CLIENT_ID / EBAY_CLIENT_SECRET
  * Sold listings    : Apify actor "caffein.dev/ebay-sold-listings" on ebay.co.uk -> APIFY_TOKEN
    (eBay no longer offers sold data through its public API, and sold
     searches on the website now require sign-in.)

Usage
  python psa10_finder.py --watchlist cards.txt
  python psa10_finder.py "Umbreon VMAX 215/203" "Charizard ex 199/165"
  python psa10_finder.py --demo            # made-up sample data, no keys needed
"""
from __future__ import annotations

import argparse
import base64
import csv
import html
import json
import os
import re
import statistics
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta, timezone

# ----------------------------------------------------------------------------
# Settings you may want to change
# ----------------------------------------------------------------------------
WINDOW_DAYS = 28            # "within 4 weeks of the date of search"
POKEMON_CATEGORY = "183454" # eBay: CCG Individual Cards
SELL_FEE_PCT = 0.0          # eBay UK private sellers currently pay no final value fee on most items.
                            # Business sellers: set roughly 0.128 (12.8%) - check eBay's current fee page.
SELL_FIXED_FEE = 0.0        # e.g. 0.30 per order for business sellers
POSTAGE_OUT = 5.00          # what it costs YOU to post the slab to your buyer (tracked/signed)
APPLY_BUYER_FEE = True      # eBay UK Buyer Protection fee when you buy from a private seller
BAD_WORDS = [
    "proxy", "custom", "replica", "fake", "reprint", "orica", "fan art", "digital",
    "lot", "bundle", "x2", "x3", "choose", "pick your", "you pick", "mystery",
    "empty slab", "slab only", "case only", "label only", "sticker",
    "cgc", "bgs", "beckett", "ace grading", "ace 10", "ags", "tag grading", "sgc",
    "psa 9", "psa 8", "psa 7", "psa9", "psa8", "not psa", "ungraded", "raw",
    "pre order", "pre-order", "preorder", "read description",
]
FOREIGN_WORDS = ["japanese", "japan", "jpn", "korean", "chinese", "s-chinese", "t-chinese", "thai", "indonesian"]

BAD_RE = re.compile(r"(?<![a-z0-9])(" + "|".join(re.escape(w) for w in BAD_WORDS) + r")(?![a-z0-9])", re.I)
PSA10_RE =re.compile(r"\bpsa\s*-?\s*10\b", re.I)
NUMBER_RE = re.compile(r"\b(\d{1,3})\s*/\s*(\d{1,3})\b")
PROMO_RE = re.compile(r"\b((?:svp|swsh|sm|xy|bw)\s*-?\s*\d{2,3})\b", re.I)


# ----------------------------------------------------------------------------
# Data classes
# ----------------------------------------------------------------------------
@dataclass
class Listing:
    title: str
    price: float          # item + postage, GBP
    url: str
    date: str             # listed date (active) or sold date (sold), YYYY-MM-DD
    kind: str = ""        # BIN / Auction / Best offer
    seller_type: str = "" # INDIVIDUAL / BUSINESS / ""


@dataclass
class CardResult:
    card: str
    value_last5_sold: float | None = None
    avg_cheapest5_listed: float | None = None
    cheapest_listed: Listing | None = None
    cheapest_sold: Listing | None = None
    sales_in_window: int = 0
    active_in_window: int = 0
    sold_used_for_value: int = 0
    buy_cost: float | None = None
    resale_net: float | None = None
    profit: float | None = None
    margin_pct: float | None = None
    discount_pct: float | None = None
    price_score: float = 0.0
    popularity_score: float = 0.0
    overall_score: float = 0.0
    verdict: str = ""
    warnings: list[str] = field(default_factory=list)
    recent_sales: list[Listing] = field(default_factory=list)
    cheapest_listings: list[Listing] = field(default_factory=list)
    error: str = ""


# ----------------------------------------------------------------------------
# HTTP helper
# ----------------------------------------------------------------------------
def http_json(url, *, method="GET", headers=None, data=None, timeout=300, retries=2):
    body = None
    if data is not None:
        body = data if isinstance(data, bytes) else json.dumps(data).encode()
    for attempt in range(retries + 1):
        req = urllib.request.Request(url, data=body, method=method, headers=headers or {})
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode() or "null")
        except urllib.error.HTTPError as e:
            msg = e.read().decode(errors="replace")[:400]
            if e.code in (429, 500, 502, 503, 504) and attempt < retries:
                time.sleep(3 * (attempt + 1))
                continue
            raise RuntimeError(f"HTTP {e.code} from {url.split('?')[0]}: {msg}") from None
        except urllib.error.URLError as e:
            if attempt < retries:
                time.sleep(3)
                continue
            raise RuntimeError(f"Network error: {e.reason}") from None


# ----------------------------------------------------------------------------
# Title matching - keeps only genuine PSA 10 copies of the card searched for
# ----------------------------------------------------------------------------
def card_tokens(card: str):
    num = NUMBER_RE.search(card)
    promo = PROMO_RE.search(card)
    words = [w for w in re.findall(r"[a-z0-9]+", card.lower())
             if not w.isdigit() and len(w) > 1 and w not in {"psa", "ex", "gx", "v"}]
    return num, promo, words


def title_matches(title: str, card: str) -> bool:
    t = title.lower()
    if not PSA10_RE.search(t):
        return False
    if BAD_RE.search(t):
        return False
    q = card.lower()
    wants_foreign = any(f in q for f in FOREIGN_WORDS)
    if not wants_foreign and any(f in t for f in FOREIGN_WORDS):
        return False
    if wants_foreign and not any(f in t for f in FOREIGN_WORDS if f in q):
        return False
    num, promo, words = card_tokens(card)
    if num:  # card number must match, e.g. 215/203 (allow "215" alone if set total missing)
        a, b = num.group(1).lstrip("0"), num.group(2).lstrip("0")
        nums = [(x.lstrip("0"), y.lstrip("0")) for x, y in NUMBER_RE.findall(t)]
        if nums:
            if (a, b) not in nums:
                return False
        elif not re.search(rf"(?<!\d)0*{a}(?!\d)", t):
            return False
    if promo:
        p = re.sub(r"[\s-]", "", promo.group(1).lower())
        if p not in re.sub(r"[\s-]", "", t):
            return False
    # main name word (first meaningful word, e.g. "umbreon") must appear
    if words and words[0] not in t:
        return False
    return True


# ----------------------------------------------------------------------------
# Data source 1: current UK listings (eBay Browse API)
# ----------------------------------------------------------------------------
class EbayBrowse:
    TOKEN_URL = "https://api.ebay.com/identity/v1/oauth2/token"
    SEARCH_URL = "https://api.ebay.com/buy/browse/v1/item_summary/search"

    def __init__(self, client_id, client_secret):
        self.client_id, self.client_secret = client_id, client_secret
        self._token, self._exp = None, 0

    def token(self):
        if self._token and time.time() < self._exp - 60:
            return self._token
        basic = base64.b64encode(f"{self.client_id}:{self.client_secret}".encode()).decode()
        data = urllib.parse.urlencode({
            "grant_type": "client_credentials",
            "scope": "https://api.ebay.com/oauth/api_scope",
        }).encode()
        r = http_json(self.TOKEN_URL, method="POST", data=data, headers={
            "Authorization": f"Basic {basic}",
            "Content-Type": "application/x-www-form-urlencoded",
        })
        self._token, self._exp = r["access_token"], time.time() + int(r.get("expires_in", 7200))
        return self._token

    def search(self, card, include_auctions=False):
        formats = "{FIXED_PRICE|AUCTION}" if include_auctions else "{FIXED_PRICE}"
        params = {
            "q": f"{card} PSA 10",
            "category_ids": POKEMON_CATEGORY,
            "filter": f"itemLocationCountry:GB,buyingOptions:{formats},priceCurrency:GBP",
            "sort": "price",
            "limit": "200",
        }
        url = self.SEARCH_URL + "?" + urllib.parse.urlencode(params)
        r = http_json(url, headers={
            "Authorization": f"Bearer {self.token()}",
            "X-EBAY-C-MARKETPLACE-ID": "EBAY_GB",
            "X-EBAY-C-ENDUSERCTX": "contextualLocation=country=GB",
        }, timeout=60)
        out = []
        for it in (r or {}).get("itemSummaries", []):
            opts = it.get("buyingOptions", [])
            is_auction = "AUCTION" in opts and "FIXED_PRICE" not in opts
            p = (it.get("currentBidPrice") if is_auction else None) or it.get("price") or {}
            if p.get("currency") != "GBP":
                continue
            ship = 0.0
            so = it.get("shippingOptions") or []
            if so and so[0].get("shippingCost"):
                ship = float(so[0]["shippingCost"].get("value", 0) or 0)
            out.append(Listing(
                title=it.get("title", ""),
                price=round(float(p["value"]) + ship, 2),
                url=it.get("itemWebUrl", ""),
                date=(it.get("itemCreationDate") or "")[:10],
                kind="Auction (current bid)" if is_auction else "Buy It Now",
                seller_type=(it.get("seller") or {}).get("sellerAccountType", ""),
            ))
        return out


# ----------------------------------------------------------------------------
# Data source 2: UK sold listings (Apify, scrapes ebay.co.uk sold results)
# ----------------------------------------------------------------------------
class ApifySold:
    ACTOR = "caffein.dev~ebay-sold-listings"

    def __init__(self, token):
        self.token = token

    def search(self, card, days):
        url = (f"https://api.apify.com/v2/acts/{self.ACTOR}/run-sync-get-dataset-items"
               f"?token={urllib.parse.quote(self.token)}")
        payload = {
            "keywords": [f"{card} PSA 10"],
            "daysToScrape": days,
            "count": 80,
            "ebaySite": "ebay.co.uk",
            "sellerCountry": "GB",
            "categoryId": POKEMON_CATEGORY,
            "sortOrder": "endedRecently",
            "includeCompletedListings": True,
            "exactMatch": True,
        }
        items = http_json(url, method="POST", data=payload,
                          headers={"Content-Type": "application/json"}, timeout=300) or []
        out = []
        for it in items:
            if (it.get("soldCurrency") or "GBP") != "GBP":
                continue
            try:
                total = float(it.get("totalPrice") or it.get("soldPrice"))
            except (TypeError, ValueError):
                continue
            boa = bool(it.get("isBestOfferAccepted"))
            out.append(Listing(
                title=it.get("title", ""),
                price=round(total, 2),
                url=it.get("url", ""),
                date=it.get("endedAt", "")[:10],
                kind="Best offer accepted" if boa else
                     ("Auction" if it.get("listingType") == "auction" else "Buy It Now"),
            ))
        return out


# ----------------------------------------------------------------------------
# Maths and scoring
# ----------------------------------------------------------------------------
def buyer_protection_fee(price):
    """eBay UK Buyer Protection fee (private sellers): GBP0.10 + 7% up to GBP300,
    4% of the part from GBP300-4,000, 2% above GBP4,000. Check current rates on eBay."""
    fee = 0.10 + 0.07 * min(price, 300)
    if price > 300:
        fee += 0.04 * (min(price, 4000) - 300)
    if price > 4000:
        fee += 0.02 * (price - 4000)
    return round(fee, 2)


def clamp(x, lo=0.0, hi=10.0):
    return max(lo, min(hi, x))


def analyse(card, active, sold, *, days=WINDOW_DAYS, listing_age=True,
            include_boa=False, today=None):
    today = today or datetime.now(timezone.utc).date()
    cutoff = (today - timedelta(days=days)).isoformat()
    res = CardResult(card=card)

    sold = [s for s in sold if title_matches(s.title, card) and s.date and s.date >= cutoff]
    if not include_boa:
        boa = [s for s in sold if s.kind == "Best offer accepted"]
        sold = [s for s in sold if s.kind != "Best offer accepted"]
        if boa:
            res.warnings.append(f"{len(boa)} best-offer sale(s) left out (real price hidden by eBay)")
    active = [a for a in active if title_matches(a.title, card)]
    if listing_age:
        active = [a for a in active if not a.date or a.date >= cutoff]

    sold.sort(key=lambda s: s.date, reverse=True)
    active.sort(key=lambda a: a.price)
    res.sales_in_window = len(sold)
    res.active_in_window = len(active)

    if not sold:
        res.verdict = "No UK sales in window"
        res.warnings.append(f"No UK PSA 10 sales in the last {days} days - value unknown")
    if not active:
        res.verdict = res.verdict or "Nothing listed"
    if not sold or not active:
        res.recent_sales, res.cheapest_listings = sold[:5], active[:5]
        if active:
            res.cheapest_listed = active[0]
            res.avg_cheapest5_listed = round(statistics.mean(a.price for a in active[:5]), 2)
        if sold:
            res.cheapest_sold = min(sold, key=lambda s: s.price)
            res.value_last5_sold = round(statistics.mean(s.price for s in sold[:5]), 2)
        return res

    last5 = sold[:5]
    res.recent_sales = last5
    res.sold_used_for_value = len(last5)
    res.value_last5_sold = round(statistics.mean(s.price for s in last5), 2)
    res.cheapest_sold = min(sold, key=lambda s: s.price)
    res.cheapest_listings = active[:5]
    res.avg_cheapest5_listed = round(statistics.mean(a.price for a in active[:5]), 2)
    res.cheapest_listed = active[0]

    if len(last5) < 5:
        res.warnings.append(f"Only {len(last5)} sale(s) in window - value is less reliable")
    median_sold = statistics.median(s.price for s in sold)
    if res.cheapest_listed.price < 0.5 * median_sold:
        res.warnings.append("Cheapest listing is under half the usual sold price - check it's genuine "
                            "(cert number on PSA site, seller feedback, photos)")
    if res.cheapest_listed.kind.startswith("Auction"):
        res.warnings.append("Cheapest is an auction - final price will likely be higher")

    # Profit maths
    buy = res.cheapest_listed.price
    if APPLY_BUYER_FEE and res.cheapest_listed.seller_type != "BUSINESS":
        buy += buyer_protection_fee(res.cheapest_listed.price)
    res.buy_cost = round(buy, 2)
    res.resale_net = round(res.value_last5_sold * (1 - SELL_FEE_PCT) - SELL_FIXED_FEE - POSTAGE_OUT, 2)
    res.profit = round(res.resale_net - res.buy_cost, 2)
    res.margin_pct = round(100 * res.profit / res.buy_cost, 1)
    res.discount_pct = round(100 * (1 - res.cheapest_listed.price / res.value_last5_sold), 1)

    # Price score: 0 at break-even, 10 at 30%+ profit margin
    res.price_score = round(clamp(res.margin_pct / 3.0), 1)

    # Popularity score: sales per 4 weeks (12+ = 10), minus a penalty if there is lots of
    # competing stock compared with how fast it sells
    per_window = res.sales_in_window * (28 / days)
    pop = clamp(per_window * 10 / 12)
    supply_ratio = res.active_in_window / max(per_window, 0.5)   # 4-week periods of stock
    if supply_ratio > 6:
        pop -= 4
    elif supply_ratio > 3:
        pop -= 2
    res.popularity_score = round(clamp(pop), 1)

    res.overall_score = round(0.55 * res.price_score + 0.45 * res.popularity_score, 1)
    if res.profit <= 0:
        res.verdict = "No profit at current prices"
        res.overall_score = min(res.overall_score, 2.5)
    elif per_window < 3:
        res.verdict = "Cheap but hard to sell"
        res.overall_score = min(res.overall_score, 4.0)
    elif res.overall_score >= 7.5:
        res.verdict = "Strong opportunity"
    elif res.overall_score >= 5.5:
        res.verdict = "Good opportunity"
    elif res.overall_score >= 3.5:
        res.verdict = "Marginal"
    else:
        res.verdict = "Weak"
    return res


# ----------------------------------------------------------------------------
# Output
# ----------------------------------------------------------------------------
def money(x):
    if x is None:
        return "-"
    return f"-£{abs(x):,.2f}" if x < 0 else f"£{x:,.2f}"


def write_csv(results, path):
    cols = ["card", "verdict", "overall_score", "price_score", "popularity_score",
            "value_last5_sold", "avg_cheapest5_listed", "cheapest_listed", "cheapest_listed_url",
            "cheapest_sold", "cheapest_sold_date", "sales_in_window", "active_in_window",
            "buy_cost", "resale_net", "profit", "margin_pct", "discount_pct", "warnings"]
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(cols)
        for r in results:
            w.writerow([r.card, r.verdict, r.overall_score, r.price_score, r.popularity_score,
                        r.value_last5_sold, r.avg_cheapest5_listed,
                        r.cheapest_listed.price if r.cheapest_listed else "",
                        r.cheapest_listed.url if r.cheapest_listed else "",
                        r.cheapest_sold.price if r.cheapest_sold else "",
                        r.cheapest_sold.date if r.cheapest_sold else "",
                        r.sales_in_window, r.active_in_window, r.buy_cost, r.resale_net,
                        r.profit, r.margin_pct, r.discount_pct, " | ".join(r.warnings or [r.error])])


def score_class(s):
    return "hi" if s >= 7.5 else "mid" if s >= 5.5 else "lo" if s >= 3.5 else "bad"


def write_html(results, path, *, days, demo=False, title="Watchlist scan", run_link="", other_link=None):
    esc = html.escape
    now = datetime.now().strftime("%d %b %Y %H:%M")
    rows = []
    for r in results:
        def link(l):
            if not l:
                return "-"
            return f'<a href="{esc(l.url)}" target="_blank" rel="noopener">{money(l.price)}</a>'
        sales = "".join(f"<li>{esc(s.date)} · {money(s.price)} · {esc(s.kind)}</li>" for s in r.recent_sales)
        lists = "".join(f'<li><a href="{esc(a.url)}" target="_blank" rel="noopener">{money(a.price)}</a> · '
                        f'{esc(a.title[:70])}</li>' for a in r.cheapest_listings)
        warn = "".join(f"<li>{esc(w)}</li>" for w in r.warnings) if r.warnings else ""
        err = f'<p class="err">{esc(r.error)}</p>' if r.error else ""
        profit = "" if r.profit is None else (
            f'<div class="profit {"pos" if r.profit > 0 else "neg"}">Est. profit {money(r.profit)} '
            f'({r.margin_pct:+.1f}%) · listed {r.discount_pct:.0f}% under value</div>')
        rows.append(f"""
<details class="card" data-score="{r.overall_score}">
 <summary>
  <div class="top"><span class="name">{esc(r.card)}</span>
   <span class="badge {score_class(r.overall_score)}">{r.overall_score:.1f}</span></div>
  <div class="verdict">{esc(r.verdict or r.error)}</div>
  {profit}
  <div class="grid">
   <div><b>Value (last 5 sold)</b>{money(r.value_last5_sold)}</div>
   <div><b>Avg cheapest 5 listed</b>{money(r.avg_cheapest5_listed)}</div>
   <div><b>Cheapest listed</b>{link(r.cheapest_listed)}</div>
   <div><b>Cheapest sold</b>{link(r.cheapest_sold)}</div>
   <div><b>Price score</b>{r.price_score:.1f}/10</div>
   <div><b>Popularity score</b>{r.popularity_score:.1f}/10</div>
   <div><b>Sold ({days}d)</b>{r.sales_in_window}</div>
   <div><b>Listed now</b>{r.active_in_window}</div>
  </div>
 </summary>
 {err}
 {"<ul class='warn'>" + warn + "</ul>" if warn else ""}
 <h4>Last 5 UK sales</h4><ul>{sales or "<li>None</li>"}</ul>
 <h4>Cheapest 5 UK listings</h4><ul>{lists or "<li>None</li>"}</ul>
 <p class="small">Buy cost incl. fees {money(r.buy_cost)} · resale after fees &amp; postage {money(r.resale_net)}</p>
</details>""")
    nav_bits = []
    if run_link:
        nav_bits.append(f'<a class="btn primary" href="{esc(run_link)}">Run a new search</a>')
    if other_link:
        nav_bits.append(f'<a class="btn" href="{esc(other_link[1])}">{esc(other_link[0])}</a>')
    nav = f'<div class="bar">{"".join(nav_bits)}</div>' if nav_bits else ""
    banner = ('<p class="demo">DEMO REPORT – made-up sample data, not real prices.</p>' if demo else "")
    doc = f"""<!DOCTYPE html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>PSA 10 Deal Finder – UK</title>
<style>
:root{{--bg:#f6f5f1;--fg:#1d1d1b;--mut:#6b6a64;--card:#fff;--line:#e4e2da;--hi:#1f7a4d;--mid:#3d6fb6;--lo:#b7791f;--bad:#a33}}
@media (prefers-color-scheme:dark){{:root{{--bg:#151514;--fg:#eceae4;--mut:#9a988f;--card:#1f1f1d;--line:#33322e}}}}
*{{box-sizing:border-box}}body{{margin:0;font:15px/1.45 system-ui,-apple-system,Segoe UI,sans-serif;background:var(--bg);color:var(--fg)}}
main{{max-width:760px;margin:0 auto;padding:16px}}h1{{font-size:22px;margin:4px 0}}.sub{{color:var(--mut);margin:0 0 12px}}
.bar{{display:flex;gap:8px;margin:10px 0 14px;flex-wrap:wrap}}.bar button{{border:1px solid var(--line);background:var(--card);color:var(--fg);padding:6px 10px;border-radius:8px;font:inherit}}
.card{{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:12px 14px;margin-bottom:10px}}
summary{{list-style:none;cursor:pointer}}summary::-webkit-details-marker{{display:none}}
.top{{display:flex;justify-content:space-between;gap:8px;align-items:center}}.name{{font-weight:650;font-size:16px}}
.badge{{color:#fff;border-radius:8px;padding:2px 9px;font-weight:700}}.hi{{background:var(--hi)}}.mid{{background:var(--mid)}}.lo{{background:var(--lo)}}.bad{{background:var(--bad)}}
.verdict{{color:var(--mut);margin:2px 0 6px}}.profit{{font-weight:600;margin-bottom:6px}}.pos{{color:var(--hi)}}.neg{{color:var(--bad)}}
.grid{{display:grid;grid-template-columns:repeat(2,1fr);gap:6px 12px}}@media(min-width:620px){{.grid{{grid-template-columns:repeat(4,1fr)}}}}
.grid b{{display:block;font-size:11px;font-weight:600;color:var(--mut);text-transform:uppercase;letter-spacing:.03em}}
a{{color:var(--mid)}}h4{{margin:12px 0 4px;font-size:13px}}ul{{margin:0;padding-left:18px}}.warn li{{color:var(--lo)}}.small{{color:var(--mut);font-size:13px}}
.err{{color:var(--bad)}}.title2{{margin:0;font-weight:600}}
.btn{{display:inline-block;border:1px solid var(--line);background:var(--card);color:var(--fg);padding:8px 12px;border-radius:8px;text-decoration:none}}
.btn.primary{{background:var(--mid);color:#fff;border-color:var(--mid)}}.demo{{background:#fde8c8;color:#5a3a00;padding:8px 10px;border-radius:8px}}
</style></head><body><main>
<h1>PSA 10 Deal Finder – UK</h1>
<p class="title2">{esc(title)}</p>
{nav}
<p class="sub">Run {esc(now)} UTC · eBay UK data from the last {days} days · tap a card for details · {len(results)} card(s)</p>
{banner}
<div class="bar"><button onclick="srt('score')">Sort by overall</button><button onclick="srt('name')">Sort by A–Z</button></div>
<div id="list">{''.join(rows)}</div>
<p class="small">Value = average of the 5 most recent UK sales. Price score: 0 = break-even, 10 = 30%+ margin after fees and postage.
Popularity score: 12+ UK sales in 4 weeks = 10, reduced when there is a lot of competing stock. Always check the PSA cert number before buying.</p>
</main><script>
function srt(k){{const l=document.getElementById('list');const c=[...l.children];
c.sort((a,b)=>k==='score'?b.dataset.score-a.dataset.score:a.querySelector('.name').textContent.localeCompare(b.querySelector('.name').textContent));
c.forEach(x=>l.appendChild(x));}}
</script></body></html>"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(doc)


def print_table(results, days):
    print(f"\n{'Card':34} {'Score':>5} {'Value':>9} {'Cheapest':>9} {'Profit':>9} {'Sold':>4}  Verdict")
    print("-" * 100)
    for r in results:
        print(f"{r.card[:34]:34} {r.overall_score:5.1f} {money(r.value_last5_sold):>9} "
              f"{money(r.cheapest_listed.price if r.cheapest_listed else None):>9} "
              f"{money(r.profit):>9} {r.sales_in_window:>4}  {r.verdict or r.error}")
    print(f"(Sold = UK sales in the last {days} days)")


# ----------------------------------------------------------------------------
# Demo data (made up, to show what the report looks like)
# ----------------------------------------------------------------------------
def demo_data(today):
    import random
    random.seed(7)
    def d(n): return (today - timedelta(days=n)).isoformat()
    specs = [  # card, typical price, sales/4wk, active count, one bargain discount
        ("Umbreon VMAX 215/203", 1450, 14, 9, 0.18),
        ("Charizard ex 199/165", 330, 22, 25, 0.10),
        ("Pikachu ex 238/191", 410, 9, 6, 0.22),
        ("Giratina V 186/196", 520, 4, 3, 0.25),
        ("Mewtwo & Mew GX 222/236", 460, 1, 4, 0.30),
        ("Iono 254/193", 120, 12, 40, 0.02),
    ]
    data = {}
    for card, p, n_sold, n_active, disc in specs:
        sold = [Listing(f"Pokemon {card} PSA 10 Gem Mint", round(p * random.uniform(0.9, 1.1), 2),
                        "https://www.ebay.co.uk/", d(random.randint(0, 27)),
                        random.choice(["Buy It Now", "Auction"])) for _ in range(n_sold)]
        sold.append(Listing(f"{card} PSA 9 Mint", p * 0.4, "https://www.ebay.co.uk/", d(2)))  # filtered out
        active = [Listing(f"{card} PSA 10 Pokemon TCG", round(p * random.uniform(1.0, 1.25), 2),
                          "https://www.ebay.co.uk/", d(random.randint(0, 27)), "Buy It Now",
                          random.choice(["INDIVIDUAL", "BUSINESS"])) for _ in range(n_active)]
        active.append(Listing(f"{card} PSA 10", round(p * (1 - disc), 2), "https://www.ebay.co.uk/",
                              d(1), "Buy It Now", "INDIVIDUAL"))
        data[card] = (active, sold)
    return data


# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------
def load_watchlist(path):
    with open(path, encoding="utf-8") as f:
        return [ln.strip() for ln in f if ln.strip() and not ln.lstrip().startswith("#")]


def main():
    global SELL_FEE_PCT, POSTAGE_OUT
    ap = argparse.ArgumentParser(description="Find undervalued PSA 10 Pokemon cards on eBay UK.")
    ap.add_argument("cards", nargs="*", help='Card searches, e.g. "Umbreon VMAX 215/203"')
    ap.add_argument("--watchlist", "-w", help="Text file with one card per line")
    ap.add_argument("--cards-csv", default="", help="Cards separated by commas or new lines")
    ap.add_argument("--title", default="Watchlist scan", help="Heading for the report")
    ap.add_argument("--run-link", default="", help="Link for the 'Run a new search' button")
    ap.add_argument("--other-link", nargs=2, metavar=("LABEL", "URL"), help="Extra link on the report")
    ap.add_argument("--days", type=int, default=WINDOW_DAYS, help="Look-back window in days (default 28)")
    ap.add_argument("--include-auctions", action="store_true", help="Include live auctions in 'listed'")
    ap.add_argument("--include-old-listings", action="store_true",
                    help="Also count listings created more than --days ago")
    ap.add_argument("--include-best-offers", action="store_true",
                    help="Count best-offer sales (eBay shows the asking price, not the accepted price)")
    ap.add_argument("--sell-fee", type=float, default=SELL_FEE_PCT, help="Your selling fee as a fraction, e.g. 0.128")
    ap.add_argument("--postage", type=float, default=POSTAGE_OUT, help="Your postage cost when reselling (GBP)")
    ap.add_argument("--min-score", type=float, default=0, help="Only show cards scoring at least this")
    ap.add_argument("--out", default="psa10_report", help="Output file name (without extension)")
    ap.add_argument("--demo", action="store_true", help="Run on made-up sample data (no API keys needed)")
    a = ap.parse_args()
    SELL_FEE_PCT, POSTAGE_OUT = a.sell_fee, a.postage
    today = datetime.now(timezone.utc).date()

    results = []
    if a.demo:
        for card, (active, sold) in demo_data(today).items():
            results.append(analyse(card, active, sold, days=a.days, today=today))
    else:
        cards = list(a.cards)
        if a.watchlist:
            cards += load_watchlist(a.watchlist)
        cards += [c.strip() for c in re.split(r"[,\n;]", a.cards_csv) if c.strip()]
        if not cards:
            ap.error("give card names or --watchlist cards.txt (or --demo)")
        need = [k for k in ("EBAY_CLIENT_ID", "EBAY_CLIENT_SECRET", "APIFY_TOKEN") if not os.environ.get(k)]
        if need:
            sys.exit("Missing settings: " + ", ".join(need) + "  (see README.md)")
        ebay = EbayBrowse(os.environ["EBAY_CLIENT_ID"], os.environ["EBAY_CLIENT_SECRET"])
        apify = ApifySold(os.environ["APIFY_TOKEN"])
        for i, card in enumerate(cards, 1):
            print(f"[{i}/{len(cards)}] {card} ...", flush=True)
            try:
                active = ebay.search(card, include_auctions=a.include_auctions)
                sold = apify.search(card, a.days)
                results.append(analyse(card, active, sold, days=a.days,
                                       listing_age=not a.include_old_listings,
                                       include_boa=a.include_best_offers, today=today))
            except Exception as e:  # keep going with the other cards
                results.append(CardResult(card=card, error=str(e)))

    results = [r for r in results if r.overall_score >= a.min_score or r.error]
    results.sort(key=lambda r: (r.overall_score, r.profit or -1e9), reverse=True)
    print_table(results, a.days)
    out_dir = os.path.dirname(a.out)
    if out_dir:
        os.makedirs(out_dir, exist_ok=True)
    write_csv(results, a.out + ".csv")
    write_html(results, a.out + ".html", days=a.days, demo=a.demo, title=a.title,
               run_link=a.run_link, other_link=tuple(a.other_link) if a.other_link else None)
    print(f"\nSaved {a.out}.html and {a.out}.csv")


if __name__ == "__main__":
    main()
