"""
SHEIN Sheinverse Product Alert Bot — v17
=========================================
WHAT'S NEW IN v17:
  - Real per-size stock detection via HTML page scraping ✓
  - Parses window.__PRELOADED_STATE__ from product page HTML ✓
  - Shows actual sizes in alerts (XS, S, M, L, XL, XXL) ✓
  - HTML only fetched for NEW products — cycles stay fast ✓
  - Restock alert fetches HTML for accurate sizes ✓
  - Disappeared products marked OOS → reappearance fires restock ✓
  - Min interval warning if < 60s ✓
  - All v16 fixes preserved ✓

HOW IT WORKS:
  1. Listing API → all products fast (JSON, no size data)
  2. NEW products only → fetch HTML → parse __PRELOADED_STATE__
  3. Extract variantOptions with real stockLevelStatus per size
  4. Show sizes like: XS • S • M • L in alert messages

ENV VARS REQUIRED:
  BOT_TOKEN        - Telegram bot token
  ADMIN_USER_ID    - Your Telegram user ID (numeric)

ENV VARS OPTIONAL:
  ALERT_CHANNEL_1  - default @shein30sec
  ALERT_CHANNEL_2  - default @helpinghands2s
  ALERT_GROUP_ID   - Your group chat ID e.g. -1001234567890
"""

import os
import io
import re
import sys
import json
import time
import asyncio
import traceback
import requests
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime

from telegram import (
    Update, BotCommand, BotCommandScopeDefault,
    InlineKeyboardButton, InlineKeyboardMarkup,
)
from telegram.ext import (
    ApplicationBuilder, CommandHandler, CallbackQueryHandler,
    ContextTypes, Application,
)
from telegram.error import TelegramError

# ── COLOURS ───────────────────────────────────────────────────────────────────
GREEN  = "\033[92m"
RED    = "\033[91m"
CYAN   = "\033[96m"
YELLOW = "\033[93m"
RESET  = "\033[0m"

# ── CONFIG ────────────────────────────────────────────────────────────────────
BOT_TOKEN     = os.environ["BOT_TOKEN"]
ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", "0"))

BASE_URL     = "https://www.sheinindia.in"
CATEGORY_API = BASE_URL + "/api/category/sverse-5939-37961"

# Alert destinations
CHANNEL_1 = os.environ.get("ALERT_CHANNEL_1", "@shein30sec")
CHANNEL_2 = os.environ.get("ALERT_CHANNEL_2", "@helpinghands2s")
REQUIRED_CHANNELS = [CHANNEL_1, CHANNEL_2]

_group_id = os.environ.get("ALERT_GROUP_ID", "").strip()
ALERT_CHANNELS: list[str] = [CHANNEL_1, CHANNEL_2]
if _group_id:
    ALERT_CHANNELS.append(_group_id)

# ── FETCH SETTINGS ────────────────────────────────────────────────────────────
PAGE_SIZE          = 45
FETCH_WORKERS      = 8
PAGE_RETRIES       = 3
HTML_FETCH_WORKERS = 8    # parallel workers for product HTML scraping
HTML_TIMEOUT       = 20   # seconds per HTML page
MIN_INTERVAL       = 60   # warn if interval set below this

# ── STOCK STATUSES ────────────────────────────────────────────────────────────
_IN_STOCK_STATUSES = {"inStock", "lowStock"}

# ── SORT MODES ────────────────────────────────────────────────────────────────
SORT_RELEVANCE     = "relevance"
SORT_DISCOUNT_DESC = "discount-desc"

# ── CATEGORY FILE RULES ───────────────────────────────────────────────────────
CATEGORY_RULES = [
    (lambda s, b: s == "Women" and ("Jeans" in b or "Jeggings" in b),    "women_jeans.txt"),
    (lambda s, b: s == "Women" and b == "Tops",                           "women_tops.txt"),
    (lambda s, b: s == "Women" and b == "Tshirts",                        "women_tshirts.txt"),
    (lambda s, b: s == "Women" and b == "Shirts",                         "women_shirts.txt"),
    (lambda s, b: s == "Women" and b == "Dresses",                        "women_dresses.txt"),
    (lambda s, b: s == "Women" and ("Trousers" in b or "Pants" in b),    "women_trousers.txt"),
    (lambda s, b: s == "Women" and "Sweatshirt" in b,                    "women_hoodies.txt"),
    (lambda s, b: s == "Women" and "Track" in b,                         "women_trackpants.txt"),
    (lambda s, b: s == "Women" and ("Jumpsuit" in b or "Playsuit" in b), "women_jumpsuits.txt"),
    (lambda s, b: s == "Women" and "Skirt" in b,                         "women_skirts.txt"),
    (lambda s, b: s == "Women" and ("Night" in b or "Lounge" in b),      "women_nightwear.txt"),
    (lambda s, b: s == "Women" and "Shapewear" in b,                     "women_lingerie.txt"),
    (lambda s, b: s == "Women" and b.strip() in ("Co", "Co-ords"),       "women_coords.txt"),
    (lambda s, b: s == "Women" and "Earring" in b,                       "women_jewellery.txt"),
    (lambda s, b: s == "Women" and "Necklace" in b,                      "women_jewellery.txt"),
    (lambda s, b: s == "Women" and "Bracelet" in b,                      "women_jewellery.txt"),
    (lambda s, b: s == "Men"   and ("Jeans" in b or "Jeggings" in b),    "men_jeans.txt"),
    (lambda s, b: s == "Men"   and b == "Tshirts",                       "men_tshirts.txt"),
    (lambda s, b: s == "Men"   and b == "Shirts",                        "men_shirts.txt"),
    (lambda s, b: s == "Men"   and "Track" in b,                         "men_trackpants.txt"),
    (lambda s, b: s == "Men"   and ("Trousers" in b or "Pants" in b),    "men_trousers.txt"),
    (lambda s, b: s == "Men"   and "Sweatshirt" in b,                    "men_hoodies.txt"),
    (lambda s, b: s == "Men"   and b == "Tops",                          "men_tops.txt"),
]
OTHER_FILE = "other_products.txt"

# ── GLOBAL STATE ──────────────────────────────────────────────────────────────
_stock_snapshot: dict[str, dict[str, str]] = {}
_alerted_new:   set[str]                   = set()
_known_codes:   set[str]                   = set()

_state = {
    "sort_mode":            SORT_DISCOUNT_DESC,
    "interval":             300,

    "monitor_started":      None,
    "monitor_running":      False,
    "is_first_cycle":       True,

    "polls_done":           0,
    "new_alerts_sent":      0,
    "restock_alerts_sent":  0,
    "sendlinks_runs":       0,

    "fc_total":             0,
    "fc_in_stock":          0,
    "fc_oos":               0,
    "fc_done":              False,

    "last_poll_time":       None,
    "last_listing_secs":    0.0,
    "last_html_secs":       0.0,
    "last_total_products":  0,
    "last_new_alerted":     0,
    "last_restock_alerted": 0,
    "last_html_fetched":    0,
}

_monitor_task: asyncio.Task | None = None

# ── HTTP SESSION — Listing API (JSON) ────────────────────────────────────────
_http = requests.Session()
_http.mount("https://", requests.adapters.HTTPAdapter(
    pool_connections=40, pool_maxsize=40, max_retries=2,
))
_http.headers.update({
    "user-agent":       (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/146.0.0.0 Safari/537.36"
    ),
    "accept":           "application/json, text/plain, */*",
    "accept-language":  "en-IN,en-GB;q=0.9,en-US;q=0.8,en;q=0.7",
    "accept-encoding":  "gzip, deflate, br",
    "x-tenant-id":      "SHEIN",
    "x-requested-with": "XMLHttpRequest",
    "origin":           "https://www.sheinindia.in",
    "referer":          "https://www.sheinindia.in/c/sverse-5939-37961",
    "sec-fetch-dest":   "empty",
    "sec-fetch-mode":   "cors",
    "sec-fetch-site":   "same-origin",
})

# ── HTTP SESSION — Product HTML scraping ──────────────────────────────────────
_html_http = requests.Session()
_html_http.mount("https://", requests.adapters.HTTPAdapter(
    pool_connections=40, pool_maxsize=40, max_retries=2,
))
_html_http.headers.update({
    "user-agent":       (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/146.0.0.0 Safari/537.36"
    ),
    "accept":           "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "accept-language":  "en-US,en;q=0.9",
    "accept-encoding":  "gzip, deflate, br",
    "sec-fetch-dest":   "document",
    "sec-fetch-mode":   "navigate",
    "referer":          "https://www.sheinindia.in/c/sverse-5939-37961",
})

# =============================================================================
# LISTING API
# NOTE: SHEIN India uses 0-based page index!
#   currentPage=0 → first page (products 1-45)
#   currentPage=1 → second page (products 46-90)
#   etc.
# =============================================================================

def _build_params(page: int, sort_mode: str) -> dict:
    """
    page is 0-indexed:
      page=0 → first page
      page=1 → second page
    """
    return {
        "fields":         "SITE",
        "currentPage":    page,          # 0-indexed!
        "pageSize":       PAGE_SIZE,
        "format":         "json",
        "query":          f":{sort_mode}",
        "sort":           sort_mode,
        "store":          "shein",
        "tagV2Enabled":   "true",
        "tagExperiment":  "A",
        "platform":       "Desktop",
        "displayRatings": "true",
        "gridColumns":    "5",
        "advfilter":      "true",
        "showAdsOnNextPage": "false",
        "is_ads_enable_plp": "true",
    }


def _fetch_listing_page(page: int, sort_mode: str) -> tuple[dict, int | None]:
    """Fetch a single listing page with retries. page is 0-indexed."""
    for attempt in range(PAGE_RETRIES + 1):
        try:
            r = _http.get(
                CATEGORY_API,
                params=_build_params(page, sort_mode),
                timeout=25,
            )
            if r.status_code == 200:
                data = r.json()
                products = data.get("products", [])
                print(f"{GREEN}[listing] page={page} → {len(products)} products{RESET}")
                return data, 200
            print(f"{RED}[listing] page={page} HTTP {r.status_code} attempt={attempt+1}{RESET}")
        except Exception as exc:
            print(f"{RED}[listing] page={page} error={exc} attempt={attempt+1}{RESET}")
        if attempt < PAGE_RETRIES:
            time.sleep(2)
    return {}, None


def _fetch_all_products(sort_mode: str) -> tuple[list | None, str | None]:
    """
    Fetch ALL products across all pages.
    Page 0 = first page (SHEIN India is 0-indexed).
    """
    t0 = time.monotonic()

    # Fetch page 0 first to get pagination info
    data, status = _fetch_listing_page(0, sort_mode)
    if status != 200 or not data:
        return None, f"Listing API failed on page 0 (HTTP {status})"

    pagination  = data.get("pagination", {})
    total_pages = pagination.get("totalPages", 1)
    total_res   = pagination.get("totalResults", 0)

    print(f"{CYAN}[listing] totalResults={total_res} totalPages={total_pages} sort={sort_mode}{RESET}")
    print(f"{CYAN}[listing] Pages are 0-indexed: fetching pages 0 to {total_pages - 1}{RESET}")

    all_products = list(data.get("products", []))

    if total_pages > 1:
        # Fetch pages 1, 2, ... (total_pages - 1) in parallel
        with ThreadPoolExecutor(max_workers=FETCH_WORKERS) as pool:
            futures = {
                pool.submit(_fetch_listing_page, pg, sort_mode): pg
                for pg in range(1, total_pages)
            }
            for future in as_completed(futures):
                pg = futures[future]
                try:
                    page_data, st = future.result()
                    if st == 200 and page_data:
                        products = page_data.get("products", [])
                        all_products.extend(products)
                        print(f"{GREEN}[listing] page={pg} added {len(products)} products{RESET}")
                    else:
                        print(f"{RED}[listing] page={pg} FAILED (status={st}){RESET}")
                except Exception as exc:
                    print(f"{RED}[listing] page={futures[future]} exception: {exc}{RESET}")

    elapsed = time.monotonic() - t0
    print(f"{GREEN}[listing] TOTAL: {len(all_products)} products fetched in {elapsed:.1f}s{RESET}")
    return all_products, None


# =============================================================================
# HTML PAGE SCRAPING — real size/stock data from __PRELOADED_STATE__
# =============================================================================

def _fetch_product_html_details(url_path: str) -> dict | None:
    """
    Fetch product HTML page, extract window.__PRELOADED_STATE__,
    return productDetails dict (which has variantOptions with real stock).
    """
    url = BASE_URL + url_path
    try:
        r = _html_http.get(url, timeout=HTML_TIMEOUT)
        if r.status_code != 200:
            print(f"{YELLOW}[html] HTTP {r.status_code} for {url_path}{RESET}")
            return None

        html = r.text

        # Find window.__PRELOADED_STATE__ = { ... };
        match = re.search(
            r"window\.__PRELOADED_STATE__\s*=\s*(\{)",
            html,
        )
        if not match:
            print(f"{YELLOW}[html] __PRELOADED_STATE__ not found for {url_path}{RESET}")
            return None

        start = match.start(1)

        # Walk the string to find the matching closing brace
        depth   = 0
        end_pos = start
        in_str  = False
        escape  = False
        for i in range(start, len(html)):
            ch = html[i]
            if escape:
                escape = False
                continue
            if ch == "\\" and in_str:
                escape = True
                continue
            if ch == '"' and not escape:
                in_str = not in_str
            if not in_str:
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        end_pos = i + 1
                        break

        raw   = html[start:end_pos]
        state = json.loads(raw)
        return state.get("product", {}).get("productDetails", {})

    except json.JSONDecodeError as exc:
        print(f"{YELLOW}[html] JSON error for {url_path}: {exc}{RESET}")
        return None
    except Exception as exc:
        print(f"{RED}[html] Error for {url_path}: {exc}{RESET}")
        return None


def _extract_stock_map_from_details(details: dict) -> dict[str, str]:
    """
    Extract {size_label: stockLevelStatus} from productDetails.variantOptions.
    variantOptions has per-size real stock data with scDisplaySize labels.
    """
    stock_map: dict[str, str] = {}

    # Primary: variantOptions — has real per-size stock
    variant_options = details.get("variantOptions", [])
    if variant_options:
        for variant in variant_options:
            status = variant.get("stock", {}).get("stockLevelStatus", "outOfStock")
            label  = variant.get("scDisplaySize", "").strip()
            if not label:
                for q in variant.get("variantOptionQualifiers", []):
                    if str(q.get("qualifier", "")).lower() == "size":
                        label = str(q.get("value", "")).strip()
                        break
            if label:
                stock_map[label] = status
        return stock_map

    # Fallback: top-level stock
    top_status = details.get("stock", {}).get("stockLevelStatus", "outOfStock")
    stock_map["__product__"] = top_status
    return stock_map


def _fetch_real_stock_map(product: dict) -> dict[str, str]:
    """
    Fetch and return a real stock map for a product via HTML scraping.
    Falls back to listing sentinel if HTML fetch fails.
    """
    url_path = product.get("url", "").strip()
    if not url_path:
        return {"__listed__": "inStock"}

    details = _fetch_product_html_details(url_path)
    if not details:
        return {"__listed__": "inStock"}

    stock_map = _extract_stock_map_from_details(details)
    return stock_map if stock_map else {"__listed__": "inStock"}


def _fetch_real_stock_maps_parallel(products: list[dict]) -> dict[str, dict[str, str]]:
    """
    Fetch real stock maps for a list of products in parallel.
    Returns {product_code: stock_map}.
    """
    results: dict[str, dict[str, str]] = {}
    if not products:
        return results

    with ThreadPoolExecutor(max_workers=HTML_FETCH_WORKERS) as pool:
        future_to_code = {
            pool.submit(_fetch_real_stock_map, p): p.get("code", "")
            for p in products
            if p.get("code") and p.get("url")
        }
        for future in as_completed(future_to_code):
            code = future_to_code[future]
            try:
                stock_map = future.result()
                results[code] = stock_map
                real = {k: v for k, v in stock_map.items() if not k.startswith("__")}
                in_s = [k for k, v in real.items() if v in _IN_STOCK_STATUSES]
                print(f"{GREEN}[html] {code}: sizes={list(real.keys())} in_stock={in_s}{RESET}")
            except Exception as exc:
                print(f"{RED}[html] {code} exception: {exc}{RESET}")
                results[code] = {"__listed__": "inStock"}

    return results


# =============================================================================
# LISTING-ONLY STOCK MAP (fallback when HTML fails)
# =============================================================================

def _get_variant_stock_map_from_listing(product: dict) -> dict[str, str]:
    """
    Extract stock map from listing API data.
    Listing API normally has NO variantOptions — returns sentinel.
    Product appearing in listing = available.
    """
    variants = product.get("variantOptions", []) or product.get("variants", [])
    if variants:
        stock_map: dict[str, str] = {}
        for variant in variants:
            status = variant.get("stock", {}).get("stockLevelStatus", "outOfStock")
            label  = variant.get("scDisplaySize", "").strip()
            if not label:
                for q in variant.get("variantOptionQualifiers", []):
                    if str(q.get("qualifier", "")).lower() == "size":
                        label = str(q.get("value", "")).strip()
                        break
            if label:
                stock_map[label] = status
        if stock_map:
            return stock_map
    return {"__listed__": "inStock"}


# =============================================================================
# PRODUCT HELPERS
# =============================================================================

def _get_product_url(product: dict) -> str:
    return product.get("url", "")


def _get_product_image(product: dict) -> str | None:
    outfit = product.get("fnlColorVariantData", {}).get("outfitPictureURL")
    if outfit:
        return outfit
    for img in product.get("images", []):
        if img.get("format") == "productGrid3ListingImage":
            return img.get("url")
    images = product.get("images", [])
    return images[0].get("url") if images else None


# Natural clothing size order
_SIZE_ORDER = ["XXS", "XS", "S", "M", "L", "XL", "XXL", "XXXL", "3XL", "4XL"]

def _sort_sizes(sizes: list[str]) -> list[str]:
    def key(s):
        try:
            return (_SIZE_ORDER.index(s.upper()), s)
        except ValueError:
            return (99, s)
    return sorted(sizes, key=key)


def _fmt_sizes(sizes: list[str]) -> str:
    if not sizes:
        return "—"
    display = [s for s in sizes if not s.startswith("__")]
    if not display:
        return "Check site"
    return " • ".join(_sort_sizes(display))


def _format_new_alert(product: dict, stock_map: dict[str, str]) -> str:
    name     = product.get("name", "Unknown Product")
    segment  = product.get("segmentNameText", "")
    brick    = product.get("brickNameText", "")
    category = f"{segment} › {brick}" if segment and brick else segment or brick
    discount = product.get("discountPercent", "")
    price    = product.get("price", {}).get("displayformattedValue", "")
    mrp      = product.get("wasPriceData", {}).get("displayformattedValue", "")
    offer    = product.get("offerPrice", {}).get("displayformattedValue", "")
    url      = BASE_URL + _get_product_url(product)

    in_stock_sizes = [
        s for s, st in stock_map.items()
        if st in _IN_STOCK_STATUSES and not s.startswith("__")
    ]

    lines = [
        "✨🆕 *NEW ARRIVAL — SHEINVERSE!* 🛍️✨", "",
        f"👗 *{name}*",
        f"🏷️ Category: _{category}_", "",
        f"💰 Selling Price: *{price}*",
    ]
    if mrp and mrp != price:
        lines.append(f"💸 MRP: {mrp}")
    if discount:
        lines.append(f"🔥 Discount: *{discount}*")
    if offer and offer != price:
        lines.append(f"🎟️ With coupon: *{offer}*")

    if in_stock_sizes:
        lines.append(f"📐 Sizes in stock: `{_fmt_sizes(in_stock_sizes)}`")
    else:
        lines.append("📐 Sizes: Check site for availability")

    lines += ["", f"🛒 [Grab It Now!]({url})", "", "⚡ _Hurry — limited stock!_"]
    return "\n".join(lines)


def _format_restock_alert(product: dict, stock_map: dict[str, str]) -> str:
    name     = product.get("name", "Unknown Product")
    segment  = product.get("segmentNameText", "")
    brick    = product.get("brickNameText", "")
    category = f"{segment} › {brick}" if segment and brick else segment or brick
    discount = product.get("discountPercent", "")
    price    = product.get("price", {}).get("displayformattedValue", "")
    mrp      = product.get("wasPriceData", {}).get("displayformattedValue", "")
    offer    = product.get("offerPrice", {}).get("displayformattedValue", "")
    url      = BASE_URL + _get_product_url(product)

    in_stock_sizes = [
        s for s, st in stock_map.items()
        if st in _IN_STOCK_STATUSES and not s.startswith("__")
    ]

    lines = [
        "🚀🔄 *BACK IN STOCK — ACT FAST!* 🎉🔥", "",
        f"👚 *{name}*",
        f"🏷️ Category: _{category}_", "",
        f"💰 Selling Price: *{price}*",
    ]
    if mrp and mrp != price:
        lines.append(f"💸 MRP: {mrp}")
    if discount:
        lines.append(f"🔥 Discount: *{discount}*")
    if offer and offer != price:
        lines.append(f"🎟️ With coupon: *{offer}*")

    if in_stock_sizes:
        lines.append(f"✅ Sizes now available: `{_fmt_sizes(in_stock_sizes)}`")
    else:
        lines.append("✅ Back in stock — check site for sizes")

    lines += ["", f"🛒 [Shop Now — Before It's Gone!]({url})", "", "⚡ _Stock is limited — move quick!_"]
    return "\n".join(lines)


def _categorize(products: list[dict]) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    seen:   dict[str, set[str]]  = {}
    for product in products:
        path = product.get("url", "").strip()
        if not path:
            continue
        full_url     = BASE_URL + path
        segment      = product.get("segmentNameText", "")
        brick        = product.get("brickNameText", "")
        matched_file = OTHER_FILE
        for matcher, filename in CATEGORY_RULES:
            try:
                if matcher(segment, brick):
                    matched_file = filename
                    break
            except Exception:
                pass
        result.setdefault(matched_file, [])
        seen.setdefault(matched_file, set())
        if full_url not in seen[matched_file]:
            result[matched_file].append(full_url)
            seen[matched_file].add(full_url)
    return result


# =============================================================================
# TELEGRAM SEND HELPER
# =============================================================================

async def _send_alert(app: Application, caption: str, image_url: str | None, code: str) -> bool:
    sent_ok = False
    for ch in ALERT_CHANNELS:
        try:
            if image_url:
                await app.bot.send_photo(
                    chat_id=ch, photo=image_url,
                    caption=caption, parse_mode="Markdown",
                )
            else:
                await app.bot.send_message(
                    chat_id=ch, text=caption,
                    parse_mode="Markdown", disable_web_page_preview=False,
                )
            sent_ok = True
            print(f"{GREEN}[alert] ✓ sent to {ch} | {code}{RESET}")
            await asyncio.sleep(0.5)
        except TelegramError as exc:
            print(f"{RED}[alert] ✗ FAILED → {ch} | {code}: {exc}{RESET}")
        except Exception as exc:
            print(f"{RED}[alert] ✗ EXCEPTION → {ch} | {code}: {exc}{RESET}")
    return sent_ok


# =============================================================================
# MEMBERSHIP CHECK
# =============================================================================

async def _check_single_channel(bot, user_id: int, channel: str) -> bool:
    try:
        member = await bot.get_chat_member(chat_id=channel, user_id=user_id)
        return member.status not in ("left", "kicked", "banned")
    except TelegramError:
        return True


async def _get_missing_channels(bot, user_id: int) -> list[str]:
    return [ch for ch in REQUIRED_CHANNELS if not await _check_single_channel(bot, user_id, ch)]


def _join_keyboard(missing: list[str]) -> InlineKeyboardMarkup | None:
    buttons = [
        [InlineKeyboardButton(f"📢 Join {ch}", url=f"https://t.me/{ch.lstrip('@')}")]
        for ch in missing
    ]
    return InlineKeyboardMarkup(buttons) if buttons else None


def _is_admin(uid: int) -> bool:
    return uid == ADMIN_USER_ID


# =============================================================================
# MONITOR — FIRST CYCLE
# =============================================================================

async def _run_first_cycle(app: Application, products: list[dict]):
    """
    Seed snapshot and send alerts for all in-stock products.
    Fetches real size data via HTML scraping for every product.
    ALWAYS sets fc_done=True at the end.
    """
    global _stock_snapshot, _alerted_new, _known_codes

    total          = len(products)
    in_stock_count = 0
    oos_count      = 0

    print(f"{CYAN}[first-cycle] Starting — {total} products | fetching HTML for real sizes...{RESET}")
    t0 = time.monotonic()

    try:
        # Fetch real stock maps for ALL products in parallel via HTML
        html_t0    = time.monotonic()
        print(f"{CYAN}[first-cycle] Parallel HTML fetch ({HTML_FETCH_WORKERS} workers)...{RESET}")
        stock_maps = await asyncio.to_thread(_fetch_real_stock_maps_parallel, products)
        html_elapsed = time.monotonic() - html_t0
        _state["last_html_secs"]    = round(html_elapsed, 1)
        _state["last_html_fetched"] = len(stock_maps)
        print(f"{GREEN}[first-cycle] HTML done in {html_elapsed:.1f}s — {len(stock_maps)} maps{RESET}")

        for i, product in enumerate(products):
            try:
                code = product.get("code", "")
                if not code:
                    continue

                _known_codes.add(code)

                # Use real HTML stock map, fall back to listing sentinel
                stock_map = stock_maps.get(code) or _get_variant_stock_map_from_listing(product)
                _stock_snapshot[code] = stock_map

                in_stock_sizes = [
                    size for size, status in stock_map.items()
                    if status in _IN_STOCK_STATUSES
                ]

                name = product.get("name", "?")[:40]
                if in_stock_sizes:
                    real = [s for s in in_stock_sizes if not s.startswith("__")]
                    print(f"{GREEN}[first-cycle] [{i+1}/{total}] IN STOCK: {code} | {name} | {real or 'available'}{RESET}")
                    caption   = _format_new_alert(product, stock_map)
                    image_url = _get_product_image(product)
                    sent_ok   = await _send_alert(app, caption, image_url, code)
                    _alerted_new.add(code)
                    if sent_ok:
                        _state["new_alerts_sent"] += 1
                    in_stock_count += 1
                else:
                    print(f"{YELLOW}[first-cycle] [{i+1}/{total}] OOS: {code} | {name}{RESET}")
                    _alerted_new.add(code)
                    oos_count += 1

            except Exception as exc:
                print(f"{RED}[first-cycle] Error on product index {i}: {exc}{RESET}")
                traceback.print_exc()
                continue

    except Exception as exc:
        print(f"{RED}[first-cycle] FATAL exception: {exc}{RESET}")
        traceback.print_exc()

    finally:
        elapsed = time.monotonic() - t0
        _state["fc_total"]    = total
        _state["fc_in_stock"] = in_stock_count
        _state["fc_oos"]      = oos_count
        _state["fc_done"]     = True

        print(
            f"{GREEN}[first-cycle] COMPLETE in {elapsed:.1f}s | "
            f"total={total} in_stock={in_stock_count} oos={oos_count} "
            f"tracked={len(_known_codes)}{RESET}"
        )


# =============================================================================
# MONITOR LOOP
# =============================================================================

async def _monitor_loop(app: Application):
    global _stock_snapshot, _alerted_new, _known_codes

    _state["monitor_running"] = True
    _state["monitor_started"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    _state["is_first_cycle"]  = True

    print(f"{GREEN}[monitor] Started v17 | sort={_state['sort_mode']} interval={_state['interval']}s{RESET}")
    print(f"{GREEN}[monitor] Alert destinations: {ALERT_CHANNELS}{RESET}")
    print(f"{GREEN}[monitor] HTML scraping: {HTML_FETCH_WORKERS} workers, {HTML_TIMEOUT}s timeout{RESET}")

    if _state["interval"] < MIN_INTERVAL:
        print(f"{YELLOW}[monitor] WARNING: interval={_state['interval']}s is below {MIN_INTERVAL}s. "
              f"Recommended 60-300s for HTML scraping.{RESET}")

    if not _group_id:
        print(f"{YELLOW}[monitor] WARNING: ALERT_GROUP_ID not set!{RESET}")

    try:
        while True:
            # Wait for next cycle
            print(f"{CYAN}[monitor] Sleeping {_state['interval']}s...{RESET}")
            await asyncio.sleep(_state["interval"])

            # Fetch all products
            t0 = time.monotonic()
            try:
                products, error = await asyncio.to_thread(
                    _fetch_all_products, _state["sort_mode"]
                )
            except Exception as exc:
                print(f"{RED}[monitor] Fetch exception: {exc}{RESET}")
                traceback.print_exc()
                continue

            if error or not products:
                print(f"{RED}[monitor] Fetch failed: {error}{RESET}")
                continue

            listing_elapsed = time.monotonic() - t0
            _state["last_listing_secs"]   = round(listing_elapsed, 1)
            _state["last_total_products"] = len(products)
            _state["last_poll_time"]      = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

            print(f"{CYAN}[monitor] Fetched {len(products)} products in {listing_elapsed:.1f}s{RESET}")

            # ── FIRST CYCLE ──────────────────────────────────────────────────
            if _state["is_first_cycle"]:
                _state["is_first_cycle"] = False
                print(f"{CYAN}[monitor] Running first cycle...{RESET}")
                await _run_first_cycle(app, products)
                print(f"{CYAN}[monitor] First cycle complete. Tracked={len(_known_codes)}{RESET}")
                continue

            # ── SUBSEQUENT CYCLES ────────────────────────────────────────────
            _state["polls_done"] += 1

            # Build code → product map
            current_map: dict[str, dict] = {}
            for p in products:
                code = p.get("code", "")
                if code and code not in current_map:
                    current_map[code] = p
            current_codes = set(current_map.keys())

            # Find brand-new products (never seen before)
            new_product_codes = [c for c in current_codes if c not in _known_codes]

            # ── HTML FETCH FOR NEW PRODUCTS ───────────────────────────────
            new_stock_maps: dict[str, dict[str, str]] = {}
            if new_product_codes:
                new_products_list = [current_map[c] for c in new_product_codes]
                print(f"{CYAN}[monitor] {len(new_product_codes)} new products — fetching HTML...{RESET}")
                html_t0 = time.monotonic()
                new_stock_maps = await asyncio.to_thread(
                    _fetch_real_stock_maps_parallel, new_products_list
                )
                html_elapsed_inner = time.monotonic() - html_t0
                _state["last_html_fetched"] = len(new_product_codes)
                _state["last_html_secs"]    = round(html_elapsed_inner, 1)
                print(f"{GREEN}[monitor] HTML done in {html_elapsed_inner:.1f}s{RESET}")
            else:
                _state["last_html_fetched"] = 0
                _state["last_html_secs"]    = 0.0

            new_alerted     = 0
            restock_alerted = 0

            for code, product in current_map.items():
                old_stock_map = _stock_snapshot.get(code, {})
                is_brand_new  = code not in _known_codes

                if is_brand_new:
                    # ── NEW PRODUCT — use HTML stock map ──────────────────
                    _known_codes.add(code)
                    stock_map = new_stock_maps.get(code) or _get_variant_stock_map_from_listing(product)
                    _stock_snapshot[code] = stock_map

                    in_stock_sizes = [
                        size for size, status in stock_map.items()
                        if status in _IN_STOCK_STATUSES
                    ]

                    if in_stock_sizes:
                        real = [s for s in in_stock_sizes if not s.startswith("__")]
                        name = product.get("name", "?")[:40]
                        print(f"{GREEN}[monitor] NEW: {code} | {name} | sizes={real or 'available'}{RESET}")
                        caption   = _format_new_alert(product, stock_map)
                        image_url = _get_product_image(product)
                        sent_ok   = await _send_alert(app, caption, image_url, code)
                        _alerted_new.add(code)
                        if sent_ok:
                            _state["new_alerts_sent"] += 1
                            new_alerted += 1
                    else:
                        _alerted_new.add(code)
                        print(f"{YELLOW}[monitor] New but OOS: {code}{RESET}")

                else:
                    # ── KNOWN PRODUCT — restock detection ─────────────────
                    # Update listing sentinel for this cycle
                    listing_map = _get_variant_stock_map_from_listing(product)

                    # Was product OOS (disappeared) and now back?
                    old_was_oos = old_stock_map and not any(
                        st in _IN_STOCK_STATUSES for st in old_stock_map.values()
                    )
                    now_in_stock = any(
                        st in _IN_STOCK_STATUSES for st in listing_map.values()
                    )

                    if old_was_oos and now_in_stock:
                        # Product is back — fetch real HTML for accurate sizes
                        name = product.get("name", "?")[:40]
                        print(f"{GREEN}[monitor] RESTOCK: {code} | {name} — fetching HTML{RESET}")
                        real_map = await asyncio.to_thread(_fetch_real_stock_map, product)
                        _stock_snapshot[code] = real_map
                        caption   = _format_restock_alert(product, real_map)
                        image_url = _get_product_image(product)
                        sent_ok   = await _send_alert(app, caption, image_url, code)
                        if sent_ok:
                            _state["restock_alerts_sent"] += 1
                            restock_alerted += 1
                    else:
                        # Just update snapshot with listing sentinel
                        _stock_snapshot[code] = listing_map

            # Mark disappeared products as OOS (don't delete — needed for restock detection)
            disappeared = _known_codes - current_codes
            for code in disappeared:
                _stock_snapshot[code] = {"__listed__": "outOfStock"}
                print(f"{YELLOW}[monitor] Disappeared: {code} — marked OOS{RESET}")
            _known_codes = current_codes

            _state["last_new_alerted"]     = new_alerted
            _state["last_restock_alerted"] = restock_alerted

            print(
                f"{CYAN}[monitor] Poll #{_state['polls_done']} done | "
                f"products={len(current_codes)} | "
                f"new={new_alerted} restock={restock_alerted} | "
                f"listing={listing_elapsed:.1f}s html={_state['last_html_secs']}s{RESET}"
            )

    except asyncio.CancelledError:
        print(f"{CYAN}[monitor] Task cancelled{RESET}")
    except Exception as exc:
        print(f"{RED}[monitor] FATAL: {exc}{RESET}")
        traceback.print_exc()
    finally:
        _state["monitor_running"] = False
        print(f"{YELLOW}[monitor] Stopped{RESET}")


# =============================================================================
# MONITOR CONTROL
# =============================================================================

def _start_monitor(app: Application):
    global _monitor_task, _stock_snapshot, _alerted_new, _known_codes

    if _monitor_task and not _monitor_task.done():
        _monitor_task.cancel()

    # Reset all state
    _stock_snapshot           = {}
    _alerted_new              = set()
    _known_codes              = set()
    _state["is_first_cycle"]  = True
    _state["fc_done"]         = False
    _state["fc_total"]        = 0
    _state["fc_in_stock"]     = 0
    _state["fc_oos"]          = 0
    _state["polls_done"]      = 0

    _monitor_task = asyncio.create_task(_monitor_loop(app))
    print(f"{GREEN}[monitor] Task created{RESET}")


def _stop_monitor():
    global _monitor_task
    if _monitor_task and not _monitor_task.done():
        _monitor_task.cancel()
        print(f"{YELLOW}[monitor] Cancelled by admin{RESET}")
    _state["monitor_running"] = False


def _admin_keyboard() -> InlineKeyboardMarkup:
    if _state["monitor_running"]:
        button = InlineKeyboardButton("🔴 Stop Monitor", callback_data="monitor_stop")
    else:
        button = InlineKeyboardButton("🟢 Start Monitor", callback_data="monitor_start")
    return InlineKeyboardMarkup([[button]])


# =============================================================================
# BOT COMMANDS
# =============================================================================

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    if not _is_admin(uid):
        await update.message.reply_text(
            "⛔ *Admin only.*\n\n👗 Use /sendlinks to get product links.\n📖 /help for info.",
            parse_mode="Markdown",
        )
        return

    sort_label  = "Relevance" if _state["sort_mode"] == SORT_RELEVANCE else "Discount ↓"
    status_icon = "🟢 Running" if _state["monitor_running"] else "🔴 Stopped"
    group_line  = f"`{_group_id}`" if _group_id else "❌ Not set — set ALERT\\_GROUP\\_ID env var"

    await update.message.reply_text(
        "🧿 *Admin Panel — Sheinverse Bot v17* 🧿\n"
        "━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"📢 Channel 1: `{CHANNEL_1}`\n"
        f"📢 Channel 2: `{CHANNEL_2}`\n"
        f"📣 Alert Group: {group_line}\n\n"
        f"⚙️ Sort mode: `{sort_label}`\n"
        f"⏱️ Interval: every `{_state['interval']}s`\n"
        f"🔭 Monitor: *{status_icon}*\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        "🪄 *How it works (v17):*\n"
        "• Real size detection via HTML scraping 🔍\n"
        "• Shows actual sizes: XS • S • M • L • XL • XXL\n"
        "• HTML only fetched for NEW products (fast!)\n"
        "• Restock: product disappears → reappears → alert\n\n"
        "👑 *Admin commands:*\n"
        "/startmonitor /stopmonitor /monitor /stats\n"
        "/sortbyrelevance /sortbydiscount /setmonitorinterval\n\n"
        "👥 *All members:* /sendlinks /help",
        parse_mode="Markdown",
        reply_markup=_admin_keyboard(),
    )


async def cmd_monitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not _is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return

    sort_label   = "Relevance" if _state["sort_mode"] == SORT_RELEVANCE else "Discount ↓"
    status_emoji = "🟢" if _state["monitor_running"] else "🔴"

    if _state["fc_done"]:
        fc_line = (
            f"✅ Done | checked={_state['fc_total']} "
            f"in_stock={_state['fc_in_stock']} oos={_state['fc_oos']}"
        )
    elif _state["monitor_running"] and not _state["is_first_cycle"]:
        fc_line = "🔄 Running..."
    elif _state["monitor_running"]:
        fc_line = "⏳ Waiting for first fetch..."
    else:
        fc_line = "⏳ Not started"

    await update.message.reply_text(
        "🔭 *Monitor Dashboard v17* 🔭\n"
        "━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"{status_emoji} Status: *{'🟢 Running' if _state['monitor_running'] else '🔴 Stopped'}*\n"
        f"⚙️ Sort: `{sort_label}`\n"
        f"⏱️ Interval: `{_state['interval']}s`\n"
        f"🕐 Started: `{_state['monitor_started'] or 'N/A'}`\n"
        f"📣 Sending to: `{ALERT_CHANNELS}`\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        f"🚀 *First Cycle:* {fc_line}\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        "*Last Cycle:*\n"
        f"🕐 Time: `{_state['last_poll_time'] or 'No cycle yet'}`\n"
        f"📡 Listing fetch: `{_state['last_listing_secs']}s`\n"
        f"🔍 HTML fetch: `{_state['last_html_secs']}s` ({_state['last_html_fetched']} products)\n"
        f"📦 Products: `{_state['last_total_products']}`\n"
        f"✨ New alerts: `{_state['last_new_alerted']}`\n"
        f"🎉 Restock alerts: `{_state['last_restock_alerted']}`\n"
        f"🔄 Cycles done: `{_state['polls_done']}`\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        f"🆕 Total new alerts: `{_state['new_alerts_sent']}`\n"
        f"🔄 Total restock alerts: `{_state['restock_alerts_sent']}`\n"
        f"🗂️ Tracked codes: `{len(_known_codes)}`",
        parse_mode="Markdown",
        reply_markup=_admin_keyboard(),
    )


async def cmd_startmonitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not _is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ *Admin only.*", parse_mode="Markdown")
        return
    if _state["monitor_running"]:
        await update.message.reply_text(
            "ℹ️ *Monitor is already running!* 🟢", parse_mode="Markdown",
            reply_markup=_admin_keyboard(),
        )
        return
    _start_monitor(context.application)
    group_note = f"\n📣 Group alerts: `{_group_id}`" if _group_id else "\n⚠️ Set ALERT\\_GROUP\\_ID for group alerts"
    await update.message.reply_text(
        "🚀 *Monitor v17 started!* ✨\n\n"
        f"⏱️ First alert in `{_state['interval']}s`\n"
        f"🔍 HTML scraping for real size data\n"
        f"📣 Channels: `{CHANNEL_1}`, `{CHANNEL_2}`"
        f"{group_note}",
        parse_mode="Markdown",
        reply_markup=_admin_keyboard(),
    )


async def cmd_stopmonitor(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not _is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ *Admin only.*", parse_mode="Markdown")
        return
    if not _state["monitor_running"]:
        await update.message.reply_text(
            "ℹ️ *Monitor is already stopped.* 🔴", parse_mode="Markdown",
            reply_markup=_admin_keyboard(),
        )
        return
    _stop_monitor()
    await update.message.reply_text(
        "🔴 *Monitor stopped.* 🛑\n\n"
        "▶️ Use /startmonitor to resume.",
        parse_mode="Markdown",
        reply_markup=_admin_keyboard(),
    )


async def cmd_sortbyrelevance(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not _is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return
    if _state["sort_mode"] == SORT_RELEVANCE:
        await update.message.reply_text("ℹ️ Already using *Relevance* sort.", parse_mode="Markdown")
        return
    _state["sort_mode"] = SORT_RELEVANCE
    _start_monitor(context.application)
    await update.message.reply_text("✅ *Sort → Relevance* | Monitor restarted.", parse_mode="Markdown")


async def cmd_sortbydiscount(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not _is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return
    if _state["sort_mode"] == SORT_DISCOUNT_DESC:
        await update.message.reply_text("ℹ️ Already using *Discount ↓* sort.", parse_mode="Markdown")
        return
    _state["sort_mode"] = SORT_DISCOUNT_DESC
    _start_monitor(context.application)
    await update.message.reply_text("✅ *Sort → Discount ↓* | Monitor restarted.", parse_mode="Markdown")


async def cmd_setmonitorinterval(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not _is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return
    args = context.args
    if not args:
        await update.message.reply_text(
            f"⚠️ *Usage:* `/setmonitorinterval <seconds>`\n\n"
            f"⏱️ Current: `{_state['interval']}s`\n"
            f"⚠️ Recommended minimum: `{MIN_INTERVAL}s` (HTML scraping needs time)\n"
            f"✅ Best: `60-300s`",
            parse_mode="Markdown",
        )
        return
    try:
        new_interval = int(args[0])
    except ValueError:
        await update.message.reply_text("❌ Enter a whole number of seconds.")
        return
    if new_interval < 10:
        await update.message.reply_text("❌ Minimum is 10 seconds.")
        return
    if new_interval > 3600:
        await update.message.reply_text("❌ Maximum is 3600 seconds.")
        return
    old = _state["interval"]
    _state["interval"] = new_interval
    _start_monitor(context.application)
    warning = (
        f"\n⚠️ _Below {MIN_INTERVAL}s — HTML scraping may not complete in time._"
        if new_interval < MIN_INTERVAL else ""
    )
    await update.message.reply_text(
        f"⏱️ *Interval updated!*\n`{old}s` → `{new_interval}s` | Monitor restarted.{warning}",
        parse_mode="Markdown",
    )


async def cmd_sendlinks(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    missing = await _get_missing_channels(context.bot, uid)
    if missing and not _is_admin(uid):
        await update.message.reply_text(
            "🔒 *Access Restricted!*\n\n"
            "👇 Join *both* channels to unlock:\n\n"
            + "\n".join(f"  🔔 {ch}" for ch in missing)
            + "\n\n1️⃣ Tap below to join\n2️⃣ Send /sendlinks again",
            parse_mode="Markdown",
            reply_markup=_join_keyboard(missing),
        )
        return

    msg = await update.message.reply_text(
        "🔍 *Fetching all Sheinverse products...*", parse_mode="Markdown"
    )
    products, error = await asyncio.to_thread(_fetch_all_products, _state["sort_mode"])
    if error or not products:
        await msg.edit_text(f"❌ Failed: `{error or 'No products found'}`", parse_mode="Markdown")
        return

    await msg.edit_text(
        f"✅ *Found {len(products):,} products!* 🎉\n\n🗂️ Categorising...",
        parse_mode="Markdown",
    )
    categorized = _categorize(products)
    total_files = len(categorized)
    total_links = sum(len(v) for v in categorized.values())

    await msg.edit_text(
        f"📂 Sending *{total_files}* files to your DM...\n🔗 Total: *{total_links:,}* links",
        parse_mode="Markdown",
    )

    files_sent = 0
    for filename, urls in sorted(categorized.items()):
        file_obj      = io.BytesIO("\n".join(urls).encode("utf-8"))
        file_obj.name = filename
        try:
            await context.bot.send_document(
                chat_id=uid, document=file_obj, filename=filename,
                caption=f"🛍️ *{filename}*\n🔗 {len(urls):,} links",
                parse_mode="Markdown",
            )
            files_sent += 1
            await asyncio.sleep(0.4)
        except Exception as exc:
            print(f"{RED}[sendlinks] {filename}: {exc}{RESET}")

    _state["sendlinks_runs"] += 1
    await context.bot.send_message(
        chat_id=uid,
        text=(
            "🎆 *All files delivered!* 🎆\n\n"
            f"📁 Files: *{files_sent}/{total_files}*\n"
            f"🔗 Links: *{total_links:,}*\n\n"
            "🛒 Happy shopping!\n"
            "🔔 _Auto alerts are active — we'll ping when new items drop!_"
        ),
        parse_mode="Markdown",
    )


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "✨ *Welcome to SHEIN Sheinverse Bot!* 🛍️✨\n"
        "━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"1️⃣ Join both channels:\n   🔔 {CHANNEL_1}\n   🔔 {CHANNEL_2}\n\n"
        "2️⃣ DM this bot: /sendlinks\n"
        "3️⃣ Get sorted product files! 🎉\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        "🛒 /sendlinks — Get product files\n"
        "📖 /help      — This message\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        "🔔 *Auto alerts in channels:*\n"
        "✨ New product listed → instant alert\n"
        "🚀 Product restocked → instant alert\n\n"
        "💜 _Stay tuned — we never miss a drop!_",
        parse_mode="Markdown",
    )


async def cmd_stats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not _is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return
    total_alerts = _state["new_alerts_sent"] + _state["restock_alerts_sent"]
    sort_label   = "Relevance" if _state["sort_mode"] == SORT_RELEVANCE else "Discount ↓"
    await update.message.reply_text(
        "📊 *Bot Stats — Sheinverse v17* 🚀\n"
        "━━━━━━━━━━━━━━━━━━━━━\n\n"
        f"🕐 Started: `{_state['monitor_started'] or 'not yet'}`\n"
        f"⚙️ Sort: `{sort_label}`\n"
        f"⏱️ Interval: `{_state['interval']}s`\n"
        f"📣 Alert destinations: `{ALERT_CHANNELS}`\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        "*First Cycle:*\n"
        f"📦 Checked: `{_state['fc_total']}` | "
        f"✅ Alerted: `{_state['fc_in_stock']}` | "
        f"⏸️ OOS: `{_state['fc_oos']}`\n\n"
        "━━━━━━━━━━━━━━━━━━━━━\n"
        "*All Time:*\n"
        f"📡 Cycles: `{_state['polls_done']}`\n"
        f"✨ New alerts: `{_state['new_alerts_sent']}`\n"
        f"🎉 Restock alerts: `{_state['restock_alerts_sent']}`\n"
        f"📣 Total alerts: `{total_alerts}`\n\n"
        f"🗂️ Tracked codes: `{len(_known_codes)}`\n"
        f"🛒 /sendlinks runs: `{_state['sendlinks_runs']}`",
        parse_mode="Markdown",
    )


async def callback_monitor_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not _is_admin(query.from_user.id):
        await query.answer("⛔ Admin only.", show_alert=True)
        return
    await query.answer()

    if query.data == "monitor_start":
        if _state["monitor_running"]:
            await query.edit_message_reply_markup(reply_markup=_admin_keyboard())
            await query.message.reply_text("ℹ️ Already running! 🟢", parse_mode="Markdown")
            return
        _start_monitor(context.application)
        await query.edit_message_reply_markup(reply_markup=_admin_keyboard())
        await query.message.reply_text(
            "🚀 *Monitor started!* ✨\n"
            f"⏱️ First alerts in `{_state['interval']}s`",
            parse_mode="Markdown",
        )

    elif query.data == "monitor_stop":
        if not _state["monitor_running"]:
            await query.edit_message_reply_markup(reply_markup=_admin_keyboard())
            await query.message.reply_text("ℹ️ Already stopped. 🔴", parse_mode="Markdown")
            return
        _stop_monitor()
        await query.edit_message_reply_markup(reply_markup=_admin_keyboard())
        await query.message.reply_text("🔴 *Monitor stopped.* 🛑", parse_mode="Markdown")


# =============================================================================
# LIFECYCLE
# =============================================================================

async def post_init(application: Application):
    await application.bot.set_my_commands(
        [
            BotCommand("sendlinks",           "Get all Sheinverse product links"),
            BotCommand("help",                "Show help"),
            BotCommand("start",               "Admin panel"),
            BotCommand("startmonitor",        "Start the product monitor"),
            BotCommand("stopmonitor",         "Stop the product monitor"),
            BotCommand("monitor",             "Monitor status"),
            BotCommand("sortbyrelevance",     "Sort by relevance"),
            BotCommand("sortbydiscount",      "Sort by discount"),
            BotCommand("setmonitorinterval",  "Set poll interval (seconds)"),
            BotCommand("stats",               "Full stats"),
        ],
        scope=BotCommandScopeDefault(),
    )
    _start_monitor(application)
    print(f"{GREEN}[bot] Ready — v17 (real size detection via HTML scraping){RESET}")
    print(f"{GREEN}[bot] Alert destinations: {ALERT_CHANNELS}{RESET}")
    if not _group_id:
        print(f"{YELLOW}[bot] WARNING: ALERT_GROUP_ID not set!{RESET}")
    else:
        print(f"{GREEN}[bot] Group alerts → {_group_id}{RESET}")


def main():
    print(f"{CYAN}{'='*55}{RESET}")
    print(f"{CYAN}  SHEIN Sheinverse Bot v17{RESET}")
    print(f"{CYAN}  Real size detection via HTML scraping{RESET}")
    print(f"{CYAN}  Pages: 0-indexed (0=first, 1=second, ...){RESET}")
    print(f"{CYAN}  Alert destinations: {ALERT_CHANNELS}{RESET}")
    if not _group_id:
        print(f"{YELLOW}  WARNING: Set ALERT_GROUP_ID to send alerts to group!{RESET}")
    if _state["interval"] < MIN_INTERVAL:
        print(f"{YELLOW}  WARNING: interval={_state['interval']}s — recommend {MIN_INTERVAL}s+{RESET}")
    print(f"{CYAN}{'='*55}{RESET}")

    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .concurrent_updates(True)
        .post_init(post_init)
        .connect_timeout(30.0)
        .read_timeout(30.0)
        .write_timeout(60.0)
        .pool_timeout(30.0)
        .build()
    )

    app.add_handler(CommandHandler("start",              cmd_start))
    app.add_handler(CommandHandler("startmonitor",       cmd_startmonitor))
    app.add_handler(CommandHandler("stopmonitor",        cmd_stopmonitor))
    app.add_handler(CommandHandler("monitor",            cmd_monitor))
    app.add_handler(CommandHandler("sortbyrelevance",    cmd_sortbyrelevance))
    app.add_handler(CommandHandler("sortbydiscount",     cmd_sortbydiscount))
    app.add_handler(CommandHandler("setmonitorinterval", cmd_setmonitorinterval))
    app.add_handler(CommandHandler("sendlinks",          cmd_sendlinks))
    app.add_handler(CommandHandler("help",               cmd_help))
    app.add_handler(CommandHandler("stats",              cmd_stats))
    app.add_handler(CallbackQueryHandler(
        callback_monitor_toggle, pattern="^monitor_(start|stop)$"
    ))

    print(f"{GREEN}Bot polling...{RESET}")
    app.run_polling(
        allowed_updates=["message", "callback_query"],
        drop_pending_updates=True,
    )


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print(f"\n{CYAN}Stopped by user.{RESET}")
        sys.exit(0)
    except Exception as exc:
        print(f"{RED}Fatal error: {exc}{RESET}")
        traceback.print_exc()
        sys.exit(1)
