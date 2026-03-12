"""
build_country_mentions.py
=========================
Scans 30 credible US/UK/CA news sources via RSS for a 24-hour window,
counts how many articles mention each of 44 tracked countries,
compares against a rolling 7-day baseline, computes z-scores,
flags trending countries, and writes public/country_mentions.json.

JSON shape (Base44-friendly):
{
  "meta": {
    "generated_at": "2026-05-02T23:54:00Z",
    "window_start":  "2026-05-01T23:54:00Z",
    "window_end":    "2026-05-02T23:54:00Z",
    "window_hours":  24,
    "articles_scanned": 1234
  },
  "countries": [
    {
      "country":       "Russia",
      "iso2":          "RU",
      "mentions":      42,
      "baseline_mean": 31.4,
      "baseline_std":  6.2,
      "z_score":       1.71,
      "trend_status":  "trending",   // "trending" | "elevated" | "normal" | "low"
      "pct_change":    33.8,
      "history": [
        { "window_end": "2026-04-26T11:54:00Z", "mentions": 28 },
        ...
      ]
    },
    ...
  ]
}

trend_status logic:
  z >= 2.0  → "trending"
  z >= 1.0  → "elevated"
  z <= -1.0 → "low"
  else      → "normal"
"""

from __future__ import annotations

import json
import re
import time
import hashlib
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from urllib.parse import urlparse, parse_qs, urlencode, urlunparse
import math

import feedparser
import requests
from dateutil import parser as dtparser


# ──────────────────────────────────────────────────────────
# CONFIG
# ──────────────────────────────────────────────────────────

WINDOW_HOURS = 24
HISTORY_DAYS = 90          # keep at most 90 days of history per country
BASELINE_MIN_RUNS = 3      # need at least this many history points before z-score is meaningful
TRENDING_Z    = 2.0        # z ≥ 2.0  → trending
ELEVATED_Z    = 1.0        # z ≥ 1.0  → elevated
LOW_Z         = -1.0       # z ≤ -1.0 → low

TIMEOUT    = 20
MAX_RETRIES = 3
RETRY_SLEEP = 1.2

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Macintosh; Intel Mac OS 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "application/rss+xml, application/xml, text/xml, */*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
}

OUTPUT_DIR  = Path("public")
OUTPUT_FILE = OUTPUT_DIR / "country_mentions.json"


# ──────────────────────────────────────────────────────────
# 30 CREDIBLE US / UK / CA NEWS SOURCES  (RSS)
# ──────────────────────────────────────────────────────────

RSS_SOURCES: Dict[str, str] = {
    # ── United States ──────────────────────────────────────
    "AP News":           "https://rsshub.app/apnews/topics/ap-top-news",
    "Reuters":           "https://feeds.reuters.com/reuters/topNews",
    "NPR World":         "https://www.npr.org/rss/rss.php?id=1004",
    "PBS NewsHour":      "https://www.pbs.org/newshour/feeds/rss/world",
    "ABC News":          "https://feeds.abcnews.com/abcnews/internationalheadlines",
    "CBS News":          "https://www.cbsnews.com/latest/rss/world",
    "NBC News":          "https://feeds.nbcnews.com/nbcnews/public/world",
    "CNN":               "http://rss.cnn.com/rss/edition_world.rss",
    "Fox News":          "https://moxie.foxnews.com/google-publisher/world.xml",
    "The New York Times":"https://rss.nytimes.com/services/xml/rss/nyt/World.xml",
    "Washington Post":   "https://feeds.washingtonpost.com/rss/world",
    "Wall Street Journal":"https://feeds.a.dj.com/rss/RSSWorldNews.xml",
    "Politico":          "https://rss.politico.com/politics-news.xml",
    "The Hill":          "https://thehill.com/feed/",
    "Foreign Policy":    "https://foreignpolicy.com/feed/",
    "Defense One":       "https://www.defenseone.com/rss/all/",
    "Voice of America":  "https://www.voanews.com/api/zk_$egt",

    # ── United Kingdom ─────────────────────────────────────
    "BBC World":         "https://feeds.bbci.co.uk/news/world/rss.xml",
    "The Guardian":      "https://www.theguardian.com/world/rss",
    "The Times UK":      "https://www.thetimes.co.uk/rss/world.xml",
    "The Telegraph":     "https://www.telegraph.co.uk/rss.xml",
    "The Independent":   "https://www.independent.co.uk/news/world/rss",
    "Sky News":          "https://feeds.skynews.com/feeds/rss/world.xml",
    "The Economist":     "https://www.economist.com/international/rss.xml",
    "Financial Times":   "https://www.ft.com/world?format=rss",

    # ── Canada ─────────────────────────────────────────────
    "CBC World":         "https://rss.cbc.ca/lineup/world.xml",
    "Globe and Mail":    "https://www.theglobeandmail.com/arc/outboundfeeds/rss/category/world/",
    "National Post":     "https://nationalpost.com/feed/",
    "Toronto Star":      "https://www.thestar.com/content/thestar/feed.rss",
    "CTV News":          "https://www.ctvnews.ca/rss/ctvnews-ca-world-public-rss-1.822289",
}


# ──────────────────────────────────────────────────────────
# TRACKED COUNTRIES  (44 countries)
# ──────────────────────────────────────────────────────────

COUNTRIES = [
    {"country": "Russia",        "iso2": "RU"},
    {"country": "India",         "iso2": "IN"},
    {"country": "Pakistan",      "iso2": "PK"},
    {"country": "China",         "iso2": "CN"},
    {"country": "United Kingdom","iso2": "GB"},
    {"country": "Germany",       "iso2": "DE"},
    {"country": "UAE",           "iso2": "AE"},
    {"country": "Saudi Arabia",  "iso2": "SA"},
    {"country": "Israel",        "iso2": "IL"},
    {"country": "Palestine",     "iso2": "PS"},
    {"country": "Mexico",        "iso2": "MX"},
    {"country": "Brazil",        "iso2": "BR"},
    {"country": "Canada",        "iso2": "CA"},
    {"country": "Nigeria",       "iso2": "NG"},
    {"country": "Japan",         "iso2": "JP"},
    {"country": "Iran",          "iso2": "IR"},
    {"country": "Syria",         "iso2": "SY"},
    {"country": "France",        "iso2": "FR"},
    {"country": "Turkey",        "iso2": "TR"},
    {"country": "Venezuela",     "iso2": "VE"},
    {"country": "Vietnam",       "iso2": "VN"},
    {"country": "Taiwan",        "iso2": "TW"},
    {"country": "South Korea",   "iso2": "KR"},
    {"country": "North Korea",   "iso2": "KP"},
    {"country": "Indonesia",     "iso2": "ID"},
    {"country": "Myanmar",       "iso2": "MM"},
    {"country": "Armenia",       "iso2": "AM"},
    {"country": "Azerbaijan",    "iso2": "AZ"},
    {"country": "Morocco",       "iso2": "MA"},
    {"country": "Somalia",       "iso2": "SO"},
    {"country": "Yemen",         "iso2": "YE"},
    {"country": "Libya",         "iso2": "LY"},
    {"country": "Egypt",         "iso2": "EG"},
    {"country": "Algeria",       "iso2": "DZ"},
    {"country": "Argentina",     "iso2": "AR"},
    {"country": "Chile",         "iso2": "CL"},
    {"country": "Peru",          "iso2": "PE"},
    {"country": "Cuba",          "iso2": "CU"},
    {"country": "Colombia",      "iso2": "CO"},
    {"country": "Panama",        "iso2": "PA"},
    {"country": "El Salvador",   "iso2": "SV"},
    {"country": "Denmark",       "iso2": "DK"},
    {"country": "Sudan",         "iso2": "SD"},
    {"country": "Ukraine",       "iso2": "UA"},
]

# ── Per-country search terms (aliases + demonyms + capitals) ──────────────
# Keys must match the "country" field above exactly.
COUNTRY_ALIASES: Dict[str, List[str]] = {
    "Russia":         ["russia", "russian", "russians", "moscow", "kremlin", "putin"],
    "India":          ["india", "indian", "indians", "new delhi", "modi"],
    "Pakistan":       ["pakistan", "pakistani", "pakistanis", "islamabad"],
    "China":          ["china", "chinese", "beijing", "xi jinping", "prc"],
    "United Kingdom": ["united kingdom", "britain", "british", "england", "english",
                       "london", "uk ", " uk,", "sunak", "starmer"],
    "Germany":        ["germany", "german", "germans", "berlin", "bundestag", "scholz"],
    "UAE":            ["uae", "united arab emirates", "abu dhabi", "dubai", "emirati"],
    "Saudi Arabia":   ["saudi arabia", "saudi", "saudis", "riyadh", "mbs", "aramco"],
    "Israel":         ["israel", "israeli", "israelis", "jerusalem", "tel aviv",
                       "idf", "netanyahu"],
    "Palestine":      ["palestine", "palestinian", "palestinians", "gaza", "west bank",
                       "hamas", "ramallah"],
    "Mexico":         ["mexico", "mexican", "mexicans", "mexico city", "sheinbaum"],
    "Brazil":         ["brazil", "brazilian", "brazilians", "brasilia", "lula"],
    "Canada":         ["canada", "canadian", "canadians", "ottawa", "trudeau", "carney"],
    "Nigeria":        ["nigeria", "nigerian", "nigerians", "abuja", "lagos"],
    "Japan":          ["japan", "japanese", "tokyo", "kishida", "ishiba"],
    "Iran":           ["iran", "iranian", "iranians", "tehran", "khamenei",
                       "irgc", "rouhani", "raisi"],
    "Syria":          ["syria", "syrian", "syrians", "damascus", "al-sharaa", "hts"],
    "France":         ["france", "french", "paris", "macron", "elysee"],
    "Turkey":         ["turkey", "turkish", "ankara", "erdogan", "istanbul"],
    "Venezuela":      ["venezuela", "venezuelan", "venezuelans", "caracas", "maduro"],
    "Vietnam":        ["vietnam", "vietnamese", "hanoi"],
    "Taiwan":         ["taiwan", "taiwanese", "taipei"],
    "South Korea":    ["south korea", "south korean", "seoul"],
    "North Korea":    ["north korea", "north korean", "pyongyang", "kim jong"],
    "Indonesia":      ["indonesia", "indonesian", "jakarta", "prabowo"],
    "Myanmar":        ["myanmar", "burmese", "naypyidaw", "tatmadaw", "burma"],
    "Armenia":        ["armenia", "armenian", "armenians", "yerevan"],
    "Azerbaijan":     ["azerbaijan", "azerbaijani", "baku", "aliyev"],
    "Morocco":        ["morocco", "moroccan", "moroccans", "rabat"],
    "Somalia":        ["somalia", "somali", "somalis", "mogadishu", "al-shabaab"],
    "Yemen":          ["yemen", "yemeni", "yemenis", "sanaa", "houthis", "houthi"],
    "Libya":          ["libya", "libyan", "libyans", "tripoli", "benghazi"],
    "Egypt":          ["egypt", "egyptian", "egyptians", "cairo", "sisi"],
    "Algeria":        ["algeria", "algerian", "algerians", "algiers"],
    "Argentina":      ["argentina", "argentinian", "argentinians", "buenos aires", "milei"],
    "Chile":          ["chile", "chilean", "chileans", "santiago"],
    "Peru":           ["peru", "peruvian", "peruvians", "lima"],
    "Cuba":           ["cuba", "cuban", "cubans", "havana"],
    "Colombia":       ["colombia", "colombian", "colombians", "bogota", "petro"],
    "Panama":         ["panama", "panamanian", "panamanians", "panama city",
                       "panama canal"],
    "El Salvador":    ["el salvador", "salvadoran", "salvadorans", "san salvador",
                       "bukele"],
    "Denmark":        ["denmark", "danish", "danes", "copenhagen", "greenland"],
    "Sudan":          ["sudan", "sudanese", "khartoum", "rsf", "darfur"],
    "Ukraine":        ["ukraine", "ukrainian", "ukrainians", "kyiv", "kiev",
                       "zelensky", "zelenskyy"],
}


# ──────────────────────────────────────────────────────────
# HELPERS
# ──────────────────────────────────────────────────────────

def _norm(s: str) -> str:
    return " ".join((s or "").lower().split())

def fetch_text(url: str) -> Optional[str]:
    sess = requests.Session()
    sess.headers.update(HEADERS)
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            r = sess.get(url, timeout=TIMEOUT, allow_redirects=True)
            if r.status_code == 200 and r.text:
                return r.text
        except requests.RequestException:
            pass
        time.sleep(RETRY_SLEEP * attempt)
    return None

def parse_dt(entry: dict) -> Optional[datetime]:
    for k in ("published_parsed", "updated_parsed", "created_parsed"):
        st = entry.get(k)
        if st:
            try:
                return datetime(*st[:6], tzinfo=timezone.utc)
            except Exception:
                pass
    for k in ("published", "updated", "created"):
        v = entry.get(k)
        if v:
            try:
                dt = dtparser.parse(v)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                return dt.astimezone(timezone.utc)
            except Exception:
                continue
    return None

def canonicalize_url(url: str) -> str:
    try:
        u = urlparse(url)
        qs = parse_qs(u.query, keep_blank_values=True)
        drop = {"utm_source","utm_medium","utm_campaign","utm_term","utm_content",
                "fbclid","gclid","mc_cid","mc_eid"}
        for p in list(qs.keys()):
            if p.lower() in drop:
                qs.pop(p, None)
        new_q = urlencode({k: v[0] for k, v in qs.items() if v})
        path = u.path or ""
        if path != "/" and path.endswith("/"):
            path = path[:-1]
        return urlunparse((u.scheme, u.netloc, path, u.params, new_q, ""))
    except Exception:
        return url


# ──────────────────────────────────────────────────────────
# RSS FETCHING
# ──────────────────────────────────────────────────────────

def fetch_articles(window_hours: int) -> Tuple[List[dict], int]:
    """
    Fetch all articles from all RSS feeds within the time window.
    Returns (articles, total_scanned).
    Each article: {"title": str, "url": str, "source": str, "text": str}
    where text = title + " " + summary (for richer matching).
    """
    now    = datetime.now(timezone.utc)
    cutoff = now - timedelta(hours=window_hours)

    seen_urls: set = set()
    articles: List[dict] = []
    total_scanned = 0

    for source, feed_url in RSS_SOURCES.items():
        raw = fetch_text(feed_url)
        if not raw:
            print(f"  ⚠  Could not fetch: {source}")
            continue

        d = feedparser.parse(raw)
        entries = getattr(d, "entries", [])
        total_scanned += len(entries)

        for e in entries:
            title = (e.get("title") or "").strip()
            link  = canonicalize_url((e.get("link") or "").strip())
            if not title or not link:
                continue
            if link in seen_urls:
                continue

            dt = parse_dt(e)
            if dt and dt < cutoff:
                continue

            seen_urls.add(link)
            summary = (e.get("summary") or e.get("description") or "")
            # strip HTML tags from summary
            summary = re.sub(r"<[^>]+>", " ", summary)
            combined = f"{title} {summary}"

            articles.append({
                "title":  title,
                "url":    link,
                "source": source,
                "text":   _norm(combined),
            })

    return articles, total_scanned


# ──────────────────────────────────────────────────────────
# MENTION COUNTING
# ──────────────────────────────────────────────────────────

def count_mentions(articles: List[dict]) -> Dict[str, int]:
    """
    For each country, count how many UNIQUE articles mention it
    (an article counts once per country even if the country appears multiple times).
    """
    counts: Dict[str, int] = {c["country"]: 0 for c in COUNTRIES}

    for art in articles:
        text = art["text"]
        for c in COUNTRIES:
            name = c["country"]
            aliases = COUNTRY_ALIASES.get(name, [name.lower()])
            for alias in aliases:
                if alias in text:
                    counts[name] += 1
                    break   # count this article once per country

    return counts


# ──────────────────────────────────────────────────────────
# STATISTICAL ANALYSIS
# ──────────────────────────────────────────────────────────

def _mean_std(values: List[float]) -> Tuple[float, float]:
    if not values:
        return 0.0, 0.0
    n   = len(values)
    mu  = sum(values) / n
    if n < 2:
        return mu, 0.0
    var = sum((x - mu) ** 2 for x in values) / (n - 1)   # sample std
    return mu, math.sqrt(var)

def compute_trend_status(z: float) -> str:
    if z >= TRENDING_Z:
        return "trending"
    if z >= ELEVATED_Z:
        return "elevated"
    if z <= LOW_Z:
        return "low"
    return "normal"

def analyze(current_counts: Dict[str, int],
            existing_data: dict,
            window_end: datetime) -> List[dict]:
    """
    For each country:
      1. Load its history from existing_data (if any).
      2. Compute rolling baseline (mean, std) from last 7 days of history points.
      3. Compute z-score for current count.
      4. Append current count to history.
      5. Prune history older than HISTORY_DAYS days.
    """
    existing_map: Dict[str, dict] = {}
    for c in existing_data.get("countries", []):
        existing_map[c["country"]] = c

    results: List[dict] = []
    cutoff_history = window_end - timedelta(days=HISTORY_DAYS)
    baseline_cutoff = window_end - timedelta(days=7)

    for c in COUNTRIES:
        name = c["country"]
        iso2 = c["iso2"]
        current = current_counts.get(name, 0)

        # ── history ───────────────────────────────────────────
        old = existing_map.get(name, {})
        history: List[dict] = old.get("history", [])

        # prune old entries
        history = [
            h for h in history
            if _parse_iso(h.get("window_end", "")) >= cutoff_history
        ]

        # ── baseline: last 7 days of history points ───────────
        baseline_values = [
            float(h["mentions"])
            for h in history
            if _parse_iso(h.get("window_end", "")) >= baseline_cutoff
        ]

        mu, sigma = _mean_std(baseline_values)

        if len(baseline_values) >= BASELINE_MIN_RUNS and sigma > 0:
            z = (current - mu) / sigma
        elif len(baseline_values) >= BASELINE_MIN_RUNS:
            # sigma == 0: all baseline values identical
            z = 0.0 if current == mu else (2.5 if current > mu else -2.5)
        else:
            # not enough history yet — treat as normal
            z = 0.0

        trend_status = compute_trend_status(z)

        pct_change = (
            round((current - mu) / mu * 100, 1)
            if mu > 0 else None
        )

        # ── append current window to history ──────────────────
        history.append({
            "window_end": window_end.isoformat().replace("+00:00", "Z"),
            "mentions":   current,
        })

        results.append({
            "country":       name,
            "iso2":          iso2,
            "mentions":      current,
            "baseline_mean": round(mu, 2),
            "baseline_std":  round(sigma, 2),
            "baseline_n":    len(baseline_values),
            "z_score":       round(z, 3),
            "trend_status":  trend_status,
            "pct_change":    pct_change,
            "history":       history,
        })

    # sort by current mentions descending for easy reading
    results.sort(key=lambda x: x["mentions"], reverse=True)
    return results

def _parse_iso(s: str) -> datetime:
    try:
        return dtparser.parse(s).astimezone(timezone.utc)
    except Exception:
        return datetime.min.replace(tzinfo=timezone.utc)


# ──────────────────────────────────────────────────────────
# MAIN
# ──────────────────────────────────────────────────────────

def main():
    now        = datetime.now(timezone.utc)
    window_end = now
    window_start = now - timedelta(hours=WINDOW_HOURS)

    print(f"🔍 Scanning articles from {window_start.isoformat()} → {window_end.isoformat()}")

    # ── load existing JSON (for history) ──────────────────────
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    existing_data: dict = {}
    if OUTPUT_FILE.exists():
        try:
            existing_data = json.loads(OUTPUT_FILE.read_text(encoding="utf-8"))
            print(f"📂 Loaded existing data ({len(existing_data.get('countries', []))} countries in history)")
        except Exception as e:
            print(f"⚠  Could not parse existing JSON: {e}")

    # ── fetch & count ──────────────────────────────────────────
    print("📡 Fetching RSS feeds…")
    articles, total_scanned = fetch_articles(WINDOW_HOURS)
    print(f"   → {len(articles)} unique articles in window (scanned {total_scanned} entries)")

    print("🔢 Counting country mentions…")
    counts = count_mentions(articles)

    # quick summary
    top = sorted(counts.items(), key=lambda x: x[1], reverse=True)[:10]
    for name, n in top:
        print(f"   {n:4d}  {name}")

    # ── statistical analysis + history update ─────────────────
    print("📊 Computing z-scores and trend status…")
    country_results = analyze(counts, existing_data, window_end)

    trending = [c for c in country_results if c["trend_status"] == "trending"]
    if trending:
        print(f"🔥 Trending: {', '.join(c['country'] for c in trending)}")

    # ── assemble final JSON ────────────────────────────────────
    output = {
        "meta": {
            "generated_at":    window_end.isoformat().replace("+00:00", "Z"),
            "window_start":    window_start.isoformat().replace("+00:00", "Z"),
            "window_end":      window_end.isoformat().replace("+00:00", "Z"),
            "window_hours":    WINDOW_HOURS,
            "articles_scanned": total_scanned,
            "articles_in_window": len(articles),
            "sources_count":   len(RSS_SOURCES),
            "trending_threshold_z": TRENDING_Z,
            "elevated_threshold_z": ELEVATED_Z,
        },
        "countries": country_results,
    }

    OUTPUT_FILE.write_text(
        json.dumps(output, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    print(f"✅ Wrote {len(country_results)} countries → {OUTPUT_FILE.resolve()}")


if __name__ == "__main__":
    main()
