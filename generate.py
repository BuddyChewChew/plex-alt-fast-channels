#!/usr/bin/env python3
"""
Plex Free Live TV – M3U + XMLTV generator
Repo: https://github.com/BuddyChewChew/plex-alt-fast-channels

Flow:
  1. Load channels from channels.json cache (if fresh enough).
  2. If cache is missing or stale, discover channels via Plex API and
     write a new channels.json.
  3. Fetch a fresh anonymous token (short-lived, always fetched at runtime).
  4. Build per-region M3U (with url-tvg= EPG header) and XMLTV files.

Per-region files written to ./playlists/:
  plex_{region}.m3u   – M3U playlist (url-tvg= points to matching .xml)
  plex_{region}.xml   – XMLTV / EPG (today + tomorrow)
  plex_all.m3u        – Combined playlist
  plex_all.xml        – Combined XMLTV

channels.json is written to the repo root (committed by the workflow) so
subsequent runs never need to re-hit the channel-discovery endpoints.

Usage:
  python generate.py                         # all regions, use cache
  python generate.py --regions us ca gb      # specific regions
  python generate.py --refresh-channels      # force re-fetch channels
  python generate.py --no-epg               # skip EPG
  python generate.py --days 3               # 3 days of EPG
"""

import argparse
import json
import logging
import os
import random
import re
import shutil
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
from xml.sax.saxutils import escape

import gzip
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

OUTPUT_DIR          = "playlists"
CHANNELS_CACHE_FILE = "channels.json"   # committed to repo root
CACHE_MAX_AGE_HOURS = 24                # refresh channel list after this many hours
MAX_WORKERS         = 6                 # parallel EPG fetch threads
EPG_DAYS            = 2                 # days of EPG to fetch (today + N-1)
REQUEST_TIMEOUT     = 30

REPO_RAW_BASE = (
    "https://raw.githubusercontent.com/BuddyChewChew/plex-alt-fast-channels/main"
)

# Geographic spoofing IPs – update if a region stops returning channels
GEO_IPS = {
    "us":  "76.81.9.69",
    "ca":  "192.206.151.131",
    "gb":  "193.62.157.66",
    "au":  "110.33.122.75",
    "nz":  "203.86.207.83",
    "mx":  "200.68.128.83",
    "es":  "88.26.241.248",
    "fr":  "176.31.84.249",
    "de":  "217.0.117.58",
    "br":  "177.75.44.30",
    "in":  "49.36.80.10",
    "jp":  "126.82.100.100",
    "kr":  "175.209.10.10",
    "se":  "94.254.2.100",
    "nl":  "77.249.128.10",
}

REGION_NAMES = {
    "us":  "United States",
    "ca":  "Canada",
    "gb":  "United Kingdom",
    "au":  "Australia",
    "nz":  "New Zealand",
    "mx":  "Mexico",
    "es":  "Spain",
    "fr":  "France",
    "de":  "Germany",
    "br":  "Brazil",
    "in":  "India",
    "jp":  "Japan",
    "kr":  "South Korea",
    "se":  "Sweden",
    "nl":  "Netherlands",
}

BASE_HEADERS = {
    "Accept":              "application/json, text/plain, */*",
    "Accept-Language":     "en",
    "Connection":          "keep-alive",
    "Origin":              "https://app.plex.tv",
    "Referer":             "https://app.plex.tv/",
    "Sec-Fetch-Dest":      "empty",
    "Sec-Fetch-Mode":      "cors",
    "Sec-Fetch-Site":      "same-site",
    "User-Agent":          (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/132.0.0.0 Safari/537.36"
    ),
    "sec-ch-ua":           '"Not A(Brand";v="8", "Chromium";v="132", "Google Chrome";v="132"',
    "sec-ch-ua-mobile":    "?0",
    "sec-ch-ua-platform":  '"Windows"',
}

BASE_PARAMS = {
    "X-Plex-Product":                  "Plex Web",
    "X-Plex-Version":                  "4.145.1",
    "X-Plex-Platform":                 "Chrome",
    "X-Plex-Platform-Version":         "132.0",
    "X-Plex-Features":                 "external-media,indirect-media,hub-style-list",
    "X-Plex-Model":                    "standalone",
    "X-Plex-Device":                   "Windows",
    "X-Plex-Device-Screen-Resolution": "1920x1080",
    "X-Plex-Provider-Version":         "7.2",
    "X-Plex-Text-Format":              "plain",
    "X-Plex-Language":                 "en",
}

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
logger = logging.getLogger("plex-gen")

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_session(retries: int = 3, backoff: float = 2.0) -> requests.Session:
    session = requests.Session()
    retry = Retry(
        total=retries,
        backoff_factor=backoff,
        status_forcelist=[429, 500, 502, 503, 504],
        raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retry)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    return session


def _new_client_id() -> str:
    return str(uuid.uuid4()).replace("-", "")


def _sanitize(text: str) -> str:
    """Strip XML-illegal control characters."""
    return re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text or "")


def cleanup_output_dir():
    if os.path.exists(OUTPUT_DIR):
        logger.info("Cleaning %s …", OUTPUT_DIR)
        for name in os.listdir(OUTPUT_DIR):
            fp = os.path.join(OUTPUT_DIR, name)
            try:
                if os.path.isfile(fp) or os.path.islink(fp):
                    os.unlink(fp)
                elif os.path.isdir(fp):
                    shutil.rmtree(fp)
            except Exception as exc:
                logger.warning("Could not delete %s: %s", fp, exc)
    else:
        os.makedirs(OUTPUT_DIR)


def write_playlist(filename: str, content: str):
    """Write a file inside OUTPUT_DIR. XML files are gzip-compressed."""
    if filename.endswith(".xml"):
        filepath = os.path.join(OUTPUT_DIR, filename + ".gz")
        with gzip.open(filepath, "wt", encoding="utf-8") as fh:
            fh.write(content)
        logger.info("Wrote playlists/%s.gz  (%d bytes compressed)", filename, os.path.getsize(filepath))
    else:
        filepath = os.path.join(OUTPUT_DIR, filename)
        with open(filepath, "w", encoding="utf-8") as fh:
            fh.write(content)
        logger.info("Wrote playlists/%s  (%d bytes)", filename, len(content))


# ---------------------------------------------------------------------------
# channels.json cache
# ---------------------------------------------------------------------------

def _cache_is_fresh() -> bool:
    """Return True if channels.json exists and is younger than CACHE_MAX_AGE_HOURS."""
    if not os.path.exists(CHANNELS_CACHE_FILE):
        return False
    age_seconds = time.time() - os.path.getmtime(CHANNELS_CACHE_FILE)
    return age_seconds < CACHE_MAX_AGE_HOURS * 3600


def load_channels_cache() -> dict | None:
    """
    Load channels.json from disk.
    Schema: { region: { gridKey: { id, slug, gridKey, name, logo, key, genres } } }
    Returns None if file is missing or unreadable.
    """
    if not os.path.exists(CHANNELS_CACHE_FILE):
        return None
    try:
        with open(CHANNELS_CACHE_FILE, encoding="utf-8") as fh:
            data = json.load(fh)
        total = sum(len(v) for v in data.get("channels", {}).values())
        logger.info(
            "Loaded channels.json – %d regions, %d total channels (age: %.1fh)",
            len(data.get("channels", {})),
            total,
            (time.time() - os.path.getmtime(CHANNELS_CACHE_FILE)) / 3600,
        )
        return data.get("channels", {})
    except Exception as exc:
        logger.warning("Could not read channels.json: %s", exc)
        return None


def save_channels_cache(channels_by_region: dict):
    """
    Write channels.json to the repo root.
    Schema: { "generated": "<ISO timestamp>", "channels": { region: {...} } }
    """
    payload = {
        "generated": datetime.now(timezone.utc).isoformat(),
        "channels":  channels_by_region,
    }
    with open(CHANNELS_CACHE_FILE, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, ensure_ascii=False)
    logger.info(
        "Saved channels.json – %d regions",
        len(channels_by_region),
    )


# ---------------------------------------------------------------------------
# Plex token  (always fetched fresh – expires in ~6 h)
# ---------------------------------------------------------------------------

def get_anonymous_token(region: str = "us") -> tuple[str | None, str | None]:
    """Returns (authToken, client_id) or (None, None)."""
    client_id = _new_client_id()
    headers   = {**BASE_HEADERS, "X-Forwarded-For": GEO_IPS.get(region, GEO_IPS["us"])}
    params    = {**BASE_PARAMS, "X-Plex-Client-Identifier": client_id}

    session = _make_session()
    for attempt in range(4):
        try:
            resp = session.post(
                "https://clients.plex.tv/api/v2/users/anonymous",
                headers=headers,
                params=params,
                timeout=15,
            )
            if resp.status_code == 429:
                wait = (2 ** attempt) * 10 + random.uniform(0, 5)
                logger.warning("429 on token (attempt %d) – waiting %.0fs", attempt + 1, wait)
                time.sleep(wait)
                continue
            if resp.status_code not in (200, 201):
                logger.warning("Token HTTP %d (%s): %s", resp.status_code, region, resp.text[:200])
                time.sleep(5)
                continue
            content_type = resp.headers.get("Content-Type", "")
            token = None
            if "json" in content_type:
                try:
                    token = resp.json().get("authToken")
                except ValueError:
                    pass
            elif "xml" in content_type:
                # Plex is returning XML for this endpoint regardless of the
                # Accept header (observed 2026-08-09) – parse it directly
                # instead of forcing a JSON parse that will always fail.
                try:
                    import xml.etree.ElementTree as ET
                    token = ET.fromstring(resp.text).attrib.get("authToken")
                except ET.ParseError as exc:
                    logger.warning("Token attempt %d failed (%s): XML parse error: %s. body=%r",
                                    attempt + 1, region, exc, resp.text[:300])
                    time.sleep(5)
                    continue
            else:
                # Unrecognized content-type – try JSON, then XML, as a fallback.
                try:
                    token = resp.json().get("authToken")
                except ValueError:
                    try:
                        import xml.etree.ElementTree as ET
                        token = ET.fromstring(resp.text).attrib.get("authToken")
                    except ET.ParseError:
                        logger.warning(
                            "Token attempt %d failed (%s): unrecognized body on HTTP %d. "
                            "content-type=%s len=%d server=%s cf-ray=%s body=%r",
                            attempt + 1, region, resp.status_code, content_type,
                            len(resp.content), resp.headers.get("Server"),
                            resp.headers.get("CF-RAY"), resp.text[:300],
                        )
                        time.sleep(5)
                        continue
            if token:
                logger.info("Token OK for region=%s (content-type=%s)", region, content_type)
                return token, client_id
            logger.warning("Token attempt %d failed (%s): HTTP %d but no authToken. content-type=%s body=%r",
                            attempt + 1, region, resp.status_code, content_type, resp.text[:300])
            time.sleep(5)
        except Exception as exc:
            logger.warning("Token attempt %d failed (%s): %s", attempt + 1, region, exc)
            time.sleep(5)
    session.close()
    logger.error("Could not get token for region=%s", region)
    return None, None


# ---------------------------------------------------------------------------
# Channel discovery  (only runs when cache is stale / missing)
# ---------------------------------------------------------------------------

def _fetch_genres(token: str, client_id: str, ip: str) -> dict[str, str]:
    """GET epg.provider.plex.tv/ → {genre_slug: genre_title}"""
    headers = {**BASE_HEADERS, "X-Forwarded-For": ip}
    params  = {**BASE_PARAMS, "X-Plex-Token": token, "X-Plex-Client-Identifier": client_id}
    session = _make_session()
    try:
        resp = session.get("https://epg.provider.plex.tv/", headers=headers,
                           params=params, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            logger.warning("Genre API HTTP %d", resp.status_code)
            return {}
        genres: dict[str, str] = {}
        for feature in resp.json().get("MediaProvider", {}).get("Feature", []):
            if "GridChannelFilter" in feature:
                for g in feature["GridChannelFilter"]:
                    genres[g["identifier"]] = g["title"]
                break
        logger.info("  %d genre slugs found", len(genres))
        return genres
    except Exception as exc:
        logger.warning("Genre fetch error: %s", exc)
        return {}
    finally:
        session.close()


def _fetch_channels_for_genre(
    genre_slug: str, token: str, client_id: str, ip: str
) -> list[dict]:
    """GET epg.provider.plex.tv/lineups/plex/channels?genre={slug}"""
    url     = f"https://epg.provider.plex.tv/lineups/plex/channels?genre={genre_slug}"
    headers = {**BASE_HEADERS, "X-Forwarded-For": ip}
    params  = {**BASE_PARAMS, "X-Plex-Token": token, "X-Plex-Client-Identifier": client_id}
    session = _make_session()
    try:
        resp = session.get(url, headers=headers, params=params, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return []
        raw = resp.json().get("MediaContainer", {}).get("Channel", [])
        results = []
        for ch in raw:
            if any(m.get("drm") for m in ch.get("Media", [])):
                continue   # skip DRM-locked channels
            keys = [p["key"] for m in ch.get("Media", []) for p in m.get("Part", [])]
            results.append({
                "id":       ch.get("id", ""),
                "slug":     ch.get("slug", ""),
                "gridKey":  ch.get("gridKey", ""),
                "name":     ch.get("title", ""),
                "logo":     ch.get("thumb", ""),
                "callSign": ch.get("callSign", ""),
                "key":      keys[0] if keys else "",
                "genres":   [],   # filled in by fetch_channels()
            })
        return results
    except Exception as exc:
        logger.warning("Channel fetch error (genre=%s): %s", genre_slug, exc)
        return []
    finally:
        session.close()


def fetch_channels_from_api(token: str, client_id: str, region: str) -> dict[str, dict]:
    """
    Discover all channels for *region* by iterating over every genre slug.
    Returns {gridKey: channel_dict}.
    """
    ip     = GEO_IPS.get(region, GEO_IPS["us"])
    genres = _fetch_genres(token, client_id, ip)

    # Fallback if genre discovery fails
    if not genres:
        genres = {"all": "All", "news": "News", "sports": "Sports", "movies": "Movies"}

    channels: dict[str, dict] = {}
    for slug, title in genres.items():
        for ch in _fetch_channels_for_genre(slug, token, client_id, ip):
            gk = ch["gridKey"]
            if gk not in channels:
                channels[gk] = {**ch, "genres": [title], "region": region}
            else:
                if title not in channels[gk]["genres"]:
                    channels[gk]["genres"].append(title)
        time.sleep(0.2)   # gentle throttle

    logger.info("  Region %s → %d unique channels", region, len(channels))
    return channels


def get_channels_for_regions(regions: list[str], force_refresh: bool = False) -> dict[str, dict]:
    """
    Return {region: {gridKey: channel_dict}}.

    Uses channels.json cache when fresh; only calls the Plex API when the
    cache is missing, stale, or --refresh-channels is passed.
    """
    # --- try cache first ---
    if not force_refresh and _cache_is_fresh():
        cached = load_channels_cache()
        if cached:
            # If all requested regions are present, use the cache entirely
            missing = [r for r in regions if r not in cached]
            if not missing:
                logger.info("All regions served from channels.json cache.")
                return {r: cached[r] for r in regions}
            logger.info("Cache missing regions: %s – will fetch those.", missing)
            # Partial cache hit: reuse what we have, fetch only missing
            channels_by_region = {r: cached[r] for r in regions if r in cached}
            regions_to_fetch   = missing
        else:
            channels_by_region = {}
            regions_to_fetch   = regions
    else:
        if force_refresh:
            logger.info("--refresh-channels: ignoring cache, fetching all regions.")
        else:
            logger.info("channels.json is stale or missing – fetching all regions.")
        channels_by_region = {}
        regions_to_fetch   = regions

    # --- fetch missing/stale regions from API ---
    for region in regions_to_fetch:
        logger.info("Fetching channel list for region=%s …", region)
        token, client_id = get_anonymous_token(region)
        if not token:
            logger.error("  Skipping %s – could not get token", region)
            continue
        chs = fetch_channels_from_api(token, client_id, region)
        if chs:
            channels_by_region[region] = chs

    # --- persist updated cache ---
    if regions_to_fetch and channels_by_region:
        # Merge with any previously cached regions that weren't in our run
        existing = load_channels_cache() or {}
        merged   = {**existing, **channels_by_region}
        save_channels_cache(merged)

    return channels_by_region


# ---------------------------------------------------------------------------
# M3U generation
# ---------------------------------------------------------------------------

def build_m3u(
    channels: dict[str, dict],
    token: str,
    region: str,
    repo_raw_base: str,
) -> str:
    """
    Build M3U content for *region*.
    The #EXTM3U header's url-tvg= points to the matching .xml in the repo.
    """
    epg_url = f"{repo_raw_base}/playlists/plex_{region}.xml.gz"

    lines = [f'#EXTM3U url-tvg="{epg_url}"\n']

    for gk, ch in sorted(channels.items(), key=lambda x: x[1].get("name", "").lower()):
        name     = _sanitize(ch.get("name", gk))
        logo     = ch.get("logo", "")
        genres   = ch.get("genres", [])
        if region == "all":
            ch_region = ch.get("region", "")
            group = REGION_NAMES.get(ch_region, ch_region.upper()) if ch_region else "Other"
        else:
            group = genres[0] if genres else REGION_NAMES.get(region, region.upper())
        plex_key = ch.get("key", "")

        if not plex_key:
            continue   # no stream path → skip

        stream_url = f"https://epg.provider.plex.tv{plex_key}?X-Plex-Token={token}"

        extinf = (
            f'#EXTINF:-1 '
            f'channel-id="plex-{gk}" '
            f'tvg-id="{gk}" '
            f'tvg-name="{name.replace(chr(34), chr(39))}" '
            f'tvg-logo="{logo}" '
            f'group-title="{group.replace(chr(34), chr(39))}",{name}\n'
        )
        lines.append(extinf)
        lines.append(stream_url + "\n")

    return "".join(lines)


# ---------------------------------------------------------------------------
# EPG / XMLTV generation
# ---------------------------------------------------------------------------

def _parse_video_to_programme(video, grid_key: str) -> str | None:
    """
    Convert a single Plex <Video> element from the /grid response into an
    XMLTV <programme> string, including title, sub-title, description,
    category, episode numbers, rating, and artwork.
    """
    import xml.etree.ElementTree as ET

    video_type = video.attrib.get("type", "").lower()
    genres = [escape(_sanitize(g.attrib.get("tag", ""))) for g in video.findall("Genre")]

    # Title / subtitle
    if video_type == "movie":
        raw_title = _sanitize(video.attrib.get("title", ""))
        year      = video.attrib.get("year", "")
        title     = escape(f"{raw_title} ({year})" if year else raw_title) if "news" not in [g.lower() for g in genres] else escape(raw_title)
        subtitle  = None
        season    = None
        episode   = None
        art       = None
    else:
        title    = escape(_sanitize(video.attrib.get("grandparentTitle", video.attrib.get("title", "Unknown"))))
        subtitle = escape(_sanitize(video.attrib.get("title", "")))
        season   = video.attrib.get("parentIndex")
        episode  = video.attrib.get("index")
        art      = escape(video.attrib.get("grandparentArt", video.attrib.get("art", "")))

    desc           = escape(_sanitize(video.attrib.get("summary", "")))
    content_rating = escape(video.attrib.get("contentRating", ""))
    orig_date      = video.attrib.get("originallyAvailableAt", "")

    programmes = []
    for media in video.findall("Media"):
        begins_at = media.get("beginsAt")
        ends_at   = media.get("endsAt")
        if not begins_at or not ends_at:
            continue
        try:
            start = datetime.fromtimestamp(int(begins_at), tz=timezone.utc).strftime("%Y%m%d%H%M%S +0000")
            stop  = datetime.fromtimestamp(int(ends_at),   tz=timezone.utc).strftime("%Y%m%d%H%M%S +0000")
        except (ValueError, OSError):
            continue

        p  = f'<programme start="{start}" stop="{stop}" channel="{grid_key}">'
        p += f'<title lang="en">{title}</title>'
        if subtitle:
            p += f'<sub-title lang="en">{subtitle}</sub-title>'
        if desc:
            p += f'<desc lang="en">{desc}</desc>'
        for genre in genres:
            p += f'<category lang="en">{genre}</category>'
        if art:
            p += f'<icon src="{art}" />'
        if orig_date:
            p += f'<date>{orig_date[:10].replace("-", "")}</date>'
        if season and episode:
            p += f'<episode-num system="onscreen">S{season}E{episode}</episode-num>'
            p += f'<episode-num system="xmltv_ns">{int(season)-1}.{int(episode)-1}.</episode-num>'
        elif episode:
            p += f'<episode-num system="onscreen">E{episode}</episode-num>'
        if content_rating:
            p += f'<rating><value>{content_rating}</value></rating>'
        p += '</programme>'
        programmes.append(p)

    return "\n".join(programmes) if programmes else None


def _parse_video_from_json(video: dict, grid_key: str) -> str | None:
    """Convert a Plex Video dict (JSON response) into an XMLTV <programme> string."""
    video_type = video.get("type", "").lower()
    genres     = [escape(_sanitize(g.get("tag", ""))) for g in video.get("Genre", [])]

    if video_type == "movie":
        raw_title = _sanitize(video.get("title", ""))
        year      = video.get("year", "")
        is_news   = any(g.lower() == "news" for g in genres)
        title     = escape(f"{raw_title} ({year})" if year and not is_news else raw_title)
        subtitle, season, episode, art = None, None, None, None
    else:
        title    = escape(_sanitize(video.get("grandparentTitle", video.get("title", "Unknown"))))
        subtitle = escape(_sanitize(video.get("title", "")))
        season   = video.get("parentIndex")
        episode  = video.get("index")
        art      = escape(video.get("grandparentArt", video.get("art", "")))

    desc           = escape(_sanitize(video.get("summary", "")))
    content_rating = escape(video.get("contentRating", ""))
    orig_date      = video.get("originallyAvailableAt", "")

    programmes = []
    for media in video.get("Media", []):
        begins_at = media.get("beginsAt")
        ends_at   = media.get("endsAt")
        if not begins_at or not ends_at:
            continue
        try:
            start = datetime.fromtimestamp(int(begins_at), tz=timezone.utc).strftime("%Y%m%d%H%M%S +0000")
            stop  = datetime.fromtimestamp(int(ends_at),   tz=timezone.utc).strftime("%Y%m%d%H%M%S +0000")
        except (ValueError, OSError):
            continue

        p  = f'<programme start="{start}" stop="{stop}" channel="{grid_key}">'
        p += f'<title lang="en">{title}</title>'
        if subtitle:
            p += f'<sub-title lang="en">{subtitle}</sub-title>'
        if desc:
            p += f'<desc lang="en">{desc}</desc>'
        for genre in genres:
            p += f'<category lang="en">{genre}</category>'
        if art:
            p += f'<icon src="{art}" />'
        if orig_date:
            p += f'<date>{orig_date[:10].replace("-", "")}</date>'
        if season and episode:
            p += f'<episode-num system="onscreen">S{season}E{episode}</episode-num>'
            try:
                p += f'<episode-num system="xmltv_ns">{int(season)-1}.{int(episode)-1}.</episode-num>'
            except (ValueError, TypeError):
                pass
        elif episode:
            p += f'<episode-num system="onscreen">E{episode}</episode-num>'
        if content_rating:
            p += f'<rating><value>{content_rating}</value></rating>'
        p += '</programme>'
        programmes.append(p)

    return "\n".join(programmes) if programmes else None


def _fetch_epg_for_channel(
    channel: dict,
    date_str: str,
    token: str,
    client_id: str,
    ip: str,
) -> str | None:
    """
    GET epg.provider.plex.tv/grid?channelGridKey={gk}&date={YYYY-MM-DD}

    Requests JSON explicitly. Plex returns a MediaContainer with a Metadata
    (or Video) array of programme objects. Falls back to XML parsing if needed.
    """
    import xml.etree.ElementTree as ET

    grid_key = channel["gridKey"]

    # Force JSON — the BASE_HEADERS Accept includes json,text,* but being
    # explicit prevents Plex from returning an empty XML shell.
    headers = {
        **BASE_HEADERS,
        "Accept":                   "application/json",
        "X-Forwarded-For":          ip,
        "x-plex-client-identifier": client_id,
        "x-plex-platform-version":  "132.0",
        "x-plex-provider-version":  "7.2",
        "x-plex-token":             token,
        "x-plex-version":           "4.145.1",
    }
    params = {"channelGridKey": grid_key, "date": date_str}

    session = _make_session(retries=3, backoff=2.0)
    try:
        resp = session.get(
            "https://epg.provider.plex.tv/grid",
            headers=headers, params=params, timeout=REQUEST_TIMEOUT,
        )
        if resp.status_code != 200:
            return None

        raw = resp.text.strip()
        if not raw:
            return None

        ct = resp.headers.get("Content-Type", "")

        # JSON path (preferred)
        if "json" in ct or raw.startswith("{"):
            try:
                data   = resp.json()
                mc     = data.get("MediaContainer", {})
                videos = mc.get("Metadata", []) or mc.get("Video", [])
            except Exception:
                videos = []
            parts = [p for v in videos for p in [_parse_video_from_json(v, grid_key)] if p]
            return "\n".join(parts) if parts else None

        # XML fallback
        try:
            root   = ET.fromstring(raw)
            videos = root.findall(".//Video")
        except ET.ParseError:
            return None
        parts = [p for v in videos for p in [_parse_video_to_programme(v, grid_key)] if p]
        return "\n".join(parts) if parts else None

    except Exception as exc:
        logger.debug("EPG fetch error for %s/%s: %s", grid_key, date_str, exc)
        return None
    finally:
        session.close()


def build_epg(
    channels:  dict[str, dict],
    token:     str,
    client_id: str,
    region:    str,
    days:      int = EPG_DAYS,
) -> str:
    """Build XMLTV content for *region* covering *days* days."""
    ip    = GEO_IPS.get(region, GEO_IPS["us"])
    today = datetime.now(timezone.utc)
    dates = [(today + timedelta(days=d)).strftime("%Y-%m-%d") for d in range(days)]

    # <channel> entries
    channel_xml: list[str] = []
    for gk, ch in channels.items():
        name = escape(_sanitize(ch.get("name", gk)))
        logo = escape(ch.get("logo", ""))
        block = f'  <channel id="{gk}">\n    <display-name>{name}</display-name>\n'
        if logo:
            block += f'    <icon src="{logo}" />\n'
        block += "  </channel>\n"
        channel_xml.append(block)

    # <programme> entries – fetched concurrently
    tasks = [(ch, date) for ch in channels.values() for date in dates]
    logger.info("  Fetching EPG: %d channels × %d days = %d requests …",
                len(channels), days, len(tasks))

    programme_xml: list[str] = []
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
        futures = {
            pool.submit(_fetch_epg_for_channel, ch, date, token, client_id, ip): (ch, date)
            for ch, date in tasks
        }
        for future in as_completed(futures):
            result = future.result()
            if result:
                programme_xml.append(result)

    logger.info("  EPG: collected %d programme blocks for %s", len(programme_xml), region)

    return (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<!DOCTYPE tv SYSTEM "xmltv.dtd">\n'
        '<tv generator-info-name="plex-alt-fast-channels" '
        'generator-info-url="https://github.com/BuddyChewChew/plex-alt-fast-channels">\n'
        + "".join(channel_xml)
        + "\n".join(programme_xml) + "\n"
        + "</tv>\n"
    )


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def parse_args():
    p = argparse.ArgumentParser(description="Generate Plex free live TV playlists")
    p.add_argument(
        "--regions", nargs="+", default=list(GEO_IPS.keys()),
        help="Region codes to generate (default: all)",
    )
    p.add_argument(
        "--refresh-channels", action="store_true",
        help="Ignore channels.json cache and re-fetch from Plex API",
    )
    p.add_argument(
        "--no-epg", action="store_true",
        help="Skip EPG / XMLTV generation",
    )
    p.add_argument(
        "--days", type=int, default=EPG_DAYS,
        help=f"Days of EPG to fetch (default: {EPG_DAYS})",
    )
    p.add_argument(
        "--repo", default=REPO_RAW_BASE,
        help="Raw base URL of the repo (used in url-tvg= links)",
    )
    return p.parse_args()


def main():
    args = parse_args()
    cleanup_output_dir()

    # ── 1. Get channel metadata (cache or API) ────────────────────────────
    channels_by_region = get_channels_for_regions(
        args.regions, force_refresh=args.refresh_channels
    )

    if not channels_by_region:
        logger.error("No channel data – aborting.")
        return

    # ── 2. Per-region M3U + EPG ───────────────────────────────────────────
    all_channels: dict[str, dict] = {}   # merged set for plex_all.*

    # One anonymous token, reused for every region. The token itself isn't
    # region-specific (it's just an anonymous session credential embedded in
    # stream/EPG URLs); geo-spoofing happens separately via X-Forwarded-For
    # on the per-region EPG/grid requests. Fetching 15 separate tokens in a
    # loop was hammering the token endpoint and tipping Plex into 429s
    # partway through the run.
    token, client_id = get_anonymous_token(args.regions[0] if args.regions else "us")
    if not token:
        logger.error("Could not obtain an anonymous token – aborting.")
        return

    for region in args.regions:
        channels = channels_by_region.get(region)
        if not channels:
            logger.warning("No channels for region=%s – skipping.", region)
            continue

        logger.info("=== %s (%d channels) ===", region.upper(), len(channels))

        # M3U  (url-tvg= header points to repo XML)
        m3u = build_m3u(channels, token, region, args.repo)
        write_playlist(f"plex_{region}.m3u", m3u)

        # EPG
        if not args.no_epg:
            xml = build_epg(channels, token, client_id, region, days=args.days)
            write_playlist(f"plex_{region}.xml", xml)

        # Accumulate for "all" files (first region wins for duplicate gridKeys)
        for gk, ch in channels.items():
            if gk not in all_channels:
                all_channels[gk] = {**ch, "region": region}

    # ── 3. Combined plex_all.* ────────────────────────────────────────────
    if all_channels:
        logger.info("=== Building plex_all.* (%d channels) ===", len(all_channels))

        # Reuse the same token fetched in step 2 – no need to hit the
        # token endpoint again.
        all_token, all_client_id = token, client_id

        if all_token:
            all_m3u = build_m3u(all_channels, all_token, "all", args.repo)
            write_playlist("plex_all.m3u", all_m3u)

            if not args.no_epg:
                # Merge per-region .xml.gz files into plex_all.xml.gz
                # Reading from already-compressed files avoids holding everything
                # in memory at once.
                logger.info("Building plex_all.xml.gz from per-region files …")
                all_out_path = os.path.join(OUTPUT_DIR, "plex_all.xml.gz")
                seen_channel_ids: set[str] = set()
                channel_blocks:   list[str] = []
                programme_blocks: list[str] = []

                for region in args.regions:
                    fp = os.path.join(OUTPUT_DIR, f"plex_{region}.xml.gz")
                    fp_plain = os.path.join(OUTPUT_DIR, f"plex_{region}.xml")
                    if not os.path.exists(fp) and not os.path.exists(fp_plain):
                        logger.warning("  No EPG file found for region=%s – skipping", region)
                        continue
                    try:
                        if os.path.exists(fp):
                            logger.info("  Merging %s …", fp)
                            with gzip.open(fp, "rt", encoding="utf-8") as fh:
                                xml_text = fh.read()
                        else:
                            logger.info("  Merging %s (uncompressed) …", fp_plain)
                            with open(fp_plain, "r", encoding="utf-8") as fh:
                                xml_text = fh.read()
                    except Exception as exc:
                        logger.warning("Could not read EPG for %s: %s", region, exc)
                        continue

                    for block in re.findall(r"<channel[^>]*>.*?</channel>", xml_text, re.DOTALL):
                        cid_match = re.search(r'id="([^"]+)"', block)
                        if cid_match:
                            cid = cid_match.group(1)
                            if cid not in seen_channel_ids:
                                seen_channel_ids.add(cid)
                                channel_blocks.append(block)

                    programme_blocks.extend(
                        re.findall(r"<programme[^>]*>.*?</programme>", xml_text, re.DOTALL)
                    )

                all_xml = (
                    '<?xml version="1.0" encoding="UTF-8"?>\n'
                    '<!DOCTYPE tv SYSTEM "xmltv.dtd">\n'
                    '<tv generator-info-name="plex-alt-fast-channels" '
                    'generator-info-url="https://github.com/BuddyChewChew/plex-alt-fast-channels">\n'
                    + "\n".join(channel_blocks) + "\n"
                    + "\n".join(programme_blocks) + "\n"
                    + "</tv>\n"
                )

                with gzip.open(all_out_path, "wt", encoding="utf-8") as fh:
                    fh.write(all_xml)
                logger.info(
                    "Wrote playlists/plex_all.xml.gz  (%d channels, %d programmes, %d bytes compressed)",
                    len(seen_channel_ids), len(programme_blocks),
                    os.path.getsize(all_out_path),
                )

    logger.info("Done – files in ./%s/", OUTPUT_DIR)


if __name__ == "__main__":
    main()
