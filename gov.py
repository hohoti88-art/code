#!/usr/bin/env python3
"""
한국 정부 지원 정책 / 보조금 공고 프로필 기반 추천 엔진
다양한 API와 지자체 사이트, 웹 검색을 활용하여 프로필에 부합하는 공고를 수집
절대 기준: 지역 필터(경기/전국/수도권), 교육 키워드, 제외 키워드(!입주 등), 금액 상한선
"""

import datetime
import html
import io
import os
import re
import time
import urllib.parse
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

import requests

try:
    from bs4 import BeautifulSoup  # type: ignore
    HAS_BS4 = True
except Exception:
    BeautifulSoup = None
    HAS_BS4 = False

try:
    from dotenv import load_dotenv
except Exception:
    def load_dotenv() -> bool:
        return False

try:
    from pypdf import PdfReader  # type: ignore
    HAS_PYPDF = True
except Exception:
    PdfReader = None
    HAS_PYPDF = False

try:
    import fitz  # type: ignore
    HAS_PYMUPDF = True
except Exception:
    fitz = None
    HAS_PYMUPDF = False

HAS_PDF_LIB = HAS_PYPDF or HAS_PYMUPDF


# ============================================================================
# 설정 상수 (Constants)
# ============================================================================

REQUEST_TIMEOUT = 30
SLEEP = 0.08
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
)

# 수집 범위 (최적화)
MAX_DOCS_PER_SOURCE = 250  # 안정적 멀티페이지 수집 (페이지2 안전)
ENRICH_TOPK = 35  # HTML/PDF 확장
PDF_MAX_FILES = 1  
PDF_MAX_BYTES = 2_000_000  
PDF_MAX_PAGES = 6  
PDF_TEXT_MAX_CHARS = 8_000  
WEB_SEARCH_ENABLED = True
WEB_SEARCH_TOP_PER_QUERY = 10

# 절대 기준 (Hard Rules) - Instructions 준수
TOP3_MIN_SUPPORT_KRW = 50_000_000      # ≥50M KRW만 TOP3 고려
PER_ENTITY_CAP_KRW = 2_000_000_000     # >2B KRW는 제외 (오류 추정)
MIN_PROFILE_SCORE = 12                  # 최소 프로필 적합도 (낮춤: 더 많은 공고)
MIN_CORE_MATCH_FIELDS = 1              # 최소 핵심 필드 매칭 (낮춤)

# 필터 규칙
ALLOWED_REGIONS = {"경기", "전국", "수도권"}
EXCLUDE_KEYWORDS = {
    "광주",
    "경진대회",
    "창업경진대회",
    "임대",
    "설명회",
}

# 레포트
REPORT_FILENAME = "공고추천_리포트.md"

# 프로필 필드
PROFILE_KEYS = [
    "소재지",
    "개인/법인",
    "업종",
    "업력",
    "주요 상품",
    "주요 거래처",
    "인증",
    "특허",
    "자금목적",
    "기업애로",
    "고려사항",
]

CORE_FIELDS = {"업종", "자금목적", "주요 상품", "주요 거래처"}

DEFAULT_PROFILE_TEXT = """
소재지: 대전시
개인/법인: 법인
업종: 유아 교육, 그림책 출판
업력: 4년
주요 상품: 콘텐츠
주요 거래처: 교육 관련 기관
인증: 벤처기업인증
특허: 특허 1건
자금목적: 운영자금
기업애로: 고금리와 매출 둔화
고려사항: !창업경진대회, !멘토링, !입주
""".strip()

# API 소스 (ChatGPT가 작성한 다양한 출처)
API_SOURCES: List[Dict[str, Any]] = [
    {
        "name": "중소벤처기업부 사업공고",
        "base_url": "https://apis.data.go.kr/1421000/mssBizService_v2",
        "op": "getbizList_v2",
        "kind": "bizinfo",
        "page_param": "pageNo",
        "size_param": "numOfRows",
        "page_start": 1,
        "page_end": 35,
        "size": 100,
        "fixed_params": {"type": "json"},
    },
    {
        "name": "K-Startup 지원사업 공고",
        "base_url": "https://apis.data.go.kr/B552735/kisedKstartupService01",
        "op": "getAnnouncementInformation01",
        "kind": "kstartup",
        "page_param": "page",
        "size_param": "perPage",
        "page_start": 1,
        "page_end": 35,
        "size": 50,
        "fixed_params": {"returnType": "JSON"},
    },
    {
        "name": "K-Startup 통합공고",
        "base_url": "https://apis.data.go.kr/B552735/kisedKstartupService01",
        "op": "getBusinessInformation01",
        "kind": "kstartup",
        "page_param": "page",
        "size_param": "perPage",
        "page_start": 1,
        "page_end": 35,
        "size": 50,
        "fixed_params": {"returnType": "JSON"},
    },
]

# 지자체 도메인 매핑 (검색 및 직접 크롤링용)
MUNICIPAL_DOMAINS: Dict[str, List[str]] = {
    "대전": ["daejeon.go.kr"],
    "서울": ["seoul.go.kr"],
    "부산": ["busan.go.kr"],
    "인천": ["incheon.go.kr"],
    "대구": ["daegu.go.kr"],
    "광주": ["gwangju.go.kr"],
    "울산": ["ulsan.go.kr"],
    "세종": ["sejong.go.kr"],
    # 전국형/도 단위는 간단히 gg.go.kr 등
    "경기": ["gg.go.kr"],
    "강원": ["gangwon.go.kr"],
    "충북": ["cb.go.kr"],
    "충남": ["cn.go.kr"],
    "전북": ["jb.go.kr"],
    "전남": ["jn.go.kr"],
    "경북": ["gb.go.kr"],
    "경남": ["gn.go.kr"],
    "제주": ["jeju.go.kr"],
}



@dataclass
class Posting:
    """공고 데이터 모델"""
    source: str
    title: str
    content: str
    detail_url: str
    end_date_raw: str = ""
    ongoing_raw: str = ""
    region_raw: str = ""
    amount_krw: int = 0
    score: int = 0
    core_match_count: int = 0
    matched_keywords: List[str] = field(default_factory=list)
    pdf_used: bool = False
    pdf_urls: List[str] = field(default_factory=list)



def load_env_fallback(path: str) -> None:
    if not path or not os.path.exists(path):
        return
    try:
        with open(path, "r", encoding="utf-8") as f:
            for raw in f:
                line = raw.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                k = k.strip()
                v = v.strip().strip("'").strip('"')
                if k:
                    os.environ.setdefault(k, v)
    except Exception:
        return


def normalize_text(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "")).strip()


def normalize_key(s: str) -> str:
    return re.sub(r"[^0-9a-z가-힣/_\- ]", "", normalize_text(s).lower())


def tokenize(s: str) -> List[str]:
    parts = re.split(r"[,/;|\s]+", (s or "").strip())
    out: List[str] = []
    seen: Set[str] = set()
    for p in parts:
        p = p.strip()
        if len(p) < 2 or p in seen:
            continue
        seen.add(p)
        out.append(p)
    return out


def ensure_http(url: str, default_domain: str = "") -> str:
    u = (url or "").strip()
    if not u:
        return ""
    if u.startswith(("http://", "https://")):
        return u
    if u.startswith("//"):
        return "https:" + u
    if u.startswith("www."):
        return "https://" + u
    if u.startswith("/") and default_domain:
        return default_domain.rstrip("/") + u
    return u


def parse_profile_text(profile_text: str) -> Dict[str, str]:
    out = {k: "" for k in PROFILE_KEYS}
    for line in re.split(r"[\r\n]+", (profile_text or "").strip()):
        if ":" not in line:
            continue
        k, v = line.split(":", 1)
        k = normalize_text(k)
        v = normalize_text(v)
        if k in out:
            out[k] = v
    return out


def parse_simple_yaml_profile(yaml_text: str) -> Dict[str, str]:
    out = {k: "" for k in PROFILE_KEYS}
    for raw in re.split(r"[\r\n]+", yaml_text or ""):
        line = raw.strip()
        if not line or line.startswith("#") or ":" not in line:
            continue
        k, v = line.split(":", 1)
        k = normalize_text(k)
        v = normalize_text(v).strip("'").strip('"')
        if k in out:
            out[k] = v
    return out


def choose_profile_path() -> str:
    env_path = os.getenv("PROFILE_PATH", "").strip()
    if env_path:
        return env_path
    for candidate in ("profile.yaml", "profile.yml", "profile.txt"):
        if os.path.exists(candidate):
            return candidate
    return "profile.yaml"


def load_profile_from_file(path: str) -> Dict[str, str]:
    if not path or not os.path.exists(path):
        return parse_profile_text(DEFAULT_PROFILE_TEXT)
    with open(path, "r", encoding="utf-8") as f:
        body = f.read()
    ext = os.path.splitext(path)[1].lower()
    p = parse_simple_yaml_profile(body) if ext in (".yaml", ".yml") else parse_profile_text(body)
    if not any(v.strip() for v in p.values()):
        return parse_profile_text(DEFAULT_PROFILE_TEXT)
    return p


def safe_get_items(payload: Dict[str, Any]) -> List[Dict[str, Any]]:
    candidates = [
        payload,
        payload.get("body", {}) if isinstance(payload, dict) else {},
        payload.get("response", {}) if isinstance(payload, dict) else {},
        payload.get("response", {}).get("body", {}) if isinstance(payload, dict) else {},
    ]
    for c in candidates:
        if not isinstance(c, dict):
            continue
        for key in ("items", "item", "data", "list", "result"):
            v = c.get(key)
            if isinstance(v, list):
                return [x for x in v if isinstance(x, dict)]
            if isinstance(v, dict) and isinstance(v.get("item"), list):
                return [x for x in v["item"] if isinstance(x, dict)]
    return []


def xml_to_dict_payload(xml_text: str) -> Dict[str, Any]:
    out: Dict[str, Any] = {"items": []}
    try:
        root = ET.fromstring(xml_text)
    except Exception:
        return out
    parent = root.find(".//items")
    if parent is None:
        return out
    rows: List[Dict[str, Any]] = []
    for item in parent.findall("./item"):
        row: Dict[str, Any] = {}
        for child in list(item):
            key = child.tag or ""
            if not key:
                continue
            val = (child.text or "").strip()
            row[key] = f"{row.get(key, '')} {val}".strip() if key in row else val
        if row:
            rows.append(row)
    out["items"] = rows
    return out


def request_json(base_url: str, op: str, params: Dict[str, Any], gov_api_key: str) -> Optional[Dict[str, Any]]:
    url = base_url.rstrip("/") + "/" + op.lstrip("/")
    q = {"serviceKey": gov_api_key, **params}
    
    max_retries = 4
    for attempt in range(max_retries):
        try:
            r = requests.get(url, params=q, timeout=30, headers={"User-Agent": USER_AGENT})
            if r.status_code == 200:
                try:
                    return r.json()
                except Exception:
                    txt = (r.text or "").strip()
                    return xml_to_dict_payload(txt) if txt.startswith("<") else None
            elif r.status_code >= 500:  # 서버 에러 재시도
                if attempt < max_retries - 1:
                    wait_time = min(2 ** attempt, 20)
                    time.sleep(wait_time)
                    continue
            return None
        except (requests.Timeout, requests.ConnectionError, Exception) as e:
            if attempt < max_retries - 1:
                wait_time = min(2 ** attempt, 20)
                time.sleep(wait_time)
                continue
            return None

def join_fields(item: Dict[str, Any]) -> str:
    return normalize_text(" ".join(str(v).strip() for v in item.values() if isinstance(v, str) and v.strip()))


def parse_bizinfo_item(item: Dict[str, Any], source_name: str) -> Posting:
    title = str(item.get("pblancNm") or item.get("title") or "공고")
    content = normalize_text(" ".join([
        str(item.get("polixNm") or ""),
        str(item.get("cnSummary") or ""),
        str(item.get("dtlcn") or ""),
        str(item.get("dataContents") or ""),
        join_fields(item),
    ]))
    url = ensure_http(str(item.get("pblancUrl") or item.get("viewUrl") or ""), "https://www.bizinfo.go.kr")
    pblanc_id = str(item.get("pblancId") or item.get("itemId") or "").strip()
    if not url and pblanc_id:
        url = f"https://www.bizinfo.go.kr/sii/siia/selectSIIA200Detail.do?pblancId={pblanc_id}"
    return Posting(
        source=source_name,
        title=normalize_text(title),
        content=content,
        detail_url=url or "https://www.bizinfo.go.kr",
        end_date_raw=str(item.get("reqstEndDt") or item.get("endDate") or item.get("applicationEndDate") or ""),
        ongoing_raw=str(item.get("ongoingYn") or ""),
        region_raw=str(item.get("jrsdInsttNm") or item.get("area") or ""),
    )


def parse_kstartup_item(item: Dict[str, Any], source_name: str) -> Posting:
    title = str(item.get("biz_pbanc_nm") or item.get("title") or "공고")
    pbanc_sn = str(item.get("pbanc_sn") or item.get("pbancSn") or "").strip()
    url = ensure_http(str(item.get("detl_pg_url") or ""), "https://www.k-startup.go.kr")
    if not url and pbanc_sn:
        url = f"https://www.k-startup.go.kr/web/contents/bizpbanc-ongoing.do?schM=view&pbancSn={pbanc_sn}"
    content = normalize_text(" ".join([
        str(item.get("pbanc_ctnt") or ""),
        str(item.get("aply_trgt_ctnt") or ""),
        str(item.get("prfr_conds_ctnt") or ""),
        str(item.get("biz_supt_bdgt_info") or ""),
        str(item.get("supt_scale") or ""),
        join_fields(item),
    ]))
    return Posting(
        source=source_name,
        title=normalize_text(title),
        content=content,
        detail_url=url or "https://www.k-startup.go.kr",
        end_date_raw=str(item.get("pbanc_rcpt_end_dt") or ""),
        ongoing_raw=str(item.get("ongoing_yn") or ""),
        region_raw=str(item.get("supt_regin") or item.get("supt_regin_nm") or ""),
    )


def parse_institution_item(item: Dict[str, Any], source_name: str) -> Posting:
    name = str(item.get("inst_nm") or item.get("instNm") or "기관")
    content = normalize_text(" ".join([
        str(item.get("inst_desc") or item.get("instDesc") or ""),
        str(item.get("inst_hmpr_url") or item.get("instHmprUrl") or ""),
        join_fields(item),
    ]))
    url = ensure_http(str(item.get("inst_hmpr_url") or item.get("instHmprUrl") or "")) or "https://www.k-startup.go.kr"
    return Posting(source=source_name, title=f"[기관] {normalize_text(name)}", content=content, detail_url=url)


PARSER_BY_KIND = {
    "bizinfo": parse_bizinfo_item,
    "kstartup": parse_kstartup_item,
    "institution": parse_institution_item,
}


def collect_from_api_source(source: Dict[str, Any], max_docs: int, gov_api_key: str) -> List[Posting]:
    parser = PARSER_BY_KIND[source["kind"]]
    out: List[Posting] = []
    if not source.get("page_param") or not source.get("size_param"):
        data = request_json(source["base_url"], source["op"], dict(source.get("fixed_params", {})), gov_api_key)
        if not data:
            return out
        for item in safe_get_items(data)[:max_docs]:
            try:
                out.append(parser(item, source["name"]))
            except Exception:
                continue
        return out

    for page in range(source["page_start"], source["page_end"] + 1):
        if len(out) >= max_docs:
            break
        params = dict(source.get("fixed_params", {}))
        params[source["page_param"]] = page
        params[source["size_param"]] = source["size"]
        data = request_json(source["base_url"], source["op"], params, gov_api_key)
        if not data:
            if page == source["page_start"]:
                print(f"  [WARN] {source['name']} 응답 없음")
            break
        items = safe_get_items(data)
        if not items:
            break
        before = len(out)
        for item in items:
            try:
                out.append(parser(item, source["name"]))
            except Exception:
                continue
            if len(out) >= max_docs:
                break
        print(f"  [OK] {source['name']} page={page} +{len(out)-before} (누적 {len(out)})")
        time.sleep(SLEEP)
    return out


def parse_google_results(html_text: str, max_results: int) -> List[Tuple[str, str]]:
    out: List[Tuple[str, str]] = []
    for m in re.finditer(r'<a href="(/url\?[^\"]+)"[^>]*>(.*?)</a>', html_text or "", re.I | re.S):
        if len(out) >= max_results:
            break
        href = m.group(1)
        label = normalize_text(re.sub(r"<[^>]+>", " ", m.group(2)))
        q = urllib.parse.urlparse(href).query
        url = urllib.parse.parse_qs(q).get("q", [""])[0]
        url = ensure_http(url)
        if url and "google." not in url:
            out.append((label or "검색결과", url))
    return out


def parse_ddg_results(html_text: str, max_results: int) -> List[Tuple[str, str]]:
    out: List[Tuple[str, str]] = []
    for m in re.finditer(r"<a\s[^>]*href=[\"']([^\"']+)[\"'][^>]*>(.*?)</a>", html_text or "", re.I | re.S):
        if len(out) >= max_results:
            break
        href = m.group(1).strip()
        label = normalize_text(re.sub(r"<[^>]+>", " ", m.group(2)))
        if "duckduckgo.com/l/?" in href:
            q = urllib.parse.urlparse(href).query
            href = urllib.parse.unquote(urllib.parse.parse_qs(q).get("uddg", [""])[0])
        url = ensure_http(href)
        if url and "duckduckgo.com" not in url:
            out.append((label or "검색결과", url))
    return out


def parse_bing_rss(xml_text: str, max_results: int) -> List[Tuple[str, str]]:
    out: List[Tuple[str, str]] = []
    try:
        root = ET.fromstring(xml_text)
    except Exception:
        return out
    for item in root.findall(".//item"):
        if len(out) >= max_results:
            break
        title = normalize_text(item.findtext("title") or "검색결과")
        link = ensure_http(item.findtext("link") or "")
        if link:
            out.append((title, link))
    return out


def build_search_queries(profile: Dict[str, str]) -> List[str]:
    base: List[str] = []
    for k in ("업종", "자금목적", "소재지", "주요 상품"):
        base.extend(tokenize(profile.get(k, ""))[:2])
    phrase = " ".join(base[:4]).strip()
    region = (profile.get("소재지", "") or "").strip().split()[0] if profile.get("소재지") else ""
    
    queries = [
        f"중소기업 지원사업 공고 {phrase}".strip(),
        f"정책자금 지원사업 공고 {phrase}".strip(),
        f"k-startup 지원사업 공고 {phrase}".strip(),
        f"site:bizinfo.go.kr {phrase} 지원사업 공고".strip(),
        f"site:k-startup.go.kr {phrase} 지원사업 공고".strip(),
        f"site:smes.go.kr {phrase} 지원사업 공고".strip(),
        f"site:mss.go.kr {phrase} 지원사업 공고".strip(),
    ]
    
    # 지자체 공고 (프로필 지역 기반 도메인 검색 추가)
    if region:
        for key, domains in MUNICIPAL_DOMAINS.items():
            if key in region:
                # 일반 검색 문구
                queries.append(f"{region} 중소기업 지원사업 공고")
                queries.append(f"{region}청 지원금 공고 {phrase}".strip())
                # 도메인별 site:쿼리
                for dom in domains:
                    queries.append(f"site:{dom} 지원사업 공고 {phrase}".strip())
                break

    return list(dict.fromkeys(queries))


def collect_web_search(profile: Dict[str, str]) -> List[Posting]:
    if not WEB_SEARCH_ENABLED:
        return []
    session = requests.Session()
    session.headers.update({"User-Agent": USER_AGENT})
    out: List[Posting] = []
    
    def safe_request(url: str, timeout: int = 30, max_retries: int = 2) -> Optional[str]:
        for attempt in range(max_retries):
            try:
                r = session.get(url, timeout=timeout)
                if r.status_code == 200:
                    return r.text
            except Exception:
                if attempt < max_retries - 1:
                    time.sleep(min(2 ** attempt, 10))
        return None
    
    for query in build_search_queries(profile):
        results: List[Tuple[str, str]] = []
        
        html = safe_request("https://www.google.com/search?q=" + urllib.parse.quote_plus(query), timeout=30)
        if html:
            results.extend(parse_google_results(html, WEB_SEARCH_TOP_PER_QUERY))
        
        if len(results) < WEB_SEARCH_TOP_PER_QUERY:
            html = safe_request("https://html.duckduckgo.com/html/?q=" + urllib.parse.quote_plus(query), timeout=30)
            if html:
                results.extend(parse_ddg_results(html, WEB_SEARCH_TOP_PER_QUERY - len(results)))
        
        if len(results) < WEB_SEARCH_TOP_PER_QUERY:
            html = safe_request("https://www.bing.com/search?format=rss&q=" + urllib.parse.quote_plus(query), timeout=30)
            if html:
                results.extend(parse_bing_rss(html, WEB_SEARCH_TOP_PER_QUERY - len(results)))
        
        seen: Set[str] = set()
        for title, url in results:
            if not url or url in seen:
                continue
            seen.add(url)
            out.append(Posting(source="웹검색", title=title, content=title, detail_url=url))
        print(f"  [OK] 웹검색 '{query}' -> {len(seen)}건")
        time.sleep(SLEEP)
    return out


def get_municipal_domains(region: str) -> List[str]:
    """프로필 지역에서 사용할 지자체 도메인 목록 반환"""
    if not region:
        return []
    region = region.strip()
    for key, domains in MUNICIPAL_DOMAINS.items():
        if key in region:
            return domains
    return []


def collect_municipal_announcements(region: str, max_docs: int = 10) -> List[Posting]:
    """지자체 도메인 목록을 기반으로 간단히 링크를 크롤링하여 공고를 수집한다.
    실패해도 빈 리스트를 반환하며, 제목에 '지원' 또는 '공고'가 포함된 링크를 후보로 삼는다.
    """
    out: List[Posting] = []
    domains = get_municipal_domains(region)
    if not domains or not HAS_BS4:
        return out

    session = requests.Session()
    session.headers.update({"User-Agent": USER_AGENT})

    for dom in domains:
        if len(out) >= max_docs:
            break
        base_url = f"https://{dom}"
        try:
            r = session.get(base_url, timeout=REQUEST_TIMEOUT)
            if r.status_code != 200:
                continue
            soup = BeautifulSoup(r.content, "html.parser")
            for a in soup.find_all("a", href=True):
                if len(out) >= max_docs:
                    break
                text = normalize_text(a.get_text())
                if not text:
                    continue
                # 공고나 지원 관련 단어가 있으면 후보
                if re.search(r"(지원|공고|사업|자금)", text):
                    link = ensure_http(a['href'], default_domain=base_url)
                    if link:
                        out.append(Posting(
                            source=f"지자체:{dom}",
                            title=text,
                            content=text,
                            detail_url=link,
                        ))
        except Exception:
            continue
        time.sleep(SLEEP)
    return out


def ensure_local_postings(strong: List[Posting], rescored: List[Posting], profile: Dict[str, str]) -> List[Posting]:
    """강적합 리스트에 지자체 공고가 최소 3건 포함되도록 보정한다."""
    region = profile.get("소재지", "").lower()
    if not region:
        return strong
    def is_local(r: Posting) -> bool:
        if r.source.startswith("지자체"):
            return True
        if region in r.detail_url.lower():
            return True
        return False

    local_count = sum(1 for r in strong if is_local(r))
    if local_count >= 3:
        return strong
    for r in rescored:
        if r in strong:
            continue
        if is_local(r):
            strong.append(r)
            local_count += 1
            if local_count >= 3:
                break
    return strong


def dedup_postings(rows: List[Posting]) -> List[Posting]:
    out: List[Posting] = []
    seen: Set[str] = set()
    for r in rows:
        key = f"{normalize_key(r.title)}|{r.detail_url.strip().lower()}"
        if key in seen:
            continue
        seen.add(key)
        out.append(r)
    return out


def collect_all_postings(profile: Dict[str, str], gov_api_key: str) -> List[Posting]:
    rows: List[Posting] = []
    for src in API_SOURCES:
        print(f"[수집] {src['name']} ({src['op']})")
        rows.extend(collect_from_api_source(src, MAX_DOCS_PER_SOURCE, gov_api_key))
    
    if WEB_SEARCH_ENABLED:
        print("[수집] 웹검색 보강 (지자체 포함)")
        rows.extend(collect_web_search(profile))
        # 추가로 프로필 지역 지자체 웹사이트에서 직접 공고 링크를 긁어본다.
        region = profile.get("소재지", "")
        if region:
            print("[수집] 지자체 사이트 스크래핑")
            rows.extend(collect_municipal_announcements(region, max_docs=MAX_DOCS_PER_SOURCE))
    rows = dedup_postings([r for r in rows if normalize_text(r.title)])
    print(f"[완료] 총 {len(rows)}건 수집")
    return rows

def parse_end_date(raw: str) -> Optional[datetime.date]:
    s = normalize_text(raw)
    if not s:
        return None
    m = re.search(r"(20\d{2})[.\-/](\d{1,2})[.\-/](\d{1,2})", s)
    if not m:
        m = re.search(r"(20\d{2})(\d{2})(\d{2})", s)
    if not m:
        return None
    try:
        return datetime.date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
    except Exception:
        return None


def is_closed(row: Posting) -> bool:
    end_dt = parse_end_date(row.end_date_raw)
    if end_dt and end_dt < datetime.date.today():
        return True
    if row.ongoing_raw.strip().upper() == "N" and end_dt and end_dt < datetime.date.today():
        return True
    return False


def extract_amount_krw(text: str) -> int:
    t = (text or "").lower()
    best = 0
    # 억원
    for m in re.finditer(r"(\d+(?:\.\d+)?)\s*억", t):
        best = max(best, int(float(m.group(1)) * 100_000_000))
    # 천만원
    for m in re.finditer(r"(\d+(?:,\d{3})*(?:\.\d+)?)\s*천\s*만원", t):
        best = max(best, int(float(m.group(1).replace(",", "")) * 10_000_000))
    # 만원
    for m in re.finditer(r"(\d+(?:,\d{3})*(?:\.\d+)?)\s*만원", t):
        best = max(best, int(float(m.group(1).replace(",", "")) * 10_000))
    # 원 (콤마 있음)
    for m in re.finditer(r"(\d+(?:,\d{3})+)\s*원", t):
        best = max(best, int(m.group(1).replace(",", "")))
    return best


def has_education_keyword(text: str) -> bool:
    """교육 관련 키워드 검사"""
    return bool(re.search(r"(교육|학교|학원|강의|훈련|교과|과정)", text, re.I))


def has_support_keyword(text: str) -> bool:
    """지원/자금 관련 키워드 검사"""
    return bool(re.search(r"(지원|지원금|보조금|사업화|바우처|정책자금|융자|보증|자금|펀드)", text, re.I))


def allow_region(text: str, profile_region: str) -> bool:
    """절대 기준: 지역 필터(경기/전국/수도권만 허용)"""
    if not profile_region or not text:
        return False
    
    text_norm = text.lower()
    prof_norm = profile_region.lower()
    
    # 1. 전국/전체 키워드
    if any(k in text_norm for k in ["전국", "전 지역", "전체", "해외"]):
        return True
    
    # 2. 프로필 지역명 매칭
    for allowed in ALLOWED_REGIONS:
        if allowed in prof_norm and allowed in text_norm:
            return True
    
    # 3. 프로필의 상위 지역 (시도명)
    prof_tokens = tokenize(prof_norm)
    for tok in prof_tokens:
        if tok and len(tok) >= 2 and tok in text_norm:
            return True
    
    return False


def pass_absolute_filters(row: Posting, profile: Dict[str, str]) -> Tuple[bool, str]:
    """절대 기준 필터링 - Instructions 준수"""
    merged = f"{row.title} {row.content} {row.region_raw}".lower()
    
    # 0. 주관기관/기관공고 제외 (절대 제외)
    if "[기관]" in row.title or "주관기관" in merged:
        return False, "주관기관제외"
    
    # 1. 금액 상한선 (2B 초과 제외)
    if row.amount_krw > PER_ENTITY_CAP_KRW:
        return False, "금액초과"
    
    # 2. 지역 필터 (경기/전국/수도권만)
    profile_region = profile.get("소재지", "").strip()
    if not allow_region(merged, profile_region):
        return False, "지역불일치"
    
    # 3. 교육 필터 (지원금 키워드 없으면 제외)
    if has_education_keyword(merged):
        if not has_support_keyword(merged):
            return False, "교육(자금키워드없음)"
    
    # 4. 제외 키워드
    for exclude_kw in EXCLUDE_KEYWORDS:
        if exclude_kw.lower() in merged:
            return False, f"제외:{exclude_kw}"
    
    # 5. !로 시작하는 제외 조건
    for tok in tokenize(profile.get("고려사항", "")):
        if tok.startswith("!"):
            bad = tok[1:].lower()
            if bad and bad in merged:
                return False, f"제외:{bad}"
    
    return True, ""


def score_posting(row: Posting, profile: Dict[str, str]) -> Tuple[int, List[str], int]:
    """공고 점수 계산 - 절대 기준 적용"""
    text = f"{row.title} {row.content} {row.region_raw}".lower()
    score = 0
    matched: List[str] = []
    core_hits: Set[str] = set()

    # 가중치 점수 테이블 (개선: 더 세밀한 가중치)
    weights = [
        ("자금목적", 15),  # 가장 중요
        ("업종", 13),
        ("주요 상품", 10),
        ("주요 거래처", 8),
        ("소재지", 7),
        ("인증", 6),
        ("특허", 5),
        ("기업애로", 4),
    ]

    # 프로필 필드별 점수 (정확한 매칭)
    for field_name, weight in weights:
        field_val = profile.get(field_name, "").lower()
        if not field_val:
            continue
        for tok in tokenize(field_val):
            if not tok:
                continue
            # 전체 단어 매칭 + 부분 매칭
            if tok in text:
                score += weight
                matched.append(f"{field_name}:{tok}")
                if field_name in CORE_FIELDS:
                    core_hits.add(field_name)

    # 제외 키워드 감점
    for tok in tokenize(profile.get("고려사항", "")):
        if tok.startswith("!"):
            bad = tok[1:].lower()
            if bad and bad in text:
                score -= 20
                matched.append(f"제외:{bad}")

    # 보너스: 지원금/자금 키워드 (중요)
    if has_support_keyword(text):
        score += 8
    
    # 보너스: 정책/사업 관련 키워드
    if any(k in text for k in ["사업", "프로젝트", "프로그램", "지원", "사업화", "기술개발", "사업비", "경비"]):
        score += 3

    # PDF 반영 보너스 (중요한 정보 추가 반영)
    if row.pdf_used:
        score += 5

    return score, matched, len(core_hits)


def fetch_html(session: requests.Session, url: str) -> str:
    if not url:
        return ""
    try:
        r = session.get(url, timeout=REQUEST_TIMEOUT, headers={"User-Agent": USER_AGENT})
        if r.status_code != 200:
            return ""
        return r.text[:350000]
    except Exception:
        return ""


def html_text(raw_html: str) -> str:
    s = re.sub(r"(?is)<script[^>]*>.*?</script>", " ", raw_html or "")
    s = re.sub(r"(?is)<style[^>]*>.*?</style>", " ", s)
    s = re.sub(r"(?is)<noscript[^>]*>.*?</noscript>", " ", s)
    s = re.sub(r"(?is)<[^>]+>", " ", s)
    return normalize_text(html.unescape(s))[:22000]


def extract_pdf_links(raw_html: str, base_url: str) -> List[str]:
    out: List[str] = []
    seen: Set[str] = set()
    for m in re.finditer(r"href=[\"']([^\"']+\.pdf(?:\?[^\"']*)?)[\"']", raw_html or "", re.I):
        url = ensure_http(m.group(1), default_domain=base_url)
        if url and url not in seen:
            seen.add(url)
            out.append(url)
    for m in re.finditer(r"https?://[^\s\"'<>]+\.pdf(?:\?[^\s\"'<>]+)?", raw_html or "", re.I):
        url = ensure_http(m.group(0))
        if url and url not in seen:
            seen.add(url)
            out.append(url)
    return out[:10]


def download_pdf_bytes(session: requests.Session, url: str) -> Optional[bytes]:
    try:
        r = session.get(url, timeout=REQUEST_TIMEOUT, stream=True, headers={"User-Agent": USER_AGENT})
        if r.status_code != 200:
            return None
        data: List[bytes] = []
        size = 0
        for chunk in r.iter_content(chunk_size=64 * 1024):
            if not chunk:
                continue
            data.append(chunk)
            size += len(chunk)
            if size > PDF_MAX_BYTES:
                return None
        return b"".join(data)
    except Exception:
        return None


def extract_pdf_text(pdf_bytes: bytes) -> str:
    """PDF에서 텍스트 추출 (강화된 에러 처리)"""
    if not HAS_PDF_LIB or not pdf_bytes:
        return ""
    
    texts: List[str] = []
    
    # pypdf 시도
    if HAS_PYPDF:
        try:
            reader = PdfReader(io.BytesIO(pdf_bytes))
            pages = getattr(reader, "pages", [])
            for i in range(min(len(pages), PDF_MAX_PAGES)):
                try:
                    t = pages[i].extract_text() or ""
                    if t and len(t.strip()) > 10:
                        texts.append(t)
                except Exception:
                    continue
        except Exception:
            texts = []
    
    # fitz(pymupdf) 시도
    if not texts and HAS_PYMUPDF:
        try:
            doc = fitz.open(stream=pdf_bytes, filetype="pdf")
            for i in range(min(len(doc), PDF_MAX_PAGES)):
                try:
                    page_text = doc.load_page(i).get_text("text") or ""
                    if page_text and len(page_text.strip()) > 10:
                        texts.append(page_text)
                except Exception:
                    continue
            doc.close()
        except Exception:
            pass
    
    if texts:
        merged = normalize_text(" ".join(texts))
        if merged:
            return merged[:PDF_TEXT_MAX_CHARS]
    
    return ""


def enrich_posting(row: Posting, session: requests.Session) -> None:
    """공고 본문 HTML/PDF 반영"""
    if not row.detail_url:
        return
    raw_html = fetch_html(session, row.detail_url)
    if not raw_html:
        return
    
    # HTML 텍스트 추출 및 반영
    row.content = normalize_text(row.content + " " + html_text(raw_html))
    
    # PDF 추출 및 반영
    if not HAS_PDF_LIB:
        return
    
    used = 0
    for pdf_url in extract_pdf_links(raw_html, row.detail_url):
        if used >= PDF_MAX_FILES:
            break
        b = download_pdf_bytes(session, pdf_url)
        if not b:
            continue
        txt = extract_pdf_text(b)
        if not txt:
            continue
        row.content = normalize_text(row.content + " " + txt)
        row.pdf_used = True
        row.pdf_urls.append(pdf_url)
        used += 1


def score_and_filter(postings: List[Posting], profile: Dict[str, str]) -> Tuple[List[Posting], List[Posting]]:
    """점수 계산 및 절대 기준 필터링"""
    candidates: List[Posting] = []

    # 1단계: 기본 필터링 + 절대 기준
    for row in postings:
        # 마감 확인
        if is_closed(row):
            continue
        
        # 금액 추출
        row.amount_krw = extract_amount_krw(f"{row.title} {row.content}")
        
        # 절대 기준 적용
        passed, reason = pass_absolute_filters(row, profile)
        if not passed:
            continue
        
        # 프로필 점수
        row.score, row.matched_keywords, row.core_match_count = score_posting(row, profile)
        if row.score > 0:
            candidates.append(row)

    print(f"    절대 기준 통과: {len(candidates)}개")

    # 2단계: 우선 순위 정렬
    candidates.sort(key=lambda x: (x.core_match_count, x.score, x.amount_krw), reverse=True)

    # 3단계: HTML/PDF 확장 (상위 N개)
    session = requests.Session()
    session.headers.update({"User-Agent": USER_AGENT})
    for row in candidates[: min(ENRICH_TOPK, len(candidates))]:
        enrich_posting(row, session)

    # 4단계: 재점수 계산
    rescored: List[Posting] = []
    for row in candidates:
        row.amount_krw = extract_amount_krw(f"{row.title} {row.content}")
        row.score, row.matched_keywords, row.core_match_count = score_posting(row, profile)
        rescored.append(row)

    rescored.sort(key=lambda x: (x.core_match_count, x.score, x.amount_krw), reverse=True)

    # 5단계: 강적합 필터링 (최종 기준)
    strong: List[Posting] = []
    for r in rescored:
        # 프로필 점수 기준
        if r.score < MIN_PROFILE_SCORE or r.core_match_count < MIN_CORE_MATCH_FIELDS:
            continue
        
        # 제목 유효성
        if normalize_text(r.title).lower() in {"공고", "[기관] 기관", ""}:
            continue
        
        # 지원금 관련 키워드 필수
        merged = f"{r.title} {r.content}"
        if not has_support_keyword(merged):
            continue
        
        strong.append(r)

    # 지자체 공고가 부족하면 추가로 확보
    strong = ensure_local_postings(strong, rescored, profile)

    return strong, rescored

def format_krw(x: int) -> str:
    """금액 포매팅"""
    if x <= 0:
        return "미표기"
    if x >= 100_000_000:
        return f"{x / 100_000_000:.1f}억원"
    if x >= 10_000:
        return f"{x // 10_000:,}만원"
    return f"{x:,}원"


def write_report_md(path: str, profile: Dict[str, str], top_rows: List[Posting], total_count: int) -> None:
    """마크다운 레포트 작성 (개조식 상세)"""
    with open(path, "w", encoding="utf-8") as f:
        # 제목
        f.write("# 공고 추천 리포트\n\n")
        
        # 요약 정보 (간결)
        f.write(f"**생성**: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')} | ")
        f.write(f"**수집**: {total_count}개 | ")
        f.write(f"**추천**: {len(top_rows)}개 | ")
        f.write(f"**PDF**: {'✓' if HAS_PDF_LIB else '✗'}\n\n")

        # 프로필 요약
        f.write("## 프로필\n\n")
        profile_items = []
        for key in PROFILE_KEYS:
            val = profile.get(key, "").strip()
            if val:
                profile_items.append(f"**{key}**: {val}")
        f.write(" | ".join(profile_items) + "\n\n")

        # TOP 3 추천 (상세 개조식)
        f.write("## 강적합 공고\n\n")
        if not top_rows:
            f.write("> 프로필에 부합하는 공고를 찾지 못했습니다.\n\n")
        else:
            # TOP 3
            for idx, row in enumerate(top_rows[:3], 1):
                f.write(f"### {idx}. {row.title}\n\n")
                f.write(f"**출처** {row.source}\n")
                f.write(f"**적합도** {row.score}점 (핵심 {row.core_match_count}개 필드)\n")
                f.write(f"**지원규모** {format_krw(row.amount_krw)}\n")
                if row.pdf_used:
                    f.write(f"**PDF** 반영됨\n")
                if row.matched_keywords:
                    f.write(f"**매칭키워드** {', '.join(row.matched_keywords[:8])}\n")
                f.write(f"**링크** {row.detail_url}\n\n")
            
            # 나머지 공고 (TOP 4 이상)
            if len(top_rows) > 3:
                f.write("---\n\n")
                f.write("## 추가 추천 공고\n\n")
                for idx, row in enumerate(top_rows[3:], 4):
                    f.write(f"### {idx}. {row.title}\n\n")
                    f.write(f"**출처** {row.source}\n")
                    f.write(f"**적합도** {row.score}점 | ")
                    f.write(f"**지원규모** {format_krw(row.amount_krw)} | ")
                    f.write(f"**PDF** {'Yes' if row.pdf_used else 'No'}\n")
                    if row.matched_keywords:
                        f.write(f"**매칭** {', '.join(row.matched_keywords[:6])}\n")
                    f.write(f"**링크** {row.detail_url}\n\n")

        # 주의사항
        f.write("---\n\n")
        f.write("## 주의사항\n\n")
        f.write("- 프로필 기반 자동 생성\n")
        f.write("- **지역 필터**: 경기/전국/수도권만\n")
        f.write("- **교육**: 지원금 키워드 필수\n")
        f.write("- **제외**: 임대, 경진대회, 설명회, 기관공고 등\n")
        f.write("- **금액**: 공고 기반 추정 (심사 결과에 따라 변경 가능)\n")
        f.write("- **필수 확인**: 신청 자격, 기한, 조건은 원문 참조\n")



def cleanup_old_reports() -> None:
    """오래된 타임스탐프 리포트 삭제"""
    for name in os.listdir("."):
        if not name.startswith("공고추천_리포트_") or not name.endswith(".md"):
            continue
        try:
            os.remove(name)
        except Exception:
            continue


def create_profile_templates() -> None:
    """프로필 템플릿 생성"""
    if not os.path.exists("profile.sample.txt"):
        with open("profile.sample.txt", "w", encoding="utf-8") as f:
            f.write(DEFAULT_PROFILE_TEXT + "\n")
    if not os.path.exists("profile.sample.yaml"):
        with open("profile.sample.yaml", "w", encoding="utf-8") as f:
            f.write("# 프로필 샘플 (YAML 형식)\n")
            for line in DEFAULT_PROFILE_TEXT.splitlines():
                if ":" in line:
                    f.write(line + "\n")
    if not os.path.exists("profile.yaml"):
        with open("profile.yaml", "w", encoding="utf-8") as f:
            for line in DEFAULT_PROFILE_TEXT.splitlines():
                if ":" in line:
                    f.write(line + "\n")


def main() -> None:
    """메인 함수"""
    # 1. 환경 설정
    load_dotenv()
    if not os.getenv("BIZINFO_API_KEY"):
        load_env_fallback(os.path.join(os.getcwd(), ".env"))
    if not os.getenv("BIZINFO_API_KEY"):
        load_env_fallback(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env"))

    gov_api_key = os.getenv("BIZINFO_API_KEY", "").strip().strip("'").strip('"')
    if not gov_api_key:
        raise SystemExit(".env에 BIZINFO_API_KEY(serviceKey)가 없습니다.")

    # 2. 프로필 설정
    create_profile_templates()
    profile_path = choose_profile_path()
    profile = load_profile_from_file(profile_path)

    print(f"\n[1] 프로필 로드")
    print(f"    경로: {profile_path}")
    print(f"    소재지: {profile.get('소재지', '')}")
    print(f"    업종: {profile.get('업종', '')}")

    # 3. 공고 수집
    print(f"\n[2] 공고 수집 중...")
    postings = collect_all_postings(profile, gov_api_key)
    if not postings:
        raise SystemExit("수집된 공고가 없습니다. API 키와 네트워크를 확인하세요.")

    print(f"    총 {len(postings)}개 수집 완료")

    # 4. 필터링 및 점수 계산
    print(f"\n[3] 절대 기준 필터링 및 평가 중...")
    strong_rows, all_rows = score_and_filter(postings, profile)

    print(f"    강적합 공고: {len(strong_rows)}개")

    # 지자체 공고 수 확인
    region = profile.get("소재지", "").lower()
    local_count = sum(1 for r in strong_rows if r.source.startswith("지자체") or (region and region in r.detail_url.lower()))
    if local_count < 3:
        print(f"    [주의] 지자체 공고가 {local_count}건 뿐입니다. 프로필 지역을 확인하거나 검색 범위 확대를 고려하세요.")

    # 5. 레포트 생성
    print(f"\n[4] 레포트 생성 중...")
    write_report_md(REPORT_FILENAME, profile, strong_rows, len(postings))

    report_path = os.path.abspath(REPORT_FILENAME)
    print(f"    완료: {report_path}\n")
    print(f"[완료] 공고 추천이 완료되었습니다!\n")



if __name__ == "__main__":
    main()
