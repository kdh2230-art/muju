"""
기상청 예보 -> 지정 지점의 '시각별' 눈/비 여부를 지도에 색으로 표시

- 내 PC에서:  python snow_map.py  -> snow_map.html 생성 후 브라우저로 열림
              (인증키는 같은 폴더의 key.txt 에 한 줄로 저장)
- GitHub Actions에서: 환경변수 SERVICE_KEY 사용 -> site/index.html 생성 (자동 게시용)
"""
import json
import math
import os
import re
import sys
import time
import traceback
import webbrowser
from datetime import datetime, timedelta

import folium
import requests

HERE = os.path.dirname(os.path.abspath(__file__))
IS_CI = bool(os.environ.get("GITHUB_ACTIONS"))
HOURS_AHEAD = 72  # 앞으로 몇 시간까지 볼지 (단기예보는 최대 5일=120)

# ---- 지사(노선)별 설정은 branches/<이름>.json 에서 읽어 옵니다 (IC/JC 좌표, 노선 모양, 특보 구역 등).
# 실행할 때 환경변수 BRANCH_FILE 로 파일을 지정합니다. 지정하지 않으면 branches/tongyeong.json 을 씁니다.
PLACES = {}        # {"산내JC": (위도, 경도), ...}  (위에서 아래 순서 = 표의 열 순서)
ROUTE = []         # 노선 모양 [(위도, 경도), ...]
BRANCHES = []      # 곁가지 연결 구간 [[(위도, 경도), ...], ...]
LABEL_DIR = {}     # 지점 이름표를 왼쪽에 둘 지점 {"추부IC": "left"}
TITLE = "기상정보"
SUBTITLE = ""
BRANCH_ID = "default"
OUT_DIR = os.path.join(HERE, "site")
CACHE_DIR = "cache"
ROUTE_DIRTY = [False]

PTY_NAME = {"0": "없음", "1": "비", "2": "비/눈", "3": "눈", "4": "소나기",
            "5": "빗방울", "6": "빗방울/눈날림", "7": "눈날림", "?": "자료 없음"}
PTY_COLOR = {"0": "#9ca3af", "1": "#059669", "2": "#7c3aed", "3": "#2563eb",
             "4": "#059669", "5": "#059669", "6": "#7c3aed", "7": "#2563eb", "?": "#374151"}
WEEK = "월화수목금토일"


def load_key():
    k = os.environ.get("SERVICE_KEY", "").strip()
    if k:
        return k
    p = os.path.join(HERE, "key.txt")
    if os.path.exists(p):
        return open(p, encoding="utf-8").read().strip()
    return ""


SERVICE_KEY = load_key()


def now_kst():
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo("Asia/Seoul")).replace(tzinfo=None)
    except Exception:
        return datetime.now()


def latlon_to_grid(lat, lon):
    """기상청 격자(nx, ny) 변환 (Lambert Conformal Conic)"""
    RE, GRID = 6371.00877, 5.0
    SLAT1, SLAT2, OLON, OLAT = 30.0, 60.0, 126.0, 38.0
    XO, YO = 43, 136
    D = math.pi / 180.0
    re = RE / GRID
    slat1, slat2, olon, olat = SLAT1 * D, SLAT2 * D, OLON * D, OLAT * D
    sn = math.tan(math.pi * 0.25 + slat2 * 0.5) / math.tan(math.pi * 0.25 + slat1 * 0.5)
    sn = math.log(math.cos(slat1) / math.cos(slat2)) / math.log(sn)
    sf = math.tan(math.pi * 0.25 + slat1 * 0.5)
    sf = math.pow(sf, sn) * math.cos(slat1) / sn
    ro = math.tan(math.pi * 0.25 + olat * 0.5)
    ro = re * sf / math.pow(ro, sn)
    ra = math.tan(math.pi * 0.25 + lat * D * 0.5)
    ra = re * sf / math.pow(ra, sn)
    theta = lon * D - olon
    if theta > math.pi:
        theta -= 2.0 * math.pi
    if theta < -math.pi:
        theta += 2.0 * math.pi
    theta *= sn
    nx = int(math.floor(ra * math.sin(theta) + XO + 0.5))
    ny = int(math.floor(ro - ra * math.cos(theta) + YO + 0.5))
    return nx, ny


def latest_base(now):
    """단기예보: 02,05,08,11,14,17,20,23시 발표 (약 10분 뒤부터 조회 가능)"""
    hours = [2, 5, 8, 11, 14, 17, 20, 23]
    t = now - timedelta(minutes=10)
    cands = [h for h in hours if h <= t.hour]
    if cands:
        return t.strftime("%Y%m%d"), f"{cands[-1]:02d}00"
    y = t - timedelta(days=1)
    return y.strftime("%Y%m%d"), "2300"


def latest_ultra_base(now):
    """초단기예보: 매시 30분 발표 (약 45분 뒤부터 조회 가능, 6시간 이내 예보)"""
    t = now - timedelta(minutes=45)
    return t.strftime("%Y%m%d"), f"{t.hour:02d}30"


class NoData(Exception):
    """발표 직후 등으로 해당 발표분 자료가 아직 없을 때"""


CACHE_FILE = os.path.join("cache", "short.json")  # apply_config 에서 지사별로 바뀜
SHORT_CACHE = {}


def load_json(path):
    try:
        with open(path, encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def load_short_cache():
    return load_json(CACHE_FILE)


ROUTE_CACHE_FILE = os.path.join("cache", "route.json")
ROUTE_CACHE = {}


def route_segments():
    """노선을 0.3km 간격으로 쪼개 격자별 구간으로 묶는다 -> (격자 목록, [[격자번호, [[lat,lon],...]], ...])"""
    grids, segs = [], []
    lines = ([ROUTE] if len(ROUTE) > 1 else []) + [b for b in BRANCHES if len(b) > 1]
    for line in lines:
        dense = []
        for (a, b), (c, d) in zip(line, line[1:]):
            n = max(1, int(math.hypot(c - a, (d - b) * 0.82) * 111 / 0.3))
            dense += [(a + (c - a) * i / n, b + (d - b) * i / n) for i in range(n)]
        dense.append(line[-1])
        cur_g, cur_pts = None, []
        for pt in dense:
            g = latlon_to_grid(*pt)
            if g not in grids:
                grids.append(g)
            gi = grids.index(g)
            if gi != cur_g and cur_pts:
                cur_pts.append([round(pt[0], 5), round(pt[1], 5)])  # 끊김 없이 이어지게 경계점 공유
                segs.append([cur_g, cur_pts])
                cur_pts = []
            cur_g = gi
            cur_pts.append([round(pt[0], 5), round(pt[1], 5)])
        if cur_pts:
            segs.append([cur_g, cur_pts])
    return grids, segs


def save_caches():
    """저장해 둔 단기예보·노선 초단기예보. 워크플로가 cache/dirty 파일이 있을 때만 캐시를 갱신한다"""
    try:
        os.makedirs(CACHE_DIR, exist_ok=True)
        for f, d in ((CACHE_FILE, SHORT_CACHE), (ROUTE_CACHE_FILE, ROUTE_CACHE)):
            with open(f, "w", encoding="utf-8") as fh:
                json.dump(d, fh, ensure_ascii=False)
        open(os.path.join(CACHE_DIR, "dirty"), "w").close()
    except Exception as e:
        print("캐시 저장 실패:", e)


def short_bases(now):
    """단기예보 발표 후보: [가장 최근, 직전] (발표 약 10분 뒤부터 조회 가능)"""
    hours = [2, 5, 8, 11, 14, 17, 20, 23]
    t = now - timedelta(minutes=10)
    cands = [h for h in hours if h <= t.hour]
    day, h = (t, cands[-1]) if cands else (t - timedelta(days=1), 23)
    out = [(day.strftime("%Y%m%d"), f"{h:02d}00")]
    i = hours.index(h)
    pday, ph = (day, hours[i - 1]) if i > 0 else (day - timedelta(days=1), 23)
    out.append((pday.strftime("%Y%m%d"), f"{ph:02d}00"))
    return out


def ultra_bases(now):
    """초단기예보 발표 후보: [가장 최근, 직전] (매시 30분 발표. 공식 안내는 45분 뒤부터 조회 가능이지만
    더 일찍 올라오는 경우가 있어 30분부터 먼저 시도하고, 아직 없으면(NO_DATA) 직전 발표로 대체)"""
    t = now - timedelta(minutes=30)
    p = t - timedelta(hours=1)
    return [(t.strftime("%Y%m%d"), f"{t.hour:02d}30"), (p.strftime("%Y%m%d"), f"{p.hour:02d}30")]


def _fetch(endpoint, nx, ny, base_date, base_time, rows):
    url = "http://apis.data.go.kr/1360000/VilageFcstInfoService_2.0/" + endpoint
    params = {
        "serviceKey": SERVICE_KEY, "pageNo": 1, "numOfRows": rows,
        "dataType": "JSON", "base_date": base_date, "base_time": base_time,
        "nx": nx, "ny": ny,
    }
    last = None
    for attempt in range(3):  # 일시적 실패 대비 3회 재시도
        try:
            r = requests.get(url, params=params, timeout=25)
            r.raise_for_status()
            try:
                j = r.json()
            except Exception:
                raise RuntimeError("JSON이 아닌 응답: " + r.text[:150].replace("\n", " "))
            head = j["response"]["header"]
            if head.get("resultCode") != "00":
                if head.get("resultCode") == "03":
                    raise NoData("03 NO_DATA")
                raise RuntimeError(f'{head.get("resultCode")} {head.get("resultMsg")}')
            items = j["response"]["body"]["items"]["item"]
            acc = {}
            for i in items:
                if i["category"] in ("PTY", "TMP", "T1H", "PCP", "RN1", "SNO"):
                    acc.setdefault((i["fcstDate"], i["fcstTime"]), {})[i["category"]] = i["fcstValue"]
            # {(날짜, 시각): (강수형태, 기온, 시간당 강수량, 시간당 신적설)}
            return {k: (v["PTY"], v.get("TMP", v.get("T1H")), clean_amt(v.get("PCP", v.get("RN1"))),
                        clean_amt(v.get("SNO")))
                    for k, v in acc.items() if "PTY" in v}
        except NoData:
            raise
        except Exception as e:
            last = e
            time.sleep(2 * (attempt + 1))
    raise last


def obs_bases(now):
    """초단기실황 발표 후보: [가장 최근 정시, 직전 정시] (매 정시 생성, 약 10분 뒤부터 조회 가능)"""
    t = now - timedelta(minutes=10)
    p = t - timedelta(hours=1)
    return [(t.strftime("%Y%m%d"), f"{t.hour:02d}00"), (p.strftime("%Y%m%d"), f"{p.hour:02d}00")]


def _num(v):
    try:
        x = float(v)
        return None if x < -90 else x  # -99 등은 결측
    except Exception:
        return None


def _fetch_obs(nx, ny, base_date, base_time):
    """초단기실황: 격자별 대표 AWS 관측값 {PTY, 기온, 1시간 강수량}"""
    url = "http://apis.data.go.kr/1360000/VilageFcstInfoService_2.0/getUltraSrtNcst"
    params = {"serviceKey": SERVICE_KEY, "pageNo": 1, "numOfRows": 20, "dataType": "JSON",
              "base_date": base_date, "base_time": base_time, "nx": nx, "ny": ny}
    last = None
    for attempt in range(3):
        try:
            r = requests.get(url, params=params, timeout=25)
            r.raise_for_status()
            try:
                j = r.json()
            except Exception:
                raise RuntimeError("JSON이 아닌 응답: " + r.text[:150].replace("\n", " "))
            head = j["response"]["header"]
            if head.get("resultCode") != "00":
                if head.get("resultCode") == "03":
                    raise NoData("03 NO_DATA")
                raise RuntimeError(f'{head.get("resultCode")} {head.get("resultMsg")}')
            vals = {i["category"]: i["obsrValue"] for i in j["response"]["body"]["items"]["item"]}
            if "PTY" not in vals:
                raise RuntimeError("실황에 PTY 없음")
            t, rn = _num(vals.get("T1H")), _num(vals.get("RN1"))
            return {"code": str(vals["PTY"]), "temp": None if t is None else round(t, 1),
                    "rain": f"{rn:g}mm" if rn else ""}
        except NoData:
            raise
        except Exception as e:
            last = e
            time.sleep(2 * (attempt + 1))
    raise last


def clean_amt(v):
    """'1.0mm'->'1mm', '1mm 미만'->'<1mm', '50.0mm 이상'->'50mm+', '강수없음'->''"""
    if v is None:
        return ""
    v = str(v).strip()
    if v in ("", "강수없음", "적설없음", "0", "0.0"):
        return ""
    v = re.sub(r"(\d+)\.0(?!\d)", r"\1", v)
    if v.endswith("미만"):
        return "<" + v[:-2].strip().replace(" ", "")
    if v.endswith("이상"):
        return v[:-2].strip().replace(" ", "") + "+"
    return v.replace(" ", "")


def to_temp(v):
    try:
        return int(round(float(v)))
    except Exception:
        return None


def hour_label(dt):
    return f"{dt:%m/%d}({WEEK[dt.weekday()]}) {dt:%H}시"


UI = """
<style>
html,body{font-family:-apple-system,BlinkMacSystemFont,"Apple SD Gothic Neo","Malgun Gothic","Noto Sans KR",system-ui,sans-serif;color:#111827}
.card{background:rgba(255,255,255,.97);border-radius:14px;box-shadow:0 4px 18px rgba(0,0,0,.2)}
#head{position:fixed;top:12px;left:12px;z-index:9999;width:330px;padding:14px 16px;box-sizing:border-box}
#head .top{display:flex;justify-content:space-between;align-items:baseline;font-size:12px;color:#6b7280}
#head .ttl{font-weight:800;font-size:14px;color:#111827}
#when{font-size:24px;font-weight:800;margin:8px 0}
#fold{display:none}
#sum{border-radius:10px;padding:9px 11px;font-size:14px;font-weight:700;line-height:1.45}
#sum.snow{background:#dbeafe;color:#1e40af}
#sum.mix{background:#ede9fe;color:#5b21b6}
#sum.rain{background:#d1fae5;color:#065f46}
#sum.clear{background:#f3f4f6;color:#374151}
.kr{margin:0 0 2px}
.kr:last-child{margin-bottom:0}
.kl{display:block;font-size:13px;font-weight:800}
.pt{display:inline-flex;flex-direction:column;align-items:center;justify-content:center;min-width:56px;margin:4px 5px 0 0;padding:3px 9px;
  background:#fff;border-radius:10px;line-height:1.25;box-shadow:0 0 0 1px rgba(0,0,0,.10);color:inherit}
.pt b{font-size:12px;font-weight:800}
.pt i{font-style:normal;font-size:12px;font-weight:700}
.pt i:empty{display:none}
#tmp{font-size:12px;color:#6b7280;margin-top:6px}
#head .row{display:flex;gap:8px;align-items:center;margin-top:12px}
#head .row button{border:0;background:#111827;color:#fff;border-radius:10px;width:42px;height:38px;font-size:15px;cursor:pointer}
#rng{flex:1;min-width:0;-webkit-appearance:none;appearance:none;height:14px;margin:4px 0;padding:0;border-radius:7px;background:#e5e7eb;outline:none}
#rng::-webkit-slider-runnable-track{height:14px;background:transparent}
#rng::-webkit-slider-thumb{-webkit-appearance:none;appearance:none;box-sizing:border-box;width:22px;height:22px;margin-top:-4px;border-radius:50%;background:#111827;border:3px solid #fff;box-shadow:0 0 0 1px #6b7280,0 1px 4px rgba(0,0,0,.4)}
#rng::-moz-range-thumb{box-sizing:border-box;width:22px;height:22px;border-radius:50%;background:#111827;border:3px solid #fff;box-shadow:0 0 0 1px #6b7280}
#rng::-moz-range-track{background:transparent;height:14px}
#legend{font-size:11px;color:#6b7280;margin-top:10px}
#wbar{margin-top:6px;border-radius:10px;padding:6px 10px;font-size:12px;line-height:1.5;background:#fef3c7;color:#92400e;border:1px solid #fcd34d}
#wbar.red{background:#fee2e2;color:#991b1b;border-color:#fca5a5}
#wbar:empty{display:none}
#panel{position:fixed;top:12px;right:12px;z-index:9999;display:flex;flex-direction:column;
  max-height:calc(100vh - 24px);overflow:hidden}
#grab{display:none}
#scroll{overflow:auto}
#panel table{border-collapse:separate;border-spacing:0;font-size:12px;width:100%}
#panel th{position:sticky;top:0;background:#fff;z-index:2;padding:9px 2px;font-size:11px;color:#6b7280;
  font-weight:700;border-bottom:1px solid #e5e7eb;text-align:center;white-space:nowrap}
#panel th:first-child{text-align:left;padding-left:9px}
#panel td{padding:0}
#panel td.t{padding:7px 9px;font-weight:700;white-space:nowrap;color:#374151;border-radius:8px 0 0 8px}
#panel td.c{text-align:center;padding:7px 2px;min-width:50px;font-weight:700;white-space:nowrap;
  border:2px solid #fff;border-radius:8px}
#panel td.c .a{display:block;font-size:10px;font-weight:600;line-height:1.25;margin-top:1px}
#panel td.d{background:#f3f4f6;color:#374151;font-weight:800;padding:5px 9px;font-size:11px}
#panel tr.r{cursor:pointer}
#panel tr.r:hover td.t{background:#f3f4f6}
#panel tr.sel td.t{background:#111827;color:#fff}
#panel tr.sel td.c{box-shadow:inset 0 0 0 2px #111827}
.lbl{background:#fff;border:0;border-radius:12px;padding:2px 8px;font-size:11px;font-weight:600;
  color:#111827;box-shadow:0 1px 5px rgba(0,0,0,.35)}
.leaflet-tooltip-left:before,.leaflet-tooltip-right:before{display:none}
path.leaflet-interactive{filter:drop-shadow(0 1px 2px rgba(0,0,0,.45))}
#edit{display:none;position:fixed;left:12px;bottom:12px;z-index:9999;width:340px;padding:14px 16px;box-sizing:border-box;font-size:13px}
#edit h3{margin:0 0 6px;font-size:15px}
#edit .hint{color:#6b7280;line-height:1.5;margin-bottom:8px}
#elist label{display:inline-block;margin:2px 10px 2px 0;font-weight:700;cursor:pointer}
#etext{width:100%;height:150px;box-sizing:border-box;margin-top:8px;font:12px/1.4 ui-monospace,Consolas,monospace}
#ecopy{margin-top:8px;border:0;background:#111827;color:#fff;border-radius:10px;padding:9px 14px;font-size:14px;cursor:pointer}
.chip{display:inline-block;font-size:11px;font-weight:700;padding:2px 8px;border-radius:999px;
  vertical-align:middle;margin-left:8px}
.chip.u{background:#dbeafe;color:#1e40af}
.chip.s{background:#e5e7eb;color:#374151}
.chip.o{background:#fef3c7;color:#92400e}
.chip.w{background:#ffedd5;color:#9a3412}
#upd{cursor:pointer}
#warn{font-size:12px;font-weight:700;color:#b45309;margin-top:6px;line-height:1.4}
#meta{margin-top:10px;border-top:1px solid #e5e7eb;padding-top:8px;display:grid;grid-template-columns:1fr 1fr;gap:6px}
.mt{background:#f9fafb;border:1px solid #eef0f3;border-radius:10px;padding:6px 9px;line-height:1.3;min-width:0}
.mt .chip{margin-left:0}
.mt .mtt{display:block;margin-top:3px;font-size:17px;font-weight:800;color:#111827;letter-spacing:-.3px}
.mt .mtt small{font-size:11px;font-weight:700;color:#6b7280;margin-right:3px}
.mt .mts{display:block;font-size:11px;color:#6b7280}
.mt .mts b{color:#374151}
.lg{display:inline-flex;align-items:center;gap:4px;margin-right:9px;white-space:nowrap}
.lg i{display:inline-block;width:12px;height:12px;border-radius:4px}
.lgr{margin-top:5px;line-height:1.6}
#panel td.t.u{box-shadow:inset 4px 0 0 #2563eb}
#panel td.t.s{box-shadow:inset 4px 0 0 #d1d5db}
#panel td.sep{font-size:10px;font-weight:800;color:#1e40af;background:#eff6ff;padding:3px 9px;
  border-top:1px dashed #93c5fd;border-bottom:1px dashed #93c5fd}
@media (max-width:700px){
  #edit{left:8px;right:8px;bottom:8px;width:auto}
  #etext{height:110px}
  #head{top:8px;left:8px;right:8px;width:auto;padding:9px 12px}
  #head .top{font-size:11px}
  #when{font-size:17px;margin:2px 0 4px;display:flex;align-items:center;gap:6px}
  #fold{display:inline-block;margin-left:auto;border:0;background:#f3f4f6;color:#374151;border-radius:8px;padding:4px 10px;font-size:12px;font-weight:700}
  #head.fold #sum,#head.fold #tmp,#head.fold #meta,#head.fold #legend{display:none}
  #sum{font-size:12px;padding:5px 8px;line-height:1.3}
  .kr{margin:0}
  .kl{display:inline-block;font-size:12px;margin:3px 4px 0 0}
  .pt{min-width:0;padding:1px 6px;margin:3px 3px 0 0;border-radius:8px;flex-direction:row;gap:4px}
  .pt b,.pt i{font-size:11px}
  #tmp{display:none}
  #head.info #tmp{display:block}
  #head .row{margin-top:6px}
  #head .row button{height:30px;width:38px}
  #wbar{margin-top:4px;padding:4px 8px;font-size:11px}
  #legend{display:none;margin-top:6px}
  #meta{display:none;margin-top:6px;padding-top:6px;gap:5px}
  #head.info #meta{display:grid}
  .mt{padding:5px 8px}
  .mt .mtt{font-size:15px}
  #head.info #legend{display:block}
  .leaflet-control-zoom{display:none}
  #panel{top:auto;left:0;right:0;bottom:0;max-height:36vh;border-radius:16px 16px 0 0}
  #grab{display:block;text-align:center;font-size:12px;font-weight:700;color:#6b7280;padding:9px 0 7px;cursor:pointer}
  #panel.min #scroll{display:none}
  #panel th{font-size:10px;padding:7px 1px}
  #panel td.t{padding:8px 5px;font-size:12px}
  #panel td.c{min-width:0;padding:8px 1px;font-size:12px}
}
</style>
<div id="head" class="card">
  <div class="top"><span class="ttl">__TITLE__</span><span id="upd">__UPDATED__</span></div>
  <div id="when"><span id="wt"></span><span id="kind" class="chip"></span><button id="fold" type="button">▴ 접기</button></div>
  <div id="sum"></div>
  <div id="wbar"></div>
  <div id="tmp"></div>
  <div id="warn"></div>
  <div class="row"><button id="prev">◀</button><input type="range" id="rng"><button id="next">▶</button></div>
  <div id="meta"></div>
  <div id="legend">
    <div class="lgr"><span class="lg"><i style="background:#2563eb"></i>눈</span><span class="lg"><i style="background:#7c3aed"></i>비/눈</span><span class="lg"><i style="background:#059669"></i>비</span><span class="lg"><i style="background:#9ca3af"></i>없음</span></div>
    <div class="lgr">시각 띠 <span class="lg"><i style="background:#2563eb"></i>초단기</span><span class="lg"><i style="background:#9ca3af"></i>단기</span></div>
    <div class="lgr">특보 구역 <span class="lg"><i style="background:#f59e0b"></i>주의보</span><span class="lg"><i style="background:#dc2626"></i>경보</span><span class="lg"><i style="background:#fff;box-shadow:0 0 0 2px #f59e0b inset"></i>예비특보</span></div>
    <div class="lgr">큰 숫자 기온(℃) · 작은 글씨 강수량(mm)·적설(cm)</div>
  </div>
</div>
<div id="edit" class="card">
  <h3>📍 위치 수정 모드</h3>
  <div class="hint">① 이름을 고르고 ② 지도를 확대해서 고속도로의 해당 IC/JC 위치를 <b>클릭</b>하세요. 클릭하면 다음 지점으로 자동으로 넘어가요. ③ 끝나면 아래 <b>복사</b>를 눌러 알려 주세요.</div>
  <div id="elist"></div>
  <textarea id="etext" readonly></textarea><br>
  <button id="ecopy">복사</button> <span id="emsg" style="color:#059669"></span>
</div>
<div id="panel" class="card">
  <div id="grab">▾ 시간별 표 접기</div>
  <div id="scroll"></div>
</div>
"""

JS = """
window.addEventListener('load', function() {
  var MAP = __MAP__;
  var PLACES = __PLACES__, TIMES = __TIMES__, KEYS = __KEYS__, TD = __TD__;
  var NAMES = __NAMES__, COLORS = __COLORS__, DIRS = __DIRS__, ULTRA = __ULTRA__, META = __META__;
  var ROUTE = __ROUTE__, BRANCH = __BRANCH__, RSEG = __RSEG__, RGC = __RGC__;
  var WRN = __WRN__, ZONEGEO = __ZONEGEO__;
  function wet(c) { return c !== '0' && c !== '?' && c !== undefined && c !== null; }
  function kind(c) { return (c === '3' || c === '7') ? 'snow' : (c === '2' || c === '6') ? 'mix' : wet(c) ? 'rain' : 'none'; }
  var ICON = {'3':'❄','7':'❄','2':'🌨','6':'🌨','1':'💧','4':'💧','5':'💧'};
  function amt(p, i) {
    var a = [];
    if (p.rain[i]) a.push(p.rain[i]);
    if (p.snow[i]) a.push(p.snow[i]);
    return a.join('·');
  }
  // 지점별 작은 카드 (이름 + 양)
  function rowHtml(label, list) {
    return '<div class="kr"><span class="kl">' + label + '</span>' + list.map(function(x) {
      return '<span class="pt"><b>' + x.n + '</b><i>' + (x.a || '') + '</i></span>';
    }).join('') + '</div>';
  }
  function fmt(t) { return (t === null || t === undefined) ? '' : String(t).replace('-', '−') + '°'; }

  L.control.zoom({position: 'bottomleft'}).addTo(MAP);

  // 지도 범위를 한반도로 제한 (세계지도 반복/먼 바깥은 안 보이게)
  MAP.options.zoomSnap = 0.1;
  try {
    var KB = L.latLngBounds([[33.0, 124.0], [43.1, 131.9]]);
    MAP.options.maxBoundsViscosity = 1.0;
    MAP.setMaxBounds(KB);
    var mz = MAP.getBoundsZoom(KB, true);
    if (isFinite(mz)) MAP.setMinZoom(mz);
  } catch (e) {}
  // ---- 기상특보: 노선이 지나는 시군 구역을 색으로 칠함 (주의보 노랑, 경보 빨강, 예비특보 점선) ----
  (function() {
    if (!WRN) return;
    var ZN = __ZN__;
    var TI = {'대설': '❄', '호우': '🌧', '강풍': '💨', '한파': '🥶', '건조': '🏜', '안개': '🌫', '폭염': '🔥', '태풍': '🌀', '황사': '😷'};
    function ti(t) { return (TI[t] || '⚠') + ' ' + t; }
    var TODAY = (function() { var k = new Date(Date.now() + 9 * 3600 * 1000); return ('0' + (k.getUTCMonth() + 1)).slice(-2) + '/' + ('0' + k.getUTCDate()).slice(-2); })();
    function dt(s) { return !s ? '' : (s.indexOf(TODAY + ' ') === 0 ? s.slice(6) : s); }   // 오늘이면 날짜 생략
    function wt(a, b) {  // 발표/발효 시각 글자 (둘이 같으면 한 번에)
      if (!a && !b) return '';
      if (a && b && a === b) return ' · 발표·발효 ' + dt(a);
      return ' · ' + (a ? '발표 ' + dt(a) : '') + (a && b ? ' · ' : '') + (b ? '발효 ' + dt(b) : '');
    }
    try {
      MAP.createPane('zones'); MAP.getPane('zones').style.zIndex = 350;
      Object.keys(ZONEGEO).forEach(function(z) {
        var w = WRN.zones[z] || {cur: [], pre: []};
        var red = w.cur.some(function(x) { return x[1] === '경보'; });
        var st = {pane: 'zones', color: '#9ca3af', weight: 1, dashArray: '3 4', fillColor: '#ffffff', fillOpacity: 0, opacity: 0.8};
        if (w.cur.length) st = {pane: 'zones', color: red ? '#dc2626' : '#f59e0b', weight: 2, fillColor: red ? '#dc2626' : '#f59e0b', fillOpacity: 0.28, opacity: 0.95};
        else if (w.pre.length) st = {pane: 'zones', color: '#f59e0b', weight: 2, dashArray: '6 5', fillColor: '#f59e0b', fillOpacity: 0.08, opacity: 0.95};
        var tip = '<b>' + ZN[z] + '</b>';
        w.cur.forEach(function(x) { tip += '<br>' + ti(x[0]) + x[1] + wt(x[2], x[3]); });
        w.pre.forEach(function(x) { tip += '<br>예비 ' + ti(x[0]) + ' · 발효 예정 ' + x[1] + (x[2] ? ' · 발표 ' + dt(x[2]) + (x[3] ? ' 이전' : '') : ''); });
        if (!w.cur.length && !w.pre.length) tip += ' · 특보 없음';
        L.polygon(ZONEGEO[z], st).addTo(MAP).bindTooltip(tip, {sticky: true});
      });
    } catch (e) {}
    // 카드 맨 위 알림 (노선 지역에 특보가 있을 때만)
    var cur = {}, pre = {}, anyRed = false;
    Object.keys(WRN.zones).forEach(function(z) {
      WRN.zones[z].cur.forEach(function(x) {
        var k = x[0] + x[1] + wt(x[2], x[3]); (cur[k] = cur[k] || []).push(ZN[z]); if (x[1] === '경보') anyRed = true;
      });
      WRN.zones[z].pre.forEach(function(x) {
        var k = x[0] + ' 예비특보 · 발효 예정 ' + x[1] + (x[2] ? ' · 발표 ' + dt(x[2]) + (x[3] ? ' 이전' : '') : ''); (pre[k] = pre[k] || []).push(ZN[z]);
      });
    });
    var h = '';
    Object.keys(cur).forEach(function(k) { h += '<div>⚠ <b>' + k + '</b> ' + cur[k].join('·') + '</div>'; });
    Object.keys(pre).forEach(function(k) { h += '<div>' + k + ' — ' + pre[k].join('·') + '</div>'; });
    var wb = document.getElementById('wbar');
    if (wb) { wb.innerHTML = h; wb.className = anyRed ? 'red' : ''; }
  })();
  if (ROUTE.length > 1 && location.hash !== '#edit') {  // 노선(도로 모양) 표시
    L.polyline(ROUTE, {color: '#ffffff', weight: 8, opacity: 0.9}).addTo(MAP);
    BRANCH.forEach(function(b) { L.polyline(b, {color: '#ffffff', weight: 8, opacity: 0.9}).addTo(MAP); });
    L.polyline(ROUTE, {color: '#4b5563', weight: 4, opacity: 0.95}).addTo(MAP);
    BRANCH.forEach(function(b) { L.polyline(b, {color: '#4b5563', weight: 4, opacity: 0.95}).addTo(MAP); });
  }
  // 구간별 날씨 색칠: 노선이 지나는 5km 격자마다 그 시각의 비/눈 색을 입힘 (비·눈이 없으면 회색 그대로)
  var segLines = (location.hash !== '#edit') ? RSEG.map(function(sg) {
    return L.polyline(sg[1], {color: '#4b5563', weight: 5, opacity: 0, lineCap: 'butt'}).addTo(MAP);
  }) : [];
  function paintRoute(i) {
    segLines.forEach(function(ln, k) {
      var code = RGC[RSEG[k][0]] ? RGC[RSEG[k][0]][i] : '?';
      if (wet(code)) ln.setStyle({color: COLORS[code], opacity: 1});
      else ln.setStyle({opacity: 0});
    });
  }
  var mk = [], rows = [];
  PLACES.forEach(function(p) {
    var c = L.circleMarker([p.lat, p.lon], {radius: 8, color: '#fff', weight: 2.5, fillOpacity: 1}).addTo(MAP);
    var left = DIRS[p.name] === 'left';
    c.bindTooltip('', {permanent: true, direction: left ? 'left' : 'right',
                       offset: [left ? -9 : 9, 0], className: 'lbl'});
    mk.push(c);
  });

  var tbl = document.createElement('table');
  var h = '<tr><th>시각</th>';
  PLACES.forEach(function(p) { h += '<th>' + p.name + '</th>'; });
  tbl.innerHTML = h + '</tr>';
  var lastDate = '';
  TD.forEach(function(t, i) {
    if (t[0] !== lastDate) {
      lastDate = t[0];
      var dc = tbl.insertRow().insertCell();
      dc.colSpan = PLACES.length + 1; dc.className = 'd'; dc.textContent = t[0];
    }
    if (ULTRA[i] && (i === 0 || !ULTRA[i - 1])) {  // 파란 띠가 시작되는 곳에만 '초단기예보' 표시
      var sc = tbl.insertRow().insertCell();
      sc.colSpan = PLACES.length + 1; sc.className = 'sep';
      sc.textContent = '초단기예보';
    }
    var tr = tbl.insertRow(); tr.className = 'r';
    var c0 = tr.insertCell(); c0.className = 't ' + (ULTRA[i] ? 'u' : 's'); c0.textContent = t[1];
    PLACES.forEach(function(p) {
      var code = p.codes[i], c = tr.insertCell(), tp = fmt(p.temps[i]);
      if (code === '?') tp = '?'; else if (!tp && code === '0') tp = '·';
      c.className = 'c';
      c.appendChild(document.createTextNode((ICON[code] ? ICON[code] + ' ' : '') + tp));
      var am = amt(p, i);
      if (am) { var sp = document.createElement('span'); sp.className = 'a'; sp.textContent = am; c.appendChild(sp); }
      c.style.background = (code === '0') ? '#f3f4f6' : COLORS[code];
      c.style.color = (code === '0') ? '#6b7280' : '#fff';
    });
    tr.onclick = function() { show(i); };
    rows.push(tr);
  });
  document.getElementById('scroll').appendChild(tbl);

  var panel = document.getElementById('panel'), head = document.getElementById('head');
  var rng = document.getElementById('rng'), sum = document.getElementById('sum');
  rng.min = 0; rng.max = TIMES.length - 1; rng.step = 1;
  // 게이지바: 시각별로 어느 지점이든 눈/비 예보가 있으면 그 색으로 칠함 (눈 > 비/눈 > 비 순으로 우선)
  (function() {
    var n = TIMES.length, T = 22, stops = [], BC = {snow: '#2563eb', mix: '#7c3aed', rain: '#059669', none: '#e5e7eb'};
    function pos(f) { return 'calc(' + (T / 2) + 'px + (100% - ' + T + 'px) * ' + f.toFixed(4) + ')'; }
    for (var i = 0; i < n; i++) {
      var best = 'none';
      PLACES.forEach(function(p) {
        var k = kind(p.codes[i]);
        if (k === 'snow' || (k === 'mix' && best !== 'snow') || (k === 'rain' && best === 'none')) best = k;
      });
      var a = n > 1 ? Math.max(0, (i - 0.5) / (n - 1)) : 0, b = n > 1 ? Math.min(1, (i + 0.5) / (n - 1)) : 1;
      var from = i === 0 ? '0%' : pos(a), to = i === n - 1 ? '100%' : pos(b);
      stops.push(BC[best] + ' ' + from + ' ' + to);
    }
    rng.style.backgroundImage = 'linear-gradient(to right,' + stops.join(',') + ')';
  })();
  var grab = document.getElementById('grab');
  grab.onclick = function() {
    var min = panel.classList.toggle('min');
    grab.textContent = min ? '▴ 시간별 표 보기' : '▾ 시간별 표 접기';
    if (!min && rows[cur] && rows[cur].scrollIntoView) rows[cur].scrollIntoView({block: 'nearest'});
  };

  // 예보 발표 시각 / 초단기 구간 / 대체 여부 안내
  // 기상청 발표 일정: 단기예보 3시간마다(02,05,...,23시 정각), 초단기예보 매시 30분. 다음 발표 시각 계산(한국시간)
  function z2(n) { return ('0' + n).slice(-2); }
  var kn = new Date(Date.now() + 9 * 3600 * 1000), nowMin = kn.getUTCHours() * 60 + kn.getUTCMinutes();
  function nextOf(mins) {  // 오늘 남은 발표가 없으면 내일 첫 발표
    for (var q = 0; q < mins.length; q++) if (mins[q] > nowMin) return {t: z2(Math.floor(mins[q] / 60)) + ':' + z2(mins[q] % 60), tom: false};
    return {t: z2(Math.floor(mins[0] / 60)) + ':' + z2(mins[0] % 60), tom: true};
  }
  var SH = [2, 5, 8, 11, 14, 17, 20, 23].map(function(h) { return h * 60; });
  var UL = []; for (var hh = 0; hh < 24; hh++) UL.push(hh * 60 + 30);
  var ns = nextOf(SH), nu = nextOf(UL);
  var todayMD = z2(kn.getUTCMonth() + 1) + '/' + z2(kn.getUTCDate());
  function tm(v) {  // 'MM/DD HH:MM' 에서 오늘 날짜는 생략 (여러 값이면 모두)
    return String(v).split(' / ').map(function(x) {
      return x.indexOf(todayMD + ' ') === 0 ? x.slice(6) : '<small>' + x.slice(0, 5) + '</small>' + x.slice(6);
    }).join(' / ');
  }
  function tile(chip, cls, time, sub) {
    return '<div class="mt"><span class="chip ' + cls + '">' + chip + '</span><span class="mtt">' + time + '</span><span class="mts">' + sub + '</span></div>';
  }
  var mt = '';
  var rg = (META.ultra_range || '').match(/(\\d+)시/g);
  if (META.ultra) mt += tile('초단기', 'u', tm(META.ultra), '다음 <b>' + (nu.tom ? '내일 ' : '') + nu.t + '</b>' + (rg && rg.length > 1 ? ' · ' + rg[0] + '~' + rg[rg.length - 1] : ''));
  if (META.short) mt += tile('단기', 's', tm(META.short), '다음 <b>' + (ns.tom ? '내일 ' : '') + ns.t + '</b>');
  if (WRN) mt += tile('특보', 'w', tm(WRN.tm), Object.keys(WRN.zones).length ? '<b style="color:#b45309">노선 지역 ' + Object.keys(WRN.zones).length + '곳 있음</b>' : '노선 지역 없음');
  document.getElementById('meta').innerHTML = mt;
  document.getElementById('upd').onclick = function() { head.classList.toggle('info'); };
  // 폰에서 위쪽 카드를 접어 지도를 넓게 볼 수 있게 (접은 상태는 이 폰에 기억)
  var fb = document.getElementById('fold');
  function setFold(v) {
    head.classList.toggle('fold', v); fb.textContent = v ? '▾ 펼치기' : '▴ 접기';
    try { localStorage.setItem('fold', v ? '1' : '0'); } catch (e) {}
  }
  var f0 = false; try { f0 = localStorage.getItem('fold') === '1'; } catch (e) {}
  setFold(f0);
  fb.onclick = function() { setFold(!head.classList.contains('fold')); };

  var mobile0 = window.innerWidth <= 700;
  if (mobile0) { panel.classList.add('min'); grab.textContent = '▴ 시간별 표 보기'; }
  var cur = 0;
  function show(i) {
    i = Math.max(0, Math.min(TIMES.length - 1, i)); cur = i; rng.value = i;
    document.getElementById('wt').textContent = TIMES[i];
    var kd = document.getElementById('kind');
    kd.textContent = ULTRA[i] ? '초단기' : '단기';
    kd.className = 'chip ' + (ULTRA[i] ? 'u' : 's');
    rows.forEach(function(r, k) { r.classList.toggle('sel', k === i); });
    paintRoute(i);
    if (rows[i].scrollIntoView) rows[i].scrollIntoView({block: 'nearest'});

    var g = {snow: [], mix: [], rain: [], unk: 0}, temps = [];
    PLACES.forEach(function(p, j) {
      var mc = p.codes[i], mt2 = p.temps[i];
      var ma = amt(p, i);
      var lab = {n: p.name, a: ma};
      if (mc === '3' || mc === '7') g.snow.push(lab);
      else if (mc === '2' || mc === '6') g.mix.push(lab);
      else if (mc === '1' || mc === '4' || mc === '5') g.rain.push(lab);
      else if (mc === '?') g.unk++;
      if (mt2 !== null && mt2 !== undefined) temps.push(mt2);
      mk[j].setStyle({fillColor: COLORS[mc]});
      mk[j].setTooltipContent('<b>' + p.name + '</b> ' + (ICON[mc] ? NAMES[mc] + ' ' : '') + fmt(mt2) + (ICON[mc] && ma ? ' · ' + ma : ''));
    });
    var lines = [];
    if (g.snow.length) lines.push(rowHtml('❄ 눈', g.snow));
    if (g.mix.length) lines.push(rowHtml('🌨 비/눈', g.mix));
    if (g.rain.length) lines.push(rowHtml('💧 비', g.rain));
    if (!lines.length) lines.push('<div>' + (g.unk === PLACES.length ? '자료 없음' : '✅ 비·눈 예보 없음') + '</div>');
    sum.className = g.snow.length ? 'snow' : g.mix.length ? 'mix' : g.rain.length ? 'rain' : 'clear';
    sum.innerHTML = lines.join('');
    var tmp = document.getElementById('tmp');
    tmp.textContent = temps.length ? ('지점 기온 ' + fmt(Math.min.apply(null, temps)) + ' ~ ' + fmt(Math.max.apply(null, temps))) : '';
  }
  rng.oninput = function() { show(parseInt(rng.value)); };
  document.getElementById('prev').onclick = function() { show(cur - 1); };
  document.getElementById('next').onclick = function() { show(cur + 1); };

  // 열어 본 '지금' 시각(한국시간)에 맞는 줄을 처음에 선택
  function z(n) { return ('0' + n).slice(-2); }
  var d = new Date(Date.now() + 9 * 3600 * 1000);
  var nk = '' + d.getUTCFullYear() + z(d.getUTCMonth() + 1) + z(d.getUTCDate()) + z(d.getUTCHours());
  var start = KEYS.length - 1;
  for (var i = 0; i < KEYS.length; i++) { if (KEYS[i] >= nk) { start = i; break; } }
  show(start);

  // 10분마다 새로고침 (위치 수정 모드에서는 하지 않음)
  // 2분마다 새로고침 (서버는 5분마다 갱신되고 빌드·배포에 1~2분 걸려서, 2분 간격이면 새 자료가 올라온 뒤 늦어도 2분 안에 반영) (주소 뒤에 시각을 붙여 브라우저/CDN에 저장된 옛날 화면을 피함)
  setTimeout(function() { if (location.hash !== '#edit') location.replace(location.pathname + '?t=' + Date.now()); }, 120000);

  // 핀 7개가 카드/표에 가려지지 않게 화면 맞춤
  try {
    var mobile = window.innerWidth <= 700;
    var b = L.latLngBounds(PLACES.map(function(p) { return [p.lat, p.lon]; }).concat(ROUTE));
    MAP.fitBounds(b, {
      paddingTopLeft: [mobile ? 16 : head.offsetWidth + 50, mobile ? head.offsetHeight + 18 : 50],
      paddingBottomRight: [(mobile ? 16 : panel.offsetWidth + 40) + (mobile ? 64 : 80),
                           mobile ? panel.offsetHeight + 18 : 50],
      maxZoom: 12
    });
  } catch (e) {}

  // ---- 위치 수정 모드: 주소 끝에 #edit 를 붙이면 켜짐 ----
  if (location.hash === '#edit') {
    head.style.display = 'none'; panel.style.display = 'none';
    var legendEl = document.getElementById('legend'); if (legendEl) legendEl.style.display = 'none';
    document.getElementById('edit').style.display = 'block';
    var elist = document.getElementById('elist'), etext = document.getElementById('etext');
    var selIdx = 0;
    function mark() {
      mk.forEach(function(m, j) { m.setStyle({radius: j === selIdx ? 12 : 8, weight: j === selIdx ? 4 : 2.5}); });
      var rs = elist.querySelectorAll('input'); if (rs[selIdx]) rs[selIdx].checked = true;
    }
    function dump() {
      etext.value = PLACES.map(function(p) {
        return '    "' + p.name + '": (' + p.lat.toFixed(5) + ', ' + p.lon.toFixed(5) + '),';
      }).join('\\n');
    }
    PLACES.forEach(function(p, i) {
      var lb = document.createElement('label');
      lb.innerHTML = '<input type="radio" name="ep"> ' + p.name;
      lb.querySelector('input').onchange = function() { selIdx = i; mark(); };
      elist.appendChild(lb);
    });
    MAP.on('click', function(e) {
      var p = PLACES[selIdx];
      p.lat = e.latlng.lat; p.lon = e.latlng.lng;
      mk[selIdx].setLatLng(e.latlng);
      selIdx = (selIdx + 1) % PLACES.length;
      mark(); dump();
    });
    document.getElementById('ecopy').onclick = function() {
      etext.select();
      try { document.execCommand('copy'); } catch (e) {}
      if (navigator.clipboard) { try { navigator.clipboard.writeText(etext.value); } catch (e) {} }
      document.getElementById('emsg').textContent = '복사됨!';
    };
    mark(); dump();
  }
});
"""


# ---------------- 기상특보 (노선이 지나는 시군 구역) ----------------
# 구역 경계: 통계청 2018 시군구 경계를 노선이 지나는 5곳만 뽑아 단순화한 것 ([위도, 경도] 목록)
ZONES_GEO = {}   # {구역키: [[[lat,lon],...], ...]}
ZONE_INFO = {}   # {구역키: {"name": 표시이름, "prov": (도 이름 앞글자들), "sub": 하위지역 찾을 글자, "metro": 광역시 여부, "members": [구 이름]}}
ZONE_NAME = {}
PROV_INFO = {  # 시도 코드 앞 2자리 -> (도 이름 앞글자들, 광역시 여부, 도시 표시 이름)
    "11": (("서울",), True, "서울"), "21": (("부산",), True, "부산"), "22": (("대구",), True, "대구"),
    "23": (("인천",), True, "인천"), "24": (("광주",), True, "광주"), "25": (("대전",), True, "대전"),
    "26": (("울산",), True, "울산"), "29": (("세종",), True, "세종"),
    "31": (("경기",), False, ""), "32": (("강원",), False, ""), "33": (("충청북도", "충북"), False, ""),
    "34": (("충청남도", "충남"), False, ""), "35": (("전북", "전라북"), False, ""),
    "36": (("전라남도", "전남"), False, ""), "37": (("경상북도", "경북"), False, ""),
    "38": (("경상남도", "경남"), False, ""), "39": (("제주",), False, ""),
}


def auto_zones(lines, points):
    """노선·지점이 지나는 시군구를 전국 경계(data/muni.json)에서 자동으로 골라 특보 구역으로 쓴다"""
    from shapely.geometry import LineString, Polygon
    from shapely.ops import unary_union
    with open(os.path.join(HERE, "data", "muni.json"), encoding="utf-8") as f:
        munis = json.load(f)
    shapes = [LineString([(lo, la) for la, lo in ln]).buffer(0.003) for ln in lines if len(ln) > 1]
    path = unary_union(shapes + [LineString([(lo, la), (lo + 1e-6, la)]).buffer(0.003) for la, lo in points])
    groups = {}
    for mu in munis:
        prov, metro, city = PROV_INFO.get(mu["c"][:2], (("",), False, ""))
        if metro:
            key, disp, base = city, city, city
        else:
            mm = re.match(r"^(.+?[시군])", mu["n"])
            disp = mm.group(1) if mm else mu["n"]
            key, base = disp[:-1], disp[:-1]
        g = groups.setdefault((mu["c"][:2], key), {"disp": disp, "key": key, "prov": prov, "metro": metro, "members": [], "rings": [], "hit": False})
        g["members"].append(re.sub(r"[구군]$", "", mu["n"]) if metro else mu["n"])
        for ring in mu["r"]:
            g["rings"].append(ring)
            if not g["hit"] and Polygon([(lo, la) for la, lo in ring]).intersects(path):
                g["hit"] = True
    zones, info, names = {}, {}, {}
    used = {}
    for (pc, key), g in sorted(groups.items()):
        if not g["hit"]:
            continue
        k = key if key not in used else f"{key}({g['prov'][0]})"
        used[key] = True
        zones[k] = g["rings"]
        info[k] = {"name": g["disp"], "prov": list(g["prov"]), "sub": g["key"], "metro": g["metro"], "members": g["members"]}
        names[k] = g["disp"]
    return zones, info, names


def auto_route(places):
    """IC/JC를 순서대로 이은 도로 모양을 OSRM(OpenStreetMap 기반 길찾기)으로 만든다. 실패하면 IC/JC를 직선으로 이음"""
    pts = list(places.values())
    shape = None
    try:
        coords = ";".join(f"{lo},{la}" for la, lo in pts)
        r = requests.get("https://router.project-osrm.org/route/v1/driving/" + coords,
                         params={"overview": "full", "geometries": "geojson"}, timeout=40)
        r.raise_for_status()
        line = r.json()["routes"][0]["geometry"]["coordinates"]
        from shapely.geometry import LineString
        simp = LineString(line).simplify(0.0004)
        shape = [(round(la, 5), round(lo, 5)) for lo, la in simp.coords]
    except Exception as e:
        print("노선 자동 생성 실패 - IC/JC를 직선으로 이음:", e)
    return shape or [tuple(p) for p in pts], shape is not None


def apply_config(path):
    """branches/<이름>.json 을 읽어 지점·노선·특보 구역을 설정"""
    global PLACES, ROUTE, BRANCHES, LABEL_DIR, TITLE, SUBTITLE, BRANCH_ID, OUT_DIR, CACHE_DIR, CACHE_FILE, ROUTE_CACHE_FILE
    global ZONES_GEO, ZONE_INFO, ZONE_NAME
    with open(path, encoding="utf-8") as f:
        cfg = json.load(f)
    BRANCH_ID = cfg.get("id") or os.path.splitext(os.path.basename(path))[0]
    TITLE, SUBTITLE = cfg.get("title", "기상정보"), cfg.get("subtitle", "")
    PLACES = {k: tuple(v) for k, v in cfg["places"].items()}
    LABEL_DIR = {k: "left" for k in cfg.get("label_left", [])}
    BRANCHES = [[tuple(p) for p in b] for b in cfg.get("branches", [])]
    CACHE_DIR = os.path.join("cache", BRANCH_ID)
    CACHE_FILE = os.path.join(CACHE_DIR, "short.json")
    ROUTE_CACHE_FILE = os.path.join(CACHE_DIR, "route.json")
    OUT_DIR = os.path.join(HERE, "site", BRANCH_ID) if IS_CI else HERE
    rt = cfg.get("route", "auto")
    if rt == "auto" or not rt:
        saved = load_json(ROUTE_CACHE_FILE).get("_shape")
        if saved:
            ROUTE = [tuple(p) for p in saved]
        else:
            ROUTE, real = auto_route(PLACES)
            if real:
                ROUTE_CACHE["_shape"] = [list(p) for p in ROUTE]
                ROUTE_DIRTY[0] = True
    else:
        ROUTE = [tuple(p) for p in rt]
    z = cfg.get("zones", "auto")
    if z == "auto":
        ZONES_GEO, ZONE_INFO, ZONE_NAME = auto_zones([ROUTE] + BRANCHES, list(PLACES.values()))
    else:  # 직접 지정: {"구역키": {"name": "...", "prov": [...], "sub": "...", "rings": [[[lat,lon],...]]}}
        ZONES_GEO = {k: v["rings"] for k, v in z.items()}
        ZONE_INFO = {k: {"name": v["name"], "prov": v["prov"], "sub": v.get("sub", k), "metro": v.get("metro", False),
                         "members": v.get("members", [])} for k, v in z.items()}
        ZONE_NAME = {k: v["name"] for k, v in z.items()}


WARN_URL = "https://apis.data.go.kr/1360000/WthrWrnInfoService/getPwnStatus"


def split_top(s):
    """괄호 안의 쉼표는 무시하고 가장 바깥 쉼표로만 나눔"""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out if x.strip()]


def zones_in(text):
    """'충청남도(태안, 금산), 대전' 같은 지역 글자에서 우리 구역을 찾기"""
    found = set()
    for tok in split_top(text):
        m = re.match(r"^([^()]+?)\s*(?:\((.*)\))?\s*$", tok, re.S)
        if not m:
            continue
        prov, subs = m.group(1).strip(), m.group(2)
        for z, info in ZONE_INFO.items():
            if not any(prov.startswith(x) for x in info["prov"]):
                continue
            if subs is None:  # 도(시) 전체
                found.add(z)
            elif info["metro"]:  # 광역시는 구 이름이 하위지역에 있을 때만
                if any(len(mb) >= 2 and mb in sub for mb in info["members"] for sub in split_top(subs)):
                    found.add(z)
            elif any(info["sub"] in sub for sub in split_top(subs)):
                found.add(z)
    return found


def parse_warnings(item):
    """특보 통보문 한 건(t1~t7, other 글자)에서 우리 구역의 현재 특보/예비특보를 뽑는다.
    반환: {구역: {"cur": [[종류, 단계]], "pre": [[종류, 시간]]}}"""
    res = {}
    texts = [str(v) for k, v in item.items() if isinstance(v, str) and (k.startswith("t") or k == "other")]
    for text in texts:
        cur_type = None
        for line in re.split(r"[\r\n]+", text):
            line = line.strip()
            m = re.match(r"^o\s*(.+?)(주의보|경보)\s*:\s*(.+)$", line)
            if m:
                for z in zones_in(m.group(3)):
                    d = res.setdefault(z, {"cur": [], "pre": []})
                    if [m.group(1).strip(), m.group(2)] not in d["cur"]:
                        d["cur"].append([m.group(1).strip(), m.group(2)])
                continue
            h = re.match(r"^\(\d+\)\s*(.+?)\s*예비특보", line)
            if h:
                cur_type = h.group(1).strip()
                continue
            if cur_type and line.startswith("o") and ":" in line:
                when, regions = line[1:].split(":", 1)
                for z in zones_in(regions):
                    d = res.setdefault(z, {"cur": [], "pre": []})
                    if [cur_type, when.strip()] not in d["pre"]:
                        d["pre"].append([cur_type, when.strip()])
    return res


MSG_URL = "https://apis.data.go.kr/1360000/WthrWrnInfoService/getWthrWrnMsg"
EV_LINE = re.compile(r"^\((\d+)\)\s*(.+?)\s*:\s*(.+)$")


def _fc_str(v):
    """202611232110 -> '11/23 21:10'"""
    t = str(v)
    return f"{t[4:6]}/{t[6:8]} {t[8:10]}:{t[10:12]}" if len(t) >= 12 else ""


def _kor_time(v):
    """'2026년 11월 23일 21시 00분' -> '11/23 21:00'"""
    m = re.search(r"(\d+)년\s*(\d+)월\s*(\d+)일\s*(\d+)시\s*(\d+)분", v or "")
    return f"{int(m.group(2)):02d}/{int(m.group(3)):02d} {int(m.group(4)):02d}:{int(m.group(5)):02d}" if m else ""


def msg_events(item):
    """통보문 한 건에서 [(종류, 단계, 발표/해제, 우리 구역들, 발효시각)] 을 뽑는다"""
    times = {}
    for line in re.split(r"[\r\n]+", str(item.get("t3", ""))):
        m = EV_LINE.match(line.strip())
        if m:
            times[int(m.group(1))] = _kor_time(m.group(3))
    out = []
    for line in re.split(r"[\r\n]+", str(item.get("t2", ""))):
        m = EV_LINE.match(line.strip())
        if not m:
            continue
        a = re.match(r"^(.+?)(주의보|경보)\s*(.*)$", m.group(2))
        if not a:
            continue
        action = "off" if "해제" in a.group(3) else ("on" if "발표" in a.group(3) else "")
        zs = zones_in(m.group(3))
        if action and zs:
            out.append((a.group(1).strip(), a.group(2), action, zs, times.get(int(m.group(1)), "")))
    return out


def enrich_warnings(zones, msgs):
    """현재 특보/예비특보에 발표시각·발효시각을 붙인다.
    msgs: 통보문 목록(오래된 것 -> 최신). 현재 특보는 [종류, 단계, 발표, 발효], 예비특보는 [종류, 발효예정, 발표, 이전여부]"""
    last_on = {}
    for it in msgs:
        fc = _fc_str(it.get("tmFc", ""))
        for typ, lvl, action, zs, eff in msg_events(it):
            for z in zs:
                if action == "on":
                    last_on[(z, typ, lvl)] = (fc, eff)
                else:
                    last_on.pop((z, typ, lvl), None)
    for z, d in zones.items():
        for x in d["cur"]:
            got = last_on.get((z, x[0], x[1]))
            x += list(got) if got else ["", ""]
        for x in d["pre"]:
            first, older = "", False
            for k in range(len(msgs) - 1, -1, -1):  # 최신부터 거슬러 올라가 처음 나온 통보문을 찾음
                pw = parse_warnings(msgs[k]).get(z, {"pre": []})["pre"]
                if [x[0], x[1]] in [y[:2] for y in pw]:
                    first, older = _fc_str(msgs[k].get("tmFc", "")), (k == 0)
                else:
                    break
            x += [first, older]
    return zones


def fetch_warn_msgs():
    """최근 이틀치 특보 통보문(전국 108). 실패하면 빈 목록 -> 시각 없이 표시"""
    now = now_kst()
    params = {"serviceKey": SERVICE_KEY, "pageNo": 1, "numOfRows": 100, "dataType": "JSON", "stnId": 108,
              "fromTmFc": (now - timedelta(days=1)).strftime("%Y%m%d"), "toTmFc": now.strftime("%Y%m%d")}
    for attempt in range(2):
        try:
            r = requests.get(MSG_URL, params=params, timeout=25)
            r.raise_for_status()
            j = r.json()
            if j["response"]["header"]["resultCode"] != "00":
                raise RuntimeError(j["response"]["header"].get("resultMsg", ""))
            items = j["response"]["body"]["items"]["item"]
            if isinstance(items, dict):
                items = [items]
            items.sort(key=lambda x: (int(x.get("tmFc", 0)), int(x.get("tmSeq", 0))))
            return items
        except Exception as e:
            print(f"특보 통보문 조회 실패({attempt + 1}/2): {e}")
            time.sleep(2)
    return []


def fetch_warnings():
    """기상특보 현황 통보문 중 가장 최근 발표분을 읽는다. 실패하면 None (화면에는 특보 표시를 하지 않음)"""
    params = {"serviceKey": SERVICE_KEY, "pageNo": 1, "numOfRows": 10, "dataType": "JSON"}
    for attempt in range(3):
        try:
            r = requests.get(WARN_URL, params=params, timeout=20)
            r.raise_for_status()
            j = r.json()
            if j["response"]["header"]["resultCode"] != "00":
                raise RuntimeError(j["response"]["header"].get("resultMsg", ""))
            items = j["response"]["body"]["items"]["item"]
            if isinstance(items, dict):
                items = [items]
            items.sort(key=lambda x: (int(x.get("tmFc", 0)), int(x.get("tmSeq", 0))))
            it = items[-1]
            tm = str(it.get("tmFc", ""))
            when = f"{tm[4:6]}/{tm[6:8]} {tm[8:10]}:{tm[10:12]}" if len(tm) >= 12 else ""
            zones = parse_warnings(it)
            try:
                zones = enrich_warnings(zones, fetch_warn_msgs())
            except Exception as e:
                print("특보 시각 정리 실패:", e)
            return {"tm": when, "zones": zones}
        except Exception as e:
            print(f"특보 조회 실패({attempt + 1}/3): {e}")
            time.sleep(2)
    return None


def main():
    cfgp = os.environ.get("BRANCH_FILE") or os.path.join(HERE, "branches", "tongyeong.json")
    apply_config(cfgp)
    now = now_kst()
    start = now.replace(minute=0, second=0, microsecond=0)
    limit = now + timedelta(hours=HOURS_AHEAD)
    sbases, ubases, obases = short_bases(now), ultra_bases(now), obs_bases(now)
    last_obs_err = None
    SHORT_CACHE.update(load_short_cache())
    FRESH = set()
    print(f"현재(한국시간) {now:%m/%d %H:%M} / 단기예보 후보 {sbases} / 초단기예보 후보 {ubases}\n")
    if not SERVICE_KEY:
        print("인증키가 없습니다. key.txt 에 키를 저장하거나 SERVICE_KEY 환경변수를 설정하세요.")
        sys.exit(1)

    def fetch_first(endpoint, nx, ny, bases, rows):
        """최신 발표분을 먼저 시도하고, 아직 자료가 없으면 직전 발표분 사용"""
        last = None
        for idx, (d, t) in enumerate(bases):
            try:
                return _fetch(endpoint, nx, ny, d, t, rows), (d, t), idx
            except Exception as e:
                last = e
        raise last

    def short_for(name, nx, ny):
        """단기예보는 3시간마다만 바뀌므로, 새 발표가 있을 때만 부르고 나머지는 저장해 둔 값을 쓴다"""
        c = SHORT_CACHE.get(name)
        if c and tuple(c["base"]) == sbases[0]:
            return {(a, b): (v, t, r, sn) for a, b, v, t, r, sn in c["rows"]}, sbases[0], 0
        try:
            rows = _fetch("getVilageFcst", nx, ny, sbases[0][0], sbases[0][1], 2000)
            base, idx = sbases[0], 0
        except Exception as e:
            if c:  # 새 발표가 아직 없거나 실패 -> 저장해 둔 이전 값
                return {(a, b): (v, t, r, sn) for a, b, v, t, r, sn in c["rows"]}, tuple(c["base"]), 1
            rows = _fetch("getVilageFcst", nx, ny, sbases[1][0], sbases[1][1], 2000)
            base, idx = sbases[1], 1
        SHORT_CACHE[name] = {"base": list(base), "rows": [[a, b, *v] for (a, b), v in rows.items()]}
        FRESH.add(name)
        return dict(rows), base, idx

    def load(name):
        lat, lon = PLACES[name]
        nx, ny = latlon_to_grid(lat, lon)
        merged, sb, sidx = short_for(name, nx, ny)
        ub, uidx, ukeys = None, 0, set()
        try:  # 가까운 6시간은 초단기예보로 덮어쓰기 (더 정확). 적설은 초단기에 없어 단기값 유지
            ultra, ub, uidx = fetch_first("getUltraSrtFcst", nx, ny, ubases, 100)
            for k, (v, t, r, _) in ultra.items():
                merged[k] = (v, t, r, merged[k][3] if k in merged else "")
                ukeys.add(k[0] + k[1][:2])  # 초단기가 적용된 시각 (YYYYMMDDHH)
        except Exception as e:
            print(f"  ({name}: 초단기예보 실패 - 단기예보만 사용: {e})")
        ob, oidx, obs = None, 0, None
        for idx, (d, t) in enumerate(obases):  # 관측: 최신 정시 -> 없으면 직전 정시
            try:
                obs, ob, oidx = _fetch_obs(nx, ny, d, t), (d, t), idx
                break
            except Exception as e:
                last_obs_err = e
        if obs is None:
            print(f"  ({name}: 관측(초단기실황) 실패 - 관측 없이 표시: {last_obs_err})")
        per = {}
        for (d, t), (v, tmp, rain, snow) in merged.items():
            dt = datetime.strptime(d + t, "%Y%m%d%H%M")
            if start <= dt <= limit:
                per[dt.strftime("%Y%m%d%H")] = (v, to_temp(tmp), rain, snow)
        return {"nx": nx, "ny": ny, "per": per, "sb": sb, "sidx": sidx, "ub": ub, "uidx": uidx, "ukeys": ukeys,
                "obs": obs, "ob": ob, "oidx": oidx}

    # 초단기예보 발표(:30) 직후라면, 새 자료가 올라올 때까지 최대 4분 기다리며 1분마다 확인 (다음 5분 실행을 기다리지 않도록)
    if 30 <= now.minute < 55:
        first = next(iter(PLACES))
        fx, fy = latlon_to_grid(*PLACES[first])
        for k in range(4):
            try:
                _fetch("getUltraSrtFcst", fx, fy, ubases[0][0], ubases[0][1], 10)
                break
            except NoData:
                if k < 3:
                    print(f"초단기예보 {ubases[0][1]} 발표 대기 중 ({k + 1}/3)")
                    time.sleep(60)
            except Exception:
                break

    results, pending = {}, list(PLACES)
    for rnd in range(3):  # 실패한 지점은 잠시 뒤 최대 2번 더 시도
        failed = []
        for name in pending:
            try:
                results[name] = load(name)
            except Exception as e:
                print(f"{name}: 조회 실패 ({e})")
                failed.append(name)
            time.sleep(0.5)
        pending = failed
        if not pending:
            break
        if rnd < 2:
            print(f"-> {len(pending)}곳 실패, 잠시 뒤 다시 시도: {', '.join(pending)}")
            time.sleep(10)

    if FRESH or ROUTE_DIRTY[0]:
        save_caches()
    data = {}
    for name in PLACES:
        if name not in results:
            data[name] = {}
            continue
        nx, ny, per = results[name]["nx"], results[name]["ny"], results[name]["per"]
        data[name] = per
        wet = [f"{hour_label(datetime.strptime(k, '%Y%m%d%H'))} {PTY_NAME[v]}({tp}°"
               + (f", 강수 {r}" if r else "") + (f", 적설 {sn}" if sn else "") + ")"
               for k, (v, tp, r, sn) in sorted(per.items()) if v != "0"]
        print(f"{name} (격자 {nx},{ny}): " + (", ".join(wet) if wet else "비/눈 예보 없음"))

    keys = sorted({k for per in data.values() for k in per})
    if not keys:
        print("\n받아온 예보가 없습니다. 인증키/신청 승인 여부를 확인하세요.")
        sys.exit(1)
    times = [hour_label(datetime.strptime(k, "%Y%m%d%H")) for k in keys]
    td = []
    for k in keys:
        d = datetime.strptime(k, "%Y%m%d%H")
        td.append([f"{d:%m/%d}({WEEK[d.weekday()]})", f"{d:%H}시"])
    ok = [results[n] for n in PLACES if n in results]
    ultra_union = set().union(*[r["ukeys"] for r in ok]) if ok else set()
    ultra_flags = [k in ultra_union for k in keys]
    ukeys_in = [k for k in keys if k in ultra_union]

    def top(field):
        vals = [r[field] for r in ok if r[field] is not None]
        return max(set(vals), key=vals.count) if vals else None

    def all_bases(field):
        vals = sorted({r[field] for r in ok if r[field] is not None})
        return " / ".join(fmt_base(b) for b in vals)

    def fmt_base(b):
        return f"{datetime.strptime(b[0] + b[1], '%Y%m%d%H%M'):%m/%d %H:%M}" if b else ""

    meta = {
        "short": all_bases("sb"),
        "ultra": all_bases("ub"),
        "ultra_range": (hour_label(datetime.strptime(ukeys_in[0], "%Y%m%d%H")) + " ~ "
                        + hour_label(datetime.strptime(ukeys_in[-1], "%Y%m%d%H"))) if ukeys_in else "",
        "short_old": any(r["sidx"] > 0 for r in ok),
        "ultra_old": any(r["ub"] is not None and r["uidx"] > 0 for r in ok),
        "ultra_fail": [n for n in PLACES if n in results and results[n]["ub"] is None],
        "fail": [n for n in PLACES if n not in results],
        "obs": all_bases("ob"),
        "obs_key": (lambda b: b[0] + b[1][:2] if b else "")(top("ob")),
        "obs_old": any(r["ob"] is not None and r["oidx"] > 0 for r in ok),
        "obs_fail": [n for n in PLACES if n in results and results[n]["obs"] is None],
    }
    wrn = fetch_warnings()
    print("특보:", json.dumps(wrn, ensure_ascii=False) if wrn else "조회 실패")
    print(f"\n단기예보 발표 {meta['short']} / 초단기예보 발표 {meta['ultra'] or '없음'} ({meta['ultra_range']})"
          f" / 초단기 대체 {meta['ultra_fail']} / 조회 실패 {meta['fail']}")
    print(f"관측(초단기실황) 기준 {meta['obs'] or '없음'} / 관측 실패 {meta['obs_fail']}")
    for n in PLACES:
        o = results.get(n, {}).get("obs")
        if o:
            print(f"  관측 {n}: {PTY_NAME.get(o['code'], o['code'])} {o['temp']}°" + (f" 강수 {o['rain']}" if o["rain"] else ""))
    # 관측(정시 기준)이 그 지점의 초단기예보(30분 발표)보다 나중 시각이면, 관측 시각의 값을 관측값으로 바꿔 넣는다
    for n in PLACES:
        r = results.get(n)
        if not r or r["obs"] is None or r["ob"] is None:
            continue
        k = r["ob"][0] + r["ob"][1][:2]
        if k not in keys:
            continue
        obs_dt = datetime.strptime(r["ob"][0] + r["ob"][1], "%Y%m%d%H%M")
        if r["ub"] is not None and datetime.strptime(r["ub"][0] + r["ub"][1], "%Y%m%d%H%M") >= obs_dt:
            continue  # 예보가 더 최신이면 예보를 그대로 사용
        o = r["obs"]
        old = data[n].get(k, ("?", None, "", ""))
        snow_amt = old[3] if o["code"] in ("3", "7") else ""
        data[n][k] = (o["code"], o["temp"], o["rain"] or "", snow_amt)
    places_js = [{"name": n, "lat": la, "lon": lo,
                  "codes": [data[n].get(k, ("?", None, "", ""))[0] for k in keys],
                  "temps": [data[n].get(k, ("?", None, "", ""))[1] for k in keys],
                  "rain": [data[n].get(k, ("?", None, "", ""))[2] for k in keys],
                  "snow": [data[n].get(k, ("?", None, "", ""))[3] for k in keys]}
                 for n, (la, lo) in PLACES.items()]

    # ---- 노선 전체 날씨: 노선이 지나는 격자 중 IC/JC가 아닌 곳은 초단기예보(+실황)만 받아 구간을 색칠한다.
    # 초단기예보·실황은 한 시간에 한 번만 바뀌므로 새 발표가 있을 때만 받고 나머지는 저장해 둔 값을 쓴다.
    rseg, rgc = [], []
    try:
        rgrids, rseg = route_segments()
        place_by_grid = {latlon_to_grid(*la_lo): n for n, la_lo in PLACES.items()}
        ROUTE_CACHE.update(load_json(ROUTE_CACHE_FILE))
        skip = {"u": False, "o": False}
        route_fresh = False

        def route_one(g):
            nonlocal route_fresh
            key = f"{g[0]},{g[1]}"
            c = ROUTE_CACHE.get(key, {})
            # 초단기예보
            if c.get("ub") != list(ubases[0]):
                got = None
                if not skip["u"]:
                    try:
                        got = (_fetch("getUltraSrtFcst", g[0], g[1], ubases[0][0], ubases[0][1], 100), ubases[0])
                    except NoData:
                        skip["u"] = True
                    except Exception as e:
                        print(f"  (노선 격자 {key}: 초단기예보 실패 {e})")
                if got is None and not c.get("ult"):
                    try:
                        got = (_fetch("getUltraSrtFcst", g[0], g[1], ubases[1][0], ubases[1][1], 100), ubases[1])
                    except Exception:
                        got = None
                if got:
                    c["ult"] = [[a, b, *v] for (a, b), v in got[0].items()]
                    c["ub"] = list(got[1])
                    route_fresh = True
            # 실황(관측)
            if c.get("ob") != list(obases[0]):
                got = None
                if not skip["o"]:
                    try:
                        got = (_fetch_obs(g[0], g[1], obases[0][0], obases[0][1]), obases[0])
                    except Exception:
                        skip["o"] = True
                if got is None and not c.get("obs"):
                    try:
                        got = (_fetch_obs(g[0], g[1], obases[1][0], obases[1][1]), obases[1])
                    except Exception:
                        got = None
                if got:
                    c["obs"], c["ob"] = got[0], list(got[1])
                    route_fresh = True
            ROUTE_CACHE[key] = c
            return c

        for gi, g in enumerate(rgrids):
            n = place_by_grid.get(g)
            if n:  # IC/JC 격자는 이미 받은 값 그대로
                rgc.append([data[n].get(k, ("?",))[0] for k in keys])
                continue
            c = route_one(g)
            per = {r[0] + r[1][:2]: r[2:] for r in c.get("ult", [])}
            if c.get("obs") and c.get("ob"):
                ok_ = c["ob"][0] + c["ob"][1][:2]
                ub_dt = datetime.strptime(c["ub"][0] + c["ub"][1], "%Y%m%d%H%M") if c.get("ub") else None
                if ub_dt is None or ub_dt < datetime.strptime(c["ob"][0] + c["ob"][1], "%Y%m%d%H%M"):
                    per[ok_] = [c["obs"]["code"]]
            rgc.append([per.get(k, ["?"])[0] for k in keys])
        if route_fresh:
            FRESH.add("route")
            save_caches()
        print(f"노선 격자 {len(rgrids)}곳 (IC/JC 제외 {len(rgrids) - len(place_by_grid)}곳 추가 조회), 구간 {len(rseg)}개")
    except Exception as e:
        print("노선 날씨 처리 실패(노선은 회색으로 표시):", e)
        rseg, rgc = [], []

    ctr = [sum(p[0] for p in PLACES.values()) / len(PLACES), sum(p[1] for p in PLACES.values()) / len(PLACES)]
    m = folium.Map(location=ctr, zoom_start=9, tiles=None, zoom_control=False)
    folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/World_Street_Map/MapServer/tile/{z}/{y}/{x}",
        attr="Esri · 노선 © OpenStreetMap contributors (ODbL)", name="Esri", no_wrap=True, max_zoom=17,
    ).add_to(m)
    m.get_root().header.add_child(folium.Element(
        "<title>" + (TITLE + (" · " + SUBTITLE if SUBTITLE else "")).replace("<", "") + "</title>"))
    m.get_root().html.add_child(folium.Element(UI.replace("__TITLE__", TITLE.replace("<", "")).replace("__UPDATED__", f"ⓘ 수집 {now:%m/%d %H:%M} · 2분마다 새로고침")))
    js = (JS.replace("__PLACES__", json.dumps(places_js, ensure_ascii=False))
            .replace("__TIMES__", json.dumps(times, ensure_ascii=False))
            .replace("__KEYS__", json.dumps(keys))
            .replace("__ULTRA__", json.dumps(ultra_flags))
            .replace("__META__", json.dumps(meta, ensure_ascii=False))
            .replace("__TD__", json.dumps(td, ensure_ascii=False))
            .replace("__NAMES__", json.dumps(PTY_NAME, ensure_ascii=False))
            .replace("__COLORS__", json.dumps(PTY_COLOR))
            .replace("__DIRS__", json.dumps(LABEL_DIR, ensure_ascii=False))
            .replace("__WRN__", json.dumps(wrn, ensure_ascii=False))
            .replace("__ZONEGEO__", json.dumps(ZONES_GEO, ensure_ascii=False))
            .replace("__ZN__", json.dumps(ZONE_NAME, ensure_ascii=False))
            .replace("__BRANCH__", json.dumps(BRANCHES))
            .replace("__ROUTE__", json.dumps(ROUTE))
            .replace("__RSEG__", json.dumps(rseg))
            .replace("__RGC__", json.dumps(rgc))
            .replace("__MAP__", m.get_name()))
    m.get_root().html.add_child(folium.Element("<script>" + js + "</script>"))

    if IS_CI:
        os.makedirs(OUT_DIR, exist_ok=True)
        out = os.path.join(OUT_DIR, "index.html")
    else:
        out = os.path.join(HERE, "snow_map.html")
    m.save(out)
    print(f"\n{out} 저장 완료.")
    if not IS_CI:
        webbrowser.open("file://" + out)


if __name__ == "__main__":
    try:
        main()
    except Exception:
        traceback.print_exc()
        if IS_CI:
            sys.exit(1)
    if not IS_CI:
        input("\n엔터를 누르면 창이 닫힙니다...")
