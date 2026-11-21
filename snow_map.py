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

# 고속도로 본선상의 IC/JC 위치 (위도, 경도). IC는 요금소(영업소) 기준. 무주IC = 한국도로공사 무주영업소.
# 위치가 어긋나 보이면 이 숫자만 고치면 됩니다. (구글맵에서 지점 우클릭 -> 첫 줄 숫자 클릭하면 복사됨)
PLACES = {
    "산내JC": (36.2816, 127.4509),
    "추부IC": (36.1963, 127.4809),
    "금산IC": (36.1054, 127.5252),
    "무주IC": (35.9746, 127.6530),
    "덕유산IC": (35.8429, 127.6489),
    "장수JC": (35.7314, 127.6064),
    "서상IC": (35.6665, 127.6797),
}

# 통영대전선 서상IC -> 산내JC 노선 (위도, 경도). 지도 캡처에 그린 자주색 선에서 추출한 도로 모양(오차 약 100~200m).
# 지도에 회색 선으로 표시되고, 앞으로 구간별 눈·비 판단에 사용합니다.
ROUTE = [
    (35.66756, 127.66880),
    (35.69066, 127.64966),
    (35.70294, 127.62306),
    (35.72528, 127.60287),
    (35.75340, 127.59455),
    (35.76304, 127.59666),
    (35.77124, 127.60280),
    (35.79437, 127.63283),
    (35.80448, 127.64015),
    (35.82808, 127.64339),
    (35.84205, 127.64860),
    (35.87045, 127.64867),
    (35.88200, 127.65659),
    (35.91328, 127.66642),
    (35.93925, 127.66107),
    (35.96233, 127.66167),
    (35.96703, 127.65896),
    (35.97905, 127.64504),
    (35.99240, 127.61059),
    (35.99635, 127.59336),
    (36.00126, 127.58590),
    (36.01231, 127.57950),
    (36.03345, 127.57270),
    (36.04402, 127.56624),
    (36.05698, 127.55172),
    (36.09779, 127.52182),
    (36.11075, 127.50908),
    (36.12130, 127.50605),
    (36.14625, 127.50638),
    (36.15483, 127.50017),
    (36.16309, 127.48638),
    (36.16879, 127.48321),
    (36.18940, 127.48764),
    (36.21337, 127.48704),
    (36.23637, 127.47820),
    (36.26607, 127.47127),
    (36.27155, 127.46685),
    (36.27846, 127.45279),
    (36.28139, 127.45200),
]

LABEL_DIR = {"산내JC": "left", "추부IC": "left", "장수JC": "left"}  # 나머지는 오른쪽

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
    """초단기예보 발표 후보: [가장 최근, 직전] (매시 30분 발표, 약 45분 뒤부터 조회 가능)"""
    t = now - timedelta(minutes=45)
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
#sum{border-radius:10px;padding:9px 11px;font-size:14px;font-weight:700;line-height:1.45}
#sum.snow{background:#dbeafe;color:#1e40af}
#sum.mix{background:#ede9fe;color:#5b21b6}
#sum.rain{background:#d1fae5;color:#065f46}
#sum.clear{background:#f3f4f6;color:#374151}
#tmp{font-size:12px;color:#6b7280;margin-top:6px}
#head .row{display:flex;gap:8px;align-items:center;margin-top:12px}
#head .row button{border:0;background:#111827;color:#fff;border-radius:10px;width:42px;height:38px;font-size:15px;cursor:pointer}
#rng{flex:1;min-width:0;-webkit-appearance:none;appearance:none;height:14px;border-radius:7px;background:#e5e7eb;outline:none;margin:0 4px}
#rng::-webkit-slider-thumb{-webkit-appearance:none;appearance:none;width:22px;height:22px;border-radius:50%;background:#111827;border:3px solid #fff;box-shadow:0 0 0 1px #6b7280,0 1px 4px rgba(0,0,0,.4)}
#rng::-moz-range-thumb{width:16px;height:16px;border-radius:50%;background:#111827;border:3px solid #fff;box-shadow:0 0 0 1px #6b7280}
#rng::-moz-range-track{background:transparent}
#legend{font-size:11px;color:#6b7280;margin-top:10px}
#panel{position:fixed;top:12px;right:12px;z-index:9999;display:flex;flex-direction:column;
  max-height:calc(100vh - 24px);overflow:hidden}
#grab{display:none}
#scroll{overflow:auto}
#panel table{border-collapse:separate;border-spacing:0;font-size:12px;width:100%}
#panel th{position:sticky;top:0;background:#fff;z-index:2;padding:9px 2px;font-size:11px;color:#6b7280;
  font-weight:700;border-bottom:1px solid #e5e7eb}
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
.lbl{background:#fff;border:0;border-radius:999px;padding:2px 8px;font-size:11px;font-weight:600;
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
#obs{margin-top:8px;border:1px solid #fde68a;background:#fffbeb;border-radius:10px;padding:7px 10px;
  font-size:12px;line-height:1.5;color:#78350f}
#obs b{color:#92400e}
#obs .diff{display:block;margin-top:3px;font-weight:800;color:#b45309}
#panel tr.obsrow td.t{background:#fef3c7;color:#92400e;border-radius:8px 0 0 8px;font-size:11px}
#panel tr.obsrow td.c{border:2px dashed #f59e0b;box-sizing:border-box}
#panel tr.obsrow td.c.diff{border:2px solid #dc2626}
#upd{cursor:pointer}
#warn{font-size:12px;font-weight:700;color:#b45309;margin-top:6px;line-height:1.4}
#meta{font-size:11px;color:#4b5563;margin-top:10px;line-height:1.7;border-top:1px solid #e5e7eb;padding-top:8px}
#panel td.t.u{box-shadow:inset 4px 0 0 #2563eb}
#panel td.t.s{box-shadow:inset 4px 0 0 #d1d5db}
#panel td.sep{font-size:10px;font-weight:800;color:#1e40af;background:#eff6ff;padding:3px 9px;
  border-top:1px dashed #93c5fd;border-bottom:1px dashed #93c5fd}
@media (max-width:700px){
  #edit{left:8px;right:8px;bottom:8px;width:auto}
  #etext{height:110px}
  #head{top:8px;left:8px;right:8px;width:auto;padding:9px 12px}
  #head .top{font-size:11px}
  #when{font-size:19px;margin:4px 0 6px}
  #sum{font-size:13px;padding:7px 9px}
  #tmp{margin-top:4px}
  #obs{margin-top:6px;padding:5px 8px;font-size:11px}
  #head .row{margin-top:8px}
  #head .row button{height:34px}
  #legend{display:none;margin-top:6px}
  #meta{margin-top:6px;padding-top:5px;font-size:10.5px;line-height:1.5}
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
  <div class="top"><span class="ttl">기상정보</span><span id="upd">__UPDATED__</span></div>
  <div id="when"><span id="wt"></span><span id="kind" class="chip"></span></div>
  <div id="sum"></div>
  <div id="tmp"></div>
  <div id="obs"></div>
  <div id="warn"></div>
  <div class="row"><button id="prev">◀</button><input type="range" id="rng"><button id="next">▶</button></div>
  <div id="meta"></div>
  <div id="legend">❄ 눈 &nbsp;🌨 비/눈 &nbsp;💧 비 &nbsp;· 없음<br>큰 숫자는 기온(℃), 작은 글씨는 시간당 강수량(mm)·적설(cm)<br><span style="color:#92400e;font-weight:800">노란 점선 칸</span>=실제 관측 · 시각 옆 <span style="color:#2563eb;font-weight:800">파란 띠</span>=초단기예보, <span style="color:#9ca3af;font-weight:800">회색 띠</span>=단기예보</div>
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
  var ROUTE = __ROUTE__;
  function wet(c) { return c !== '0' && c !== '?' && c !== undefined && c !== null; }
  function kind(c) { return (c === '3' || c === '7') ? 'snow' : (c === '2' || c === '6') ? 'mix' : wet(c) ? 'rain' : 'none'; }
  var OBSIDX = KEYS.indexOf(META.obs_key);  // 관측 시각이 표에 있으면 예보와 비교
  var ICON = {'3':'❄','7':'❄','2':'🌨','6':'🌨','1':'💧','4':'💧','5':'💧'};
  function amt(p, i) {
    var a = [];
    if (p.rain[i]) a.push(p.rain[i]);
    if (p.snow[i]) a.push(p.snow[i]);
    return a.join('·');
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
  if (ROUTE.length > 1 && location.hash !== '#edit') {  // 노선(도로 모양) 표시
    L.polyline(ROUTE, {color: '#ffffff', weight: 8, opacity: 0.9}).addTo(MAP);
    L.polyline(ROUTE, {color: '#4b5563', weight: 4, opacity: 0.95}).addTo(MAP);
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
  var hasObs = PLACES.some(function(p) { return p.obs; });
  if (hasObs) {
    var orow = tbl.insertRow(); orow.className = 'obsrow';
    var oc0 = orow.insertCell(); oc0.className = 't';
    oc0.textContent = '관측 ' + (META.obs ? META.obs.slice(-5).slice(0, 2) + '시' : '');
    PLACES.forEach(function(p, j) {
      var c = orow.insertCell(); c.className = 'c', o = p.obs;
      if (!o) { c.textContent = '?'; c.style.background = '#333'; c.style.color = '#fff'; return; }
      var tp = fmt(o.temp);
      c.appendChild(document.createTextNode((ICON[o.code] ? ICON[o.code] + ' ' : '') + (tp || '·')));
      if (o.rain) { var sp = document.createElement('span'); sp.className = 'a'; sp.textContent = o.rain; c.appendChild(sp); }
      c.style.background = (o.code === '0') ? '#f3f4f6' : COLORS[o.code];
      c.style.color = (o.code === '0') ? '#6b7280' : '#fff';
      if (OBSIDX >= 0 && kind(p.codes[OBSIDX]) !== kind(o.code) && p.codes[OBSIDX] !== '?') c.classList.add('diff');
    });
  }
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
    rng.style.background = 'linear-gradient(to right,' + stops.join(',') + ')';
  })();
  var grab = document.getElementById('grab');
  grab.onclick = function() {
    var min = panel.classList.toggle('min');
    grab.textContent = min ? '▴ 시간별 표 보기' : '▾ 시간별 표 접기';
    if (!min && rows[cur] && rows[cur].scrollIntoView) rows[cur].scrollIntoView({block: 'nearest'});
  };

  // 예보 발표 시각 / 초단기 구간 / 대체 여부 안내
  var mt = '';
  if (META.ultra) mt += '<div><span class="chip u" style="margin-left:0">초단기</span> <b>' + META.ultra + '</b> 발표 · ' + META.ultra_range + '</div>';
  if (META.short) mt += '<div><span class="chip s" style="margin-left:0">단기</span> <b>' + META.short + '</b> 발표</div>';
  if (META.obs) mt += '<div><span class="chip o" style="margin-left:0">관측</span> <b>' + META.obs + '</b> 기준 (초단기실황)</div>';
  document.getElementById('meta').innerHTML = mt;
  (function() {
    var box = document.getElementById('obs');
    var ps = PLACES.filter(function(p) { return p.obs; });
    if (!ps.length) {
      box.style.display = 'none';
      return;
    }
    var g = {snow: [], mix: [], rain: []}, tt = [], diffs = [];
    ps.forEach(function(p) {
      var o = p.obs, k = kind(o.code);
      var lab = p.name + (o.rain ? '(' + o.rain + ')' : '');
      if (k !== 'none') g[k].push(lab);
      if (o.temp !== null && o.temp !== undefined) tt.push(o.temp);
      if (OBSIDX >= 0) {
        var fc = p.codes[OBSIDX];
        if (fc !== '?' && kind(fc) !== k) {
          var nm = function(c) { return c === '0' ? '없음' : NAMES[c]; };
          diffs.push(p.name + ' 예보 ' + nm(fc) + ' → 관측 ' + nm(o.code));
        }
      }
    });
    var lines = [];
    if (g.snow.length) lines.push('❄ 눈 · ' + g.snow.join(', '));
    if (g.mix.length) lines.push('🌨 비/눈 · ' + g.mix.join(', '));
    if (g.rain.length) lines.push('💧 비 · ' + g.rain.join(', '));
    if (!lines.length) lines.push('✅ 비·눈 관측 없음');
    var tr = tt.length ? ' · 기온 ' + fmt(Math.min.apply(null, tt)) + ' ~ ' + fmt(Math.max.apply(null, tt)) : '';
    var html = '<span class="chip o" style="margin-left:0">관측</span> <b>' + (META.obs ? META.obs.slice(-5) : '') + '</b> 기준' + tr + '<br>' + lines.join('<br>');
    if (diffs.length) html += '<span class="diff">⚠ 예보와 다름: ' + diffs.join(' / ') + '</span>';
    box.innerHTML = html;
  })();
  document.getElementById('upd').onclick = function() { head.classList.toggle('info'); };

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
    if (rows[i].scrollIntoView) rows[i].scrollIntoView({block: 'nearest'});

    var g = {snow: [], mix: [], rain: [], unk: 0}, temps = [];
    PLACES.forEach(function(p, j) {
      var code = p.codes[i], tp = p.temps[i];
      var lab = p.name + (amt(p, i) ? '(' + amt(p, i) + ')' : '');
      if (code === '3' || code === '7') g.snow.push(lab);
      else if (code === '2' || code === '6') g.mix.push(lab);
      else if (code === '1' || code === '4' || code === '5') g.rain.push(lab);
      else if (code === '?') g.unk++;
      if (tp !== null && tp !== undefined) temps.push(tp);
      mk[j].setStyle({fillColor: COLORS[code]});
      var state = ICON[code] ? NAMES[code] + ' ' : '';
      var am = ICON[code] ? amt(p, i) : '';
      var extra = '';
      if (i === OBSIDX && p.obs) {
        var same = kind(p.obs.code) === kind(code) || code === '?';
        extra = same ? ' · 관측 일치' : ' · <span style="color:#dc2626">⚠ 관측 ' + (p.obs.code === '0' ? '없음' : NAMES[p.obs.code]) + '</span>';
      }
      mk[j].setTooltipContent('<b>' + p.name + '</b> ' + state + fmt(tp) + (am ? ' · ' + am : '') + extra);
    });
    var lines = [];
    if (g.snow.length) lines.push('❄ 눈 · ' + g.snow.join(', '));
    if (g.mix.length) lines.push('🌨 비/눈 · ' + g.mix.join(', '));
    if (g.rain.length) lines.push('💧 비 · ' + g.rain.join(', '));
    if (!lines.length) lines.push(g.unk === PLACES.length ? '자료 없음' : '✅ 비·눈 예보 없음');
    sum.className = g.snow.length ? 'snow' : g.mix.length ? 'mix' : g.rain.length ? 'rain' : 'clear';
    sum.innerHTML = lines.join('<br>');
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
  setTimeout(function() { if (location.hash !== '#edit') location.reload(); }, 600000);

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


def main():
    now = now_kst()
    start = now.replace(minute=0, second=0, microsecond=0)
    limit = now + timedelta(hours=HOURS_AHEAD)
    sbases, ubases, obases = short_bases(now), ultra_bases(now), obs_bases(now)
    last_obs_err = None
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

    def load(name):
        lat, lon = PLACES[name]
        nx, ny = latlon_to_grid(lat, lon)
        merged, sb, sidx = fetch_first("getVilageFcst", nx, ny, sbases, 2000)
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
    print(f"\n단기예보 발표 {meta['short']} / 초단기예보 발표 {meta['ultra'] or '없음'} ({meta['ultra_range']})"
          f" / 초단기 대체 {meta['ultra_fail']} / 조회 실패 {meta['fail']}")
    print(f"관측(초단기실황) 기준 {meta['obs'] or '없음'} / 관측 실패 {meta['obs_fail']}")
    for n in PLACES:
        o = results.get(n, {}).get("obs")
        if o:
            print(f"  관측 {n}: {PTY_NAME.get(o['code'], o['code'])} {o['temp']}°" + (f" 강수 {o['rain']}" if o["rain"] else ""))
    places_js = [{"name": n, "lat": la, "lon": lo,
                  "codes": [data[n].get(k, ("?", None, "", ""))[0] for k in keys],
                  "temps": [data[n].get(k, ("?", None, "", ""))[1] for k in keys],
                  "rain": [data[n].get(k, ("?", None, "", ""))[2] for k in keys],
                  "snow": [data[n].get(k, ("?", None, "", ""))[3] for k in keys],
                  "obs": results[n]["obs"] if n in results else None}
                 for n, (la, lo) in PLACES.items()]

    m = folium.Map(location=[36.0, 127.55], zoom_start=9, tiles=None, zoom_control=False)
    folium.TileLayer(
        tiles="https://server.arcgisonline.com/ArcGIS/rest/services/World_Street_Map/MapServer/tile/{z}/{y}/{x}",
        attr="Esri", name="Esri", no_wrap=True, max_zoom=17,
    ).add_to(m)
    m.get_root().header.add_child(folium.Element(
        '<title>기상정보</title>'))
    m.get_root().html.add_child(folium.Element(UI.replace("__UPDATED__", f"ⓘ 수집 {now:%m/%d %H:%M}")))
    js = (JS.replace("__PLACES__", json.dumps(places_js, ensure_ascii=False))
            .replace("__TIMES__", json.dumps(times, ensure_ascii=False))
            .replace("__KEYS__", json.dumps(keys))
            .replace("__ULTRA__", json.dumps(ultra_flags))
            .replace("__META__", json.dumps(meta, ensure_ascii=False))
            .replace("__TD__", json.dumps(td, ensure_ascii=False))
            .replace("__NAMES__", json.dumps(PTY_NAME, ensure_ascii=False))
            .replace("__COLORS__", json.dumps(PTY_COLOR))
            .replace("__DIRS__", json.dumps(LABEL_DIR, ensure_ascii=False))
            .replace("__ROUTE__", json.dumps(ROUTE))
            .replace("__MAP__", m.get_name()))
    m.get_root().html.add_child(folium.Element("<script>" + js + "</script>"))

    if IS_CI:
        os.makedirs(os.path.join(HERE, "site"), exist_ok=True)
        out = os.path.join(HERE, "site", "index.html")
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
