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
#obs{margin-top:8px;border:1px solid #fde68a;background:#fffbeb;border-radius:10px;padding:7px 10px;
  font-size:12px;line-height:1.5;color:#78350f}
#obs b{color:#92400e}
#obs .diff{display:block;margin-top:3px;font-weight:800;color:#b45309}
#obs .pt{box-shadow:0 0 0 1px #fcd34d}
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
  .pt{min-width:50px;padding:2px 7px;margin:3px 4px 0 0}
  .pt b,.pt i{font-size:11px}
  .kl{font-size:12px}
  #tmp{margin-top:4px}
  #obs{margin-top:6px;padding:5px 8px;font-size:11px}
  #head .row{margin-top:8px}
  #head .row button{height:34px}
  #wbar{margin-top:4px;padding:4px 8px;font-size:11px}
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
  <div id="wbar"></div>
  <div id="tmp"></div>
  <div id="obs"></div>
  <div id="warn"></div>
  <div class="row"><button id="prev">◀</button><input type="range" id="rng"><button id="next">▶</button></div>
  <div id="meta"></div>
  <div id="legend">❄ 눈 &nbsp;🌨 비/눈 &nbsp;💧 비 &nbsp;· 없음<br>큰 숫자는 기온(℃), 작은 글씨는 시간당 강수량(mm)·적설(cm)<br><span style="color:#92400e;font-weight:800">노란 점선 칸</span>=실제 관측 · 시각 옆 <span style="color:#2563eb;font-weight:800">파란 띠</span>=초단기예보, <span style="color:#9ca3af;font-weight:800">회색 띠</span>=단기예보<br>지도 구역색: <span style="color:#b45309;font-weight:800">노랑</span>=특보 주의보, <span style="color:#dc2626;font-weight:800">빨강</span>=특보 경보, 점선=예비특보</div>
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
  var WRN = __WRN__, ZONEGEO = __ZONEGEO__;
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
    var ZN = {'함양': '함양군', '장수': '장수군', '무주': '무주군', '금산': '금산군', '대전': '대전'};
    var TI = {'대설': '❄', '호우': '🌧', '강풍': '💨', '한파': '🥶', '건조': '🏜', '안개': '🌫', '폭염': '🔥', '태풍': '🌀', '황사': '😷'};
    function ti(t) { return (TI[t] || '⚠') + ' ' + t; }
    try {
      MAP.createPane('zones'); MAP.getPane('zones').style.zIndex = 350;
      Object.keys(ZONEGEO).forEach(function(z) {
        var w = WRN.zones[z] || {cur: [], pre: []};
        var red = w.cur.some(function(x) { return x[1] === '경보'; });
        var st = {pane: 'zones', color: '#9ca3af', weight: 1, dashArray: '3 4', fillColor: '#ffffff', fillOpacity: 0, opacity: 0.8};
        if (w.cur.length) st = {pane: 'zones', color: red ? '#dc2626' : '#f59e0b', weight: 2, fillColor: red ? '#dc2626' : '#f59e0b', fillOpacity: 0.28, opacity: 0.95};
        else if (w.pre.length) st = {pane: 'zones', color: '#f59e0b', weight: 2, dashArray: '6 5', fillColor: '#f59e0b', fillOpacity: 0.08, opacity: 0.95};
        var tip = '<b>' + ZN[z] + '</b>';
        w.cur.forEach(function(x) { tip += '<br>' + ti(x[0]) + x[1]; });
        w.pre.forEach(function(x) { tip += '<br>예비 ' + ti(x[0]) + ' ' + x[1]; });
        if (!w.cur.length && !w.pre.length) tip += ' · 특보 없음';
        L.polygon(ZONEGEO[z], st).addTo(MAP).bindTooltip(tip, {sticky: true});
      });
    } catch (e) {}
    // 카드 맨 위 알림 (노선 지역에 특보가 있을 때만)
    var cur = {}, pre = {}, anyRed = false;
    Object.keys(WRN.zones).forEach(function(z) {
      WRN.zones[z].cur.forEach(function(x) {
        var k = x[0] + x[1]; (cur[k] = cur[k] || []).push(ZN[z]); if (x[1] === '경보') anyRed = true;
      });
      WRN.zones[z].pre.forEach(function(x) {
        var k = x[0] + ' ' + x[1]; (pre[k] = pre[k] || []).push(ZN[z]);
      });
    });
    var h = '';
    Object.keys(cur).forEach(function(k) { h += '<div>⚠ <b>' + k + '</b> ' + cur[k].join('·') + '</div>'; });
    Object.keys(pre).forEach(function(k) { h += '<div>예비특보 ' + k + ' — ' + pre[k].join('·') + '</div>'; });
    var wb = document.getElementById('wbar');
    if (wb) { wb.innerHTML = h; wb.className = anyRed ? 'red' : ''; }
  })();
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
    tr.onclick = function() { obsMode = false; show(i); };
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
  var mt = '';
  mt += '<div><span class="chip u" style="margin-left:0">초단기</span> ' + (META.ultra ? '<b>' + META.ultra + '</b> 발표' + (META.ultra_range ? ' · ' + META.ultra_range : '') : '') +
        '<br>매시 30분 발표 · 다음 <b>' + (nu.tom ? '내일 ' : '') + nu.t + '</b></div>';
  mt += '<div><span class="chip s" style="margin-left:0">단기</span> ' + (META.short ? '<b>' + META.short + '</b> 발표' : '') +
        '<br>3시간마다(02·05·08·11·14·17·20·23시) 발표 · 다음 <b>' + (ns.tom ? '내일 ' : '') + ns.t + '</b></div>';
  if (META.obs) mt += '<div><span class="chip o" style="margin-left:0">관측</span> <b>' + META.obs + '</b> 기준 (초단기실황, 매시 정각)</div>';
  mt += '<div style="color:#6b7280">※ 발표 후 이 화면에 반영되기까지 20~30분쯤 걸릴 수 있어요</div>';
  if (WRN) mt += '<div><span class="chip" style="margin-left:0;background:#fef3c7;color:#92400e">특보</span> <b>' + WRN.tm + '</b> 발표 기준' + (Object.keys(WRN.zones).length ? '' : ' · 노선 지역 특보 없음') + '</div>';
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
      if (k !== 'none') g[k].push({n: p.name, a: o.rain || ''});
      if (o.temp !== null && o.temp !== undefined) tt.push(o.temp);
      if (OBSIDX >= 0) {
        var fc = p.codes[OBSIDX];
        if (fc !== '?' && kind(fc) !== k) {
          var nm = function(c) { return c === '0' ? '없음' : NAMES[c]; };
          diffs.push({n: p.name, a: '예보 ' + nm(fc) + ' → 관측 ' + nm(o.code)});
        }
      }
    });
    var lines = [];
    if (g.snow.length) lines.push(rowHtml('❄ 눈', g.snow));
    if (g.mix.length) lines.push(rowHtml('🌨 비/눈', g.mix));
    if (g.rain.length) lines.push(rowHtml('💧 비', g.rain));
    if (!lines.length) lines.push('<div>✅ 비·눈 관측 없음</div>');
    var tr = tt.length ? ' · 기온 ' + fmt(Math.min.apply(null, tt)) + ' ~ ' + fmt(Math.max.apply(null, tt)) : '';
    var html = '<span class="chip o" style="margin-left:0">관측</span> <b>' + (META.obs ? META.obs.slice(-5) : '') + '</b> 기준' + tr + lines.join('');
    if (diffs.length) html += '<div class="diff">' + rowHtml('⚠ 예보와 다름', diffs) + '</div>';
    box.innerHTML = html;
  })();
  document.getElementById('upd').onclick = function() { head.classList.toggle('info'); };

  var mobile0 = window.innerWidth <= 700;
  if (mobile0) { panel.classList.add('min'); grab.textContent = '▴ 시간별 표 보기'; }
  var cur = 0;
  var obsMode = true;  // 처음 화면은 관측값, 슬라이더/표를 건드리면 예보값
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
      var lab = {n: p.name, a: amt(p, i)};
      if (code === '3' || code === '7') g.snow.push(lab);
      else if (code === '2' || code === '6') g.mix.push(lab);
      else if (code === '1' || code === '4' || code === '5') g.rain.push(lab);
      else if (code === '?') g.unk++;
      if (tp !== null && tp !== undefined) temps.push(tp);
      // 처음 열었을 때는 마커에 관측(초단기실황) 값, 시간을 움직이면 그 시각의 예보 값
      var useObs = obsMode && p.obs;
      var mc = useObs ? p.obs.code : code, mt2 = useObs ? p.obs.temp : tp;
      var ma = useObs ? (p.obs.rain || '') : amt(p, i);
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
  rng.oninput = function() { obsMode = false; show(parseInt(rng.value)); };
  document.getElementById('prev').onclick = function() { obsMode = false; show(cur - 1); };
  document.getElementById('next').onclick = function() { obsMode = false; show(cur + 1); };

  // 열어 본 '지금' 시각(한국시간)에 맞는 줄을 처음에 선택
  function z(n) { return ('0' + n).slice(-2); }
  var d = new Date(Date.now() + 9 * 3600 * 1000);
  var nk = '' + d.getUTCFullYear() + z(d.getUTCMonth() + 1) + z(d.getUTCDate()) + z(d.getUTCHours());
  var start = KEYS.length - 1;
  for (var i = 0; i < KEYS.length; i++) { if (KEYS[i] >= nk) { start = i; break; } }
  show(start);

  // 10분마다 새로고침 (위치 수정 모드에서는 하지 않음)
  // 5분마다 새로고침 (주소 뒤에 시각을 붙여 브라우저/CDN에 저장된 옛날 화면을 피함)
  setTimeout(function() { if (location.hash !== '#edit') location.replace(location.pathname + '?t=' + Date.now()); }, 300000);

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
ZONES_GEO = json.loads(r'''{"함양":[[[35.7633,127.6843],[35.7577,127.6994],[35.7474,127.7097],[35.7311,127.7162],[35.7197,127.7337],[35.7311,127.7481],[35.7335,127.7552],[35.7308,127.761],[35.721,127.7641],[35.7129,127.777],[35.707,127.7816],[35.7042,127.7954],[35.6957,127.8012],[35.6859,127.8034],[35.6857,127.8114],[35.681,127.8127],[35.6751,127.8184],[35.6756,127.8216],[35.6698,127.8264],[35.6699,127.8329],[35.6595,127.8348],[35.6608,127.8381],[35.6565,127.8468],[35.6594,127.8615],[35.6632,127.8621],[35.6709,127.869],[35.6694,127.8769],[35.6671,127.8778],[35.6633,127.8753],[35.6519,127.8744],[35.6427,127.8751],[35.641,127.8779],[35.634,127.8707],[35.6256,127.8695],[35.6211,127.8714],[35.6112,127.8632],[35.608,127.8641],[35.5965,127.8538],[35.5946,127.8472],[35.5872,127.8426],[35.5831,127.8352],[35.5773,127.8355],[35.5779,127.8504],[35.5694,127.8564],[35.5606,127.8523],[35.558,127.8478],[35.5458,127.8404],[35.5399,127.832],[35.5291,127.8243],[35.5254,127.8169],[35.5217,127.816],[35.5166,127.8233],[35.5097,127.8203],[35.5066,127.8229],[35.4997,127.8228],[35.4907,127.8163],[35.4912,127.8061],[35.4894,127.8054],[35.4856,127.8053],[35.4827,127.8095],[35.4781,127.8077],[35.4705,127.814],[35.4665,127.7967],[35.4591,127.7823],[35.4518,127.7894],[35.446,127.7893],[35.4443,127.7858],[35.4469,127.7773],[35.4447,127.7733],[35.4397,127.7727],[35.4393,127.7759],[35.4343,127.78],[35.4262,127.7689],[35.4207,127.77],[35.4153,127.7593],[35.4027,127.7585],[35.3971,127.7484],[35.3832,127.7526],[35.3724,127.7386],[35.3648,127.7388],[35.3612,127.7341],[35.3552,127.7329],[35.3471,127.7352],[35.3375,127.7312],[35.3344,127.7185],[35.3158,127.6996],[35.3227,127.6839],[35.3206,127.6647],[35.3288,127.6582],[35.3246,127.6402],[35.3326,127.6207],[35.3422,127.6233],[35.3559,127.6122],[35.3659,127.6102],[35.3769,127.6257],[35.3847,127.6253],[35.3992,127.6363],[35.4027,127.6464],[35.4139,127.6568],[35.4144,127.6605],[35.4262,127.6636],[35.4274,127.6658],[35.4356,127.6652],[35.4457,127.6741],[35.4487,127.6704],[35.4475,127.6612],[35.4516,127.6534],[35.4491,127.6452],[35.4594,127.6367],[35.4782,127.6366],[35.4869,127.6531],[35.4913,127.65],[35.4979,127.6504],[35.5001,127.6442],[35.5133,127.6336],[35.5202,127.6344],[35.5253,127.6257],[35.5314,127.6253],[35.536,127.6287],[35.5337,127.6247],[35.5338,127.6207],[35.5366,127.6192],[35.5356,127.6127],[35.5409,127.6093],[35.5474,127.5968],[35.5534,127.5915],[35.5539,127.5849],[35.5648,127.5888],[35.5737,127.5961],[35.5776,127.6048],[35.5816,127.6063],[35.5839,127.6112],[35.5949,127.6075],[35.5989,127.6121],[35.6082,127.613],[35.6104,127.6182],[35.6151,127.6214],[35.6185,127.6353],[35.6291,127.6257],[35.638,127.6245],[35.6416,127.6203],[35.6461,127.6201],[35.651,127.6222],[35.6566,127.6295],[35.664,127.6289],[35.6728,127.6405],[35.679,127.6391],[35.6929,127.6418],[35.7014,127.6498],[35.7038,127.6494],[35.7058,127.6574],[35.7099,127.661],[35.7158,127.6599],[35.7249,127.6631],[35.7375,127.6604],[35.7416,127.6631],[35.7608,127.6623],[35.7688,127.6658],[35.7714,127.6695],[35.7709,127.6758],[35.7633,127.6843]]],"장수":[[[35.8241,127.621],[35.8148,127.6295],[35.8185,127.6343],[35.8122,127.6467],[35.8117,127.6549],[35.8181,127.6635],[35.8098,127.6708],[35.8103,127.6773],[35.8039,127.6868],[35.7955,127.6882],[35.7882,127.6997],[35.7777,127.6848],[35.7685,127.6794],[35.7714,127.6695],[35.764,127.6635],[35.7416,127.6631],[35.7375,127.6604],[35.7249,127.6631],[35.7158,127.6599],[35.7099,127.661],[35.7058,127.6574],[35.7038,127.6494],[35.7014,127.6498],[35.6929,127.6418],[35.679,127.6391],[35.6728,127.6405],[35.664,127.6289],[35.6566,127.6295],[35.651,127.6222],[35.6461,127.6201],[35.6416,127.6203],[35.638,127.6245],[35.6291,127.6257],[35.6185,127.6353],[35.6151,127.6214],[35.6104,127.6182],[35.6082,127.613],[35.5989,127.6121],[35.5949,127.6075],[35.5839,127.6112],[35.5816,127.6063],[35.5776,127.6048],[35.5737,127.5961],[35.5648,127.5888],[35.5528,127.5842],[35.5475,127.5785],[35.5461,127.5728],[35.5347,127.5715],[35.5333,127.5686],[35.5248,127.5685],[35.5189,127.5711],[35.5139,127.58],[35.502,127.5801],[35.4909,127.5635],[35.4801,127.5596],[35.4735,127.5618],[35.4678,127.545],[35.4716,127.5416],[35.4704,127.5358],[35.4789,127.515],[35.4811,127.5153],[35.4858,127.5267],[35.4958,127.5273],[35.4983,127.5161],[35.5089,127.5134],[35.5146,127.5036],[35.5217,127.5016],[35.5271,127.4913],[35.5341,127.4924],[35.5408,127.4709],[35.5464,127.4675],[35.5465,127.4562],[35.5401,127.4528],[35.5472,127.4412],[35.5516,127.4402],[35.5505,127.4241],[35.5608,127.4105],[35.5601,127.4056],[35.5531,127.3992],[35.5483,127.4026],[35.5461,127.3841],[35.558,127.3637],[35.5668,127.3635],[35.5764,127.3789],[35.5836,127.377],[35.5866,127.3718],[35.5981,127.3749],[35.6062,127.3727],[35.6132,127.3817],[35.6148,127.4253],[35.6221,127.4363],[35.6189,127.4427],[35.6214,127.4687],[35.6288,127.4701],[35.6375,127.4664],[35.6471,127.4739],[35.6547,127.4741],[35.6586,127.4777],[35.6611,127.4766],[35.6676,127.4642],[35.6746,127.4598],[35.6848,127.4669],[35.693,127.4649],[35.7025,127.4778],[35.7184,127.4761],[35.7223,127.4835],[35.7369,127.4952],[35.7543,127.5225],[35.7712,127.5128],[35.7777,127.5111],[35.7864,127.5134],[35.7916,127.5108],[35.7995,127.5133],[35.803,127.5184],[35.8122,127.5214],[35.8153,127.5331],[35.8068,127.5429],[35.8082,127.5529],[35.8003,127.5591],[35.7976,127.5673],[35.7944,127.5701],[35.7939,127.5787],[35.8029,127.5919],[35.8085,127.5946],[35.8053,127.599],[35.8066,127.6006],[35.8298,127.6067],[35.8388,127.6178],[35.8389,127.62],[35.8313,127.6227],[35.8241,127.621]]],"무주":[[[36.0668,127.6446],[36.0626,127.6484],[36.058,127.6491],[36.0559,127.6544],[36.0382,127.6609],[36.0387,127.6691],[36.0416,127.6727],[36.0514,127.6698],[36.0627,127.689],[36.058,127.6907],[36.0588,127.695],[36.0459,127.695],[36.0353,127.7019],[36.0357,127.7134],[36.0319,127.7192],[36.0323,127.7348],[36.0248,127.7415],[36.0297,127.7473],[36.0241,127.7539],[36.0252,127.7616],[36.0216,127.7626],[36.0152,127.7593],[36.0123,127.7651],[36.0165,127.7815],[36.0145,127.7876],[36.0266,127.8007],[36.0282,127.816],[36.0352,127.8304],[36.0391,127.8528],[36.0329,127.8557],[36.0315,127.8606],[36.0243,127.8661],[36.0225,127.8768],[36.0089,127.8757],[36.0025,127.8786],[35.9969,127.8756],[35.9859,127.8939],[35.9797,127.8896],[35.9777,127.8963],[35.9719,127.8963],[35.9569,127.9023],[35.9512,127.9101],[35.9459,127.9101],[35.9406,127.9061],[35.9342,127.8957],[35.9289,127.8822],[35.9195,127.8824],[35.9148,127.8882],[35.9096,127.8851],[35.9099,127.8795],[35.904,127.8693],[35.9065,127.8595],[35.897,127.8583],[35.8901,127.8507],[35.8813,127.8537],[35.8776,127.8511],[35.8779,127.8468],[35.8756,127.8449],[35.8703,127.8449],[35.8662,127.8418],[35.8683,127.8266],[35.8625,127.8194],[35.8596,127.8194],[35.8568,127.8145],[35.8536,127.8139],[35.8587,127.8044],[35.8508,127.7838],[35.8432,127.7772],[35.8383,127.7688],[35.8368,127.7578],[35.8444,127.7445],[35.8352,127.738],[35.8271,127.7386],[35.8209,127.7325],[35.8149,127.7312],[35.8125,127.7246],[35.8053,127.724],[35.7973,127.7194],[35.7918,127.7105],[35.7882,127.6997],[35.7916,127.6934],[35.7955,127.6882],[35.8039,127.6868],[35.8103,127.6773],[35.8098,127.6708],[35.8181,127.6635],[35.8117,127.6549],[35.8122,127.6467],[35.8185,127.6343],[35.8148,127.6295],[35.8241,127.621],[35.8313,127.6227],[35.8406,127.6194],[35.8474,127.6248],[35.8593,127.6177],[35.8585,127.6128],[35.8723,127.5992],[35.8776,127.5981],[35.8803,127.6031],[35.8811,127.6016],[35.8817,127.5931],[35.8776,127.5892],[35.8765,127.5813],[35.8789,127.5746],[35.8979,127.5849],[35.9085,127.5767],[35.9127,127.5684],[35.9183,127.5673],[35.9229,127.5631],[35.9234,127.554],[35.9331,127.5486],[35.9375,127.553],[35.9469,127.5549],[35.9542,127.5479],[35.9602,127.5466],[35.9651,127.5395],[35.9708,127.5366],[35.9712,127.5338],[35.9782,127.5369],[35.9775,127.5279],[35.9851,127.5244],[35.9949,127.5359],[36.0005,127.5361],[36.008,127.5321],[36.0117,127.5399],[36.0199,127.5361],[36.0259,127.5388],[36.0326,127.5369],[36.0346,127.532],[36.0408,127.5314],[36.0381,127.5469],[36.0328,127.5522],[36.0312,127.5663],[36.0233,127.5745],[36.0272,127.5826],[36.026,127.5898],[36.021,127.5915],[36.019,127.5963],[36.0119,127.6001],[36.0119,127.6066],[36.001,127.6106],[36.0006,127.6135],[36.008,127.6187],[36.0191,127.6164],[36.0223,127.611],[36.0253,127.6107],[36.0246,127.6229],[36.0269,127.6269],[36.032,127.6284],[36.0295,127.635],[36.0323,127.6397],[36.0354,127.6327],[36.0422,127.6305],[36.0423,127.6251],[36.0392,127.6191],[36.0642,127.6206],[36.0673,127.6239],[36.0667,127.638],[36.0686,127.6382],[36.0668,127.6446]]],"금산":[[[36.2715,127.3776],[36.2623,127.3903],[36.2525,127.3866],[36.2459,127.3879],[36.2429,127.3909],[36.2342,127.3873],[36.2325,127.3993],[36.2229,127.4045],[36.2176,127.4106],[36.2129,127.408],[36.2052,127.4294],[36.1986,127.4335],[36.1948,127.4411],[36.2008,127.4556],[36.207,127.4542],[36.2097,127.4592],[36.2129,127.4603],[36.2148,127.4691],[36.2223,127.4673],[36.2267,127.4778],[36.2297,127.4779],[36.2325,127.4885],[36.2371,127.49],[36.238,127.4926],[36.2406,127.5181],[36.2509,127.5326],[36.2509,127.5368],[36.2473,127.5351],[36.2428,127.5379],[36.2393,127.5494],[36.2255,127.5453],[36.2277,127.5639],[36.2335,127.5703],[36.2328,127.5795],[36.2175,127.5978],[36.2051,127.5997],[36.1952,127.5925],[36.1849,127.5977],[36.1774,127.5931],[36.169,127.6015],[36.16,127.6017],[36.1448,127.5909],[36.1345,127.5894],[36.1235,127.599],[36.1182,127.6055],[36.1185,127.6101],[36.1118,127.6131],[36.1089,127.6191],[36.1049,127.6169],[36.0936,127.6173],[36.0824,127.6321],[36.0736,127.6342],[36.0679,127.6383],[36.0673,127.6239],[36.0642,127.6206],[36.0392,127.6191],[36.0423,127.6251],[36.0422,127.6305],[36.0354,127.6327],[36.0323,127.6397],[36.0295,127.635],[36.032,127.6284],[36.0269,127.6269],[36.0246,127.6229],[36.0253,127.6107],[36.0223,127.611],[36.0191,127.6164],[36.008,127.6187],[36.0008,127.6142],[36.001,127.6106],[36.0119,127.6066],[36.0119,127.6001],[36.019,127.5963],[36.021,127.5915],[36.026,127.5898],[36.0272,127.5826],[36.0233,127.5745],[36.0312,127.5663],[36.0328,127.5522],[36.0381,127.5469],[36.0408,127.5314],[36.0346,127.532],[36.0326,127.5369],[36.0259,127.5388],[36.0199,127.5361],[36.0117,127.5399],[36.008,127.5321],[36.0005,127.5361],[35.9949,127.5359],[35.9851,127.5244],[35.9796,127.5067],[35.9874,127.4993],[35.9862,127.4944],[35.9783,127.4877],[35.9806,127.4759],[35.9881,127.4684],[35.9839,127.4639],[35.9838,127.4558],[35.9932,127.4486],[35.9989,127.4481],[36.0036,127.4442],[36.0066,127.445],[36.0093,127.4372],[36.0146,127.4352],[36.0206,127.4373],[36.0295,127.4346],[36.0227,127.4196],[36.0152,127.4134],[36.0142,127.4073],[36.0087,127.4012],[36.0169,127.392],[36.0162,127.3896],[36.0213,127.3839],[36.0229,127.3765],[36.0306,127.3782],[36.0345,127.3735],[36.0411,127.3736],[36.0545,127.3604],[36.0615,127.3606],[36.0658,127.3643],[36.0682,127.364],[36.0692,127.3595],[36.0762,127.3617],[36.0815,127.357],[36.0869,127.3573],[36.0894,127.3601],[36.0946,127.3502],[36.0983,127.3477],[36.1083,127.3549],[36.1136,127.3531],[36.1179,127.3444],[36.1305,127.3385],[36.1306,127.3228],[36.1459,127.3232],[36.1541,127.3184],[36.1643,127.3191],[36.1678,127.3217],[36.1711,127.3204],[36.1753,127.327],[36.1836,127.3306],[36.1834,127.3355],[36.1967,127.344],[36.1976,127.3476],[36.2041,127.3469],[36.2118,127.353],[36.2139,127.3594],[36.2182,127.3604],[36.2189,127.3642],[36.2267,127.3601],[36.2323,127.3634],[36.2342,127.3619],[36.2436,127.3651],[36.2516,127.3642],[36.2547,127.3596],[36.2691,127.3629],[36.2699,127.3712],[36.2722,127.3725],[36.2715,127.3776]]],"대전":[[[36.2041,127.4309],[36.2129,127.408],[36.2176,127.4106],[36.2229,127.4045],[36.2325,127.3993],[36.2342,127.3873],[36.2429,127.3909],[36.2459,127.3879],[36.2525,127.3866],[36.2623,127.3903],[36.2715,127.3776],[36.2722,127.3725],[36.2699,127.3712],[36.2691,127.3629],[36.2622,127.3602],[36.2547,127.3596],[36.2516,127.3642],[36.2436,127.3651],[36.2342,127.3619],[36.2323,127.3634],[36.2267,127.3601],[36.2189,127.3642],[36.2185,127.3606],[36.2139,127.3594],[36.2118,127.353],[36.208,127.3495],[36.2033,127.3467],[36.1976,127.3476],[36.1967,127.344],[36.1834,127.3355],[36.1835,127.3327],[36.1942,127.3298],[36.2007,127.3336],[36.2041,127.3281],[36.2037,127.323],[36.2134,127.3215],[36.2213,127.3153],[36.2297,127.3036],[36.2226,127.3032],[36.2215,127.2973],[36.2231,127.2938],[36.2298,127.2923],[36.2358,127.2818],[36.2524,127.2794],[36.2585,127.2826],[36.2647,127.2918],[36.2652,127.2812],[36.2761,127.2588],[36.291,127.2467],[36.2969,127.2541],[36.2957,127.2598],[36.3019,127.2607],[36.3035,127.2584],[36.3099,127.258],[36.3217,127.2608],[36.3272,127.2598],[36.3285,127.2661],[36.3314,127.2681],[36.3372,127.2654],[36.341,127.2686],[36.3448,127.2791],[36.3541,127.2724],[36.3609,127.2706],[36.3653,127.2777],[36.3749,127.281],[36.3867,127.2781],[36.4146,127.2821],[36.4162,127.2911],[36.4232,127.2964],[36.4247,127.3109],[36.4205,127.3164],[36.4234,127.322],[36.4221,127.3263],[36.4305,127.3405],[36.4357,127.3403],[36.4444,127.3449],[36.4479,127.3534],[36.4559,127.3586],[36.4633,127.3565],[36.4748,127.364],[36.4826,127.3589],[36.4885,127.3602],[36.4886,127.3692],[36.4995,127.3803],[36.5002,127.3839],[36.4855,127.403],[36.4766,127.4042],[36.4618,127.3997],[36.456,127.4021],[36.4564,127.4359],[36.4504,127.4441],[36.4493,127.4513],[36.4561,127.4626],[36.4645,127.4638],[36.4737,127.4703],[36.4766,127.484],[36.4573,127.4783],[36.4528,127.4869],[36.4562,127.5006],[36.4519,127.5045],[36.4412,127.4935],[36.4341,127.4897],[36.4087,127.5016],[36.4096,127.5105],[36.4225,127.5145],[36.4216,127.5209],[36.4234,127.5243],[36.4192,127.5294],[36.4193,127.5423],[36.4121,127.5429],[36.4088,127.5456],[36.3982,127.5597],[36.3949,127.554],[36.3979,127.5392],[36.3917,127.5334],[36.3875,127.5249],[36.3701,127.5266],[36.3543,127.5224],[36.3461,127.512],[36.3463,127.5074],[36.3432,127.5081],[36.3393,127.5006],[36.3256,127.503],[36.3208,127.5],[36.3199,127.496],[36.3164,127.4978],[36.312,127.4946],[36.3057,127.499],[36.3016,127.4974],[36.2999,127.4924],[36.297,127.4912],[36.2828,127.4988],[36.2727,127.4888],[36.2684,127.4903],[36.2612,127.486],[36.2578,127.4898],[36.2514,127.4876],[36.2411,127.4932],[36.2335,127.49],[36.2297,127.4779],[36.226,127.4768],[36.223,127.4679],[36.2152,127.4696],[36.2129,127.4603],[36.2097,127.4592],[36.207,127.4542],[36.2011,127.4559],[36.1948,127.4437],[36.1986,127.4335],[36.2041,127.4309]]]}''')
ZONE_NAME = {"함양": "함양군", "장수": "장수군", "무주": "무주군", "금산": "금산군", "대전": "대전"}
ZONE_PROV = {"함양": ("경상남도", "경남"), "장수": ("전북", "전라북"), "무주": ("전북", "전라북"),
             "금산": ("충청남도", "충남"), "대전": ("대전",)}
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
    """'충청남도(태안, 금산), 대전' 같은 지역 글자에서 우리 구역(함양/장수/무주/금산/대전) 찾기"""
    found = set()
    for tok in split_top(text):
        m = re.match(r"^([^()]+?)\s*(?:\((.*)\))?\s*$", tok, re.S)
        if not m:
            continue
        prov, subs = m.group(1).strip(), m.group(2)
        for z, prefixes in ZONE_PROV.items():
            if not any(prov.startswith(x) for x in prefixes):
                continue
            if z == "대전" or subs is None:  # 대전 전체이거나 도 전체
                found.add(z)
            elif any(z in sub for sub in split_top(subs)):
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
            return {"tm": when, "zones": parse_warnings(it)}
        except Exception as e:
            print(f"특보 조회 실패({attempt + 1}/3): {e}")
            time.sleep(2)
    return None


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
    wrn = fetch_warnings()
    print("특보:", json.dumps(wrn, ensure_ascii=False) if wrn else "조회 실패")
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
            .replace("__WRN__", json.dumps(wrn, ensure_ascii=False))
            .replace("__ZONEGEO__", json.dumps(ZONES_GEO, ensure_ascii=False))
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
