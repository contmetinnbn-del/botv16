#!/usr/bin/env python3
"""
Bot V15 Production - Adaptive regime scalper with shared risk manager.

Features:
- 3-state regime detection (TREND/RANGE/CHOP) tuned for 1m
- Dynamic TP/SL per regime with proper fee/slippage/buffer accounting
- Shared Market Risk Manager with auto-pause/resume (hysteresis)
- Trade frequency controller with adaptive selectivity
- Rolling winrate protection
- Telegram commands (/status, /pause, /resume, /close, /restart)
- Heartbeat notifications with toxicity score
- Position reconciliation on startup
- Idle watchdog diagnostics
- Multi-instance safe runtime
"""

from __future__ import annotations

import argparse, csv, dataclasses, datetime as dt, fcntl, hashlib, json, math, os, signal, sys, threading, time
from collections import deque
from typing import Any, Dict, List, Optional, Tuple, Callable

try:
    import ccxt
except Exception:
    print("Missing ccxt. Install: pip install ccxt", file=sys.stderr)
    raise

import requests

def utcnow(): return dt.datetime.now(dt.timezone.utc)
def ts(): return utcnow().strftime("%Y-%m-%d %H:%M:%S UTC")
def ensure_dir(p):
    d = os.path.dirname(p) if os.path.splitext(p)[1] else p
    if d and not os.path.exists(d): os.makedirs(d, exist_ok=True)
def safe_float(x, default=None):
    try: return float(x) if x is not None else default
    except: return default
def pct(a, b): return (b/a - 1.0) * 100.0 if a != 0 else 0.0
def round_step(x, step): return math.floor(x/step)*step if step > 0 else x
def html_escape(s): return s.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
def sma(vals, n): return sum(vals[-n:])/n if len(vals) >= n else None
def ema(vals, n):
    if len(vals) < n: return None
    alpha, result = 2.0/(n+1), vals[-n]
    for v in vals[-n+1:]: result = alpha*v + (1-alpha)*result
    return result
def atr(high, low, close, n=14):
    if len(close) < n+1: return None
    trs = [max(high[i]-low[i], abs(high[i]-close[i-1]), abs(low[i]-close[i-1])) for i in range(-n, 0)]
    return sum(trs)/n
def slope(vals, n):
    if len(vals) < n: return None
    y = vals[-n:]
    x_mean, y_mean = (n-1)/2, sum(y)/n
    num = sum((i-x_mean)*(yi-y_mean) for i,yi in enumerate(y))
    den = sum((i-x_mean)**2 for i in range(n))
    return num/den if den != 0 else None
def wick_ok(o, h, l, c, min_wick_ratio):
    rng = max(h-l, 1e-12)
    return (max(h-max(o,c),0) + max(min(o,c)-l,0))/rng >= min_wick_ratio

def get_instance_id(cfg_path): return hashlib.md5(os.path.abspath(cfg_path).encode()).hexdigest()[:12]

class InstanceLock:
    def __init__(self, iid, lock_dir="/tmp"):
        self.lock_path = os.path.join(lock_dir, f"bot_{iid}.lock")
        self.pid_path = os.path.join(lock_dir, f"bot_{iid}.pid")
        self.lock_file = None
    def acquire(self):
        try:
            self.lock_file = open(self.lock_path, "w")
            fcntl.flock(self.lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            with open(self.pid_path, "w") as f: f.write(str(os.getpid()))
            return True
        except (IOError, OSError):
            if self.lock_file: self.lock_file.close(); self.lock_file = None
            return False
    def release(self):
        if self.lock_file:
            try: fcntl.flock(self.lock_file.fileno(), fcntl.LOCK_UN); self.lock_file.close()
            except: pass
            self.lock_file = None
        for p in [self.lock_path, self.pid_path]:
            try: os.remove(p)
            except: pass

class Telegram:
    def __init__(self, token, chat_id, enabled=True, timeout_s=10):
        self.enabled = enabled and bool(token) and bool(chat_id)
        self.token = token or os.environ.get("TG_TOKEN", "")
        self.chat_id = chat_id or os.environ.get("TG_CHAT_ID", "")
        self.timeout_s = timeout_s
        self._last_update_id = 0
        self._handlers: Dict[str, Callable] = {}
    def send(self, text_html):
        if not self.enabled: return False
        try:
            r = requests.post(f"https://api.telegram.org/bot{self.token}/sendMessage",
                data={"chat_id": self.chat_id, "text": text_html, "parse_mode": "HTML", "disable_web_page_preview": True}, timeout=self.timeout_s)
            return r.status_code == 200
        except: return False
    def register_command(self, cmd, handler): self._handlers[cmd.lower()] = handler
    def poll_commands(self):
        if not self.enabled: return
        try:
            r = requests.get(f"https://api.telegram.org/bot{self.token}/getUpdates",
                params={"offset": self._last_update_id+1, "timeout": 0, "limit": 10}, timeout=5)
            if r.status_code != 200: return
            for upd in r.json().get("result", []):
                self._last_update_id = max(self._last_update_id, upd.get("update_id", 0))
                msg = upd.get("message", {})
                txt, cid = msg.get("text", ""), str(msg.get("chat", {}).get("id", ""))
                if cid == self.chat_id and txt.startswith("/"):
                    cmd = txt.split()[0].lower().replace("/", "")
                    if cmd in self._handlers:
                        try: self._handlers[cmd]()
                        except Exception as e: self.send(f"❌ Error: {html_escape(str(e))}")
        except: pass

def fmt_money(x, q): return f"{x:.4f} {q}"
def fmt_price(x):
    if x >= 1000: return f"{x:.2f}"
    if x >= 100: return f"{x:.3f}"
    if x >= 1: return f"{x:.6f}"
    return f"{x:.8f}"
def pnl_badge(p): return "🟢" if p >= 0 else "🔴"
def wl_badge(p): return "W 🏆" if p >= 0 else "L 🪦"

@dataclasses.dataclass
class ToxicityScore:
    total: float; spread_score: float; volatility_score: float; whipsaw_score: float
    loss_cluster_score: float; error_score: float; reasons: List[str]
    @property
    def is_toxic(self): return self.total >= 100.0

class MarketRiskManager:
    def __init__(self, spread_threshold_pct=0.10, atr_spike_mult=3.0, whipsaw_threshold=5,
                 loss_cluster_threshold=3, error_threshold=5, pause_toxicity=100.0,
                 resume_toxicity=50.0, resume_sustain_s=60.0):
        self.spread_threshold_pct = spread_threshold_pct
        self.atr_spike_mult = atr_spike_mult
        self.whipsaw_threshold = whipsaw_threshold
        self.loss_cluster_threshold = loss_cluster_threshold
        self.error_threshold = error_threshold
        self.pause_toxicity = pause_toxicity
        self.resume_toxicity = resume_toxicity
        self.resume_sustain_s = resume_sustain_s
        self.paused = False
        self.paused_at = None
        self.last_toxicity = ToxicityScore(0,0,0,0,0,0,[])
        self.ma_cross_history: deque = deque(maxlen=20)
        self.recent_errors: deque = deque(maxlen=20)
        self.recent_losses: deque = deque(maxlen=10)
        self.baseline_atr = None
        self._good_since = None
    def record_error(self): self.recent_errors.append(time.time())
    def record_trade_result(self, pnl): self.recent_losses.append((time.time(), pnl < 0))
    def record_ma_cross(self, price, ma7): self.ma_cross_history.append((time.time(), price > ma7))
    def update_baseline_atr(self, atr_val):
        if self.baseline_atr is None: self.baseline_atr = atr_val
        else: self.baseline_atr = 0.95 * self.baseline_atr + 0.05 * atr_val
    def assess_toxicity(self, spread_pct, atr_pct, slippage_est_pct):
        reasons = []
        spread_score = min(40, (spread_pct/self.spread_threshold_pct - 1)*20) if spread_pct > self.spread_threshold_pct else 0
        if spread_score > 0: reasons.append(f"spread={spread_pct:.3f}%")
        volatility_score = 0
        if self.baseline_atr and atr_pct > self.baseline_atr * self.atr_spike_mult:
            volatility_score = min(40, (atr_pct/self.baseline_atr - 1)*15)
            reasons.append(f"atr_spike={atr_pct:.3f}%")
        now = time.time()
        recent_crosses = [x for x in self.ma_cross_history if x[0] > now - 300]
        flips = sum(1 for i in range(1, len(recent_crosses)) if recent_crosses[i][1] != recent_crosses[i-1][1]) if len(recent_crosses) >= 2 else 0
        whipsaw_score = min(30, flips*5) if flips >= self.whipsaw_threshold else 0
        if whipsaw_score > 0: reasons.append(f"whipsaw={flips}")
        recent_loss_results = [x for x in self.recent_losses if x[0] > now - 600]
        consec = 0
        for _, is_loss in reversed(recent_loss_results):
            if is_loss: consec += 1
            else: break
        loss_cluster_score = min(30, consec*10) if consec >= self.loss_cluster_threshold else 0
        if loss_cluster_score > 0: reasons.append(f"loss_cluster={consec}")
        recent_errs = len([e for e in self.recent_errors if e > now - 300])
        error_score = min(20, recent_errs*4) if recent_errs >= self.error_threshold else 0
        if error_score > 0: reasons.append(f"errors={recent_errs}")
        total = spread_score + volatility_score + whipsaw_score + loss_cluster_score + error_score
        self.last_toxicity = ToxicityScore(total, spread_score, volatility_score, whipsaw_score, loss_cluster_score, error_score, reasons)
        return self.last_toxicity
    def should_pause(self):
        if self.paused: return False, ""
        if self.last_toxicity.total >= self.pause_toxicity:
            return True, f"toxicity={self.last_toxicity.total:.0f} ({', '.join(self.last_toxicity.reasons)})"
        return False, ""
    def should_resume(self):
        if not self.paused: return False, ""
        now = time.time()
        if self.last_toxicity.total < self.resume_toxicity:
            if self._good_since is None: self._good_since = now
            elif now - self._good_since >= self.resume_sustain_s:
                self._good_since = None
                return True, f"toxicity={self.last_toxicity.total:.0f} sustained below {self.resume_toxicity}"
        else: self._good_since = None
        return False, ""
    def pause(self): self.paused = True; self.paused_at = time.time(); self._good_since = None
    def resume(self): self.paused = False; self.paused_at = None; self._good_since = None
    def entries_allowed(self): return not self.paused

@dataclasses.dataclass
class RegimeParams:
    tp_pct: float; sl_pct: float; trailing: bool; trail_activate_pct: float
    trail_step_pct: float; min_score_adjust: float; min_tp_edge_adjust: float

@dataclasses.dataclass
class RiskCfg:
    sl_pct: float; tp_pct: float; trailing: bool; trail_activate_pct: float; trail_step_pct: float
    max_hold_minutes: int; cooldown_after_close_s: int; daily_loss_limit_pct: float; max_consecutive_losses: int
    trend_params: RegimeParams; range_params: RegimeParams; chop_params: RegimeParams

@dataclasses.dataclass
class FrequencyControlCfg:
    enabled: bool; target_trades_per_2h: int; window_minutes: int; adjust_step_score: float
    adjust_step_edge: float; adjust_step_spread: float; min_score_floor: float; min_edge_floor: float; max_spread_ceiling: float

@dataclasses.dataclass
class WinrateProtectionCfg:
    enabled: bool; rolling_window_trades: int; threshold_pct: float; tighten_score_add: float
    tighten_edge_add: float; tighten_cooldown_add_s: int

@dataclasses.dataclass
class RegimeDetectionCfg:
    chop_max_atr_pct: float; chop_max_ma_dist_pct: float; chop_max_slope_pct: float
    chop_max_vol_ratio: float; trend_min_strength: float; block_entries_in_chop: bool

@dataclasses.dataclass
class EntryCfg:
    timeframe: str; min_atr_pct: float; max_atr_pct: float; max_spread_pct: float
    min_vol_ratio: float; min_wick_ratio: float; min_score: float; min_tp_edge_pct: float; entry_gap_s: int

@dataclasses.dataclass
class MoneyCfg:
    symbol: str; quote_budget: float; max_positions: int; fee_bps: float; slippage_bps: float

@dataclasses.dataclass
class PathsCfg:
    log_path: str; state_path: str; journal_path: str; paper_journal_path: str

@dataclasses.dataclass
class TgCfg:
    enabled: bool; token: str; chat_id: str; heartbeat_minutes: int

@dataclasses.dataclass
class BotCfg:
    name: str; exchange: str; api_key: str; api_secret: str; testnet: bool; dry_run: bool
    money: MoneyCfg; entry: EntryCfg; risk: RiskCfg; regime_detection: RegimeDetectionCfg
    frequency_control: FrequencyControlCfg; winrate_protection: WinrateProtectionCfg; paths: PathsCfg; telegram: TgCfg

def load_cfg(path):
    raw = json.load(open(path, "r", encoding="utf-8"))
    money, entry, risk, paths, tg = raw["money"], raw["entry"], raw["risk"], raw.get("paths", {}), raw.get("telegram", {})
    regime_det, freq_ctrl, winrate_prot = raw.get("regime_detection", {}), raw.get("frequency_control", {}), raw.get("winrate_protection", {})
    trend_p, range_p, chop_p = risk.get("trend_params", {}), risk.get("range_params", {}), risk.get("chop_params", {})
    return BotCfg(
        name=raw.get("name", "V15"), exchange=raw.get("exchange", "binance"),
        api_key=raw.get("api_key", ""), api_secret=raw.get("api_secret", ""),
        testnet=bool(raw.get("testnet", False)), dry_run=bool(raw.get("dry_run", False)),
        money=MoneyCfg(symbol=money["symbol"], quote_budget=float(money["quote_budget"]),
            max_positions=int(money.get("max_positions", 1)), fee_bps=float(money.get("fee_bps", 10.0)),
            slippage_bps=float(money.get("slippage_bps", 2.0))),
        entry=EntryCfg(timeframe=entry.get("timeframe", "1m"), min_atr_pct=float(entry.get("min_atr_pct", 0.02)),
            max_atr_pct=float(entry.get("max_atr_pct", 1.0)), max_spread_pct=float(entry.get("max_spread_pct", 0.08)),
            min_vol_ratio=float(entry.get("min_vol_ratio", 0.6)), min_wick_ratio=float(entry.get("min_wick_ratio", 0.10)),
            min_score=float(entry.get("min_score", 2.0)), min_tp_edge_pct=float(entry.get("min_tp_edge_pct", 0.04)),
            entry_gap_s=int(entry.get("entry_gap_s", 8))),
        risk=RiskCfg(sl_pct=float(risk.get("sl_pct", 0.22)), tp_pct=float(risk.get("tp_pct", 0.38)),
            trailing=bool(risk.get("trailing", True)), trail_activate_pct=float(risk.get("trail_activate_pct", 0.18)),
            trail_step_pct=float(risk.get("trail_step_pct", 0.08)), max_hold_minutes=int(risk.get("max_hold_minutes", 18)),
            cooldown_after_close_s=int(risk.get("cooldown_after_close_s", 8)),
            daily_loss_limit_pct=float(risk.get("daily_loss_limit_pct", 2.5)),
            max_consecutive_losses=int(risk.get("max_consecutive_losses", 99999)),
            trend_params=RegimeParams(tp_pct=float(trend_p.get("tp_pct", 0.40)), sl_pct=float(trend_p.get("sl_pct", 0.22)),
                trailing=bool(trend_p.get("trailing", True)), trail_activate_pct=float(trend_p.get("trail_activate_pct", 0.22)),
                trail_step_pct=float(trend_p.get("trail_step_pct", 0.08)), min_score_adjust=float(trend_p.get("min_score_adjust", -0.3)),
                min_tp_edge_adjust=float(trend_p.get("min_tp_edge_adjust", -0.02))),
            range_params=RegimeParams(tp_pct=float(range_p.get("tp_pct", 0.35)), sl_pct=float(range_p.get("sl_pct", 0.22)),
                trailing=bool(range_p.get("trailing", True)), trail_activate_pct=float(range_p.get("trail_activate_pct", 0.18)),
                trail_step_pct=float(range_p.get("trail_step_pct", 0.08)), min_score_adjust=float(range_p.get("min_score_adjust", 0.0)),
                min_tp_edge_adjust=float(range_p.get("min_tp_edge_adjust", 0.0))),
            chop_params=RegimeParams(tp_pct=float(chop_p.get("tp_pct", 0.30)), sl_pct=float(chop_p.get("sl_pct", 0.20)),
                trailing=bool(chop_p.get("trailing", True)), trail_activate_pct=float(chop_p.get("trail_activate_pct", 0.16)),
                trail_step_pct=float(chop_p.get("trail_step_pct", 0.06)), min_score_adjust=float(chop_p.get("min_score_adjust", 0.2)),
                min_tp_edge_adjust=float(chop_p.get("min_tp_edge_adjust", 0.01)))),
        regime_detection=RegimeDetectionCfg(chop_max_atr_pct=float(regime_det.get("chop_max_atr_pct", 0.06)),
            chop_max_ma_dist_pct=float(regime_det.get("chop_max_ma_dist_pct", 0.10)),
            chop_max_slope_pct=float(regime_det.get("chop_max_slope_pct", 0.06)),
            chop_max_vol_ratio=float(regime_det.get("chop_max_vol_ratio", 1.0)),
            trend_min_strength=float(regime_det.get("trend_min_strength", 0.20)),
            block_entries_in_chop=bool(regime_det.get("block_entries_in_chop", False))),
        frequency_control=FrequencyControlCfg(enabled=bool(freq_ctrl.get("enabled", True)),
            target_trades_per_2h=int(freq_ctrl.get("target_trades_per_2h", 12)),
            window_minutes=int(freq_ctrl.get("window_minutes", 120)),
            adjust_step_score=float(freq_ctrl.get("adjust_step_score", 0.06)),
            adjust_step_edge=float(freq_ctrl.get("adjust_step_edge", 0.015)),
            adjust_step_spread=float(freq_ctrl.get("adjust_step_spread", 0.003)),
            min_score_floor=float(freq_ctrl.get("min_score_floor", 1.5)),
            min_edge_floor=float(freq_ctrl.get("min_edge_floor", 0.02)),
            max_spread_ceiling=float(freq_ctrl.get("max_spread_ceiling", 0.12))),
        winrate_protection=WinrateProtectionCfg(enabled=bool(winrate_prot.get("enabled", True)),
            rolling_window_trades=int(winrate_prot.get("rolling_window_trades", 20)),
            threshold_pct=float(winrate_prot.get("threshold_pct", 45.0)),
            tighten_score_add=float(winrate_prot.get("tighten_score_add", 0.15)),
            tighten_edge_add=float(winrate_prot.get("tighten_edge_add", 0.02)),
            tighten_cooldown_add_s=int(winrate_prot.get("tighten_cooldown_add_s", 2))),
        paths=PathsCfg(log_path=paths.get("log_path", "logs/bot.log"), state_path=paths.get("state_path", "logs/state.json"),
            journal_path=paths.get("journal_path", "logs/trade_journal.csv"),
            paper_journal_path=paths.get("paper_journal_path", "logs/paper_signals.csv")),
        telegram=TgCfg(enabled=bool(tg.get("enabled", False)), token=str(tg.get("token", "")),
            chat_id=str(tg.get("chat_id", "")), heartbeat_minutes=int(tg.get("heartbeat_minutes", 15))))

class V15Bot:
    def __init__(self, cfg: BotCfg, instance_id: str = "default"):
        self.cfg = cfg
        self.instance_id = instance_id
        ensure_dir(cfg.paths.log_path); ensure_dir(cfg.paths.state_path)
        ensure_dir(cfg.paths.journal_path); ensure_dir(cfg.paths.paper_journal_path)
        self.tg = Telegram(cfg.telegram.token, cfg.telegram.chat_id, enabled=cfg.telegram.enabled)
        self._register_tg_commands()
        if not cfg.dry_run:
            self.ex = self._make_exchange()
            self.symbol = cfg.money.symbol
            self.market = self._init_market(self.symbol)
            self.base, self.quote = self.symbol.split("/")
        else:
            self.symbol = cfg.money.symbol
            self.base, self.quote = self.symbol.split("/")
            self._log("INFO", "DRY RUN MODE")
        self.risk_manager = MarketRiskManager(spread_threshold_pct=cfg.entry.max_spread_pct*1.5, pause_toxicity=100.0, resume_toxicity=40.0, resume_sustain_s=90.0)
        self.trade_history: deque = deque(maxlen=100)
        self.recent_trades: deque = deque(maxlen=cfg.winrate_protection.rolling_window_trades)
        self.last_entry_attempt_ts = time.time()
        self.idle_diagnostics_interval = 300
        self.last_idle_diagnostic_ts = 0.0
        self._load_state()
        self._reconcile_position()
        self._log_session_summary()
        self.last_heartbeat = time.time()
        self.running = True
        self._manual_pause = False
        self._start_time = time.time()

    def _register_tg_commands(self):
        self.tg.register_command("status", self._cmd_status)
        self.tg.register_command("pause", self._cmd_pause)
        self.tg.register_command("resume", self._cmd_resume)
        self.tg.register_command("close", self._cmd_close)
        self.tg.register_command("restart", self._cmd_restart)

    def _cmd_status(self):
        pos = self.state.get("position")
        day_pnl = float(self.state.get("day_pnl_quote", 0.0))
        toxicity = self.risk_manager.last_toxicity
        pos_text = f"LONG {float(pos['qty']):.4f} @ {fmt_price(float(pos['entry']))}" if pos else "FLAT"
        wins = sum(1 for p in self.recent_trades if p >= 0)
        winrate = (wins/len(self.recent_trades)*100) if self.recent_trades else 0
        paused = "YES" if self.risk_manager.paused or self._manual_pause else "NO"
        self.tg.send(f"📊 <b>STATUS</b> {html_escape(self.cfg.name)}\n<code>Position:</code> {pos_text}\n<code>Day PnL:</code> {pnl_badge(day_pnl)} {day_pnl:+.4f} {self.quote}\n<code>W/L:</code> {wins}/{len(self.recent_trades)-wins} ({winrate:.1f}%)\n<code>Paused:</code> {paused}\n<code>Toxicity:</code> {toxicity.total:.0f}/100\n🕐 {ts()}")

    def _cmd_pause(self):
        self._manual_pause = True
        self.tg.send("⏸️ <b>PAUSED</b> - Manual pause active")

    def _cmd_resume(self):
        self._manual_pause = False
        self.risk_manager.resume()
        self.tg.send("▶️ <b>RESUMED</b> - Entries enabled")

    def _cmd_close(self):
        pos = self.state.get("position")
        if not pos: self.tg.send("ℹ️ No position"); return
        self.tg.send("🔄 Closing...")
        try: self._force_close_position("MANUAL")
        except Exception as e: self.tg.send(f"❌ Close failed: {html_escape(str(e))}")

    def _cmd_restart(self):
        self.tg.send("🔄 Restarting...")
        self.running = False

    def _make_exchange(self):
        ex = ccxt.binance({"apiKey": self.cfg.api_key, "secret": self.cfg.api_secret, "enableRateLimit": True, "options": {"defaultType": "spot"}})
        if self.cfg.testnet: ex.set_sandbox_mode(True)
        return ex

    def _init_market(self, symbol):
        for attempt in range(3):
            try: self.ex.load_markets(reload=True); break
            except: time.sleep(2**attempt)
        sym = symbol.strip().upper().replace("-", "/")
        markets = getattr(self.ex, "markets", {}) or {}
        if sym not in markets: sym = symbol.strip()
        if sym not in markets: raise ValueError(f"Symbol '{symbol}' not found")
        self.symbol = sym
        return self.ex.market(sym)

    def _log(self, level, msg):
        line = f"[{level}] {ts()} | {msg}"
        print(line, flush=True)
        try:
            with open(self.cfg.paths.log_path, "a", encoding="utf-8") as f: f.write(line+"\n")
        except: pass

    def _load_state(self):
        self.state = {"position": None, "cooldown_until": 0.0, "day": utcnow().date().isoformat(), "day_pnl_quote": 0.0, "consecutive_losses": 0, "last_entry_ts": 0.0, "adaptive_score_adjust": 0.0, "adaptive_edge_adjust": 0.0, "adaptive_spread_adjust": 0.0, "last_order_id": None}
        if os.path.exists(self.cfg.paths.state_path):
            try: self.state.update(json.load(open(self.cfg.paths.state_path, "r", encoding="utf-8")))
            except: pass
        if self.state.get("day") != utcnow().date().isoformat():
            self.state["day"] = utcnow().date().isoformat(); self.state["day_pnl_quote"] = 0.0; self.state["consecutive_losses"] = 0

    def _save_state(self):
        try:
            tmp = self.cfg.paths.state_path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f: json.dump(self.state, f, indent=2)
            os.replace(tmp, self.cfg.paths.state_path)
        except Exception as e: self._log("ERROR", f"Save state failed: {e}")

    def _reconcile_position(self):
        if self.cfg.dry_run: return
        try:
            bal = self.ex.fetch_balance()
            total_base = float(bal.get(self.base, {}).get("total", 0) or 0)
            min_qty = self._min_qty() or 1.0
            ticker = self.ex.fetch_ticker(self.symbol)
            price = float(ticker.get("last", 0) or 0)
            notional = total_base * price if price > 0 else 0
            state_pos = self.state.get("position")
            if notional >= 5.0 and total_base >= min_qty:
                if not state_pos:
                    self._log("WARN", f"Reconciliation: Found orphan position {total_base:.6f} {self.base}")
                    try:
                        trades = self.ex.fetch_my_trades(self.symbol, limit=10)
                        buy_trades = [t for t in trades if t.get("side") == "buy"]
                        if buy_trades:
                            entry_price = float(buy_trades[-1].get("price", price))
                            self.state["position"] = {"qty": total_base, "entry": entry_price, "entry_ts": time.time()-300,
                                "sl": entry_price*(1-self.cfg.risk.sl_pct/100), "tp": entry_price*(1+self.cfg.risk.tp_pct/100),
                                "trail_active": False, "trail_sl": entry_price*(1-self.cfg.risk.sl_pct/100), "regime": "RANGE",
                                "regime_params": dataclasses.asdict(self.cfg.risk.range_params)}
                            self._save_state()
                    except Exception as e: self._log("ERROR", f"Reconciliation failed: {e}")
        except Exception as e: self._log("ERROR", f"Reconciliation error: {e}")

    def _journal(self, row):
        path = self.cfg.paths.journal_path
        exists = os.path.exists(path); ensure_dir(path)
        try:
            with open(path, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=list(row.keys()))
                if not exists: w.writeheader()
                w.writerow(row)
        except: pass

    def _paper_journal(self, row):
        path = self.cfg.paths.paper_journal_path
        exists = os.path.exists(path); ensure_dir(path)
        try:
            with open(path, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=list(row.keys()))
                if not exists: w.writeheader()
                w.writerow(row)
        except: pass

    def _fee_pct(self): return (self.cfg.money.fee_bps * 2) / 100.0
    def _slip_pct(self): return (self.cfg.money.slippage_bps * 2) / 100.0
    def _safety_buffer_pct(self): return 0.04
    def _total_cost_pct(self): return self._fee_pct() + self._slip_pct() + self._safety_buffer_pct()

    def _spread_pct(self):
        if self.cfg.dry_run: return 0.02
        try:
            ob = self.ex.fetch_order_book(self.symbol, limit=5)
            bid, ask = (ob["bids"][0][0] if ob["bids"] else None), (ob["asks"][0][0] if ob["asks"] else None)
            if not bid or not ask: return 999.0
            return (ask - bid) / ((bid + ask) / 2) * 100.0
        except: self.risk_manager.record_error(); return 999.0

    def _free_quote(self):
        if self.cfg.dry_run: return self.cfg.money.quote_budget * 10
        try:
            bal = self.ex.fetch_balance()
            free = bal.get(self.quote, {}).get("free", None)
            if free is None: free = bal["free"].get(self.quote, 0.0)
            return float(free)
        except: return 0.0

    def _min_qty(self):
        if self.cfg.dry_run: return 0.0001
        return float((self.market.get("limits") or {}).get("amount", {}).get("min") or 0.0)

    def _qty_step(self):
        if self.cfg.dry_run: return 0.0001
        prec = (self.market.get("precision") or {}).get("amount")
        return 10**(-int(prec)) if prec is not None else 0.0

    def _calc_qty(self, price):
        qty = self.cfg.money.quote_budget / price
        step = self._qty_step()
        if step > 0: qty = round_step(qty, step)
        minq = self._min_qty()
        if minq and qty < minq: qty = minq
        return max(qty, 0.0)

    def _fetch_ohlcv(self, limit=200):
        if self.cfg.dry_run:
            import random
            base = 2.1
            o = [base + random.uniform(-0.01, 0.01) for _ in range(limit)]
            h = [x + random.uniform(0, 0.005) for x in o]
            l = [x - random.uniform(0, 0.005) for x in o]
            c = [random.uniform(l[i], h[i]) for i in range(limit)]
            v = [random.uniform(1000, 5000) for _ in range(limit)]
            return o, h, l, c, v
        for attempt in range(3):
            try:
                ohlcv = self.ex.fetch_ohlcv(self.symbol, timeframe=self.cfg.entry.timeframe, limit=limit)
                return [float(x[1]) for x in ohlcv], [float(x[2]) for x in ohlcv], [float(x[3]) for x in ohlcv], [float(x[4]) for x in ohlcv], [float(x[5]) for x in ohlcv]
            except: self.risk_manager.record_error(); time.sleep(2**attempt)
        return [], [], [], [], []

    def _vol_ratio(self, vol, n=20):
        if len(vol) < n+1: return 1.0
        base = sum(vol[-n-1:-1])/n
        return vol[-1]/base if base > 0 else 1.0

    def _regime(self, o, h, l, c, v):
        ma7, ma25, ma99 = sma(c, 7), sma(c, 25), sma(c, 99)
        if ma7 is None or ma25 is None or ma99 is None: return "UNKNOWN", 0.0
        ma_dist = abs(ma7 - ma25) / c[-1] * 100.0
        sl = slope(c, 20) or 0.0
        slope_pct = abs(sl) / c[-1] * 100.0
        a = atr(h, l, c, 14)
        atr_pct = (a / c[-1] * 100.0) if a else 0.0
        vol_r = self._vol_ratio(v, 20)
        cfg = self.cfg.regime_detection
        is_chop = atr_pct <= cfg.chop_max_atr_pct and ma_dist <= cfg.chop_max_ma_dist_pct and slope_pct <= cfg.chop_max_slope_pct and vol_r <= cfg.chop_max_vol_ratio
        if is_chop: return "CHOP", 0.0
        strength = ma_dist + slope_pct + atr_pct * 0.5
        return ("TREND", strength) if strength >= cfg.trend_min_strength else ("RANGE", strength)

    def _get_regime_params(self, regime):
        if regime == "TREND": return self.cfg.risk.trend_params
        elif regime == "RANGE": return self.cfg.risk.range_params
        elif regime == "CHOP": return self.cfg.risk.chop_params
        return RegimeParams(self.cfg.risk.tp_pct, self.cfg.risk.sl_pct, self.cfg.risk.trailing, self.cfg.risk.trail_activate_pct, self.cfg.risk.trail_step_pct, 0.0, 0.0)

    def _score_entry(self, regime, o, h, l, c, ma7, ma25, ma99, atr_pct, vol_r, spread_pct):
        reasons, score = [], 0.0
        regime_params = self._get_regime_params(regime)
        tp_pct = regime_params.tp_pct
        if atr_pct >= self.cfg.entry.min_atr_pct: score += 1.2; reasons.append("atr_ok")
        else: reasons.append("atr_low")
        if atr_pct <= self.cfg.entry.max_atr_pct: score += 1.0; reasons.append("atr_ok2")
        else: reasons.append("atr_high")
        max_spread = self.cfg.entry.max_spread_pct + float(self.state.get("adaptive_spread_adjust", 0.0))
        if spread_pct <= max_spread: score += 1.4; reasons.append("spread_ok")
        else: reasons.append(f"spread_high({spread_pct:.3f}>{max_spread:.3f})")
        if vol_r >= self.cfg.entry.min_vol_ratio: score += 1.3; reasons.append("vol_ok")
        else: score += 0.5; reasons.append("vol_low")
        if wick_ok(o, h, l, c, self.cfg.entry.min_wick_ratio): score += 1.0; reasons.append("wick_ok")
        else: score += 0.3; reasons.append("wick_low")
        pullback = c <= ma7 or c <= ma25
        bounce = c > o and (l <= min(ma7, ma25))
        overext = abs(c - ma25) / c * 100.0 <= 0.55
        if pullback: score += 1.0; reasons.append("pullback")
        if bounce: score += 1.1; reasons.append("bounce")
        if overext: score += 0.8; reasons.append("overext_ok")
        else: reasons.append("overext_bad")
        ma99_dist_pct = abs(c - ma99) / c * 100.0
        if ma99_dist_pct <= 0.15 and c > o: score += 1.5; reasons.append("ma99_bounce")
        trend_ok, trend_down = ma7 >= ma25 >= ma99, ma7 <= ma25 <= ma99
        if regime == "TREND":
            if trend_ok: score += 1.8; reasons.append("trend_up")
            elif trend_down: score -= 2.0; reasons.append("trend_down_block")
            else: score += 0.5; reasons.append("trend_mixed")
        elif regime == "RANGE":
            if c >= ma99 * 0.998: score += 1.2; reasons.append("range_ok")
            else: score += 0.2; reasons.append("below_ma99")
        elif regime == "CHOP":
            if abs(c - ma25) / c * 100.0 <= 0.25: score += 1.0; reasons.append("chop_near_ma")
            else: score += 0.3; reasons.append("chop_away_ma")
        total_cost = self._total_cost_pct() + spread_pct
        tp_edge = tp_pct - total_cost
        return score, reasons, tp_edge

    def _update_adaptive_params(self):
        if not self.cfg.frequency_control.enabled: return
        cfg = self.cfg.frequency_control
        now = time.time()
        cutoff = now - cfg.window_minutes * 60
        actual_rate = len([t for t in self.trade_history if t >= cutoff])
        delta = actual_rate - cfg.target_trades_per_2h
        if delta < -3:
            self.state["adaptive_score_adjust"] = max(float(self.state.get("adaptive_score_adjust", 0.0)) - cfg.adjust_step_score, -(self.cfg.entry.min_score - cfg.min_score_floor))
            self.state["adaptive_edge_adjust"] = max(float(self.state.get("adaptive_edge_adjust", 0.0)) - cfg.adjust_step_edge, -(self.cfg.entry.min_tp_edge_pct - cfg.min_edge_floor))
            self.state["adaptive_spread_adjust"] = min(float(self.state.get("adaptive_spread_adjust", 0.0)) + cfg.adjust_step_spread, cfg.max_spread_ceiling - self.cfg.entry.max_spread_pct)
        elif delta > 3:
            self.state["adaptive_score_adjust"] = min(float(self.state.get("adaptive_score_adjust", 0.0)) + cfg.adjust_step_score, 1.0)
            self.state["adaptive_edge_adjust"] = min(float(self.state.get("adaptive_edge_adjust", 0.0)) + cfg.adjust_step_edge, 0.15)
            self.state["adaptive_spread_adjust"] = max(float(self.state.get("adaptive_spread_adjust", 0.0)) - cfg.adjust_step_spread, -self.cfg.entry.max_spread_pct * 0.3)

    def _get_winrate_adjustment(self):
        if not self.cfg.winrate_protection.enabled: return 0.0, 0.0, 0
        cfg = self.cfg.winrate_protection
        if len(self.recent_trades) < min(8, cfg.rolling_window_trades // 3): return 0.0, 0.0, 0
        wins = sum(1 for pnl in self.recent_trades if pnl >= 0)
        winrate = (wins / len(self.recent_trades)) * 100.0
        if winrate < cfg.threshold_pct: return cfg.tighten_score_add, cfg.tighten_edge_add, cfg.tighten_cooldown_add_s
        return 0.0, 0.0, 0

    def _can_trade(self):
        now = time.time()
        if self._manual_pause: return False, "manual_pause"
        if not self.risk_manager.entries_allowed(): return False, "risk_paused"
        wr_score_add, wr_edge_add, wr_cooldown_add = self._get_winrate_adjustment()
        effective_cooldown = float(self.state.get("cooldown_until", 0.0)) + wr_cooldown_add
        if now < effective_cooldown: return False, "cooldown"
        if now - float(self.state.get("last_entry_ts", 0.0)) < self.cfg.entry.entry_gap_s: return False, "entry_gap"
        day_pnl = float(self.state.get("day_pnl_quote", 0.0))
        limit = -abs(self.cfg.money.quote_budget) * (self.cfg.risk.daily_loss_limit_pct / 100.0)
        if day_pnl <= limit: return False, "daily_loss_limit"
        if int(self.state.get("consecutive_losses", 0)) >= self.cfg.risk.max_consecutive_losses: return False, "consecutive_losses_limit"
        if self.state.get("position") is not None: return False, "in_position"
        return True, "ok"

    def _place_buy(self, qty):
        if self.cfg.dry_run: return {"average": None, "filled": qty, "id": "dry_run"}
        last_order_id = self.state.get("last_order_id")
        if last_order_id:
            try:
                existing = self.ex.fetch_order(last_order_id, self.symbol)
                if existing.get("status") in ["open", "closed"] and existing.get("side") == "buy":
                    self._log("WARN", f"Skip duplicate buy - order {last_order_id} exists")
                    return existing
            except: pass
        order = self.ex.create_market_buy_order(self.symbol, qty)
        self.state["last_order_id"] = order.get("id")
        return order

    def _place_sell(self, qty):
        if self.cfg.dry_run: return {"average": None, "filled": qty, "id": "dry_run"}
        return self.ex.create_market_sell_order(self.symbol, qty)

    def _notify_buy(self, price, qty, regime, score, atr_pct, spread_pct, sl_px, tp_px, dry_run=False):
        prefix = "🟡 [DRY] " if dry_run else "🟢 "
        self.tg.send(f"{prefix}<b>BUY</b> {html_escape(self.symbol)}\n<code>Price:</code> {fmt_price(price)} | <code>TF:</code> {html_escape(self.cfg.entry.timeframe)}\n<code>Qty:</code> {qty:.6f} {html_escape(self.base)}\n<code>Cost:</code> {fmt_money(price*qty, self.quote)}\n<code>Regime:</code> <b>{html_escape(regime)}</b> | <code>Score:</code> {score:.2f}\n<code>ATR:</code> {atr_pct:.3f}% | <code>Spread:</code> {spread_pct:.3f}%\n<code>SL:</code> {fmt_price(sl_px)} | <code>TP:</code> {fmt_price(tp_px)}\n🕐 {ts()}")

    def _notify_sell(self, reason, entry, exit_, qty, pnl_q, pnl_pct, fees, dry_run=False):
        prefix = "🟡 [DRY] " if dry_run else ("✅" if pnl_q >= 0 else "❌")
        self.tg.send(f"{prefix} <b>SELL</b> {html_escape(self.symbol)} ({html_escape(reason)})\n<code>Entry:</code> {fmt_price(entry)} → <code>Exit:</code> {fmt_price(exit_)}\n<code>Qty:</code> {qty:.6f} {html_escape(self.base)}\n<code>Fees:</code> ~{fmt_money(fees, self.quote)}\n<code>PnL:</code> {pnl_badge(pnl_q)} <b>{pnl_q:+.4f} {html_escape(self.quote)}</b> ({pnl_pct:+.2f}%)\n<code>Result:</code> <b>{html_escape(wl_badge(pnl_q))}</b>\n🕐 {ts()}")

    def _notify_heartbeat(self, regime, strength, atr_pct, spread_pct):
        last_trade = f"{int((time.time() - self.trade_history[-1])/60)}m ago" if self.trade_history else "N/A"
        day_pnl = float(self.state.get("day_pnl_quote", 0.0))
        recent = [t for t in self.trade_history if t >= time.time() - 7200]
        wins = sum(1 for pnl in self.recent_trades if pnl >= 0)
        winrate = (wins / len(self.recent_trades) * 100) if self.recent_trades else 0
        toxicity = self.risk_manager.last_toxicity
        paused = "⏸️ " if self.risk_manager.paused or self._manual_pause else ""
        self.tg.send(f"💓 {paused}<b>HEARTBEAT</b> {html_escape(self.cfg.name)}\n<code>Regime:</code> <b>{html_escape(regime)}</b> (str: {strength:.2f})\n<code>ATR:</code> {atr_pct:.3f}% | <code>Spread:</code> {spread_pct:.3f}%\n<code>Trades(2h):</code> {len(recent)} | <code>Last:</code> {last_trade}\n<code>Day PnL:</code> {pnl_badge(day_pnl)} <b>{day_pnl:+.4f} {html_escape(self.quote)}</b>\n<code>W/L:</code> {wins}/{len(self.recent_trades)-wins} ({winrate:.1f}%)\n<code>Toxicity:</code> {toxicity.total:.0f}/100\n🕐 {ts()}")

    def _notify_pause(self, reason): self.tg.send(f"⚠️ <b>PAUSED</b> - Toxic market\n<code>Reason:</code> {html_escape(reason)}\n🕐 {ts()}")
    def _notify_resume(self, reason): self.tg.send(f"▶️ <b>RESUMED</b>\n<code>Reason:</code> {html_escape(reason)}\n🕐 {ts()}")

    def _log_session_summary(self):
        self._log("INFO", f"===== SESSION SUMMARY ({self.cfg.name}) =====")
        self._log("INFO", f"MODE: {'DRY RUN' if self.cfg.dry_run else 'LIVE'} | Instance: {self.instance_id}")
        self._log("INFO", f"PAIR {self.symbol} @ {self.cfg.entry.timeframe} | tradeSize={self.cfg.money.quote_budget:.2f}{self.quote}")
        self._log("INFO", f"ENTRY min_atr={self.cfg.entry.min_atr_pct}% min_score={self.cfg.entry.min_score} min_edge={self.cfg.entry.min_tp_edge_pct}%")
        self._log("INFO", f"COSTS fee={self._fee_pct():.3f}% slip={self._slip_pct():.3f}% buffer={self._safety_buffer_pct():.3f}%")

    def _idle_watchdog(self, regime, atr_pct, spread_pct, score, edge):
        now = time.time()
        if now - self.last_idle_diagnostic_ts < self.idle_diagnostics_interval: return
        if self.state.get("position"): return
        time_since_entry = now - float(self.state.get("last_entry_ts", 0))
        if time_since_entry < 600: return
        self.last_idle_diagnostic_ts = now
        constraints = []
        if atr_pct < self.cfg.entry.min_atr_pct: constraints.append(f"atr({atr_pct:.3f}%<{self.cfg.entry.min_atr_pct}%)")
        if spread_pct > self.cfg.entry.max_spread_pct: constraints.append(f"spread({spread_pct:.3f}%>{self.cfg.entry.max_spread_pct}%)")
        if score < self.cfg.entry.min_score: constraints.append(f"score({score:.2f}<{self.cfg.entry.min_score})")
        if edge < self.cfg.entry.min_tp_edge_pct: constraints.append(f"edge({edge:.3f}%<{self.cfg.entry.min_tp_edge_pct}%)")
        self._log("WARN", f"IDLE WATCHDOG: flat for {int(time_since_entry/60)}m | regime={regime} | blocking: {', '.join(constraints) or 'none'}")

    def _write_live_metrics(self, regime, strength, atr_pct, spread_pct, current_price):
        pos = self.state.get("position")
        unrealized_pnl = (current_price - float(pos["entry"])) * float(pos["qty"]) if pos else 0.0
        wins = sum(1 for p in self.recent_trades if p >= 0)
        metrics = {"ts": time.time(), "price": current_price, "spread_pct": spread_pct, "atr_pct": atr_pct, "regime": regime, "regime_strength": strength, "toxicity_score": self.risk_manager.last_toxicity.total, "position": {"qty": float(pos["qty"]), "entry": float(pos["entry"]), "unrealized_pnl": unrealized_pnl} if pos else None, "pnl_day": float(self.state.get("day_pnl_quote", 0)), "wins": wins, "losses": len(self.recent_trades)-wins, "trades_today": len(self.recent_trades), "paused": self.risk_manager.paused or self._manual_pause, "uptime": time.time() - self._start_time}
        metrics_path = os.path.join(os.path.dirname(self.cfg.paths.state_path), f"live_metrics_{self.instance_id}.json")
        try:
            with open(metrics_path + ".tmp", "w") as f: json.dump(metrics, f)
            os.replace(metrics_path + ".tmp", metrics_path)
        except: pass

    def run(self):
        self._log("INFO", "Bot running. Press Ctrl+C to stop.")
        self.tg.send(f"🚀 <b>Bot Started</b> {html_escape(self.cfg.name)}\n🕐 {ts()}")
        last_candle_ts = 0
        while self.running:
            try:
                self.tg.poll_commands()
                self._tick(last_candle_ts)
                last_candle_ts = int(self.state.get("_last_candle_ts", last_candle_ts))
            except KeyboardInterrupt:
                self._log("INFO", "Stopping (KeyboardInterrupt).")
                self._save_state()
                return
            except Exception as e:
                self._log("ERROR", f"Tick error: {repr(e)}")
                self.risk_manager.record_error()
                time.sleep(2.0)
        self._log("INFO", "Bot stopped.")
        self.tg.send(f"🛑 <b>Bot Stopped</b> {html_escape(self.cfg.name)}\n🕐 {ts()}")

    def _tick(self, last_candle_ts):
        o, h, l, c, v = self._fetch_ohlcv(limit=210)
        if not o: time.sleep(2.0); return
        if not self.cfg.dry_run:
            raw = self.ex.fetch_ohlcv(self.symbol, timeframe=self.cfg.entry.timeframe, limit=2)
            candle_open_ms = int(raw[-1][0])
        else: candle_open_ms = int(time.time() * 1000) // (60 * 1000) * (60 * 1000)
        ma7, ma25, ma99, a = sma(c, 7), sma(c, 25), sma(c, 99), atr(h, l, c, 14)
        if ma7 is None or ma25 is None or ma99 is None or a is None: self._log("INFO", "Waiting for warmup..."); time.sleep(1.0); return
        atr_pct = a / c[-1] * 100.0
        spread_pct = self._spread_pct()
        vol_r = self._vol_ratio(v, 20)
        current_price = c[-1]
        regime, strength = self._regime(o, h, l, c, v)
        self.risk_manager.update_baseline_atr(atr_pct)
        self.risk_manager.record_ma_cross(current_price, ma7)
        toxicity = self.risk_manager.assess_toxicity(spread_pct, atr_pct, self._slip_pct())
        should_pause, pause_reason = self.risk_manager.should_pause()
        if should_pause: self.risk_manager.pause(); self._notify_pause(pause_reason)
        should_resume, resume_reason = self.risk_manager.should_resume()
        if should_resume: self.risk_manager.resume(); self._notify_resume(resume_reason)
        if time.time() - self.last_heartbeat >= self.cfg.telegram.heartbeat_minutes * 60:
            self._notify_heartbeat(regime, strength, atr_pct, spread_pct)
            self.last_heartbeat = time.time()
        self._write_live_metrics(regime, strength, atr_pct, spread_pct, current_price)
        if candle_open_ms == last_candle_ts:
            self._manage_position(current_price=current_price)
            time.sleep(1.0); return
        self.state["_last_candle_ts"] = candle_open_ms
        self._save_state()
        self._update_adaptive_params()
        regime_params = self._get_regime_params(regime)
        if regime == "CHOP" and self.cfg.regime_detection.block_entries_in_chop:
            self._log("INFO", f"CHOP blocked. price={fmt_price(current_price)}")
            self._manage_position(current_price=current_price); return
        score, reasons, base_tp_edge = self._score_entry(regime, o[-1], h[-1], l[-1], c[-1], ma7, ma25, ma99, atr_pct, vol_r, spread_pct)
        adaptive_score = float(self.state.get("adaptive_score_adjust", 0.0))
        adaptive_edge = float(self.state.get("adaptive_edge_adjust", 0.0))
        wr_score_add, wr_edge_add, _ = self._get_winrate_adjustment()
        adjusted_score = score + regime_params.min_score_adjust + adaptive_score + wr_score_add
        adjusted_edge_threshold = self.cfg.entry.min_tp_edge_pct + regime_params.min_tp_edge_adjust + adaptive_edge + wr_edge_add
        viable = adjusted_score >= self.cfg.entry.min_score and base_tp_edge >= adjusted_edge_threshold
        self._log("INFO", f"price={fmt_price(current_price)} regime={regime}({strength:.2f}) score={score:.2f}→{adjusted_score:.2f} atr={atr_pct:.3f}% vR={vol_r:.2f} spread={spread_pct:.3f}% edge={base_tp_edge:.3f}≥{adjusted_edge_threshold:.3f} viable={viable} tox={toxicity.total:.0f}")
        self._manage_position(current_price=current_price)
        self._idle_watchdog(regime, atr_pct, spread_pct, adjusted_score, base_tp_edge)
        can, why = self._can_trade()
        if not can:
            if viable: self._paper_journal({"ts": ts(), "symbol": self.symbol, "regime": regime, "score": f"{adjusted_score:.2f}", "price": f"{current_price:.8f}", "blocked_reason": why, "reasons": ",".join(reasons)})
            return
        free_q = self._free_quote()
        if free_q < self.cfg.money.quote_budget * 0.98: self._log("WARN", f"Low {self.quote} balance ({free_q:.2f})."); return
        if not viable:
            self._paper_journal({"ts": ts(), "symbol": self.symbol, "regime": regime, "score": f"{adjusted_score:.2f}", "price": f"{current_price:.8f}", "blocked_reason": "score_or_edge", "reasons": ",".join(reasons)})
            return
        qty = self._calc_qty(price=current_price)
        if qty <= 0: self._log("WARN", "qty <= 0"); return
        entry_price = current_price
        sl_px = entry_price * (1.0 - regime_params.sl_pct / 100.0)
        tp_px = entry_price * (1.0 + regime_params.tp_pct / 100.0)
        try:
            order = self._place_buy(qty)
            filled_qty = safe_float(order.get("filled"), safe_float(order.get("amount"), qty))
            if not self.cfg.dry_run:
                try: filled_qty = float(self.ex.amount_to_precision(self.symbol, filled_qty))
                except: pass
            filled = safe_float(order.get("average"), entry_price) or entry_price
            self.state["position"] = {"qty": filled_qty, "entry": filled, "entry_ts": time.time(), "sl": sl_px, "tp": tp_px, "trail_active": False, "trail_sl": sl_px, "regime": regime, "regime_params": {"tp_pct": regime_params.tp_pct, "sl_pct": regime_params.sl_pct, "trailing": regime_params.trailing, "trail_activate_pct": regime_params.trail_activate_pct, "trail_step_pct": regime_params.trail_step_pct}}
            self.state["last_entry_ts"] = time.time()
            self._save_state()
            self._log("INFO", f"{'[DRY] ' if self.cfg.dry_run else ''}BUY filled qty={qty:.6f} entry={fmt_price(filled)} sl={fmt_price(sl_px)} tp={fmt_price(tp_px)} regime={regime}")
            self._notify_buy(price=filled, qty=qty, regime=regime, score=adjusted_score, atr_pct=atr_pct, spread_pct=spread_pct, sl_px=sl_px, tp_px=tp_px, dry_run=self.cfg.dry_run)
        except Exception as e: self._log("ERROR", f"BUY failed: {repr(e)}"); self.risk_manager.record_error()

    def _manage_position(self, current_price):
        pos = self.state.get("position")
        if not pos: return
        entry, qty, sl, tp = float(pos["entry"]), float(pos["qty"]), float(pos["sl"]), float(pos["tp"])
        trail_active, trail_sl = bool(pos.get("trail_active", False)), float(pos.get("trail_sl", sl))
        regime_params_dict = pos.get("regime_params", {})
        trailing_enabled = regime_params_dict.get("trailing", True)
        trail_activate_pct = regime_params_dict.get("trail_activate_pct", self.cfg.risk.trail_activate_pct)
        trail_step_pct = regime_params_dict.get("trail_step_pct", self.cfg.risk.trail_step_pct)
        if trailing_enabled:
            up_pct = pct(entry, current_price)
            if not trail_active and up_pct >= trail_activate_pct:
                trail_active = True
                trail_sl = max(trail_sl, entry * (1.0 + (trail_activate_pct - trail_step_pct) / 100.0))
            if trail_active:
                desired = current_price * (1.0 - trail_step_pct / 100.0)
                if desired > trail_sl: trail_sl = desired
        held_min = (time.time() - float(pos["entry_ts"])) / 60.0
        time_stop = held_min >= self.cfg.risk.max_hold_minutes
        hit_sl = current_price <= (trail_sl if trail_active else sl)
        hit_tp = current_price >= tp
        if hit_tp or hit_sl or time_stop:
            reason = "TP" if hit_tp else ("SL" if hit_sl else "TIME")
            self._close_position(reason, current_price, pos)
        else:
            pos["trail_active"], pos["trail_sl"] = trail_active, trail_sl
            self.state["position"] = pos
            self._save_state()

    def _close_position(self, reason, current_price, pos):
        entry, qty = float(pos["entry"]), float(pos["qty"])
        try:
            sell_qty = qty
            if not self.cfg.dry_run:
                bal = self.ex.fetch_balance()
                free_base = float(bal.get(self.base, {}).get("free", 0) or 0)
                sell_qty = min(qty, free_base * 0.995)
                try: sell_qty = float(self.ex.amount_to_precision(self.symbol, sell_qty))
                except: pass
                minq = self._min_qty()
                if minq and sell_qty < minq: self._log("WARN", f"SELL skipped: qty {sell_qty:.8f} < min {minq:.8f}"); return
            order = self._place_sell(sell_qty)
            exit_p = safe_float(order.get("average"), current_price) or current_price
        except Exception as e: self._log("ERROR", f"SELL failed: {repr(e)}"); self.risk_manager.record_error(); return
        gross = (exit_p - entry) * sell_qty
        fees = (entry * sell_qty + exit_p * sell_qty) * (self.cfg.money.fee_bps / 10000.0)
        pnl_q = gross - fees
        pnl_pct = (pnl_q / (entry * sell_qty)) * 100.0 if entry * sell_qty > 0 else 0.0
        self._log("INFO", f"{'[DRY] ' if self.cfg.dry_run else ''}SELL {reason} qty={sell_qty:.6f} entry={fmt_price(entry)} exit={fmt_price(exit_p)} pnl={pnl_q:+.4f}{self.quote} ({pnl_pct:+.2f}%)")
        self.trade_history.append(time.time())
        self.recent_trades.append(pnl_q)
        self.risk_manager.record_trade_result(pnl_q)
        self.state["day_pnl_quote"] = float(self.state.get("day_pnl_quote", 0.0)) + pnl_q
        self.state["consecutive_losses"] = int(self.state.get("consecutive_losses", 0)) + 1 if pnl_q < 0 else 0
        self.state["position"] = None
        self.state["cooldown_until"] = time.time() + self.cfg.risk.cooldown_after_close_s
        self.state["last_order_id"] = None
        self._save_state()
        self._journal({"ts": ts(), "symbol": self.symbol, "regime": pos.get("regime", "UNKNOWN"), "reason": reason, "qty": f"{sell_qty:.8f}", "entry": f"{entry:.8f}", "exit": f"{exit_p:.8f}", "gross_quote": f"{gross:.8f}", "fees_quote_est": f"{fees:.8f}", "pnl_quote": f"{pnl_q:.8f}", "pnl_pct": f"{pnl_pct:.4f}", "day_pnl_quote": f"{float(self.state.get('day_pnl_quote', 0.0)):.8f}"})
        self._notify_sell(reason=reason, entry=entry, exit_=exit_p, qty=sell_qty, pnl_q=pnl_q, pnl_pct=pnl_pct, fees=fees, dry_run=self.cfg.dry_run)

    def _force_close_position(self, reason):
        pos = self.state.get("position")
        if not pos: return
        if self.cfg.dry_run: current_price = 2.1
        else:
            ticker = self.ex.fetch_ticker(self.symbol)
            current_price = float(ticker.get("last", 0))
        self._close_position(reason, current_price, pos)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True, help="Path to config json")
    args = ap.parse_args()
    instance_id = get_instance_id(args.config)
    lock = InstanceLock(instance_id)
    if not lock.acquire():
        print(f"ERROR: Another instance running for {args.config}", file=sys.stderr)
        sys.exit(1)
    try:
        cfg = load_cfg(args.config)
        bot = V15Bot(cfg, instance_id=instance_id)
        def sig_handler(sig, frame): bot.running = False
        signal.signal(signal.SIGTERM, sig_handler)
        signal.signal(signal.SIGINT, sig_handler)
        bot.run()
    finally:
        lock.release()

if __name__ == "__main__":
    main()
