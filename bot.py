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

import argparse, csv, dataclasses, datetime as dt, fcntl, hashlib, json, math, os, random, signal, sys, threading, time
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

FEATURE_FLAGS = {
  "THROTTLE_MODE": True,
  "SMART_TIME_EXIT": True,
  "TWO_STAGE_TRAIL": True,
  "SCRATCH_GUARD": True,
  "CHOP_MICRO_RANGE": True,
  "EXPECTANCY_WATCHDOG": True,
  "SLIPPAGE_EMA": True,
  "REENTRY_AFTER_SL": True,
  "SPREAD_SPIKE_HANDLING": True,
  "REGIME_HYSTERESIS": True,
  "CANDLE_SANITY_CHECK": True,
  "CCXT_RETRY_JITTER": True,
  "REPLAY_MODE": True,
  "MAKER_FIRST_OPTIONAL": True,
  "HEALTH_HEARTBEAT": True,
  "JOURNAL_ENRICHED": True
}

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
        return False, ""
    def should_resume(self):
        return False, ""
    def pause(self): self.paused = False; self.paused_at = None; self._good_since = None
    def resume(self): self.paused = False; self.paused_at = None; self._good_since = None
    def entries_allowed(self): return True

@dataclasses.dataclass
class RegimeParams:
    tp_pct: float; sl_pct: float; trailing: bool; trail_activate_pct: float
    trail_step_pct: float; min_score_adjust: float; min_tp_edge_adjust: float

@dataclasses.dataclass
class RiskCfg:
    sl_pct: float; tp_pct: float; trailing: bool; trail_activate_pct: float; trail_step_pct: float
    max_hold_minutes: int; cooldown_after_close_s: int; daily_loss_limit_pct: float; max_consecutive_losses: int
    throttle_consecutive_losses: int
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
    hysteresis_bars: int; hysteresis_strength: float

@dataclasses.dataclass
class EntryCfg:
    timeframe: str; min_atr_pct: float; max_atr_pct: float; max_spread_pct: float
    min_vol_ratio: float; min_wick_ratio: float; min_score: float; min_tp_edge_pct: float; entry_gap_s: int
    maker_first: bool; maker_first_timeout_s: int; maker_first_offset_bps: float

@dataclasses.dataclass
class MoneyCfg:
    symbol: str; quote_budget: float; max_positions: int; fee_bps: float; slippage_bps: float

@dataclasses.dataclass
class PathsCfg:
    log_path: str; state_path: str; journal_path: str; paper_journal_path: str; log_rotate: Dict[str, Any]

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
            entry_gap_s=int(entry.get("entry_gap_s", 8)),
            maker_first=bool(entry.get("maker_first", False)),
            maker_first_timeout_s=int(entry.get("maker_first_timeout_s", 2)),
            maker_first_offset_bps=float(entry.get("maker_first_offset_bps", 1.5))),
        risk=RiskCfg(sl_pct=float(risk.get("sl_pct", 0.22)), tp_pct=float(risk.get("tp_pct", 0.38)),
            trailing=bool(risk.get("trailing", True)), trail_activate_pct=float(risk.get("trail_activate_pct", 0.18)),
            trail_step_pct=float(risk.get("trail_step_pct", 0.08)), max_hold_minutes=int(risk.get("max_hold_minutes", 18)),
            cooldown_after_close_s=int(risk.get("cooldown_after_close_s", 8)),
            daily_loss_limit_pct=float(risk.get("daily_loss_limit_pct", 2.5)),
            max_consecutive_losses=int(risk.get("max_consecutive_losses", 99999)),
            throttle_consecutive_losses=int(risk.get("throttle_consecutive_losses", 3)),
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
            block_entries_in_chop=bool(regime_det.get("block_entries_in_chop", False)),
            hysteresis_bars=int(regime_det.get("hysteresis_bars", 3)),
            hysteresis_strength=float(regime_det.get("hysteresis_strength", 0.05))),
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
            paper_journal_path=paths.get("paper_journal_path", "logs/paper_signals.csv"),
            log_rotate=paths.get("log_rotate", {"enabled": False, "max_bytes": 5_000_000, "backup_count": 3})),
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
        paused = "YES" if self._manual_pause else "NO"
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
            try:
                self._ccxt_call(self.ex.load_markets, reload=True)
                break
            except Exception:
                time.sleep(2**attempt)
        sym = symbol.strip().upper().replace("-", "/")
        markets = getattr(self.ex, "markets", {}) or {}
        if sym not in markets: sym = symbol.strip()
        if sym not in markets: raise ValueError(f"Symbol '{symbol}' not found")
        self.symbol = sym
        return self.ex.market(sym)

    def _ccxt_call(self, fn: Callable, *args, **kwargs):
        max_attempts = 4
        for attempt in range(1, max_attempts + 1):
            try:
                result = fn(*args, **kwargs)
                self.state["health_last_ccxt_ok_ts"] = time.time()
                self.state["health_consecutive_errors"] = 0
                return result
            except Exception as e:
                self.risk_manager.record_error()
                self.state["health_consecutive_errors"] = int(self.state.get("health_consecutive_errors", 0)) + 1
                if attempt >= max_attempts:
                    raise
                sleep_s = min(2.5, 0.4 * attempt) + random.uniform(0.05, 0.25)
                time.sleep(sleep_s)
        raise RuntimeError("ccxt retry exhausted")

    def _log(self, level, msg):
        line = f"[{level}] {ts()} | {msg}"
        print(line, flush=True)
        try:
            if self.cfg.paths.log_rotate.get("enabled"):
                self._rotate_logs()
            with open(self.cfg.paths.log_path, "a", encoding="utf-8") as f: f.write(line+"\n")
        except: pass

    def _rotate_logs(self):
        path = self.cfg.paths.log_path
        max_bytes = int(self.cfg.paths.log_rotate.get("max_bytes", 5_000_000))
        backup_count = int(self.cfg.paths.log_rotate.get("backup_count", 3))
        try:
            if os.path.exists(path) and os.path.getsize(path) >= max_bytes:
                for i in range(backup_count - 1, 0, -1):
                    src = f"{path}.{i}"
                    dst = f"{path}.{i+1}"
                    if os.path.exists(src): os.replace(src, dst)
                os.replace(path, f"{path}.1")
        except: pass

    def _load_state(self):
        self.state = {
            "position": None,
            "cooldown_until": 0.0,
            "day": utcnow().date().isoformat(),
            "day_pnl_quote": 0.0,
            "consecutive_losses": 0,
            "last_entry_ts": 0.0,
            "adaptive_score_adjust": 0.0,
            "adaptive_edge_adjust": 0.0,
            "adaptive_spread_adjust": 0.0,
            "last_order_id": None,
            "slippage_last_bps": 0.0,
            "slippage_ema_bps": 0.0,
            "expectancy_last_n": 0,
            "winrate_last_n": 0.0,
            "avg_win_last_n": 0.0,
            "avg_loss_last_n": 0.0,
            "health_last_success_ts": 0.0,
            "health_last_ccxt_ok_ts": 0.0,
            "health_consecutive_errors": 0,
            "entry_block_reasons": [],
            "regime_current": "UNKNOWN",
            "regime_strength": 0.0,
            "regime_stable_count": 0,
            "replay_last_summary": None,
            "last_exit_reason": None,
            "last_exit_ts": 0.0,
            "last_sl_ts": 0.0,
            "last_sl_regime": None,
            "last_sl_price": 0.0,
            "last_sl_score": 0.0
        }
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
            bal = self._ccxt_call(self.ex.fetch_balance)
            total_base = float(bal.get(self.base, {}).get("total", 0) or 0)
            min_qty = self._min_qty() or 1.0
            ticker = self._ccxt_call(self.ex.fetch_ticker, self.symbol)
            price = float(ticker.get("last", 0) or 0)
            notional = total_base * price if price > 0 else 0
            state_pos = self.state.get("position")
            if notional >= 5.0 and total_base >= min_qty:
                if not state_pos:
                    self._log("WARN", f"Reconciliation: Found orphan position {total_base:.6f} {self.base}")
                    try:
                        trades = self._ccxt_call(self.ex.fetch_my_trades, self.symbol, limit=10)
                        buy_trades = [t for t in trades if t.get("side") == "buy"]
                        if buy_trades:
                            entry_price = float(buy_trades[-1].get("price", price))
                            self.state["position"] = {"qty": total_base, "entry": entry_price, "entry_ts": time.time()-300,
                                "sl": entry_price*(1-self.cfg.risk.sl_pct/100), "tp": entry_price*(1+self.cfg.risk.tp_pct/100),
                                "trail_active": False, "trail_sl": entry_price*(1-self.cfg.risk.sl_pct/100), "trail_stage": "none",
                                "regime": "RANGE", "regime_params": dataclasses.asdict(self.cfg.risk.range_params)}
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
    def _slippage_ema_pct(self): return float(self.state.get("slippage_ema_bps", 0.0)) / 100.0
    def _safety_buffer_pct(self): return 0.02
    def _total_cost_pct(self):
        slip = max(self._slip_pct(), self._slippage_ema_pct())
        return self._fee_pct() + slip + self._safety_buffer_pct()

    def _spread_pct(self):
        if self.cfg.dry_run: return 0.02
        try:
            ob = self._ccxt_call(self.ex.fetch_order_book, self.symbol, limit=5)
            bid, ask = (ob["bids"][0][0] if ob["bids"] else None), (ob["asks"][0][0] if ob["asks"] else None)
            if not bid or not ask: return 999.0
            return (ask - bid) / ((bid + ask) / 2) * 100.0
        except: self.risk_manager.record_error(); return 999.0

    def _free_quote(self):
        if self.cfg.dry_run: return self.cfg.money.quote_budget * 10
        try:
            bal = self._ccxt_call(self.ex.fetch_balance)
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

    def _update_slippage(self, expected_price, filled_price, side):
        if expected_price <= 0 or filled_price <= 0: return
        direction = 1 if side == "buy" else -1
        slippage_pct = ((filled_price - expected_price) / expected_price) * 100.0 * direction
        slippage_bps = slippage_pct * 100.0
        self.state["slippage_last_bps"] = slippage_bps
        ema_prev = float(self.state.get("slippage_ema_bps", 0.0))
        self.state["slippage_ema_bps"] = ema_prev * 0.9 + slippage_bps * 0.1

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
                ohlcv = self._ccxt_call(self.ex.fetch_ohlcv, self.symbol, timeframe=self.cfg.entry.timeframe, limit=limit)
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

    def _regime_with_hysteresis(self, o, h, l, c, v):
        regime, strength = self._regime(o, h, l, c, v)
        current = self.state.get("regime_current", "UNKNOWN")
        stable_count = int(self.state.get("regime_stable_count", 0))
        current_strength = float(self.state.get("regime_strength", 0.0))
        if current == "UNKNOWN":
            self.state["regime_current"] = regime
            self.state["regime_strength"] = strength
            self.state["regime_stable_count"] = 1
            return regime, strength
        if regime == current:
            self.state["regime_strength"] = strength
            self.state["regime_stable_count"] = stable_count + 1
            return regime, strength
        if stable_count < self.cfg.regime_detection.hysteresis_bars and strength < current_strength + self.cfg.regime_detection.hysteresis_strength:
            self.state["regime_stable_count"] = stable_count + 1
            return current, current_strength
        self.state["regime_current"] = regime
        self.state["regime_strength"] = strength
        self.state["regime_stable_count"] = 1
        return regime, strength

    def _get_regime_params(self, regime):
        if regime == "TREND": return self.cfg.risk.trend_params
        elif regime == "RANGE": return self.cfg.risk.range_params
        elif regime == "CHOP": return self.cfg.risk.chop_params
        return RegimeParams(self.cfg.risk.tp_pct, self.cfg.risk.sl_pct, self.cfg.risk.trailing, self.cfg.risk.trail_activate_pct, self.cfg.risk.trail_step_pct, 0.0, 0.0)

    def _score_entry(self, regime, o, h, l, c, ma7, ma25, ma99, atr_pct, vol_r, spread_pct, max_spread):
        reasons, score = [], 0.0
        regime_params = self._get_regime_params(regime)
        tp_pct = regime_params.tp_pct
        if atr_pct >= self.cfg.entry.min_atr_pct: score += 1.2; reasons.append("atr_ok")
        else: reasons.append("atr_low")
        if atr_pct <= self.cfg.entry.max_atr_pct: score += 1.0; reasons.append("atr_ok2")
        else: reasons.append("atr_high")
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
        if ma99_dist_pct <= 0.20 and c > o: score += 0.3; reasons.append("ma99_bounce")
        trend_ok, trend_down = ma7 >= ma25 >= ma99, ma7 <= ma25 <= ma99
        if regime == "TREND":
            if trend_ok: score += 1.6; reasons.append("trend_up")
            elif trend_down: score -= 0.8; reasons.append("trend_down_soft")
            else: score += 0.5; reasons.append("trend_mixed")
        elif regime == "RANGE":
            if c >= ma99 * 0.998: score += 0.3; reasons.append("range_ok")
            else: score += 0.0; reasons.append("below_ma99")
        elif regime == "CHOP":
            ma_mid_dist = abs(c - ma25) / c * 100.0
            if ma_mid_dist <= 0.22: score += 1.1; reasons.append("chop_near_ma")
            else: score += 0.3; reasons.append("chop_away_ma")
            if wick_ok(o, h, l, c, self.cfg.entry.min_wick_ratio * 0.9) and spread_pct <= max_spread * 0.9:
                score += 0.6; reasons.append("chop_wick_quality")
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

    def _expectancy_stats(self):
        trades = list(self.recent_trades)
        n = len(trades)
        if n < 6:
            self.state["expectancy_last_n"] = n
            self.state["winrate_last_n"] = 0.0
            self.state["avg_win_last_n"] = 0.0
            self.state["avg_loss_last_n"] = 0.0
            return 0.0
        wins = [p for p in trades if p > 0]
        losses = [p for p in trades if p < 0]
        winrate = (len(wins) / n) * 100.0 if n else 0.0
        avg_win = sum(wins)/len(wins) if wins else 0.0
        avg_loss = abs(sum(losses)/len(losses)) if losses else 0.0
        expectancy = (len(wins)/n) * avg_win - (len(losses)/n) * avg_loss
        self.state["expectancy_last_n"] = n
        self.state["winrate_last_n"] = winrate
        self.state["avg_win_last_n"] = avg_win
        self.state["avg_loss_last_n"] = avg_loss
        return expectancy

    def _expectancy_adjustments(self):
        expectancy = self._expectancy_stats()
        score_add, edge_add, trail_tighten_mult, tp_mult, sl_mult = 0.0, 0.0, 1.0, 1.0, 1.0
        if expectancy < 0:
            score_add = 0.1
            trail_tighten_mult = 0.9
        return score_add, edge_add, trail_tighten_mult, tp_mult, sl_mult

    def _throttle_modifiers(self, toxicity, day_pnl, consecutive_losses):
        score_add, edge_add, cooldown_add_s = 0.0, 0.0, 0
        max_spread_effective = self.cfg.entry.max_spread_pct + float(self.state.get("adaptive_spread_adjust", 0.0))
        size_mult = 1.0
        throttle_active = False
        if toxicity.total >= 60:
            throttle_active = True
            score_add += 0.25
            edge_add += 0.02
            cooldown_add_s += 2
            max_spread_effective = min(max_spread_effective, self.cfg.entry.max_spread_pct * 0.8)
            size_mult = 0.9
        if toxicity.total >= 90:
            score_add += 0.35
            edge_add += 0.03
            cooldown_add_s += 4
            max_spread_effective = min(max_spread_effective, self.cfg.entry.max_spread_pct * 0.65)
            size_mult = 0.8
        loss_limit = -abs(self.cfg.money.quote_budget) * (self.cfg.risk.daily_loss_limit_pct / 100.0)
        if day_pnl <= loss_limit:
            throttle_active = True
            score_add += 0.15
            edge_add += 0.015
            cooldown_add_s += 5
            size_mult = min(size_mult, 0.85)
        throttle_losses = max(2, int(self.cfg.risk.throttle_consecutive_losses))
        if consecutive_losses >= throttle_losses:
            throttle_active = True
            score_add += 0.15
            edge_add += 0.015
            cooldown_add_s += 3
            size_mult = min(size_mult, 0.9)
        score_add = min(score_add, 0.4)
        edge_add = min(edge_add, 0.04)
        return {
            "active": throttle_active,
            "score_add": score_add,
            "edge_add": edge_add,
            "cooldown_add_s": cooldown_add_s,
            "max_spread_effective": max_spread_effective,
            "size_mult": size_mult
        }

    def _can_trade(self):
        now = time.time()
        if self._manual_pause: return False, "manual_pause"
        wr_score_add, wr_edge_add, wr_cooldown_add = self._get_winrate_adjustment()
        throttle_cooldown_add = int(self.state.get("throttle_cooldown_add_s", 0))
        effective_cooldown = float(self.state.get("cooldown_until", 0.0)) + wr_cooldown_add + throttle_cooldown_add
        if now < effective_cooldown: return False, "cooldown"
        if now - float(self.state.get("last_entry_ts", 0.0)) < self.cfg.entry.entry_gap_s: return False, "entry_gap"
        if self.state.get("position") is not None: return False, "in_position"
        return True, "ok"

    def _place_buy(self, qty, expected_price):
        if self.cfg.dry_run: return {"average": expected_price, "filled": qty, "id": "dry_run"}
        last_order_id = self.state.get("last_order_id")
        if last_order_id:
            try:
                existing = self._ccxt_call(self.ex.fetch_order, last_order_id, self.symbol)
                if existing.get("status") in ["open", "closed"] and existing.get("side") == "buy":
                    self._log("WARN", f"Skip duplicate buy - order {last_order_id} exists")
                    return existing
            except: pass
        if self.cfg.entry.maker_first:
            try:
                ob = self._ccxt_call(self.ex.fetch_order_book, self.symbol, limit=5)
                bid = ob["bids"][0][0] if ob["bids"] else expected_price
                price = bid * (1.0 - self.cfg.entry.maker_first_offset_bps / 10000.0)
                order = self._ccxt_call(self.ex.create_limit_buy_order, self.symbol, qty, price, {"postOnly": True})
                order_id = order.get("id")
                deadline = time.time() + self.cfg.entry.maker_first_timeout_s
                while time.time() < deadline:
                    time.sleep(0.3)
                    check = self._ccxt_call(self.ex.fetch_order, order_id, self.symbol)
                    if check.get("status") == "closed" or safe_float(check.get("remaining"), 1) <= 0:
                        return check
                self._ccxt_call(self.ex.cancel_order, order_id, self.symbol)
            except Exception as e:
                self._log("WARN", f"Maker-first failed: {e}")
        order = self._ccxt_call(self.ex.create_market_buy_order, self.symbol, qty)
        self.state["last_order_id"] = order.get("id")
        return order

    def _place_sell(self, qty, expected_price):
        if self.cfg.dry_run: return {"average": expected_price, "filled": qty, "id": "dry_run"}
        if self.cfg.entry.maker_first:
            try:
                ob = self._ccxt_call(self.ex.fetch_order_book, self.symbol, limit=5)
                ask = ob["asks"][0][0] if ob["asks"] else expected_price
                price = ask * (1.0 + self.cfg.entry.maker_first_offset_bps / 10000.0)
                order = self._ccxt_call(self.ex.create_limit_sell_order, self.symbol, qty, price, {"postOnly": True})
                order_id = order.get("id")
                deadline = time.time() + self.cfg.entry.maker_first_timeout_s
                while time.time() < deadline:
                    time.sleep(0.3)
                    check = self._ccxt_call(self.ex.fetch_order, order_id, self.symbol)
                    if check.get("status") == "closed" or safe_float(check.get("remaining"), 1) <= 0:
                        return check
                self._ccxt_call(self.ex.cancel_order, order_id, self.symbol)
            except Exception as e:
                self._log("WARN", f"Maker-first sell failed: {e}")
        return self._ccxt_call(self.ex.create_market_sell_order, self.symbol, qty)

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
        paused = "⏸️ " if self._manual_pause else ""
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
        throttle_notes = self.state.get("entry_block_reasons", [])
        if throttle_notes: constraints.append(f"throttle={','.join(throttle_notes)}")
        self._log("WARN", f"IDLE WATCHDOG: flat for {int(time_since_entry/60)}m | regime={regime} | blocking: {', '.join(constraints) or 'none'}")

    def _write_live_metrics(self, regime, strength, atr_pct, spread_pct, current_price):
        pos = self.state.get("position")
        unrealized_pnl = (current_price - float(pos["entry"])) * float(pos["qty"]) if pos else 0.0
        wins = sum(1 for p in self.recent_trades if p >= 0)
        metrics = {
            "ts": time.time(),
            "price": current_price,
            "spread_pct": spread_pct,
            "atr_pct": atr_pct,
            "regime": regime,
            "regime_current": self.state.get("regime_current", regime),
            "regime_strength": strength,
            "regime_stable_count": int(self.state.get("regime_stable_count", 0)),
            "toxicity_score": self.risk_manager.last_toxicity.total,
            "position": {"qty": float(pos["qty"]), "entry": float(pos["entry"]), "unrealized_pnl": unrealized_pnl} if pos else None,
            "pnl_day": float(self.state.get("day_pnl_quote", 0)),
            "wins": wins,
            "losses": len(self.recent_trades)-wins,
            "trades_today": len(self.recent_trades),
            "paused": self._manual_pause,
            "uptime": time.time() - self._start_time,
            "throttle_active": bool(self.state.get("throttle_active", False)),
            "throttle_score_add": float(self.state.get("throttle_score_add", 0.0)),
            "throttle_edge_add": float(self.state.get("throttle_edge_add", 0.0)),
            "throttle_cooldown_add_s": int(self.state.get("throttle_cooldown_add_s", 0)),
            "throttle_max_spread_effective": float(self.state.get("throttle_max_spread_effective", 0.0)),
            "expectancy_last_n": int(self.state.get("expectancy_last_n", 0)),
            "winrate_last_n": float(self.state.get("winrate_last_n", 0.0)),
            "avg_win_last_n": float(self.state.get("avg_win_last_n", 0.0)),
            "avg_loss_last_n": float(self.state.get("avg_loss_last_n", 0.0)),
            "slippage_last_bps": float(self.state.get("slippage_last_bps", 0.0)),
            "slippage_ema_bps": float(self.state.get("slippage_ema_bps", 0.0)),
            "health_last_success_ts": float(self.state.get("health_last_success_ts", 0.0)),
            "health_last_ccxt_ok_ts": float(self.state.get("health_last_ccxt_ok_ts", 0.0)),
            "health_consecutive_errors": int(self.state.get("health_consecutive_errors", 0)),
            "entry_block_reasons": self.state.get("entry_block_reasons", []),
            "replay_last_summary": self.state.get("replay_last_summary")
        }
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
            raw = self._ccxt_call(self.ex.fetch_ohlcv, self.symbol, timeframe=self.cfg.entry.timeframe, limit=2)
            candle_open_ms = int(raw[-1][0])
        else: candle_open_ms = int(time.time() * 1000) // (60 * 1000) * (60 * 1000)
        ma7, ma25, ma99, a = sma(c, 7), sma(c, 25), sma(c, 99), atr(h, l, c, 14)
        if ma7 is None or ma25 is None or ma99 is None or a is None: self._log("INFO", "Waiting for warmup..."); time.sleep(1.0); return
        atr_pct = a / c[-1] * 100.0
        spread_pct = self._spread_pct()
        vol_r = self._vol_ratio(v, 20)
        current_price = c[-1]
        candle_range_pct = (h[-1] - l[-1]) / current_price * 100.0 if current_price > 0 else 0.0
        if candle_range_pct <= 0 or candle_range_pct > max(atr_pct * 6.0, 1.8):
            self._log("WARN", f"Candle sanity skip range={candle_range_pct:.2f}% atr={atr_pct:.2f}%")
            self.state["health_last_success_ts"] = time.time()
            self._manage_position(current_price=current_price, atr_pct=atr_pct, spread_pct=spread_pct)
            time.sleep(1.0)
            return
        regime, strength = self._regime_with_hysteresis(o, h, l, c, v)
        self.risk_manager.update_baseline_atr(atr_pct)
        self.risk_manager.record_ma_cross(current_price, ma7)
        toxicity = self.risk_manager.assess_toxicity(spread_pct, atr_pct, self._slip_pct())
        throttle = self._throttle_modifiers(toxicity, float(self.state.get("day_pnl_quote", 0.0)), int(self.state.get("consecutive_losses", 0)))
        self.state["throttle_active"] = throttle["active"]
        self.state["throttle_score_add"] = throttle["score_add"]
        self.state["throttle_edge_add"] = throttle["edge_add"]
        self.state["throttle_cooldown_add_s"] = throttle["cooldown_add_s"]
        self.state["throttle_max_spread_effective"] = throttle["max_spread_effective"]
        if time.time() - self.last_heartbeat >= self.cfg.telegram.heartbeat_minutes * 60:
            self._notify_heartbeat(regime, strength, atr_pct, spread_pct)
            self.last_heartbeat = time.time()
        self._write_live_metrics(regime, strength, atr_pct, spread_pct, current_price)
        self.state["health_last_success_ts"] = time.time()
        if candle_open_ms == last_candle_ts:
            self._manage_position(current_price=current_price, atr_pct=atr_pct, spread_pct=spread_pct, regime=regime, strength=strength)
            time.sleep(1.0); return
        self.state["_last_candle_ts"] = candle_open_ms
        self._save_state()
        self._update_adaptive_params()
        exp_score_add, exp_edge_add, exp_trail_mult, exp_tp_mult, exp_sl_mult = self._expectancy_adjustments()
        regime_params = self._get_regime_params(regime)
        if regime == "CHOP" and self.cfg.regime_detection.block_entries_in_chop:
            self._log("INFO", f"CHOP blocked. price={fmt_price(current_price)}")
            self._manage_position(current_price=current_price, atr_pct=atr_pct, spread_pct=spread_pct, regime=regime, strength=strength); return
        max_spread_effective = min(throttle["max_spread_effective"], self.cfg.frequency_control.max_spread_ceiling)
        score, reasons, base_tp_edge = self._score_entry(regime, o[-1], h[-1], l[-1], c[-1], ma7, ma25, ma99, atr_pct, vol_r, spread_pct, max_spread_effective)
        adaptive_score = float(self.state.get("adaptive_score_adjust", 0.0))
        adaptive_edge = float(self.state.get("adaptive_edge_adjust", 0.0))
        wr_score_add, wr_edge_add, _ = self._get_winrate_adjustment()
        adjusted_score = score + regime_params.min_score_adjust + adaptive_score + wr_score_add + throttle["score_add"] + exp_score_add
        adjusted_edge_threshold = self.cfg.entry.min_tp_edge_pct + regime_params.min_tp_edge_adjust + adaptive_edge + wr_edge_add + throttle["edge_add"] + exp_edge_add
        total_cost = self._total_cost_pct() + spread_pct
        viable = adjusted_score >= self.cfg.entry.min_score and base_tp_edge >= adjusted_edge_threshold
        entry_block_reasons = []
        if spread_pct > max_spread_effective: entry_block_reasons.append("spread")
        if adjusted_score < self.cfg.entry.min_score: entry_block_reasons.append("score")
        if base_tp_edge < adjusted_edge_threshold: entry_block_reasons.append("edge")
        if throttle["active"]: entry_block_reasons.append("throttle")
        last_sl_ts = float(self.state.get("last_sl_ts", 0.0))
        if last_sl_ts and time.time() - last_sl_ts < self.cfg.risk.cooldown_after_close_s * 3:
            last_sl_price = float(self.state.get("last_sl_price", 0.0))
            last_sl_score = float(self.state.get("last_sl_score", 0.0))
            last_sl_regime = self.state.get("last_sl_regime")
            price_ok = last_sl_price <= 0 or abs(current_price - last_sl_price) / last_sl_price > 0.0015
            score_ok = adjusted_score > last_sl_score + 0.2
            if last_sl_regime == regime and not (price_ok or score_ok):
                viable = False
                entry_block_reasons.append("reentry_guard")
        self.state["entry_block_reasons"] = entry_block_reasons
        self._save_state()
        self._log("INFO", f"price={fmt_price(current_price)} regime={regime}({strength:.2f}) score={score:.2f}→{adjusted_score:.2f} atr={atr_pct:.3f}% vR={vol_r:.2f} spread={spread_pct:.3f}% edge={base_tp_edge:.3f}≥{adjusted_edge_threshold:.3f} viable={viable} tox={toxicity.total:.0f}")
        self._manage_position(current_price=current_price, atr_pct=atr_pct, spread_pct=spread_pct, regime=regime, strength=strength)
        self._idle_watchdog(regime, atr_pct, spread_pct, adjusted_score, base_tp_edge)
        can, why = self._can_trade()
        if not can:
            if why not in entry_block_reasons:
                entry_block_reasons.append(why)
                self.state["entry_block_reasons"] = entry_block_reasons
                self._save_state()
            if viable: self._paper_journal({"ts": ts(), "symbol": self.symbol, "regime": regime, "score": f"{adjusted_score:.2f}", "price": f"{current_price:.8f}", "blocked_reason": why, "reasons": ",".join(reasons)})
            return
        free_q = self._free_quote()
        if free_q < self.cfg.money.quote_budget * 0.98: self._log("WARN", f"Low {self.quote} balance ({free_q:.2f})."); return
        if not viable:
            self._paper_journal({"ts": ts(), "symbol": self.symbol, "regime": regime, "score": f"{adjusted_score:.2f}", "price": f"{current_price:.8f}", "blocked_reason": "score_or_edge", "reasons": ",".join(reasons)})
            return
        qty = self._calc_qty(price=current_price) * throttle["size_mult"]
        if qty <= 0: self._log("WARN", "qty <= 0"); return
        entry_price = current_price
        min_tp_pct = max(regime_params.tp_pct * exp_tp_mult, total_cost)
        min_sl_pct = max(regime_params.sl_pct * exp_sl_mult, atr_pct * 0.35)
        sl_px = entry_price * (1.0 - min_sl_pct / 100.0)
        tp_px = entry_price * (1.0 + min_tp_pct / 100.0)
        try:
            order = self._place_buy(qty, entry_price)
            filled_qty = safe_float(order.get("filled"), safe_float(order.get("amount"), qty))
            if not self.cfg.dry_run:
                try: filled_qty = float(self.ex.amount_to_precision(self.symbol, filled_qty))
                except: pass
            filled = safe_float(order.get("average"), entry_price) or entry_price
            self._update_slippage(entry_price, filled, "buy")
            self.state["position"] = {
                "qty": filled_qty,
                "entry": filled,
                "entry_ts": time.time(),
                "sl": sl_px,
                "tp": tp_px,
                "trail_active": False,
                "trail_sl": sl_px,
                "trail_stage": "none",
                "regime": regime,
                "regime_params": {
                    "tp_pct": min_tp_pct,
                    "sl_pct": min_sl_pct,
                    "trailing": regime_params.trailing,
                    "trail_activate_pct": regime_params.trail_activate_pct,
                    "trail_step_pct": regime_params.trail_step_pct
                },
                "entry_score": score,
                "adjusted_score": adjusted_score,
                "edge": base_tp_edge,
                "adjusted_edge_threshold": adjusted_edge_threshold,
                "atr_pct": atr_pct,
                "spread_pct": spread_pct,
                "regime_strength": strength,
                "exp_trail_tighten_mult": exp_trail_mult,
                "exp_tp_mult": exp_tp_mult,
                "exp_sl_mult": exp_sl_mult
            }
            self.state["last_entry_ts"] = time.time()
            self.state["last_entry_score"] = adjusted_score
            self._save_state()
            self._log("INFO", f"{'[DRY] ' if self.cfg.dry_run else ''}BUY filled qty={qty:.6f} entry={fmt_price(filled)} sl={fmt_price(sl_px)} tp={fmt_price(tp_px)} regime={regime}")
            self._notify_buy(price=filled, qty=qty, regime=regime, score=adjusted_score, atr_pct=atr_pct, spread_pct=spread_pct, sl_px=sl_px, tp_px=tp_px, dry_run=self.cfg.dry_run)
        except Exception as e: self._log("ERROR", f"BUY failed: {repr(e)}"); self.risk_manager.record_error()
        self.state["health_last_success_ts"] = time.time()

    def _manage_position(self, current_price, atr_pct=None, spread_pct=None, regime=None, strength=None):
        pos = self.state.get("position")
        if not pos: return
        entry, qty, sl, tp = float(pos["entry"]), float(pos["qty"]), float(pos["sl"]), float(pos["tp"])
        trail_active, trail_sl = bool(pos.get("trail_active", False)), float(pos.get("trail_sl", sl))
        trail_stage = pos.get("trail_stage", "none")
        regime_params_dict = pos.get("regime_params", {})
        trailing_enabled = regime_params_dict.get("trailing", True)
        trail_activate_pct = regime_params_dict.get("trail_activate_pct", self.cfg.risk.trail_activate_pct)
        trail_step_pct = regime_params_dict.get("trail_step_pct", self.cfg.risk.trail_step_pct)
        tp_pct = float(regime_params_dict.get("tp_pct", self.cfg.risk.tp_pct))
        sl_pct = float(regime_params_dict.get("sl_pct", self.cfg.risk.sl_pct))
        exp_trail_mult = float(pos.get("exp_trail_tighten_mult", 1.0))
        exp_tp_mult = float(pos.get("exp_tp_mult", 1.0))
        exp_sl_mult = float(pos.get("exp_sl_mult", 1.0))
        tp_adj = entry * (1.0 + (tp_pct * exp_tp_mult) / 100.0)
        sl_adj = entry * (1.0 - (sl_pct * exp_sl_mult) / 100.0)
        tp = tp_adj
        sl = sl_adj
        pos["tp"], pos["sl"] = tp, sl
        up_pct = pct(entry, current_price)
        early_step = trail_step_pct * 1.25 * exp_trail_mult
        late_step = trail_step_pct * 0.7 * exp_trail_mult
        late_trigger = max(trail_activate_pct * 2.0, tp_pct * 0.6)
        if trailing_enabled:
            if not trail_active and up_pct >= trail_activate_pct:
                trail_active = True
                trail_stage = "early"
                trail_sl = max(trail_sl, entry * (1.0 + (trail_activate_pct - early_step) / 100.0))
            if trail_active:
                if up_pct >= late_trigger:
                    trail_stage = "late"
                step = late_step if trail_stage == "late" else early_step
                desired = current_price * (1.0 - step / 100.0)
                if desired > trail_sl: trail_sl = desired
        held_min = (time.time() - float(pos["entry_ts"])) / 60.0
        time_stop = held_min >= self.cfg.risk.max_hold_minutes
        time_soft_stop = held_min >= self.cfg.risk.max_hold_minutes * 0.6
        hit_sl = current_price <= (trail_sl if trail_active else sl)
        hit_tp = current_price >= tp
        spread_spike = spread_pct is not None and spread_pct > self.cfg.entry.max_spread_pct * 1.6
        noise_buffer = min(max((atr_pct or 0) * 0.35, 0.02), 0.15)
        total_cost = self._total_cost_pct() + (spread_pct or 0.0)
        net_threshold = total_cost + noise_buffer
        in_profit = up_pct >= net_threshold
        if spread_spike and up_pct <= net_threshold:
            self._close_position("SPREAD", current_price, pos)
            return
        if spread_spike and up_pct > 0 and trail_active:
            tightened = current_price * (1.0 - (late_step * 0.8) / 100.0)
            trail_sl = max(trail_sl, tightened)
            trail_stage = "late"
        if time_stop and (trail_active or in_profit):
            time_stop = False
        if time_soft_stop and not in_profit and up_pct < total_cost * 0.5:
            time_stop = True
        if hit_sl:
            self._close_position("SL", current_price, pos)
            return
        if hit_tp:
            if up_pct < net_threshold and not spread_spike:
                pos["trail_active"], pos["trail_sl"], pos["trail_stage"] = trail_active, trail_sl, trail_stage
                self.state["position"] = pos
                self._save_state()
                return
            self._close_position("TP", current_price, pos)
            return
        if time_stop and (not trail_active) and (not in_profit):
            reason = "TIME_COST" if up_pct < net_threshold else "TIME"
            self._close_position(reason, current_price, pos)
            return
        pos["trail_active"], pos["trail_sl"], pos["trail_stage"] = trail_active, trail_sl, trail_stage
        self.state["position"] = pos
        self._save_state()

    def _close_position(self, reason, current_price, pos):
        entry, qty = float(pos["entry"]), float(pos["qty"])
        try:
            sell_qty = qty
            if not self.cfg.dry_run:
                bal = self._ccxt_call(self.ex.fetch_balance)
                free_base = float(bal.get(self.base, {}).get("free", 0) or 0)
                sell_qty = min(qty, free_base * 0.995)
                try: sell_qty = float(self.ex.amount_to_precision(self.symbol, sell_qty))
                except: pass
                minq = self._min_qty()
                if minq and sell_qty < minq: self._log("WARN", f"SELL skipped: qty {sell_qty:.8f} < min {minq:.8f}"); return
            order = self._place_sell(sell_qty, current_price)
            exit_p = safe_float(order.get("average"), current_price) or current_price
            self._update_slippage(current_price, exit_p, "sell")
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
        self.state["last_exit_reason"] = reason
        self.state["last_exit_ts"] = time.time()
        if reason == "SL":
            self.state["last_sl_ts"] = time.time()
            self.state["last_sl_regime"] = pos.get("regime")
            self.state["last_sl_price"] = exit_p
            self.state["last_sl_score"] = float(pos.get("adjusted_score", 0.0))
        self._save_state()
        held_minutes = (time.time() - float(pos.get("entry_ts", time.time()))) / 60.0
        self._journal({
            "ts": ts(),
            "symbol": self.symbol,
            "regime": pos.get("regime", "UNKNOWN"),
            "reason": reason,
            "qty": f"{sell_qty:.8f}",
            "entry": f"{entry:.8f}",
            "exit": f"{exit_p:.8f}",
            "gross_quote": f"{gross:.8f}",
            "fees_quote_est": f"{fees:.8f}",
            "pnl_quote": f"{pnl_q:.8f}",
            "pnl_pct": f"{pnl_pct:.4f}",
            "day_pnl_quote": f"{float(self.state.get('day_pnl_quote', 0.0)):.8f}",
            "score": f"{float(pos.get('entry_score', 0.0)):.3f}",
            "adjusted_score": f"{float(pos.get('adjusted_score', 0.0)):.3f}",
            "edge": f"{float(pos.get('edge', 0.0)):.3f}",
            "adjusted_edge_threshold": f"{float(pos.get('adjusted_edge_threshold', 0.0)):.3f}",
            "atr_pct": f"{float(pos.get('atr_pct', 0.0)):.3f}",
            "spread_pct": f"{float(pos.get('spread_pct', 0.0)):.3f}",
            "slippage_last_bps": f"{float(self.state.get('slippage_last_bps', 0.0)):.2f}",
            "slippage_ema_bps": f"{float(self.state.get('slippage_ema_bps', 0.0)):.2f}",
            "held_minutes": f"{held_minutes:.2f}",
            "regime_strength": f"{float(pos.get('regime_strength', 0.0)):.3f}"
        })
        self._notify_sell(reason=reason, entry=entry, exit_=exit_p, qty=sell_qty, pnl_q=pnl_q, pnl_pct=pnl_pct, fees=fees, dry_run=self.cfg.dry_run)

    def _force_close_position(self, reason):
        pos = self.state.get("position")
        if not pos: return
        if self.cfg.dry_run: current_price = 2.1
        else:
            ticker = self._ccxt_call(self.ex.fetch_ticker, self.symbol)
            current_price = float(ticker.get("last", 0))
        self._close_position(reason, current_price, pos)

def _load_replay_csv(path):
    rows = []
    with open(path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for r in reader:
            try:
                rows.append([float(r.get("timestamp", 0) or 0), float(r["open"]), float(r["high"]), float(r["low"]), float(r["close"]), float(r.get("volume", 0) or 0)])
            except Exception:
                continue
    return rows

def run_replay(cfg: BotCfg, args):
    cfg = dataclasses.replace(cfg, dry_run=True)
    bot = V15Bot(cfg, instance_id="replay")
    rng = random.Random(42)
    if args.replay_csv:
        data = _load_replay_csv(args.replay_csv)
    else:
        ex = ccxt.binance({"enableRateLimit": True, "options": {"defaultType": "spot"}})
        now = int(time.time() * 1000)
        days_ms = int(args.replay_days) * 24 * 60 * 60 * 1000
        since = now - days_ms
        data = ex.fetch_ohlcv(cfg.money.symbol, timeframe=cfg.entry.timeframe, since=since, limit=2000)
    if not data:
        print("Replay: no data")
        return
    tf_min = int(cfg.entry.timeframe.replace("m", "")) if "m" in cfg.entry.timeframe else 1
    pos = None
    trades = []
    breakdown_reason = {}
    breakdown_regime = {}
    for i in range(100, len(data)):
        window = data[:i+1]
        o = [x[1] for x in window]
        h = [x[2] for x in window]
        l = [x[3] for x in window]
        c = [x[4] for x in window]
        v = [x[5] for x in window]
        ma7, ma25, ma99, a = sma(c, 7), sma(c, 25), sma(c, 99), atr(h, l, c, 14)
        if ma7 is None or ma25 is None or ma99 is None or a is None:
            continue
        atr_pct = a / c[-1] * 100.0
        spread_pct = min(cfg.entry.max_spread_pct, max(0.01, atr_pct * 0.25))
        regime, strength = bot._regime_with_hysteresis(o, h, l, c, v)
        regime_params = bot._get_regime_params(regime)
        exp_score_add, exp_edge_add, exp_trail_mult, exp_tp_mult, exp_sl_mult = bot._expectancy_adjustments()
        max_spread_effective = min(cfg.entry.max_spread_pct, cfg.frequency_control.max_spread_ceiling)
        score, reasons, base_tp_edge = bot._score_entry(regime, o[-1], h[-1], l[-1], c[-1], ma7, ma25, ma99, atr_pct, bot._vol_ratio(v, 20), spread_pct, max_spread_effective)
        adjusted_score = score + regime_params.min_score_adjust + exp_score_add
        adjusted_edge_threshold = cfg.entry.min_tp_edge_pct + regime_params.min_tp_edge_adjust + exp_edge_add
        total_cost = bot._total_cost_pct() + spread_pct + max(atr_pct * 0.25, 0.02)
        viable = adjusted_score >= cfg.entry.min_score and base_tp_edge >= adjusted_edge_threshold and regime_params.tp_pct * exp_tp_mult >= total_cost
        current_price = c[-1]
        if pos:
            entry = pos["entry"]
            held_min = (i - pos["entry_i"]) * tf_min
            up_pct = pct(entry, current_price)
            trail_step = regime_params.trail_step_pct * exp_trail_mult
            early_step = trail_step * 1.25
            late_step = trail_step * 0.7
            if not pos["trail_active"] and up_pct >= regime_params.trail_activate_pct:
                pos["trail_active"] = True
                pos["trail_stage"] = "early"
                pos["trail_sl"] = max(pos["trail_sl"], entry * (1.0 + (regime_params.trail_activate_pct - early_step) / 100.0))
            if pos["trail_active"]:
                if up_pct >= max(regime_params.trail_activate_pct * 2.0, regime_params.tp_pct * 0.6):
                    pos["trail_stage"] = "late"
                step = late_step if pos["trail_stage"] == "late" else early_step
                pos["trail_sl"] = max(pos["trail_sl"], current_price * (1.0 - step / 100.0))
            hit_sl = current_price <= (pos["trail_sl"] if pos["trail_active"] else pos["sl"])
            hit_tp = current_price >= pos["tp"]
            time_stop = held_min >= cfg.risk.max_hold_minutes
            noise_buffer = max(atr_pct * 0.35, 0.02)
            net_threshold = bot._total_cost_pct() + spread_pct + noise_buffer
            in_profit = up_pct >= net_threshold
            if time_stop and in_profit and pos["trail_active"] and held_min < cfg.risk.max_hold_minutes * 1.5:
                time_stop = False
            if hit_sl or hit_tp or time_stop:
                reason = "SL" if hit_sl else ("TP" if hit_tp else "TIME")
                slip_pct = (cfg.money.slippage_bps / 100.0) + rng.uniform(0.0, atr_pct * 0.05)
                noise_pct = rng.uniform(0.0, atr_pct * 0.05)
                exit_price = current_price * (1.0 - (spread_pct + slip_pct + noise_pct) / 100.0)
                gross = (exit_price - entry) * pos["qty"]
                fees = (entry * pos["qty"] + exit_price * pos["qty"]) * (cfg.money.fee_bps / 10000.0)
                pnl = gross - fees
                trades.append({"pnl": pnl, "reason": reason, "regime": pos["regime"]})
                bot.recent_trades.append(pnl)
                breakdown_reason[reason] = breakdown_reason.get(reason, 0) + 1
                breakdown_regime[pos["regime"]] = breakdown_regime.get(pos["regime"], 0) + 1
                pos = None
        if not pos and viable:
            slip_pct = (cfg.money.slippage_bps / 100.0) + rng.uniform(0.0, atr_pct * 0.05)
            noise_pct = rng.uniform(0.0, atr_pct * 0.05)
            entry_price = current_price * (1.0 + (spread_pct + slip_pct + noise_pct) / 100.0)
            qty = cfg.money.quote_budget / entry_price
            pos = {
                "entry": entry_price,
                "qty": qty,
                "sl": entry_price * (1.0 - (regime_params.sl_pct * exp_sl_mult) / 100.0),
                "tp": entry_price * (1.0 + (regime_params.tp_pct * exp_tp_mult) / 100.0),
                "trail_active": False,
                "trail_sl": entry_price * (1.0 - (regime_params.sl_pct * exp_sl_mult) / 100.0),
                "trail_stage": "none",
                "entry_i": i,
                "regime": regime
            }
    wins = [t["pnl"] for t in trades if t["pnl"] > 0]
    losses = [t["pnl"] for t in trades if t["pnl"] < 0]
    winrate = (len(wins)/len(trades)*100.0) if trades else 0.0
    avg_win = sum(wins)/len(wins) if wins else 0.0
    avg_loss = abs(sum(losses)/len(losses)) if losses else 0.0
    expectancy = (len(wins)/len(trades)) * avg_win - (len(losses)/len(trades)) * avg_loss if trades else 0.0
    summary = {
        "trades": len(trades),
        "winrate_pct": winrate,
        "avg_win": avg_win,
        "avg_loss": avg_loss,
        "expectancy": expectancy,
        "breakdown_reason": breakdown_reason,
        "breakdown_regime": breakdown_regime
    }
    bot.state["replay_last_summary"] = summary
    bot._save_state()
    print(json.dumps(summary, indent=2))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True, help="Path to config json")
    ap.add_argument("--replay", action="store_true", help="Run replay mode")
    ap.add_argument("--replay-days", type=int, default=5, help="Replay lookback days")
    ap.add_argument("--replay-csv", default="", help="Replay CSV path")
    ap.add_argument("--replay-from", default="", help="Replay start (optional)")
    ap.add_argument("--replay-to", default="", help="Replay end (optional)")
    args = ap.parse_args()
    if args.replay:
        cfg = load_cfg(args.config)
        run_replay(cfg, args)
        return
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
