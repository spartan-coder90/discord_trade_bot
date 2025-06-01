# Part 1: Imports, Config, Logging, and Database Setup
import json
import re
import random
from datetime import datetime, timedelta, timezone, date
from alpaca_trade_api import REST
import requests
import threading
import time
from queue import Queue
from threading import Thread
import sqlite3
import os
import pandas as pd
import numpy as np 

# ------------------------------------------------------------------
# 1. LOAD CONFIG
# ------------------------------------------------------------------
def load_config(file_path):
    """Load configuration from a JSON file."""
    with open(file_path, "r") as file:
        return json.load(file)

config = load_config("config.json")

# Extract settings from config
DISCORD_USER_TOKEN      = config["discord"]["user_token"]
DISCORD_CHANNEL_ID      = config["discord"]["channel_id"]
ALPACA_API_KEY          = config["alpaca"]["api_key"]
ALPACA_API_SECRET       = config["alpaca"]["api_secret"]
ALPACA_BASE_URL         = config["alpaca"]["base_url"]

# Strategy toggles
STRATEGY_MODE           = config.get("strategy", {}).get("mode", "none")

# Bot settings
daily_kitty             = config["settings"]["daily_kitty"]
max_trades             = config["settings"]["max_trades"]
MAX_ALLOCATION_PER_TRADE = config["settings"]["max_allocation_per_trade"]
POLL_INTERVAL          = config["settings"]["poll_interval"]
PROFIT_MARGIN          = config["settings"]["profit_margin"]
STOP_LOSS             = config["settings"]["stop_loss"]
PRE_CLOSE_MINUTES      = config["settings"]["pre_close_minutes"]
DEBUG_LOGGING          = config["settings"].get("debug_logging", False)
RECENT_ALERT_MINUTES   = config["settings"]["recent_alert_minutes"]
DISCORD_MSG_LIMIT      = config["settings"]["discord_messages_limit"]
MONITOR_INTERVAL       = config["settings"]["monitor_interval"]
TRAIL_BY              = config["settings"]["trail_by"]
LIMIT_ORDER_DISCOUNT   = config["settings"]["limit_order_discount"]
LIMIT_ORDER_TIMEOUT    = config["settings"]["limit_order_timeout"]

# Risk config
risk_config            = config.get("risk", {})
MAX_PROFIT_PCT         = risk_config.get("max_profit_pct", 0.25)
MAX_LOSS_PCT          = risk_config.get("max_loss_pct", 0.20)

# DB config
DB_PATH               = config["database"]["path"]
DAILY_REPORT_PATH     = config["database"]["daily_report_path"]

# Alpaca API client
alpaca                = REST(ALPACA_API_KEY, ALPACA_API_SECRET, ALPACA_BASE_URL)

# Global variables
active_trades         = {}
completed_trades      = []
trade_lock           = threading.Lock()
alert_queue          = Queue()
symbol_monitors      = {}  # Track symbol monitoring threads

# Store the initial daily kitty
initial_daily_kitty  = daily_kitty

# ------------------------------------------------------------------
# 2. LOGGING
# ------------------------------------------------------------------
def log_message(message):
    """Log messages for debugging and tracking."""
    date_str = datetime.utcnow().strftime('%Y-%m-%d')
    log_dir = "logs"
    os.makedirs(log_dir, exist_ok=True)
    log_file_path = os.path.join(log_dir, f"trade_bot_{date_str}.log")
    
    with open(log_file_path, "a") as log_file:
        timestamp = datetime.utcnow()
        log_file.write(f"{timestamp} - {message}\n")
    print(f"{timestamp} - {message}")

def debug_log(message):
    """Log debug messages if DEBUG_LOGGING is enabled."""
    if DEBUG_LOGGING:
        log_message(f"DEBUG: {message}")

# ------------------------------------------------------------------
# 3. DATABASE INITIALIZATION
# ------------------------------------------------------------------

def init_db():
    """Initialize database with proper schema."""
    try:
        os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
        conn = sqlite3.connect(DB_PATH)
        c = conn.cursor()
        
        # Check if trades table exists
        c.execute("""SELECT name FROM sqlite_master 
                    WHERE type='table' AND name='trades'""")
        
        if c.fetchone() is None:
            # Create new table with all columns
            c.execute('''CREATE TABLE trades
                     (trade_id TEXT PRIMARY KEY,
                      symbol TEXT,
                      trade_number INTEGER,
                      strike_price REAL, 
                      expiration_date TEXT,
                      option_type TEXT,
                      quantity INTEGER,
                      entry_price REAL,
                      exit_price REAL,
                      profit_loss REAL,
                      profit_loss_pct REAL,
                      entry_time TIMESTAMP,
                      exit_time TIMESTAMP,
                      trade_status TEXT,
                      trade_date DATE,
                      UNIQUE(symbol, trade_number, trade_date))''')
        else:
            # Check if trade_number column exists
            c.execute("PRAGMA table_info(trades)")
            columns = [col[1] for col in c.fetchall()]
            
            if 'trade_number' not in columns:
                # Add trade_number column if it doesn't exist
                c.execute("""ALTER TABLE trades 
                           ADD COLUMN trade_number INTEGER DEFAULT 1""")
                
                # Update existing records
                c.execute("""UPDATE trades 
                           SET trade_number = 1 
                           WHERE trade_number IS NULL""")
                           
                # Add unique constraint
                c.execute("""CREATE UNIQUE INDEX IF NOT EXISTS 
                           idx_unique_trade 
                           ON trades(symbol, trade_number, trade_date)""")
        
        conn.commit()
    except Exception as e:
        log_message(f"Database initialization error: {e}")
        raise
    finally:
        conn.close()

def get_db_connection():
    """Get SQLite connection with row factory."""
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def get_trade_number(symbol, trade_date):
    """Get the next trade number for a symbol on a given date."""
    conn = get_db_connection()
    c = conn.cursor()
    c.execute("""
        SELECT COALESCE(MAX(trade_number), 0) + 1
        FROM trades 
        WHERE symbol = ? AND trade_date = ?
    """, (symbol, trade_date))
    next_num = c.fetchone()[0]
    conn.close()
    return next_num

def get_trade_id(trade_data):
    """Generate unique trade ID including trade number."""
    trade_date = date.today()
    trade_num = get_trade_number(trade_data['symbol'], trade_date)
    return f"{trade_data['symbol']}_{trade_date}_{trade_num}"

def update_trade_exit(trade_id, exit_price, profit_loss, profit_loss_pct):
    """Update trade record with exit information."""
    conn = get_db_connection()
    c = conn.cursor()
    try:
        c.execute("""UPDATE trades 
                     SET exit_price = ?,
                         exit_time = datetime('now'),
                         profit_loss = ?,
                         profit_loss_pct = ?,
                         trade_status = 'CLOSED'
                     WHERE trade_id = ?""",
                     (exit_price, profit_loss, profit_loss_pct, trade_id))
        conn.commit()
    finally:
        conn.close()

def get_active_trades():
    """Get all active trades from database."""
    conn = get_db_connection()
    c = conn.cursor()
    c.execute("SELECT * FROM trades WHERE trade_status = 'OPEN'")
    trades = [dict(row) for row in c.fetchall()]
    conn.close()
    return trades

# Part 2: Market Data and Order Handling Functions

# ------------------------------------------------------------------
# 1. MARKET DATA FUNCTIONS
# ------------------------------------------------------------------
def get_option_quote(option_symbol):
    """
    Enhanced quote fetching with retries and validation.
    """
    max_retries = 3
    retry_delay = 1  # seconds
    
    for attempt in range(max_retries):
        try:
            url = "https://data.alpaca.markets/v1beta1/options/snapshots"
            params = {"symbols": option_symbol}
            headers = {
                "APCA-API-KEY-ID": ALPACA_API_KEY,
                "APCA-API-SECRET-KEY": ALPACA_API_SECRET,
            }
            r = requests.get(url, params=params, headers=headers)
            r.raise_for_status()
            data = r.json().get("snapshots", {}).get(option_symbol, {})
            
            if not data or "latestQuote" not in data:
                if attempt < max_retries - 1:
                    time.sleep(retry_delay)
                    continue
                return (None, None)
            
            quote = data["latestQuote"]
            bid = float(quote.get("bp", 0) or 0)
            ask = float(quote.get("ap", 0) or 0)
            last = float(data.get("latestTrade", {}).get("p", 0) or 0)
            
            # Validate quote data
            if bid <= 0 and ask <= 0 and last <= 0:
                if attempt < max_retries - 1:
                    time.sleep(retry_delay)
                    continue
                return (None, None)
                
            # If bid/ask is missing but we have last price, use it to construct spread
            if bid <= 0 and ask <= 0 and last > 0:
                bid = last * 0.98  # Estimated bid 2% below last
                ask = last * 1.02  # Estimated ask 2% above last
            # If only one side is missing, estimate it from the other
            elif bid <= 0 and ask > 0:
                bid = ask * 0.98
            elif ask <= 0 and bid > 0:
                ask = bid * 1.02
                
            return (bid, ask)
            
        except Exception as e:
            log_message(f"Error fetching quote (attempt {attempt+1}): {e}")
            if attempt < max_retries - 1:
                time.sleep(retry_delay)
            else:
                return (None, None)

def fetch_underlying_candles(symbol: str, timeframe: str="1Min", limit: int=10) -> pd.DataFrame:
    """
    Fetch candlestick data for underlying symbol with error handling.
    """
    try:
        url = f"https://data.alpaca.markets/v2/stocks/{symbol}/bars"
        end_dt = datetime.now(timezone.utc)
        start_dt = end_dt - timedelta(days=1)
        params = {
            "timeframe": timeframe,
            "limit": limit,
            "start": start_dt.isoformat(),
            "end": end_dt.isoformat(),
            "feed": "iex"
        }

        r = requests.get(url, 
            params=params,
            headers={
                "APCA-API-KEY-ID": ALPACA_API_KEY,
                "APCA-API-SECRET-KEY": ALPACA_API_SECRET
            }
        )
        r.raise_for_status()
        data = r.json().get("bars", [])
        
        if not data:
            debug_log(f"No bars returned for {symbol}")
            return pd.DataFrame()
            
        df = pd.DataFrame(data)
        df["t"] = pd.to_datetime(df["t"], utc=True)
        df.set_index("t", inplace=True)
        df.sort_index(inplace=True)
        return df
        
    except Exception as e:
        log_message(f"Error fetching candles for {symbol}: {e}")
        return pd.DataFrame()

# ------------------------------------------------------------------
# 2. ORDER HANDLING FUNCTIONS
# ------------------------------------------------------------------
def calculate_limit_price(bid, ask, side="buy", aggressive=False):
    """
    Calculate appropriate limit price based on market conditions.
    """
    if bid <= 0 or ask <= 0:
        return None
        
    spread = ask - bid
    spread_pct = spread / ask
    
    if side == "buy":
        if aggressive or spread_pct <= 0.03:  # Tight spread
            return round(ask, 2)  # Pay the ask
        elif spread_pct <= 0.05:  # Normal spread
            return round(bid + spread * 0.6, 2)  # 60% into spread
        else:  # Wide spread
            return round(bid + spread * 0.4, 2)  # More conservative
    else:  # sell
        if aggressive or spread_pct <= 0.03:
            return round(bid, 2)  # Hit the bid
        elif spread_pct <= 0.05:
            return round(ask - spread * 0.6, 2)
        else:
            return round(ask - spread * 0.4, 2)

def wait_for_order_fill(order_id, timeout=60, poll_interval=2):
    """
    Enhanced order fill monitoring with better validation.
    """
    start_time = time.time()
    last_status = None
    
    while time.time() - start_time < timeout:
        try:
            response = requests.get(
                f"{ALPACA_BASE_URL}/v2/orders/{order_id}",
                headers={
                    "APCA-API-KEY-ID": ALPACA_API_KEY,
                    "APCA-API-SECRET-KEY": ALPACA_API_SECRET,
                }
            )
            response.raise_for_status()
            order_data = response.json()
            
            current_status = order_data.get("status")
            if current_status != last_status:
                debug_log(f"Order {order_id} status: {current_status}")
                last_status = current_status
            
            # Check for rejected or cancelled status
            if current_status in ["rejected", "canceled"]:
                log_message(f"Order {order_id} {current_status}: {order_data.get('reason', 'No reason provided')}")
                return None
                
            # Check for filled status
            if current_status == "filled":
                filled_qty = float(order_data.get("filled_qty", 0))
                filled_price = float(order_data.get("filled_avg_price", 0))
                
                if filled_qty > 0 and filled_price > 0:
                    return {
                        "symbol": order_data["symbol"],
                        "quantity": int(filled_qty),
                        "filled_avg_price": filled_price
                    }
                    
            elif current_status == "partially_filled":
                log_message(f"Order {order_id} partially filled: {order_data.get('filled_qty')} @ {order_data.get('filled_avg_price')}")
                
            time.sleep(poll_interval)
            
        except Exception as e:
            log_message(f"Error checking order {order_id} status: {e}")
            time.sleep(poll_interval)
            
    log_message(f"Order {order_id} timed out after {timeout} seconds")
    return None

def cancel_order(order_id):
    """Cancel an existing order."""
    try:
        response = requests.delete(
            f"{ALPACA_BASE_URL}/v2/orders/{order_id}",
            headers={
                "APCA-API-KEY-ID": ALPACA_API_KEY,
                "APCA-API-SECRET-KEY": ALPACA_API_SECRET
            }
        )
        if response.status_code not in [200, 204]:
            log_message(f"Failed to cancel order {order_id}. Response: {response.text}")
        else:
            debug_log(f"Successfully cancelled order {order_id}")
    except Exception as e:
        log_message(f"Error canceling order: {e}")

def place_trade(trade_input):
    """
    Enhanced trade placement with dynamic limit prices and retry logic.
    """
    try:
        debug_log(f"Placing trade with input: {trade_input}")
        if not is_market_open():
            log_message("Market is closed. Cannot place trade.")
            return None

        # Construct option symbol
        expiration_date = datetime.strptime(trade_input["expiration_date"], '%Y-%m-%d')
        formatted_expiration = expiration_date.strftime('%y%m%d')
        strike_price_padded = f"{int(float(trade_input['strike_price']) * 1000):08d}"
        option_type_char = "C" if trade_input["option_type"].lower() == "call" else "P"
        option_symbol = f"{trade_input['symbol']}{formatted_expiration}{option_type_char}{strike_price_padded}"

        debug_log(f"Constructed option symbol: {option_symbol}")
        
        max_attempts = 3  # Maximum number of price adjustments
        initial_aggressive = False  # Start with normal pricing
        
        for attempt in range(max_attempts):
            # Get fresh quote
            bid_price, ask_price = get_option_quote(option_symbol)
            if bid_price is None or ask_price is None:
                log_message("Failed to get valid quote data")
                time.sleep(1)
                continue
            
            # Calculate limit price
            limit_price = calculate_limit_price(
                bid_price, 
                ask_price, 
                side="buy",
                aggressive=(attempt > 0 or initial_aggressive)
            )
            
            if limit_price is None or limit_price <= 0:
                log_message(f"Invalid limit price calculated: {limit_price}")
                time.sleep(1)
                continue
            
            debug_log(f"Attempt {attempt + 1}: Bid={bid_price:.2f}, Ask={ask_price:.2f}, Limit={limit_price:.2f}")
            
            # Place order
            payload = {
                "symbol": option_symbol,
                "qty": str(trade_input["quantity"]),
                "side": "buy",
                "type": "limit",
                "time_in_force": "day",
                "limit_price": str(limit_price)
            }

            response = requests.post(
                f"{ALPACA_BASE_URL}/v2/orders",
                json=payload,
                headers={
                    "APCA-API-KEY-ID": ALPACA_API_KEY,
                    "APCA-API-SECRET-KEY": ALPACA_API_SECRET,
                }
            )
            
            if response.status_code not in [200, 201]:
                log_message(f"Error from Alpaca API: {response.status_code}")
                log_message(f"Response: {response.text}")
                if attempt < max_attempts - 1:
                    time.sleep(1)
                    continue
                return None

            order_data = response.json()
            
            # Wait for fill with shorter timeout for first attempts
            timeout = LIMIT_ORDER_TIMEOUT if attempt == max_attempts - 1 else 20
            filled_order = wait_for_order_fill(order_data["id"], timeout=timeout)
            
            if filled_order:
                log_message(f"Order filled successfully on attempt {attempt + 1}")
                filled_order.update({
                    "strike_price": trade_input["strike_price"],
                    "expiration_date": trade_input["expiration_date"],
                    "option_type": trade_input["option_type"],
                    "direction": trade_input.get("direction", "bullish")
                })
                return filled_order
            
            # Cancel unfilled order before retrying
            cancel_order(order_data["id"])
            log_message(f"Canceled unfilled order, adjusting price for next attempt")
            
            if attempt < max_attempts - 1:
                time.sleep(1)  # Brief pause before retrying
                
        log_message("Failed to fill order after all attempts")
        return None

    except Exception as e:
        log_message(f"Error in place_trade: {e}")
        return None

# ------------------------------------------------------------------
# 3. MARKET STATUS FUNCTIONS
# ------------------------------------------------------------------
def is_market_open():
    """Check if the options market is open."""
    try:
        response = requests.get(
            f"{ALPACA_BASE_URL}/v2/clock",
            headers={
                "APCA-API-KEY-ID": ALPACA_API_KEY,
                "APCA-API-SECRET-KEY": ALPACA_API_SECRET,
            },
        )
        response.raise_for_status()
        clock_data = response.json()
        return clock_data.get('is_open', False)
    except Exception as e:
        log_message(f"Error checking market hours: {e}")
        return False

def calculate_quantity(price, allocation):
    """
    Calculate position size based on allocation limits.
    """
    try:
        total_price_per_contract = price * 100
        if total_price_per_contract <= 0:
            return 0
            
        # Use the smaller of daily_kitty/max_trades or max_allocation_per_trade
        max_allocation = MAX_ALLOCATION_PER_TRADE
        
        if allocation:
            max_allocation = min(max_allocation, allocation)
            
        max_quantity = max_allocation // total_price_per_contract
        return max(1, int(max_quantity)) if total_price_per_contract <= max_allocation else 0
    except Exception as e:
        log_message(f"Error calculating quantity: {e}")
        return 0
    
    # Part 3: Monitoring and Strategy Functions

# ------------------------------------------------------------------
# 1. STRATEGY FUNCTIONS
# ------------------------------------------------------------------
def calculate_technical_indicators(df):
    """Calculate technical indicators using numpy arrays."""
    try:
        if df.empty:
            return df
            
        # Convert price data to numpy arrays
        closes = df['c'].values
        highs = df['h'].values
        lows = df['l'].values
        volumes = df['v'].values
        
        # VWAP
        typical_price = (highs + lows + closes) / 3
        df['vwap'] = np.cumsum(typical_price * volumes) / np.cumsum(volumes)
        
        # EMAs
        df['ema_9'] = df['c'].ewm(span=9, adjust=False).mean()
        df['ema_20'] = df['c'].ewm(span=20, adjust=False).mean()
        df['ema_50'] = df['c'].ewm(span=50, adjust=False).mean()
        
        # RSI
        delta = df['c'].diff()
        gain = (delta.where(delta > 0, 0)).rolling(window=14).mean()
        loss = (-delta.where(delta < 0, 0)).rolling(window=14).mean()
        rs = gain / loss
        df['rsi'] = 100 - (100 / (1 + rs))
        
        # MACD
        exp1 = df['c'].ewm(span=12, adjust=False).mean()
        exp2 = df['c'].ewm(span=26, adjust=False).mean()
        df['macd'] = exp1 - exp2
        df['signal'] = df['macd'].ewm(span=9, adjust=False).mean()
        
        # Bollinger Bands
        df['bb_middle'] = df['c'].rolling(window=20).mean()
        bb_std = df['c'].rolling(window=20).std()
        df['bb_upper'] = df['bb_middle'] + (bb_std * 2)
        df['bb_lower'] = df['bb_middle'] - (bb_std * 2)
        
        # ATR
        high_low = highs - lows
        high_close = np.abs(highs - np.roll(closes, 1))
        low_close = np.abs(lows - np.roll(closes, 1))
        true_range = np.maximum.reduce([high_low, high_close, low_close])
        df['atr'] = pd.Series(true_range).rolling(window=14).mean()
        
        # Volume analysis
        df['vol_sma'] = df['v'].rolling(window=20).mean()
        df['vol_ratio'] = df['v'] / df['vol_sma']
        
        return df
        
    except Exception as e:
        log_message(f"Error calculating indicators: {str(e)}")
        return df

def insert_trade(trade_data):
    """Insert a new trade with proper trade number handling."""
    conn = get_db_connection()
    c = conn.cursor()
    
    try:
        trade_date = date.today()
        
        # Get the next trade number for this symbol/date
        c.execute("""
            SELECT COALESCE(MAX(trade_number), 0) + 1
            FROM trades 
            WHERE symbol = ? AND trade_date = ?
        """, (trade_data['symbol'], trade_date))
        
        trade_number = c.fetchone()[0]
        trade_id = f"{trade_data['symbol']}_{trade_date}_{trade_number}"
        
        c.execute("""
            INSERT INTO trades (
                trade_id, symbol, trade_number, strike_price, 
                expiration_date, option_type, quantity, 
                entry_price, entry_time, trade_status, trade_date
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, datetime('now'), ?, date('now'))
        """, (
            trade_id,
            trade_data['symbol'],
            trade_number,
            trade_data['strike_price'],
            trade_data['expiration_date'],
            trade_data['option_type'],
            trade_data['quantity'],
            trade_data['filled_avg_price'],
            'OPEN'
        ))
        
        conn.commit()
        return True
        
    except sqlite3.IntegrityError as e:
        log_message(f"Database integrity error: {e}")
        return False
    except Exception as e:
        log_message(f"Error inserting trade: {e}")
        return False
    finally:
        conn.close()

def check_entry_conditions(df, strategy_mode="none"):
    """
    Enhanced entry condition checking with multiple strategies.
    Returns dict with entry signal and additional data.
    """
    try:
        if len(df) < 50:  # Need enough data for indicators
            return {"signal": False}
            
        # Calculate technical indicators
        df = calculate_technical_indicators(df)
        
        # Get latest values
        current_price = df['c'].iloc[-1]
        current_volume = df['v'].iloc[-1]
        vwap = df['vwap'].iloc[-1]
        rsi = df['rsi'].iloc[-1]
        macd = df['macd'].iloc[-1]
        macd_signal = df['signal'].iloc[-1]
        vol_ratio = df['vol_ratio'].iloc[-1]
        atr = df['atr'].iloc[-1]
        
        # Base stop loss and target calculations
        base_stop = max(STOP_LOSS, atr / current_price * 1.5)  # Dynamic based on ATR
        base_target = max(PROFIT_MARGIN, atr / current_price * 3)  # 2:1 reward-risk
        
        if strategy_mode == "momentum":
            """
            Momentum strategy looking for:
            - Strong uptrend (EMAs aligned)
            - High volume
            - RSI showing strength but not overbought
            - MACD crossover
            """
            if (df['ema_9'].iloc[-1] > df['ema_20'].iloc[-1] > df['ema_50'].iloc[-1] and
                current_price > vwap and
                vol_ratio > 1.5 and
                45 < rsi < 75 and
                macd > macd_signal and
                macd > 0):
                
                return {
                    "signal": True,
                    "entry_price": current_price,
                    "stop_loss": current_price * (1 - base_stop),
                    "target": current_price * (1 + base_target),
                    "confidence": "high" if vol_ratio > 2 and rsi > 55 else "medium"
                }
                
        elif strategy_mode == "pullback":
            """
            Pullback strategy looking for:
            - Overall uptrend but temporary pullback
            - Support at moving averages
            - RSI showing oversold conditions
            - Volume declining during pullback
            """
            recent_high = df['h'].rolling(window=20).max().iloc[-1]
            pullback_pct = (recent_high - current_price) / recent_high
            
            if (df['ema_50'].iloc[-1] > df['ema_50'].iloc[-10] and  # Uptrend
                0.03 < pullback_pct < 0.08 and  # Healthy pullback size
                current_price >= df['ema_20'].iloc[-1] and  # Finding support
                rsi < 40 and  # Oversold
                vol_ratio < 0.8):  # Declining volume on pullback
                
                return {
                    "signal": True,
                    "entry_price": current_price,
                    "stop_loss": min(df['l'].iloc[-5:]) * 0.99,
                    "target": recent_high,
                    "confidence": "high" if rsi < 35 else "medium"
                }
                
        elif strategy_mode == "breakout":
            """
            Breakout strategy looking for:
            - Price breaking above resistance
            - High volume confirmation
            - RSI showing strength
            - Bollinger Band expansion
            """
            resistance = df['h'].rolling(window=20).max().iloc[-2]  # Prior high
            bb_width = (df['bb_upper'] - df['bb_lower']) / df['bb_middle']
            bb_expansion = bb_width.iloc[-1] > bb_width.iloc[-5:].mean()
            
            if (current_price > resistance and
                vol_ratio > 2.0 and
                rsi > 60 and
                bb_expansion):
                
                return {
                    "signal": True,
                    "entry_price": current_price,
                    "stop_loss": resistance * 0.98,  # Just below breakout level
                    "target": current_price + (current_price - resistance) * 2,
                    "confidence": "high" if vol_ratio > 3 else "medium"
                }
                
        elif strategy_mode == "mean_reversion":
            """
            Mean reversion strategy looking for:
            - Price significantly below VWAP
            - Oversold RSI with bullish divergence
            - Support at Bollinger Band lower
            - Decreasing volume on downmove
            """
            vwap_dist = (vwap - current_price) / current_price
            at_bb_lower = current_price <= df['bb_lower'].iloc[-1]
            
            if (vwap_dist > 0.02 and
                at_bb_lower and
                rsi < 30 and
                vol_ratio < 0.7):
                
                return {
                    "signal": True,
                    "entry_price": current_price,
                    "stop_loss": current_price * (1 - base_stop),
                    "target": vwap,  # Target mean reversion to VWAP
                    "confidence": "high" if rsi < 25 else "medium"
                }
                
        elif strategy_mode == "none":
            """
            Basic trend following with volume confirmation
            """
            if (current_price > vwap and
                current_price > df['ema_20'].iloc[-1] and
                vol_ratio > 1.2):
                
                return {
                    "signal": True,
                    "entry_price": current_price,
                    "stop_loss": current_price * (1 - base_stop),
                    "target": current_price * (1 + base_target),
                    "confidence": "medium"
                }
                
        return {"signal": False}
        
    except Exception as e:
        log_message(f"Error in check_entry_conditions: {e}")
        return {"signal": False}

def fetch_real_time_data(symbol, timeframe="1Min", bars=50):
    """
    Fetch real-time market data with retries and validation.
    """
    try:
        # Get multiple timeframes for better analysis
        dfs = {}
        timeframes = {
            "1Min": bars,
            "5Min": bars//5,
            "15Min": bars//15
        }
        
        for tf, limit in timeframes.items():
            df = fetch_underlying_candles(symbol, timeframe=tf, limit=limit)
            if not df.empty:
                dfs[tf] = df
        
        if not dfs:
            log_message(f"Could not fetch data for {symbol}")
            return pd.DataFrame()
            
        # Use the most granular timeframe as primary
        return dfs["1Min"]
        
    except Exception as e:
        log_message(f"Error fetching real-time data: {e}")
        return pd.DataFrame()


# ------------------------------------------------------------------
# 2. MONITORING FUNCTIONS
# ------------------------------------------------------------------
def monitor_symbol(symbol):
    """
    Monitor a symbol for entry/exit opportunities using technical analysis.
    """
    try:
        log_message(f"Starting technical monitor for {symbol}")
        last_trade_time = None
        min_trade_interval = timedelta(minutes=5)  # Minimum time between trades

        while True:
            try:
                if not is_market_open():
                    time.sleep(60)
                    continue

                current_time = datetime.now(timezone.utc)
                
                # Respect minimum trade interval
                if last_trade_time and (current_time - last_trade_time < min_trade_interval):
                    time.sleep(MONITOR_INTERVAL)
                    continue

                # 1. Get multi-timeframe data
                df_1m = fetch_underlying_candles(symbol, timeframe="1Min", limit=50)
                df_5m = fetch_underlying_candles(symbol, timeframe="5Min", limit=30)
                df_15m = fetch_underlying_candles(symbol, timeframe="15Min", limit=20)

                if df_1m.empty or df_5m.empty or df_15m.empty:
                    time.sleep(MONITOR_INTERVAL)
                    continue

                # 2. Calculate technicals for each timeframe
                df_1m = calculate_technical_indicators(df_1m)
                df_5m = calculate_technical_indicators(df_5m)
                df_15m = calculate_technical_indicators(df_15m)

                # 3. Check for entry conditions based on strategy
                entry_conditions = False
                entry_reason = ""

                if STRATEGY_MODE == "momentum":
                    # Strong trend with volume confirmation
                    if (
                        # Trend alignment across timeframes
                        df_15m['ema_9'].iloc[-1] > df_15m['ema_20'].iloc[-1] > df_15m['ema_50'].iloc[-1] and
                        df_5m['ema_9'].iloc[-1] > df_5m['ema_20'].iloc[-1] and
                        df_1m['ema_9'].iloc[-1] > df_1m['ema_20'].iloc[-1] and
                        
                        # MACD momentum
                        df_15m['macd'].iloc[-1] > df_15m['signal'].iloc[-1] and
                        df_15m['macd'].iloc[-1] > 0 and
                        
                        # RSI not overbought
                        45 < df_15m['rsi'].iloc[-1] < 75 and
                        
                        # Volume confirmation
                        df_15m['vol_ratio'].iloc[-1] > 1.5
                    ):
                        entry_conditions = True
                        entry_reason = "Momentum alignment with volume confirmation"

                elif STRATEGY_MODE == "pullback":
                    # Pullback in uptrend
                    recent_high = df_15m['h'].rolling(window=20).max().iloc[-1]
                    pullback_level = recent_high * 0.97  # 3% pullback
                    
                    if (
                        # Overall uptrend
                        df_15m['ema_50'].iloc[-1] > df_15m['ema_50'].iloc[-10] and
                        
                        # Price pulled back
                        df_15m['c'].iloc[-1] <= pullback_level and
                        
                        # RSI showing oversold
                        df_15m['rsi'].iloc[-1] < 40 and
                        
                        # Volume declining on pullback
                        df_15m['vol_ratio'].iloc[-1] < 0.8 and
                        
                        # Finding support
                        df_15m['c'].iloc[-1] >= df_15m['bb_lower'].iloc[-1]
                    ):
                        entry_conditions = True
                        entry_reason = "Healthy pullback in uptrend"

                elif STRATEGY_MODE == "breakout":
                    # High volume breakout
                    resistance = df_15m['h'].rolling(window=20).max().iloc[-2]  # Prior high
                    
                    if (
                        # Price breaking resistance
                        df_15m['c'].iloc[-1] > resistance and
                        
                        # Volume surge
                        df_15m['vol_ratio'].iloc[-1] > 2.0 and
                        
                        # Momentum confirmation
                        df_15m['rsi'].iloc[-1] > 60 and
                        df_15m['macd'].iloc[-1] > df_15m['signal'].iloc[-1]
                    ):
                        entry_conditions = True
                        entry_reason = "High volume breakout with momentum"

                # 4. Process alerts if conditions met
                if entry_conditions:
                    with trade_lock:
                        # Get all current alerts for this symbol
                        symbol_alerts = []
                        while not alert_queue.empty():
                            alert, timestamp = alert_queue.peek()
                            if alert['symbol'] == symbol and is_recent_alert(timestamp):
                                alert, _ = alert_queue.get()
                                symbol_alerts.append((alert, timestamp))
                            else:
                                break

                        # Process valid alerts
                        for alert, timestamp in symbol_alerts:
                            try:
                                # Check existing trades count
                                active_count = len([t for t in active_trades.values() 
                                                  if t['symbol'].startswith(symbol)])
                                                  
                                if active_count >= 3:  # Max 3 concurrent trades per symbol
                                    log_message(f"Max trades reached for {symbol}")
                                    continue

                                # Calculate position size
                                allocation = min(
                                    MAX_ALLOCATION_PER_TRADE,
                                    daily_kitty / max_trades
                                )
                                quantity = calculate_quantity(alert["current_price"], allocation)
                                
                                if quantity <= 0:
                                    continue

                                # Place trade
                                trade_input = {
                                    'symbol': alert['symbol'],
                                    'expiration_date': datetime.strptime(
                                        alert['expiration_date'], '%b %d %Y'
                                    ).strftime('%Y-%m-%d'),
                                    'strike_price': alert['strike_price'],
                                    'option_type': alert['option_type'],
                                    'quantity': quantity,
                                    'current_price': alert['current_price'],
                                    'direction': alert.get('direction', 'bullish'),
                                    'entry_reason': entry_reason,
                                    'technical_data': {
                                        'rsi': df_15m['rsi'].iloc[-1],
                                        'macd': df_15m['macd'].iloc[-1],
                                        'vol_ratio': df_15m['vol_ratio'].iloc[-1]
                                    }
                                }

                                # Log analysis
                                log_message(f"\n=== Entry Analysis for {symbol} ===")
                                log_message(f"Strategy: {STRATEGY_MODE}")
                                log_message(f"Reason: {entry_reason}")
                                log_message(f"RSI: {df_15m['rsi'].iloc[-1]:.2f}")
                                log_message(f"Volume Ratio: {df_15m['vol_ratio'].iloc[-1]:.2f}")
                                log_message(f"Quantity: {quantity}")

                                trade_data = place_trade(trade_input)
                                
                                if trade_data and trade_data["quantity"] > 0:
                                    last_trade_time = current_time
                                    
                                    if insert_trade(trade_data):
                                        monitor_thread = threading.Thread(
                                            target=monitor_trade,
                                            args=(trade_data,),
                                            name=f"monitor_{trade_data['symbol']}",
                                            daemon=True
                                        )
                                        monitor_thread.start()
                                        
                                        active_trades[trade_data['symbol']] = trade_data
                                        log_message(f"Successfully entered position in {symbol}")

                            except Exception as e:
                                log_message(f"Error processing alert for {symbol}: {e}")

                # 5. Check exit conditions for existing trades
                with trade_lock:
                    symbol_trades = [t for t in active_trades.values() 
                                   if t['symbol'].startswith(symbol)]
                    
                    for trade in symbol_trades:
                        try:
                            exit_signal = False
                            exit_reason = ""

                            # Strategy-specific exit conditions
                            if STRATEGY_MODE == "momentum":
                                if (df_15m['ema_9'].iloc[-1] < df_15m['ema_20'].iloc[-1] or
                                    df_15m['macd'].iloc[-1] < df_15m['signal'].iloc[-1] or
                                    df_15m['rsi'].iloc[-1] < 45):
                                    exit_signal = True
                                    exit_reason = "Trend/momentum breakdown"

                            elif STRATEGY_MODE == "pullback":
                                if (df_15m['c'].iloc[-1] > df_15m['bb_upper'].iloc[-1] or
                                    df_15m['rsi'].iloc[-1] > 60):
                                    exit_signal = True
                                    exit_reason = "Target reached / RSI overbought"

                            elif STRATEGY_MODE == "breakout":
                                if (df_15m['c'].iloc[-1] < df_15m['bb_middle'].iloc[-1] or
                                    df_15m['vol_ratio'].iloc[-1] < 1.0):
                                    exit_signal = True
                                    exit_reason = "Failed breakout / low volume"

                            if exit_signal:
                                log_message(f"Exit signal for {trade['symbol']}: {exit_reason}")
                                sell_trade(trade)

                        except Exception as e:
                            log_message(f"Error checking exit conditions: {e}")

                time.sleep(MONITOR_INTERVAL)

            except Exception as e:
                log_message(f"Error in monitor loop for {symbol}: {e}")
                time.sleep(5)

    except Exception as e:
        log_message(f"Fatal error in monitor_symbol for {symbol}: {e}")
    finally:
        log_message(f"Monitor stopped for {symbol}")

def monitor_trade(trade_data):
    """
    Monitor individual trade for exit conditions.
    """
    try:
        symbol = trade_data["symbol"]
        quantity = trade_data["quantity"]
        entry_price = float(trade_data["filled_avg_price"])
        direction = trade_data.get("direction", "bullish")
        strategy_mode = STRATEGY_MODE

        entry_time = datetime.now(timezone.utc)
        highest_price = entry_price
        last_logged = entry_price
        
        log_message(f"\n=== Starting Trade Monitor ===")
        log_message(f"Symbol: {symbol}")
        log_message(f"Strategy: {strategy_mode.upper()}")
        log_message(f"Entry Price: ${entry_price:.2f}")
        log_message(f"Quantity: {quantity}")

        while True:
            if not is_market_open():
                log_message("Market closed => forcing exit.")
                sell_trade(trade_data, None)
                break

            # Get current market data
            bid_price, ask_price = get_option_quote(symbol)
            if bid_price is None or ask_price is None:
                time.sleep(2)
                continue
                
            current_price = bid_price  # Use bid for conservative P&L calculation
            
            # Update trailing stop if applicable
            if current_price > highest_price:
                highest_price = current_price
                new_stop = highest_price * (1 - TRAIL_BY)
                log_message(f"New trailing stop: ${new_stop:.2f}")

            # Calculate current P&L
            unrealized_pl = (current_price - entry_price) * quantity * 100
            unrealized_pl_pct = ((current_price - entry_price) / entry_price) * 100

            # Log significant price changes
            pct_change = abs((current_price - last_logged) / last_logged)
            if pct_change >= 0.01:  # Log 1% or greater moves
                log_message(f"Price: ${current_price:.2f}, P&L: ${unrealized_pl:.2f} ({unrealized_pl_pct:.1f}%)")
                last_logged = current_price

            # Check for exit conditions based on underlying price
            underlying_symbol = re.match(r"^([A-Z]+)", symbol).group(1)
            df = fetch_underlying_candles(underlying_symbol, timeframe="1Min", limit=5)
            
            if not df.empty:
                exit_check = check_exit_conditions(df, trade_data, strategy_mode)
                if exit_check["signal"]:
                    log_message(f"Exit signal: {exit_check['reason']}")
                    if sell_trade(trade_data, exit_check["price"]):
                        break

            time.sleep(MONITOR_INTERVAL)

    except Exception as e:
        log_message(f"Error in monitor_trade({symbol}): {e}")
    finally:
        exit_time = datetime.now(timezone.utc)
        duration = exit_time - entry_time
        log_message(f"=== Monitor exited for {symbol} | Duration: {duration} ===")

def sell_trade(trade_data, exit_price=None):
    """
    Place sell order for a trade.
    """
    try:
        symbol = trade_data["symbol"]
        quantity = trade_data["quantity"]
        
        if not is_market_open():
            log_message("Market closed. Cannot place sell order.")
            return None
            
        # Get fresh quote if exit_price not provided
        if exit_price is None:
            bid_price, ask_price = get_option_quote(symbol)
            if bid_price is None:
                log_message("Cannot get valid quote for exit")
                return None
            exit_price = bid_price
            
        # Place sell order
        payload = {
            "symbol": symbol,
            "qty": str(quantity),
            "side": "sell",
            "type": "limit",
            "time_in_force": "day",
            "limit_price": str(exit_price)
        }
        
        response = requests.post(
            f"{ALPACA_BASE_URL}/v2/orders",
            json=payload,
            headers={
                "APCA-API-KEY-ID": ALPACA_API_KEY,
                "APCA-API-SECRET-KEY": ALPACA_API_SECRET,
            }
        )
        
        if response.status_code not in [200, 201]:
            log_message(f"Error placing sell order: {response.text}")
            return None
            
        order_data = response.json()
        filled_order = wait_for_order_fill(order_data["id"], timeout=30)
        
        if filled_order:
            profit_loss = (filled_order["filled_avg_price"] - trade_data["entry_price"]) * quantity * 100
            update_trade_exit(
                trade_id=get_trade_id(trade_data),
                exit_price=filled_order["filled_avg_price"],
                profit_loss=profit_loss,
                profit_loss_pct=(profit_loss / (trade_data["entry_price"] * quantity * 100)) * 100
            )
            return filled_order
            
        return None
        
    except Exception as e:
        log_message(f"Error in sell_trade: {e}")
        return None

def close_all_trades():
    """
    Close all active trades with retries and proper position tracking.
    Returns summary of closed trades.
    """
    global daily_kitty
    summary = {
        "success": 0,
        "failed": 0,
        "total_pl": 0
    }
    
    try:
        # 1. Get all active trades from both memory and database
        active_positions = []
        
        # Check memory-tracked trades
        with trade_lock:
            active_positions.extend(list(active_trades.values()))
            
        # Check database for any additional active trades
        conn = get_db_connection()
        c = conn.cursor()
        c.execute("SELECT * FROM trades WHERE trade_status = 'OPEN' AND trade_date = date('now')")
        db_trades = c.fetchall()
        conn.close()
        
        for db_trade in db_trades:
            if not any(t.get('symbol') == db_trade['symbol'] for t in active_positions):
                active_positions.append(dict(db_trade))
        
        if not active_positions:
            log_message("No active trades to close.")
            return summary
            
        log_message(f"Attempting to close {len(active_positions)} active trades...")
        
        # 2. Close each position with retries
        for trade_data in active_positions:
            try:
                symbol = trade_data['symbol']
                max_attempts = 3
                
                for attempt in range(max_attempts):
                    try:
                        # Get current market data
                        bid_price, ask_price = get_option_quote(symbol)
                        if bid_price is None:
                            if attempt == max_attempts - 1:
                                raise Exception("Cannot get valid quote after all attempts")
                            time.sleep(1)
                            continue
                            
                        # Place sell order
                        result = sell_trade(trade_data, bid_price)
                        if result:
                            # Calculate P&L
                            entry_price = float(trade_data['entry_price'])
                            exit_price = float(result['filled_avg_price'])
                            quantity = int(trade_data['quantity'])
                            
                            profit_loss = (exit_price - entry_price) * quantity * 100
                            pl_pct = (profit_loss / (entry_price * quantity * 100)) * 100
                            
                            # Update database
                            update_trade_exit(
                                trade_id=get_trade_id(trade_data),
                                exit_price=exit_price,
                                profit_loss=profit_loss,
                                profit_loss_pct=pl_pct
                            )
                            
                            # Update tracking
                            daily_kitty += profit_loss
                            summary["success"] += 1
                            summary["total_pl"] += profit_loss
                            
                            log_message(f"Closed {symbol}: P&L=${profit_loss:.2f} ({pl_pct:.1f}%)")
                            break
                            
                        elif attempt < max_attempts - 1:
                            log_message(f"Retrying close for {symbol} (attempt {attempt + 1})")
                            time.sleep(2)
                        else:
                            raise Exception("Failed to fill sell order after all attempts")
                            
                    except Exception as e:
                        if attempt == max_attempts - 1:
                            raise e
                        time.sleep(1)
                        
            except Exception as e:
                log_message(f"Failed to close {symbol}: {str(e)}")
                summary["failed"] += 1
                
        # 3. Clear active trades tracking
        with trade_lock:
            active_trades.clear()
            
        # 4. Log summary
        log_message("\n=== Trade Closing Summary ===")
        log_message(f"Successfully closed: {summary['success']}")
        log_message(f"Failed to close: {summary['failed']}")
        log_message(f"Total P&L: ${summary['total_pl']:.2f}")
        log_message(f"Updated daily kitty: ${daily_kitty:.2f}")
        log_message("=============================\n")
        
    except Exception as e:
        log_message(f"Error in close_all_trades: {e}")
    
    return summary
                
                

# Part 4: Alert Processing, Reporting, and Main Program

# ------------------------------------------------------------------
# 1. ALERT PROCESSING
# ------------------------------------------------------------------
def fetch_latest_messages():
    """Fetch recent messages from Discord."""
    url = f"https://discord.com/api/v9/channels/{DISCORD_CHANNEL_ID}/messages?limit={DISCORD_MSG_LIMIT}"
    headers = {
        "Authorization": DISCORD_USER_TOKEN,
        "Content-Type": "application/json",
    }
    try:
        response = requests.get(url, headers=headers)
        response.raise_for_status()
        messages = response.json()
        log_message(f"Fetched {len(messages)} messages from Discord.")
        return messages
    except requests.exceptions.RequestException as e:
        log_message(f"Error fetching messages: {e}")
        return []

def is_recent_alert(timestamp):
    """Check if alert is within recent time window."""
    try:
        if not timestamp:
            return False
            
        alert_time = datetime.fromisoformat(str(timestamp).replace("Z", "+00:00"))
        if not alert_time.tzinfo:
            alert_time = alert_time.replace(tzinfo=timezone.utc)
        
        current_time = datetime.now(timezone.utc)
        time_diff = current_time - alert_time
        
        is_recent = time_diff <= timedelta(minutes=RECENT_ALERT_MINUTES)
        if not is_recent:
            debug_log(f"Alert not recent: {timestamp}")
        return is_recent
        
    except Exception as e:
        log_message(f"Error checking alert timestamp: {e}")
        return False

def parse_alert(content, embeds):
    """Parse alert data from Discord message."""
    try:
        debug_log(f"Parsing alert content")
        alerts = []
        if embeds:
            for embed in embeds:
                title = embed.get("title", "")
                if ":green_circle: EXPLOSIVE SETUP DETECTED" in title:
                    embed_direction = "bullish"
                elif ":red_circle: EXPLOSIVE SETUP DETECTED" in title:
                    embed_direction = "bearish"
                else:
                    embed_direction = "bullish"  # default

                for field in embed.get("fields", []):
                    if field["name"] == "Alert:" and "Current Price:" in field["value"]:
                        alert_texts = field["value"].split("\n\n")
                        for alert_text in alert_texts:
                            if "Current Price:" in alert_text:
                                pattern = (r"(\w+)\s+"
                                           r"((?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\s+\d{1,2}\s+\d{4})\s+"
                                           r"\$(\d+\.\d+)\s+"
                                           r"(Call|Put)\s+Current\s+Price:\s+(\d+\.?\d*)")
                                match = re.search(pattern, alert_text.strip())
                                if match:
                                    try:
                                        strike_val = float(match.group(3))
                                        current_val = float(match.group(5))
                                        alert_parsed = {
                                            "symbol": match.group(1),
                                            "expiration_date": match.group(2),
                                            "strike_price": strike_val,
                                            "option_type": match.group(4).lower(),
                                            "current_price": current_val,
                                            "direction": embed_direction
                                        }
                                        alerts.append(alert_parsed)
                                    except ValueError as e:
                                        debug_log(f"Numeric parse issue: {e}")

        return alerts
    except Exception as e:
        log_message(f"Error parsing alert: {e}")
        return []

def check_daily_limits(force_close_if_exceeded=False):
    """Check if daily P&L limits have been reached."""
    global daily_kitty, initial_daily_kitty
    daily_pl = daily_kitty - initial_daily_kitty

    # Check profit cap
    if daily_pl >= (initial_daily_kitty * MAX_PROFIT_PCT):
        log_message(f"Daily profit target reached: +${daily_pl:.2f}")
        if force_close_if_exceeded:
            close_all_trades()
        return False

    # Check loss cap
    if daily_pl <= -(initial_daily_kitty * MAX_LOSS_PCT):
        log_message(f"Daily loss limit reached: ${daily_pl:.2f}")
        if force_close_if_exceeded:
            close_all_trades()
        return False

    return True

def process_alert_queue():
    """Process alerts from the queue with strategy checks."""
    while True:
        try:
            if not alert_queue.empty():
                alert, timestamp = alert_queue.get()

                # Check daily limits
                if not check_daily_limits(force_close_if_exceeded=False):
                    log_message("Daily P&L limits exceeded. Skipping new trades.")
                    alert_queue.task_done()
                    continue

                # Basic checks
                if not is_recent_alert(timestamp):
                    alert_queue.task_done()
                    continue

                if not is_market_open():
                    alert_queue.task_done()
                    continue

                # Start symbol monitor if needed
                symbol = alert["symbol"]
                if symbol not in symbol_monitors:
                    monitor = threading.Thread(
                        target=monitor_symbol,
                        args=(symbol,),
                        name=f"symbol_monitor_{symbol}",
                        daemon=True
                    )
                    monitor.start()
                    symbol_monitors[symbol] = monitor

                # Calculate position size
                allocation = daily_kitty / max_trades
                quantity = calculate_quantity(alert["current_price"], allocation)
                if quantity == 0:
                    log_message(f"Invalid quantity calculated for {symbol}")
                    alert_queue.task_done()
                    continue

                # Place trade
                trade_input = {
                    'symbol': alert['symbol'],
                    'expiration_date': datetime.strptime(alert['expiration_date'], '%b %d %Y').strftime('%Y-%m-%d'),
                    'strike_price': alert['strike_price'],
                    'option_type': alert['option_type'],
                    'quantity': quantity,
                    'current_price': alert['current_price'],
                    'direction': alert.get('direction', 'bullish')
                }

                trade_data = place_trade(trade_input)
                if trade_data and trade_data["quantity"] > 0:
                    if insert_trade(trade_data):
                        # Start trade monitor
                        monitor_thread = threading.Thread(
                            target=monitor_trade,
                            args=(trade_data,),
                            name=f"monitor_{trade_data['symbol']}",
                            daemon=True
                        )
                        monitor_thread.start()
                        
                        with trade_lock:
                            active_trades[trade_data['symbol']] = trade_data

                alert_queue.task_done()
            time.sleep(1)
        except Exception as e:
            log_message(f"Error in alert queue processing: {e}")
            time.sleep(POLL_INTERVAL)

# ------------------------------------------------------------------
# 2. REPORTING FUNCTIONS
# ------------------------------------------------------------------
def generate_daily_report():
    """Generate end-of-day trading report."""
    try:
        conn = get_db_connection()
        c = conn.cursor()
        
        report = []
        report.append(f"\n=== Daily Trading Report {date.today()} ===\n")
        
        # Get daily statistics
        c.execute("""
            SELECT COUNT(*) as total_trades,
                   COUNT(CASE WHEN profit_loss > 0 THEN 1 END) as winners,
                   SUM(profit_loss) as total_pl,
                   AVG(profit_loss_pct) as avg_pl_pct
            FROM trades 
            WHERE trade_date = date('now')
        """)
        row = c.fetchone()
        
        total = row['total_trades'] or 0
        winners = row['winners'] or 0
        total_pl = row['total_pl'] or 0.0
        avg_pl_pct = row['avg_pl_pct'] or 0.0
        
        report.append(f"Total Trades: {total}")
        report.append(f"Winners: {winners}")
        report.append(f"Win Rate: {(winners/total*100 if total else 0):.1f}%")
        report.append(f"Total P&L: ${total_pl:.2f}")
        report.append(f"Avg P&L %: {avg_pl_pct:.1f}%\n")
        
        # Get best and worst trades
        c.execute("""
            SELECT * FROM trades 
            WHERE trade_date = date('now') 
            ORDER BY profit_loss DESC 
            LIMIT 1
        """)
        best = c.fetchone()
        if best:
            report.append("Best Trade:")
            report.append(f"Symbol: {best['symbol']}")
            report.append(f"P&L: ${best['profit_loss']:.2f} ({best['profit_loss_pct']:.1f}%)\n")
            
        c.execute("""
            SELECT * FROM trades 
            WHERE trade_date = date('now') 
            ORDER BY profit_loss ASC 
            LIMIT 1
        """)
        worst = c.fetchone()
        if worst:
            report.append("Worst Trade:")
            report.append(f"Symbol: {worst['symbol']}")
            report.append(f"P&L: ${worst['profit_loss']:.2f} ({worst['profit_loss_pct']:.1f}%)\n")
        
        report_text = "\n".join(report)
        
        # Save report
        with open(DAILY_REPORT_PATH, 'a') as f:
            f.write(report_text)
            f.write("\n")
            
        log_message(report_text)
        
    except Exception as e:
        log_message(f"Error generating daily report: {e}")
    finally:
        conn.close()

def market_close_watcher():
    """Monitor for market close and handle end-of-day tasks."""
    while True:
        try:
            current_time = datetime.now(timezone.utc)
            market_close_time = current_time.replace(hour=21, minute=0, second=0, microsecond=0)
            warning_time = market_close_time - timedelta(minutes=PRE_CLOSE_MINUTES)
            
            if current_time >= warning_time:
                log_message("Market close approaching. Closing all trades.")
                close_all_trades()
                generate_daily_report()
                break
                
            time.sleep(60)
            
        except Exception as e:
            log_message(f"Error in market close watcher: {e}")
            time.sleep(60)

# ------------------------------------------------------------------
# 3. MAIN PROGRAM
# ------------------------------------------------------------------
def main():
    """Main program execution."""
    try:
        # Initialize database
        init_db()
        
        # Start alert queue processor
        queue_processor = threading.Thread(
            target=process_alert_queue,
            daemon=True,
            name="QueueProcessor"
        )
        queue_processor.start()
        log_message("Alert queue processor started")

        # Start market close watcher
        market_watcher = threading.Thread(
            target=market_close_watcher,
            daemon=True,
            name="MarketWatcher"
        )
        market_watcher.start()
        log_message("Market close watcher started")

        # Reconcile any existing positions
        #reconcile_trades_with_alpaca()

        # Main alert processing loop
        log_message("Starting alert monitoring...")
        while True:
            try:
                if not is_market_open():
                    time.sleep(300)  # 5 minutes
                    continue
                    
                messages = fetch_latest_messages()
                if not messages:
                    time.sleep(POLL_INTERVAL)
                    continue

                for message in messages:
                    content = message.get("content", "")
                    embeds = message.get("embeds", [])
                    timestamp = message.get("timestamp")
                    
                    if not timestamp or not is_recent_alert(timestamp):
                        continue

                    alerts = parse_alert(content, embeds)
                    for alert in alerts:
                        alert_queue.put((alert, timestamp))

                time.sleep(POLL_INTERVAL)
                
            except Exception as e:
                log_message(f"Error in main loop: {e}")
                time.sleep(POLL_INTERVAL)
                
    except KeyboardInterrupt:
        log_message("Shutting down gracefully...")
        close_all_trades()
        generate_daily_report()
    except Exception as e:
        log_message(f"Fatal error: {e}")
        close_all_trades()
        generate_daily_report()
    finally:
        log_message("Program terminated")

if __name__ == "__main__":
    main()