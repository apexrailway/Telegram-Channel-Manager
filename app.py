from flask import Flask, render_template, request, redirect, url_for, session, jsonify, Response
from flask_sqlalchemy import SQLAlchemy
from werkzeug.security import generate_password_hash, check_password_hash  
from telethon import TelegramClient, events
from telethon.sessions import StringSession 
from telethon.errors import SessionPasswordNeededError, FloodWaitError, UserPrivacyRestrictedError, ChatWriteForbiddenError, UserDeactivatedBanError, UserDeactivatedError
from telethon.tl.functions.messages import SetTypingRequest
from telethon.tl.types import SendMessageTypingAction
import asyncio
import os 
from datetime import datetime, timedelta              
import httpx
import logging
import random
import json
import time
from functools import wraps
from sqlalchemy import Index
import queue
import threading

logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - [%(filename)s:%(lineno)d] - %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('telegram_manager.log', encoding='utf-8')
    ]
)
logger = logging.getLogger(__name__)

app = Flask(__name__)
SECRET_KEY = "o9j3k4l5m6n7p8q9r0s1t2u3v4w5x6y7z8a9b0c1d2"
if not SECRET_KEY:
    SECRET_KEY = os.urandom(24).hex()
    logger.warning("No SECRET_KEY environment variable set! Using generated key.")
app.secret_key = SECRET_KEY

database_url = os.environ.get('DATABASE_URL', 'sqlite:///telegram_manager.db')
if database_url.startswith('postgres://'):
    database_url = database_url.replace('postgres://', 'postgresql://', 1)

app.config['SQLALCHEMY_DATABASE_URI'] = database_url
app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False
app.config['SQLALCHEMY_ENGINE_OPTIONS'] = {
    'pool_pre_ping': True,
    'pool_recycle': 300,
    'pool_size': 10,
    'max_overflow': 20
}

app.config['SESSION_COOKIE_SECURE'] = os.environ.get('FLASK_ENV') == 'production'
app.config['SESSION_COOKIE_HTTPONLY'] = True
app.config['SESSION_COOKIE_SAMESITE'] = 'Lax'
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=30)
app.config['SESSION_COOKIE_NAME'] = 'telegram_manager_session'

db = SQLAlchemy(app)

stop_sending_flag = {}
active_tasks = {}
completed_accounts = {}  # Track which accounts completed: {session_id: {account_id: True}}
global_log_queue = queue.Queue(maxsize=5000)
activity_log_queue = queue.Queue(maxsize=1000)

messaging_lock = threading.Lock()
currently_messaging = {}
global_messaged_users = {}

# ADVANCED DUPLICATE PREVENTION SYSTEM
permanent_user_blacklist = set()  # Global blacklist across all sessions
user_cache_lock = threading.Lock()
messaged_users_cache = {}  # Cache for quick lookup: {(channel_id, user_id): True/False}
cache_ttl = 3600  # Cache time-to-live in seconds
last_cache_clear = time.time()


running_threads = {}
session_log_listeners = {}  # session_id -> list of queues
session_log_history = {}    # session_id -> list of messages (history)
session_threads_lock = threading.Lock()

def broadcast_log(session_id, message_dict):
    """Broadcast a log message to all connected clients and save to history"""
    with session_threads_lock:
        # Save to history
        if session_id not in session_log_history:
            session_log_history[session_id] = []
        
        # Limit history to 500 entries to prevent memory bloat
        if len(session_log_history[session_id]) > 500:
            session_log_history[session_id].pop(0)
            
        session_log_history[session_id].append(message_dict)

        # Broadcast to all listeners
        if session_id in session_log_listeners:
            dead_listeners = []
            for q in session_log_listeners[session_id]:
                try:
                    q.put_nowait(message_dict)
                except queue.Full:
                    # If a specific client is stalled, we might drop their message 
                    # or mark for removal, but put_nowait raises Full immediately.
                    # Ideally we use a larger maxsize for listeners.
                    pass
                except Exception:
                    dead_listeners.append(q)
            
            # Remove any dead listeners (though mostly handled in stream loop)
            for q in dead_listeners:
                if q in session_log_listeners[session_id]:
                    session_log_listeners[session_id].remove(q)

def register_session_start(session_id):
    with messaging_lock:
        if session_id not in global_messaged_users:
            global_messaged_users[session_id] = set()

def clear_session_data(session_id):
    with messaging_lock:
        if session_id in global_messaged_users:
            del global_messaged_users[session_id]

        to_remove = [uid for uid, (sid, _) in currently_messaging.items() if sid == session_id]
        for uid in to_remove:
            del currently_messaging[uid]

def check_stop_flag_from_db(account_id):
    """
    🛑 DATABASE-PERSISTED STOP CHECK

    Checks stop signal from BOTH RAM and DATABASE.
    This is CRITICAL for Railway deployments where:
    - RAM flags are lost on restart
    - Connection can drop mid-operation
    - EventSource streams disconnect

    Returns True if stop is requested, False otherwise.
    """
    try:
        # 1. Quick check: RAM flag (fast, but lost on restart)
        if stop_sending_flag.get(account_id, False):
            return True

        # 2. Reliable check: DATABASE flag (survives Railway restarts!)
        with app.app_context():
            task = ActiveTask.query.filter_by(
                account_id=account_id,
                task_type='send_messages'
            ).first()

            if task and task.stop_requested:
                # Database has stop signal - sync to RAM for speed
                stop_sending_flag[account_id] = True
                logger.info(f"🛑 Stop detected from DATABASE for account {account_id}")
                return True

        return False
    except Exception as e:
        logger.error(f"Error checking stop flag from DB for account {account_id}: {e}")
        # Fallback to RAM flag only
        return stop_sending_flag.get(account_id, False)

def cleanup_completed_tasks(session_id):
    """Delete completed ActiveTask records from database and clear log history"""
    try:
        # Delete all completed tasks for this session
        deleted_count = ActiveTask.query.filter_by(
            session_id=session_id,
            is_completed=True
        ).delete()

        db.session.commit()
        logger.info(f"Cleaned up {deleted_count} completed tasks for session {session_id}")

        # Clear log history for this session to free memory
        with session_threads_lock:
            if session_id in session_log_history:
                del session_log_history[session_id]
                logger.info(f"Cleared log history for session {session_id}")

            if session_id in session_log_listeners:
                del session_log_listeners[session_id]
                logger.info(f"Cleared log listeners for session {session_id}")
                
        return deleted_count
    except Exception as e:
        db.session.rollback()
        logger.error(f"Error cleaning up completed tasks: {str(e)}", exc_info=True)
        return 0

def clear_cache_if_needed():
    """Clear cache periodically to prevent memory bloat"""
    global last_cache_clear, messaged_users_cache
    current_time = time.time()

    if current_time - last_cache_clear > cache_ttl:
        with user_cache_lock:
            messaged_users_cache.clear()
            last_cache_clear = current_time
            logger.info(f"Cleared messaged_users_cache (TTL: {cache_ttl}s)")

def add_to_permanent_blacklist(user_id, channel_id=None):
    """Add user to permanent blacklist across all sessions"""
    with user_cache_lock:
        permanent_user_blacklist.add(user_id)
        if channel_id:
            messaged_users_cache[(channel_id, user_id)] = True
        logger.debug(f"Added user {user_id} to permanent blacklist")

def is_user_in_blacklist(user_id):
    """Quick check if user is in permanent blacklist"""
    return user_id in permanent_user_blacklist

def try_claim_user(session_id, user_id, account_id):
    if not session_id:
        return True, None
    
    with messaging_lock:
        if user_id in global_messaged_users.get(session_id, set()):
            return False, "already_messaged_in_session"
        
        if user_id in currently_messaging:
            other_session, other_account = currently_messaging[user_id]
            return False, f"currently_messaging_by_account_{other_account}"
        
        currently_messaging[user_id] = (session_id, account_id)
        return True, None

def release_user(user_id, mark_as_sent=False, session_id=None):
    if not session_id:
        return
    
    with messaging_lock:
        if user_id in currently_messaging:
            sid, _ = currently_messaging[user_id]
            del currently_messaging[user_id]
            
            if mark_as_sent and session_id:
                if session_id not in global_messaged_users:
                    global_messaged_users[session_id] = set()
                global_messaged_users[session_id].add(user_id)


def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if 'authenticated' not in session or not session['authenticated']:
            logger.warning(f"Unauthorized access attempt to {f.__name__} from IP: {request.remote_addr}")
            return jsonify({
                'success': False,
                'message': 'Session expired. Please refresh the page and login again.',
                'redirect': '/login'
            }), 401
        return f(*args, **kwargs)
    return decorated_function

SESSION_FOLDER = 'source'
PASSWORD_FILE = 'password.txt'
CONFIG_FILE = 'config.json'

if not os.path.exists(SESSION_FOLDER):
    os.makedirs(SESSION_FOLDER)

DEFAULT_CONFIG = {
    'min_delay': 15,
    'max_delay': 25,
    'typing_duration': 3,
    'daily_message_limit': 500,
    'session_break_after': 20,
    'session_break_duration': 40,
    'max_retries': 3,
    'retry_delay_multiplier': 3,
    'enable_typing': True,
    'enable_rate_limiting': True,
    'flood_wait_extra_time': 60,
    'connection_retry_attempts':9
}

def load_config():
    try:
        if os.path.exists(CONFIG_FILE):
            with open(CONFIG_FILE, 'r') as f:
                config = {**DEFAULT_CONFIG, **json.load(f)}
                logger.info(f"Config loaded from file: {CONFIG_FILE}")
                return config
        logger.info(f"Using default config")
        return DEFAULT_CONFIG
    except Exception as e:
        logger.error(f"Error loading config: {str(e)}", exc_info=True)
        return DEFAULT_CONFIG

def save_config(config):
    try:
        with open(CONFIG_FILE, 'w') as f:
            json.dump(config, f, indent=4)
        logger.info(f"Config saved to file: {CONFIG_FILE}")
    except Exception as e:
        logger.error(f"Error saving config: {str(e)}", exc_info=True)

def load_credentials():
    credentials = {}
    
    try:
        if os.path.exists(PASSWORD_FILE):
            with open(PASSWORD_FILE, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    line = line.strip()
                    if ':' in line:
                        key, value = line.split(':', 1)
                        key = key.strip().lower()
                        if key == 'username':
                            credentials['login'] = value.strip()
                        elif key == 'password':
                            credentials['password'] = value.strip()
                        else:
                            credentials[key] = value.strip()
            logger.info(f"Credentials loaded from {PASSWORD_FILE}")
    except Exception as e:
        logger.error(f"Error loading credentials from file: {str(e)}", exc_info=True)
    
    if not credentials:
        username = os.environ.get('LOGIN_USERNAME')
        password = os.environ.get('LOGIN_PASSWORD')
        if username and password:
            credentials['login'] = username
            credentials['password'] = password
            logger.info(f"Credentials loaded from environment variables")
    
    return credentials

class ActivityLog(db.Model):
    __tablename__ = 'activity_log'
    
    id = db.Column(db.Integer, primary_key=True)
    proxy_id = db.Column(db.Integer, db.ForeignKey('proxy.id'), nullable=True, index=True)
    proxy = db.relationship('Proxy', backref='accounts', lazy=True)
    timestamp = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)
    user = db.Column(db.String(100))
    action = db.Column(db.String(200), nullable=False)
    details = db.Column(db.Text)
    ip_address = db.Column(db.String(50))
    status = db.Column(db.String(20))

class SystemLog(db.Model):
    __tablename__ = 'system_log'
    
    id = db.Column(db.Integer, primary_key=True)
    timestamp = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)
    level = db.Column(db.String(20), nullable=False, index=True)
    component = db.Column(db.String(100))
    message = db.Column(db.Text, nullable=False)
    account_id = db.Column(db.Integer)
    user_id = db.Column(db.BigInteger)
    error_details = db.Column(db.Text)

class TelegramAccount(db.Model):
    __tablename__ = 'telegram_account'
    
    id = db.Column(db.Integer, primary_key=True)
    phone = db.Column(db.String(20), nullable=False, unique=True, index=True)
    session_file = db.Column(db.String(200), nullable=True)
    session_string = db.Column(db.Text, nullable=True)
    api_id = db.Column(db.String(50), nullable=False)
    api_hash = db.Column(db.String(100), nullable=False)
    account_name = db.Column(db.String(200))
    daily_limit = db.Column(db.Integer, default=500)
    is_active = db.Column(db.Boolean, default=True)
    last_session_check = db.Column(db.DateTime)
    session_status = db.Column(db.String(20))
    proxy_id = db.Column(db.Integer, db.ForeignKey('proxy.id'), nullable=True)
    channels = db.relationship('Channel', backref='account', lazy=True, cascade='all, delete-orphan')
    message_history = db.relationship('MessageHistory', backref='account', lazy=True, cascade='all, delete-orphan')
    daily_stats = db.relationship('DailyStats', backref='account', lazy=True, cascade='all, delete-orphan')
    created_at = db.Column(db.DateTime, default=datetime.utcnow)


class Proxy(db.Model):
    __tablename__ = 'proxy'
    
    id = db.Column(db.Integer, primary_key=True)
    host = db.Column(db.String(100), nullable=False)
    port = db.Column(db.Integer, nullable=False)
    username = db.Column(db.String(100))
    password = db.Column(db.String(100))
    protocol = db.Column(db.String(10), default='socks5')
    status = db.Column(db.String(20), default='unknown')
    last_checked = db.Column(db.DateTime)
    response_time = db.Column(db.Float)
    created_at = db.Column(db.DateTime, default=datetime.utcnow)
    is_active = db.Column(db.Boolean, default=True)
    location = db.Column(db.String(100))
    country = db.Column(db.String(50))
    country_code = db.Column(db.String(5))
    city = db.Column(db.String(100))
    
    def to_dict(self):
        return {
            'id': self.id,
            'host': self.host,
            'port': self.port,
            'username': self.username,
            'has_auth': bool(self.username and self.password),
            'protocol': self.protocol,
            'status': self.status,
            'last_checked': self.last_checked.isoformat() if self.last_checked else None,
            'response_time': self.response_time,
            'is_active': self.is_active,
            'created_at': self.created_at.isoformat() if self.created_at else None,
            'location': self.location,
            'country': self.country,
            'country_code': self.country_code,
            'city': self.city
        }
    
    def get_proxy_url(self):
        if self.username and self.password:
            return f"{self.protocol}://{self.username}:{self.password}@{self.host}:{self.port}"
        return f"{self.protocol}://{self.host}:{self.port}"

class Channel(db.Model):
    __tablename__ = 'channel'
    
    id = db.Column(db.Integer, primary_key=True)
    account_id = db.Column(db.Integer, db.ForeignKey('telegram_account.id'), nullable=False, index=True)
    channel_id = db.Column(db.String(100), nullable=False, index=True)
    channel_name = db.Column(db.String(200))
    created_at = db.Column(db.DateTime, default=datetime.utcnow)

class MessageHistory(db.Model):
    __tablename__ = 'message_history'
    
    id = db.Column(db.Integer, primary_key=True)
    account_id = db.Column(db.Integer, db.ForeignKey('telegram_account.id'), nullable=False, index=True)
    channel_id = db.Column(db.String(100), nullable=False, index=True)
    user_id = db.Column(db.BigInteger, nullable=False, index=True)
    user_name = db.Column(db.String(200))
    user_username = db.Column(db.String(200))
    message_sent = db.Column(db.Text, nullable=False)
    sent_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False, index=True)
    success = db.Column(db.Boolean, default=True, index=True)
    error_message = db.Column(db.Text)
    retry_count = db.Column(db.Integer, default=0)
    
    __table_args__ = (
        Index('idx_account_user', 'account_id', 'user_id'),
        Index('idx_channel_user', 'channel_id', 'user_id'),
        Index('idx_account_channel_user', 'account_id', 'channel_id', 'user_id'),
    )

class DailyStats(db.Model):
    __tablename__ = 'daily_stats'
    
    id = db.Column(db.Integer, primary_key=True)
    account_id = db.Column(db.Integer, db.ForeignKey('telegram_account.id'), nullable=False, index=True)
    date = db.Column(db.Date, default=datetime.utcnow().date, nullable=False, index=True)
    messages_sent = db.Column(db.Integer, default=0, nullable=False)
    messages_failed = db.Column(db.Integer, default=0, nullable=False)
    unique_users = db.Column(db.Integer, default=0)
    
    __table_args__ = (
        Index('idx_account_date', 'account_id', 'date', unique=True),
    )

class ActiveTask(db.Model):
    __tablename__ = 'active_task'

    id = db.Column(db.Integer, primary_key=True)
    account_id = db.Column(db.Integer, db.ForeignKey('telegram_account.id'), nullable=False, index=True)
    task_type = db.Column(db.String(50), nullable=False)
    account_name = db.Column(db.String(200))
    started_at = db.Column(db.DateTime, default=datetime.utcnow, nullable=False)
    session_id = db.Column(db.String(100))
    message = db.Column(db.Text)
    skip_sent = db.Column(db.Boolean, default=False)
    user_count_limit = db.Column(db.Integer)
    is_completed = db.Column(db.Boolean, default=False)  # Track if account completed
    completed_at = db.Column(db.DateTime)  # When it completed
    stop_requested = db.Column(db.Boolean, default=False)  # Database-persisted stop signal (survives Railway restarts!)
    
    def to_dict(self):
        return {
            'account_id': self.account_id,
            'task_type': self.task_type,
            'account_name': self.account_name,
            'started_at': self.started_at.strftime('%Y-%m-%d %H:%M:%S'),
            'session_id': self.session_id,
            'message': self.message,
            'skip_sent': self.skip_sent,
            'user_count_limit': self.user_count_limit
        }

with app.app_context():
    try:
        logger.info("Checking database schema...")
        
        inspector = db.inspect(db.engine)
        
        if inspector.has_table('telegram_account'):
            columns = [col['name'] for col in inspector.get_columns('telegram_account')]
            
            if 'proxy_id' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE telegram_account ADD COLUMN proxy_id INTEGER'))
                        conn.commit()
                        logger.info("Added 'proxy_id' column")
                except Exception as e:
                    logger.warning(f"Could not add proxy_id column: {str(e)}")
            
            if 'last_active' in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE telegram_account DROP COLUMN IF EXISTS last_active'))
                        conn.commit()
                        logger.info("Removed deprecated 'last_active' column")
                except Exception as e:
                    logger.warning(f"Could not remove column: {str(e)}")
            
            if 'is_active' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE telegram_account ADD COLUMN is_active BOOLEAN DEFAULT TRUE'))
                        conn.commit()
                        logger.info("Added 'is_active' column")
                except Exception as e:
                    logger.warning(f"Could not add is_active column: {str(e)}")
            
            if 'last_session_check' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE telegram_account ADD COLUMN last_session_check TIMESTAMP'))
                        conn.commit()
                        logger.info("Added 'last_session_check' column")
                except Exception as e:
                    logger.warning(f"Could not add last_session_check column: {str(e)}")
            
            if 'session_status' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE telegram_account ADD COLUMN session_status VARCHAR(20)'))
                        conn.commit()
                        logger.info("Added 'session_status' column")
                except Exception as e:
                    logger.warning(f"Could not add session_status column: {str(e)}")
        
        if inspector.has_table('message_history'):
            columns = [col['name'] for col in inspector.get_columns('message_history')]
            
            if 'user_username' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE message_history ADD COLUMN user_username VARCHAR(200)'))
                        conn.commit()
                        logger.info("Added 'user_username' column to message_history")
                except Exception as e:
                    logger.warning(f"Could not add user_username column: {str(e)}")
            
            if 'retry_count' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE message_history ADD COLUMN retry_count INTEGER DEFAULT 0'))
                        conn.commit()
                        logger.info("Added 'retry_count' column to message_history")
                except Exception as e:
                    logger.warning(f"Could not add retry_count column: {str(e)}")
        
        if inspector.has_table('daily_stats'):
            columns = [col['name'] for col in inspector.get_columns('daily_stats')]

            if 'unique_users' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE daily_stats ADD COLUMN unique_users INTEGER DEFAULT 0'))
                        conn.commit()
                        logger.info("Added 'unique_users' column to daily_stats")
                except Exception as e:
                    logger.warning(f"Could not add unique_users column: {str(e)}")

        # Add new completion tracking fields to active_task table
        if inspector.has_table('active_task'):
            columns = [col['name'] for col in inspector.get_columns('active_task')]

            if 'is_completed' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE active_task ADD COLUMN is_completed BOOLEAN DEFAULT FALSE'))
                        conn.commit()
                        logger.info("Added 'is_completed' column to active_task")
                except Exception as e:
                    logger.warning(f"Could not add is_completed column: {str(e)}")

            if 'completed_at' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE active_task ADD COLUMN completed_at TIMESTAMP'))
                        conn.commit()
                        logger.info("Added 'completed_at' column to active_task")
                except Exception as e:
                    logger.warning(f"Could not add completed_at column: {str(e)}")

            # CRITICAL: Database-persisted stop signal (survives Railway restarts!)
            if 'stop_requested' not in columns:
                try:
                    with db.engine.connect() as conn:
                        conn.execute(db.text('ALTER TABLE active_task ADD COLUMN stop_requested BOOLEAN DEFAULT FALSE'))
                        conn.commit()
                        logger.info("✅ Added 'stop_requested' column to active_task - Database-persisted stop signals enabled!")
                except Exception as e:
                    logger.warning(f"Could not add stop_requested column: {str(e)}")

        db.create_all()
        logger.info("Database tables ready")
        
        account_count = TelegramAccount.query.count()
        channel_count = Channel.query.count()
        history_count = MessageHistory.query.count()
        
        logger.info(f"Database statistics: Accounts: {account_count}, Channels: {channel_count}, History: {history_count}")
        
        if account_count > 0:
            accounts = TelegramAccount.query.all()
            for account in accounts:
                if account.is_active is None:
                    account.is_active = True
                if account.session_status is None:
                    account.session_status = 'unknown'
            db.session.commit()
            logger.info(f"Updated {account_count} accounts with default values")
        
    except Exception as e:
        logger.error(f"Error during database initialization: {str(e)}", exc_info=True)
        db.session.rollback()

def log_activity(action, details=None, status='success'):
    try:
        with app.app_context():
            activity = ActivityLog(
                user=session.get('username', 'system'),
                action=action,
                details=details,
                ip_address=request.remote_addr if request else None,
                status=status
            )
            db.session.add(activity)
            db.session.commit()
            
            activity_log_queue.put({
                'timestamp': activity.timestamp.isoformat(),
                'user': activity.user,
                'action': action,
                'details': details,
                'status': status
            })
    except Exception as e:
        logger.error(f"Error logging activity: {str(e)}")

def log_system(level, message, component=None, account_id=None, user_id=None, error_details=None):
    try:
        with app.app_context():
            sys_log = SystemLog(
                level=level,
                component=component,
                message=message,
                account_id=account_id,
                user_id=user_id,
                error_details=error_details
            )
            db.session.add(sys_log)
            db.session.commit()
            
            global_log_queue.put({
                'timestamp': sys_log.timestamp.isoformat(),
                'level': level,
                'component': component or 'system',
                'message': message,
                'account_id': account_id,
                'error': error_details
            })
    except Exception as e:
        logger.error(f"Error logging system event: {str(e)}")

def load_session_string(session_file=None, account=None):
    try:
        if account and account.session_string:
            return account.session_string
        
        if session_file:
            session_path = os.path.join(SESSION_FOLDER, session_file)
            if os.path.exists(session_path):
                with open(session_path, 'r') as f:
                    return f.read()
        
        return None
    except Exception as e:
        logger.error(f"Error loading session: {str(e)}", exc_info=True)
        log_system('ERROR', f'Session load failed: {str(e)}', 'session_manager', error_details=str(e))
        return None

def process_message(message, user_name):
    import re
    try:
        if not message:
            return ""
        processed_message = str(message)
        processed_message = processed_message.replace('{name}', user_name)
        pattern = r'\{([^}]+?)\s*->\s*(https?://[^\s}]+)\}'
        def replace_link(match):
            text = match.group(1).strip()
            url = match.group(2).strip()
            return f'<a href="{url}">{text}</a>'
        processed_message = re.sub(pattern, replace_link, processed_message)
        return processed_message
    except Exception as e:
        logger.error(f"Error processing message: {str(e)}", exc_info=True)
        return message

def get_daily_message_count(account_id):
    try:
        with app.app_context():
            today = datetime.utcnow().date()
            stat = DailyStats.query.filter_by(account_id=account_id, date=today).first()
            return stat.messages_sent if (stat and stat.messages_sent is not None) else 0
    except Exception as e:
        logger.error(f"Error getting daily message count: {str(e)}", exc_info=True)
        return 0

def increment_daily_stats(account_id, success=True):
    max_retries = 3
    for attempt in range(max_retries):
        try:
            with app.app_context():
                today = datetime.utcnow().date()
                stat = DailyStats.query.filter_by(account_id=account_id, date=today).with_for_update().first()
                
                if not stat:
                    stat = DailyStats(account_id=account_id, date=today, messages_sent=0, messages_failed=0, unique_users=0)
                    db.session.add(stat)
                
                if stat.messages_sent is None:
                    stat.messages_sent = 0
                if stat.messages_failed is None:
                    stat.messages_failed = 0
                
                if success:
                    stat.messages_sent += 1
                else:
                    stat.messages_failed += 1
                
                db.session.commit()
                return
        except Exception as e:
            logger.error(f"Error incrementing stats (attempt {attempt + 1}): {str(e)}", exc_info=True)
            db.session.rollback()
            if attempt < max_retries - 1:
                time.sleep(1)

def has_user_been_messaged(account_id, channel_id, user_id):
    """
    IMPROVED: Check if user has been messaged by ANY account (not just this one)
    Uses cache for performance optimization
    """
    try:
        # Quick blacklist check first
        if is_user_in_blacklist(user_id):
            logger.debug(f"User {user_id} found in permanent blacklist (quick check)")
            return True

        # Check cache
        cache_key = (channel_id, user_id)
        with user_cache_lock:
            if cache_key in messaged_users_cache:
                logger.debug(f"User {user_id} found in cache for channel {channel_id}")
                return messaged_users_cache[cache_key]

        # Database check - NOW CHECKS ALL ACCOUNTS, NOT JUST THIS ONE!
        with app.app_context():
            exists = MessageHistory.query.filter_by(
                # account_id=account_id,  ← REMOVED! Now checks ALL accounts
                channel_id=channel_id,
                user_id=user_id,
                success=True
            ).first()

            result = exists is not None

            # Update cache
            with user_cache_lock:
                messaged_users_cache[cache_key] = result

            # Add to permanent blacklist if messaged
            if result:
                add_to_permanent_blacklist(user_id, channel_id)
                logger.info(f"✅ User {user_id} has been messaged before by ANY account in channel {channel_id}")

            return result

    except Exception as e:
        logger.error(f"Error checking message history: {str(e)}")
        return False

@app.route('/')
def index():
    logger.info(f"Index page accessed from IP: {request.remote_addr}")
    if 'authenticated' in session and session['authenticated']:
        return redirect(url_for('dashboard'))
    return render_template('index.html')

@app.route('/health')
def health():
    try:
        db.session.execute(db.text('SELECT 1'))
        db_status = 'connected'
        
        account_count = TelegramAccount.query.count()
        active_accounts = TelegramAccount.query.filter_by(is_active=True).count()
        channel_count = Channel.query.count()
        history_count = MessageHistory.query.count()
        
        return jsonify({
            'status': 'healthy',
            'database': db_status,
            'accounts': account_count,
            'active_accounts': active_accounts,
            'channels': channel_count,
            'message_history': history_count,
            'timestamp': datetime.utcnow().isoformat()
        }), 200
    except Exception as e:
        logger.error(f"Health check failed: {str(e)}", exc_info=True)
        return jsonify({
            'status': 'unhealthy',
            'error': str(e),
            'timestamp': datetime.utcnow().isoformat()
        }), 503

@app.route('/debug/accounts')
def debug_accounts():
    try:
        accounts = TelegramAccount.query.all()
        result = []
        for acc in accounts:
            result.append({
                'id': acc.id,
                'phone': acc.phone,
                'account_name': acc.account_name,
                'has_session_string': bool(acc.session_string),
                'session_string_length': len(acc.session_string) if acc.session_string else 0,
                'is_active': acc.is_active,
                'session_status': acc.session_status,
                'channels_count': len(acc.channels),
                'created_at': acc.created_at.isoformat() if acc.created_at else None
            })
        
        return jsonify({
            'success': True,
            'count': len(result),
            'accounts': result
        }), 200
    except Exception as e:
        logger.error(f"Debug accounts failed: {str(e)}", exc_info=True)
        return jsonify({
            'success': False,
            'error': str(e)
        }), 500

@app.route('/login', methods=['POST'])
def login():
    try:
        data = request.json
        username = data.get('username')
        password = data.get('password')
        
        credentials = load_credentials()
        
        if credentials.get('login') == username and credentials.get('password') == password:
            session.permanent = True
            session['authenticated'] = True
            session['username'] = username
            session['login_time'] = datetime.utcnow().isoformat()
            
            log_activity('LOGIN', f'User {username} logged in', 'success')
            logger.info(f"Login successful for user: {username}")
            
            return jsonify({'success': True, 'message': 'Login successful'})
        
        log_activity('LOGIN_FAILED', f'Failed login attempt for {username}', 'failed')
        logger.warning(f"Failed login attempt for username: {username}")
        
        return jsonify({'success': False, 'message': 'Invalid username or password'}), 401
    except Exception as e:
        logger.error(f"Login error: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': 'An error occurred'}), 500

@app.route('/logout')
def logout():
    username = session.get('username', 'Unknown')
    log_activity('LOGOUT', f'User {username} logged out')
    session.clear()
    return redirect(url_for('index'))

@app.route('/dashboard')
def dashboard():
    if 'authenticated' not in session or not session['authenticated']:
        return redirect(url_for('index'))
    return render_template('dashboard.html')


@app.route('/add_account', methods=['POST'])
@login_required
def add_account():
    data = request.json
    phone = data.get('phone')
    account_name = data.get('account_name')
    api_id = data.get('api_id')
    api_hash = data.get('api_hash')
    code = data.get('code')
    password = data.get('password')
    proxy_id = data.get('proxy_id')

    if not all([phone, api_id, api_hash]):
        return jsonify({'success': False, 'message': 'Missing required fields'}), 400

    phone_code_hash = session.get('phone_code_hash')
    temp_session = session.get('temp_session')
    temp_account_name = session.get('temp_account_name')
    temp_proxy_id = session.get('temp_proxy_id')

    if not phone_code_hash:
        return jsonify({
            'success': False,
            'message': 'Verification code expired. Please click "Send Code" again.'
        }), 400

    final_account_name = account_name if account_name else temp_account_name
    final_proxy_id = proxy_id if proxy_id else temp_proxy_id
    
    try:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        result = loop.run_until_complete(create_telegram_session(phone, api_id, api_hash, phone_code_hash, temp_session, code, password, final_proxy_id))
        loop.close()
        
        if result['success']:
            session_filename = f"{phone.replace('+', '')}.session"
            session_path = os.path.join(SESSION_FOLDER, session_filename)
            
            try:
                with open(session_path, 'w') as f:
                    f.write(result['session_string'])
            except Exception as e:
                logger.warning(f"Could not write session file: {str(e)}")
            
            existing_account = TelegramAccount.query.filter_by(phone=phone).first()
            if existing_account:
                existing_account.session_string = result['session_string']
                existing_account.api_id = api_id
                existing_account.api_hash = api_hash
                existing_account.account_name = final_account_name or result.get('account_name', phone)
                existing_account.is_active = True
                existing_account.session_status = 'active'
                existing_account.last_session_check = datetime.utcnow()
                existing_account.proxy_id = final_proxy_id
                db.session.commit()
                new_account = existing_account
                log_activity('ACCOUNT_UPDATE', f'Updated account {phone}')
            else:
                new_account = TelegramAccount(
                    phone=phone,
                    session_file=session_filename,
                    session_string=result['session_string'],
                    api_id=api_id,
                    api_hash=api_hash,
                    account_name=final_account_name or result.get('account_name', phone),
                    daily_limit=500,
                    is_active=True,
                    session_status='active',
                    last_session_check=datetime.utcnow(),
                    proxy_id=final_proxy_id
                )
                db.session.add(new_account)
                db.session.commit()
                log_activity('ACCOUNT_ADD', f'Added new account {phone}')
            
            log_system('INFO', f'Account added/updated: {phone}', 'account_manager', account_id=new_account.id)
            
            session.pop('phone_code_hash', None)
            session.pop('temp_session', None)
            session.pop('temp_phone', None)
            session.pop('temp_account_name', None)
            session.pop('temp_api_id', None)
            session.pop('temp_api_hash', None)
            session.pop('temp_proxy_id', None)
            
            return jsonify({'success': True, 'message': 'Account added successfully', 'account_id': new_account.id})
        else:
            log_system('ERROR', f'Failed to add account {phone}: {result.get("message")}', 'account_manager', error_details=result.get('message'))
            return jsonify(result), 400
            
    except Exception as e:
        logger.error(f"Error adding account {phone}: {str(e)}", exc_info=True)
        log_system('ERROR', f'Exception adding account {phone}', 'account_manager', error_details=str(e))
        return jsonify({'success': False, 'message': f'Error: {str(e)}'}), 500

@app.route('/send_code', methods=['POST'])
@login_required
def send_code():
    data = request.json
    phone = data.get('phone')
    account_name = data.get('account_name')
    api_id = data.get('api_id')
    api_hash = data.get('api_hash')
    proxy_id = data.get('proxy_id')

    if not all([phone, api_id, api_hash]):
        return jsonify({'success': False, 'message': 'Missing required fields'}), 400

    try:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        result = loop.run_until_complete(send_verification_code(phone, api_id, api_hash, proxy_id))
        loop.close()

        if result.get('success') and result.get('phone_code_hash'):
            session['phone_code_hash'] = result['phone_code_hash']
            session['temp_session'] = result.get('temp_session')
            session['temp_phone'] = phone
            session['temp_account_name'] = account_name
            session['temp_api_id'] = api_id
            session['temp_api_hash'] = api_hash
            session['temp_proxy_id'] = proxy_id
            session.modified = True
            log_activity('SEND_CODE', f'Verification code sent to {phone}')

        return jsonify(result)
    except Exception as e:
        logger.error(f"Error sending code to {phone}: {str(e)}", exc_info=True)
        log_system('ERROR', f'Failed to send code to {phone}', 'account_manager', error_details=str(e))
        return jsonify({'success': False, 'message': f'Error: {str(e)}'}), 500

@app.route('/add_channel', methods=['POST'])
@login_required
def add_channel():
    data = request.json
    account_id = data.get('account_id')
    channel_id = data.get('channel_id')
    
    account = TelegramAccount.query.filter_by(id=account_id).first()
    
    if not account:
        return jsonify({'success': False, 'message': 'Account not found'}), 404
    
    try:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        result = loop.run_until_complete(verify_channel_admin(account, channel_id))
        loop.close()
        
        logger.info(f"Verify channel result: {result}")
        
        if result['success']:
            existing_channel = Channel.query.filter_by(account_id=account_id, channel_id=channel_id).first()
            
            channel_name = result.get('channel_name', '')
            logger.info(f"Channel name from verify: {channel_name}")
            
            if existing_channel:
                if not existing_channel.channel_name or existing_channel.channel_name != channel_name:
                    existing_channel.channel_name = channel_name
                    db.session.commit()
                    logger.info(f"Updated existing channel name to: {channel_name}")
                    return jsonify({'success': True, 'message': 'Channel updated successfully'})
                return jsonify({'success': True, 'message': 'Channel already added'})
            
            new_channel = Channel(
                account_id=account_id,
                channel_id=channel_id,
                channel_name=channel_name
            )
            db.session.add(new_channel)
            db.session.commit()
            
            logger.info(f"Added new channel: {channel_name} (ID: {channel_id})")
            log_activity('CHANNEL_ADD', f'Added channel {channel_id} to account {account.phone}')
            log_system('INFO', f'Channel added: {channel_id}', 'channel_manager', account_id=account_id)
            
            return jsonify({'success': True, 'message': 'Channel added successfully'})
        else:
            log_system('ERROR', f'Failed to verify channel {channel_id}', 'channel_manager', account_id=account_id, error_details=result.get('message'))
            return jsonify(result), 400
            
    except Exception as e:
        logger.error(f"Error adding channel {channel_id}: {str(e)}", exc_info=True)
        log_system('ERROR', f'Exception adding channel {channel_id}', 'channel_manager', account_id=account_id, error_details=str(e))
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/get_accounts')
@login_required
def get_accounts():
    try:
        accounts = TelegramAccount.query.all()
        
        accounts_data = []
        for account in accounts:
            try:
                proxy_info = None
                if hasattr(account, 'proxy_id') and account.proxy_id:
                    proxy_obj = db.session.get(Proxy, account.proxy_id)
                    if proxy_obj:
                        proxy_info = {
                            'id': proxy_obj.id,
                            'host': proxy_obj.host,
                            'port': proxy_obj.port,
                            'status': proxy_obj.status,
                            'is_active': proxy_obj.is_active
                        }
                
                account_dict = {
                    'id': account.id,
                    'phone': account.phone or '',
                    'account_name': account.account_name or account.phone or 'Unknown',
                    'daily_limit': account.daily_limit if account.daily_limit is not None else 500,
                    'is_active': account.is_active if account.is_active is not None else True,
                    'session_status': account.session_status or 'unknown',
                    'proxy': proxy_info,
                    'channels': []
                }
                
                for ch in account.channels:
                    account_dict['channels'].append({
                        'id': ch.id,
                        'channel_id': ch.channel_id or '',
                        'channel_name': ch.channel_name or ch.channel_id or 'Unknown'
                    })
                
                accounts_data.append(account_dict)
            except Exception as acc_error:
                logger.error(f"Error processing account {account.id}: {str(acc_error)}", exc_info=True)
                continue
        
        logger.info(f"Returned {len(accounts_data)} accounts")
        return jsonify({'success': True, 'accounts': accounts_data})
    except Exception as e:
        logger.error(f"Error getting accounts: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/get_active_tasks')
@login_required
def get_active_tasks():
    try:
        db_tasks = ActiveTask.query.filter_by(task_type='send_messages').all()
        tasks = []

        for db_task in db_tasks:
            task_dict = db_task.to_dict()
            tasks.append(task_dict)

            if db_task.account_id not in active_tasks or not active_tasks[db_task.account_id].get('active', False):
                active_tasks[db_task.account_id] = {
                    'active': True,
                    'task_type': db_task.task_type,
                    'started_at': db_task.started_at.strftime('%Y-%m-%d %H:%M:%S'),
                    'account_name': db_task.account_name,
                    'session_id': db_task.session_id
                }

        has_active_tasks = len(db_tasks) > 0

        return jsonify({
            'success': True,
            'tasks': tasks,
            'has_active_tasks': has_active_tasks
        })
    except Exception as e:
        logger.error(f"Error getting active tasks: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/get_pending_requests', methods=['POST'])
@login_required
def get_pending_requests():
    data = request.json
    account_ids = data.get('account_ids', [])
    
    if not account_ids:
        return jsonify({'success': False, 'message': 'No accounts selected'}), 400
    
    all_results = []
    
    for account_id in account_ids:
        try:
            account = TelegramAccount.query.filter_by(id=account_id).first()
            
            if not account:
                all_results.append({
                    'account_id': account_id,
                    'account_name': 'Unknown',
                    'success': False,
                    'message': 'Account not found'
                })
                continue
            
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            result = loop.run_until_complete(get_join_requests(account))
            loop.close()
            
            result['account_id'] = account_id
            result['account_name'] = account.account_name or account.phone
            all_results.append(result)
            
        except Exception as e:
            logger.error(f"Error getting requests for account {account_id}: {str(e)}", exc_info=True)
            log_system('ERROR', f'Failed to get requests', 'request_fetcher', account_id=account_id, error_details=str(e))
            all_results.append({
                'account_id': account_id,
                'account_name': account.account_name if account else 'Unknown',
                'success': False,
                'message': str(e)
            })
    
    log_activity('REFRESH_REQUESTS', f'Refreshed requests for {len(account_ids)} accounts')
    return jsonify({'success': True, 'results': all_results})

@app.route('/get_channel_names')
@login_required
def get_channel_names():
    try:
        channels = Channel.query.all()
        logger.info(f"Found {len(channels)} channels in database")
        
        channel_names = set()
        for ch in channels:
            logger.debug(f"Channel ID: {ch.id}, Name: {ch.channel_name}, Channel ID: {ch.channel_id}, Account ID: {ch.account_id}")
            if ch.channel_name:
                channel_names.add(ch.channel_name)
        
        channel_list = sorted(list(channel_names))
        logger.info(f"Returning {len(channel_list)} unique channel names: {channel_list}")
        
        return jsonify({'success': True, 'channel_names': channel_list})
    except Exception as e:
        logger.error(f"Error getting channel names: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/update_channel_names', methods=['POST'])
@login_required
def update_channel_names():
    try:
        channels = Channel.query.all()
        updated_count = 0
        error_count = 0
        
        for channel in channels:
            try:
                account = TelegramAccount.query.filter_by(id=channel.account_id).first()
                if not account:
                    continue
                
                if not channel.channel_name or channel.channel_name.strip() == '':
                    loop = asyncio.new_event_loop()
                    asyncio.set_event_loop(loop)
                    result = loop.run_until_complete(verify_channel_admin(account, channel.channel_id))
                    loop.close()
                    
                    if result['success'] and result.get('channel_name'):
                        channel.channel_name = result['channel_name']
                        db.session.commit()
                        updated_count += 1
                        logger.info(f"Updated channel {channel.id} name to: {result['channel_name']}")
                    else:
                        error_count += 1
                        logger.warning(f"Failed to update channel {channel.id}: {result.get('message')}")
            except Exception as e:
                error_count += 1
                logger.error(f"Error updating channel {channel.id}: {str(e)}")
                continue
        
        return jsonify({
            'success': True,
            'updated': updated_count,
            'errors': error_count,
            'message': f'Updated {updated_count} channels, {error_count} errors'
        })
    except Exception as e:
        logger.error(f"Error updating channel names: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/get_accounts_by_channel', methods=['POST'])
@login_required
def get_accounts_by_channel():
    try:
        data = request.json
        channel_name = data.get('channel_name')
        
        if not channel_name:
            return jsonify({'success': False, 'message': 'Channel name is required'}), 400
        
        channels = Channel.query.filter_by(channel_name=channel_name).all()
        account_ids = [ch.account_id for ch in channels]
        accounts = TelegramAccount.query.filter(TelegramAccount.id.in_(account_ids)).all()
        
        accounts_data = []
        for account in accounts:
            channel = next((ch for ch in channels if ch.account_id == account.id), None)
            accounts_data.append({
                'id': account.id,
                'account_name': account.account_name or account.phone,
                'phone': account.phone,
                'channel_id': channel.channel_id if channel else '',
                'is_active': account.is_active if account.is_active is not None else True
            })
        
        return jsonify({'success': True, 'accounts': accounts_data})
    except Exception as e:
        logger.error(f"Error getting accounts by channel: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/get_channel_users', methods=['POST'])
@login_required
def get_channel_users():
    try:
        data = request.json
        account_id = data.get('account_id')
        channel_name = data.get('channel_name')
        
        if not account_id or not channel_name:
            return jsonify({'success': False, 'message': 'Account ID and channel name are required'}), 400
        
        account = TelegramAccount.query.filter_by(id=account_id).first()
        if not account:
            return jsonify({'success': False, 'message': 'Account not found'}), 404
        
        channel = Channel.query.filter_by(account_id=account_id, channel_name=channel_name).first()
        if not channel:
            return jsonify({'success': False, 'message': 'Channel not found for this account'}), 404
        
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        result = loop.run_until_complete(get_join_requests_from_channel(account, channel.channel_id))
        loop.close()
        
        return jsonify(result)
    except Exception as e:
        logger.error(f"Error getting channel users: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/get_channel_users_stream', methods=['POST'])
@login_required
def get_channel_users_stream():
    try:
        data = request.json
        account_id = data.get('account_id')
        channel_name = data.get('channel_name')
        
        if not account_id or not channel_name:
            return jsonify({'success': False, 'message': 'Account ID and channel name are required'}), 400
        
        account = TelegramAccount.query.filter_by(id=account_id).first()
        if not account:
            return jsonify({'success': False, 'message': 'Account not found'}), 404
        
        channel = Channel.query.filter_by(account_id=account_id, channel_name=channel_name).first()
        if not channel:
            return jsonify({'success': False, 'message': 'Channel not found for this account'}), 404
        
        def generate():
            with app.app_context():
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                
                try:
                    async def process():
                        async for update in get_join_requests_from_channel_streaming(account, channel.channel_id):
                            yield update
                    
                    async_gen = process()
                    
                    while True:
                        try:
                            update = loop.run_until_complete(async_gen.__anext__())
                            yield f"data: {json.dumps(update)}\n\n"
                        except StopAsyncIteration:
                            break
                        except Exception as e:
                            logger.error(f"Error in stream: {str(e)}", exc_info=True)
                            break
                            
                finally:
                    loop.close()
        
        response = Response(generate(), mimetype='text/event-stream')
        response.headers['Cache-Control'] = 'no-cache'
        response.headers['X-Accel-Buffering'] = 'no'
        return response
    except Exception as e:
        logger.error(f"Error in streaming channel users: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

async def async_generator_to_list(async_gen):
    result = []
    async for item in async_gen:
        result.append(item)
    return result

@app.route('/stream_all_join_requests', methods=['POST'])
@login_required
def stream_all_join_requests():
    data = request.json
    account_ids = data.get('account_ids', [])
    
    if not account_ids:
        return jsonify({'success': False, 'message': 'No accounts selected'}), 400
    
    for account_id in account_ids:
        account = db.session.get(TelegramAccount, account_id)
        account_name = account.account_name if account else f'Account {account_id}'
        
        existing_task = ActiveTask.query.filter_by(account_id=account_id).first()
        if existing_task:
            db.session.delete(existing_task)
        
        new_task = ActiveTask(
            account_id=account_id,
            task_type='fetch_users',
            account_name=account_name,
            started_at=datetime.now()
        )
        db.session.add(new_task)
        
        active_tasks[account_id] = {
            'active': True,
            'task_type': 'fetch_users',
            'started_at': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            'account_name': account_name
        }
    
    db.session.commit()
    
    def generate():
        import threading
        from sqlalchemy.orm import scoped_session, sessionmaker
        
        with app.app_context():
            session_factory = sessionmaker(bind=db.engine)
            ThreadSafeSession = scoped_session(session_factory)
        
        log_queue = queue.Queue(maxsize=1000)
        
        def account_worker(account_id):
            try:
                with app.app_context():
                    db_session = ThreadSafeSession()
                    
                    try:
                        account = db_session.query(TelegramAccount).filter_by(id=account_id).first()
                        
                        if not account:
                            log_queue.put({
                                'account_id': account_id,
                                'type': 'error',
                                'message': f'Account {account_id} not found'
                            })
                            if account_id in active_tasks:
                                active_tasks[account_id]['active'] = False
                            return
                        
                        if account_id in active_tasks:
                            active_tasks[account_id]['account_name'] = account.account_name
                        
                        log_queue.put({
                            'account_id': account_id,
                            'account_name': account.account_name,
                            'type': 'info',
                            'message': f'Starting fetch for account: {account.account_name}'
                        })
                        
                        loop = asyncio.new_event_loop()
                        asyncio.set_event_loop(loop)
                        
                        try:
                            async_gen = get_all_join_requests_streaming(account, db_session)
                            
                            while True:
                                try:
                                    log_data = loop.run_until_complete(async_gen.__anext__())
                                    log_data['account_id'] = account_id
                                    log_data['account_name'] = account.account_name
                                    log_queue.put(log_data, timeout=5)
                                    time.sleep(0.01)
                                except StopAsyncIteration:
                                    break
                                except queue.Full:
                                    time.sleep(0.1)
                                except Exception as e:
                                    logger.error(f"Error in generator loop: {str(e)}", exc_info=True)
                                    log_queue.put({
                                        'account_id': account_id,
                                        'account_name': account.account_name,
                                        'type': 'error',
                                        'message': f'Error: {str(e)}'
                                    })
                                    break
                        finally:
                            try:
                                loop.close()
                            except:
                                pass
                    finally:
                        try:
                            db_session.close()
                        except:
                            pass
            except Exception as e:
                logger.error(f"Fatal error in worker: {str(e)}", exc_info=True)
                log_queue.put({
                    'account_id': account_id,
                    'type': 'error',
                    'message': f'Fatal error: {str(e)}'
                })
            finally:
                if account_id in active_tasks:
                    active_tasks[account_id]['active'] = False
                
                try:
                    with app.app_context():
                        db_session_cleanup = ThreadSafeSession()
                        task_to_remove = db_session_cleanup.query(ActiveTask).filter_by(account_id=account_id, task_type='fetch_users').first()
                        if task_to_remove:
                            db_session_cleanup.delete(task_to_remove)
                            db_session_cleanup.commit()
                        db_session_cleanup.close()
                except Exception as cleanup_error:
                    logger.error(f"Error cleaning up task from database: {str(cleanup_error)}")
        
        threads = []
        for account_id in account_ids:
            thread = threading.Thread(target=account_worker, args=(account_id,), daemon=False)
            thread.start()
            threads.append(thread)
        
        start_time = time.time()
        max_wait_time = 3600
        last_keepalive = time.time()
        keepalive_interval = 5
        
        while True:
            all_finished = not any(t.is_alive() for t in threads)
            
            try:
                log_data = log_queue.get(timeout=0.5)
                yield f"data: {json.dumps(log_data)}\n\n"
                last_keepalive = time.time()
            except queue.Empty:
                if all_finished:
                    break
                if time.time() - start_time > max_wait_time:
                    yield f"data: {json.dumps({'type': 'error', 'message': 'Timeout exceeded'})}\n\n"
                    break
                
                if time.time() - last_keepalive >= keepalive_interval:
                    yield f"data: {json.dumps({'type': 'keepalive'})}\n\n"
                    last_keepalive = time.time()
        
        for thread in threads:
            thread.join(timeout=5)
        
        yield f"data: {json.dumps({'type': 'all_finished'})}\n\n"
    
    return Response(generate(), mimetype='text/event-stream')

def parse_sending_pattern(pattern_str, total_accounts):
    """
    Parse sending pattern string into list of integers.
    Examples:
        "3:3:4" -> [3, 3, 4]
        "2:2:2:3:1" -> [2, 2, 2, 3, 1]
        "" or None -> [total_accounts] (all at once)
    """
    if not pattern_str or not pattern_str.strip():
        return [total_accounts]

    try:
        parts = [int(p.strip()) for p in pattern_str.split(':')]

        if any(p <= 0 for p in parts):
            raise ValueError("All pattern numbers must be positive")

        if sum(parts) != total_accounts:
            raise ValueError(f"Pattern sum ({sum(parts)}) must equal total accounts ({total_accounts})")

        logger.info(f"Parsed pattern '{pattern_str}' into stages: {parts}")
        return parts
    except Exception as e:
        logger.error(f"Error parsing pattern '{pattern_str}': {e}")
        raise ValueError(f"Invalid pattern format: {e}")


@app.route('/send_welcome_messages', methods=['POST'])
@login_required
def send_welcome_messages():
    data = request.json
    account_ids = data.get('account_ids', [])
    message = data.get('message')
    skip_sent = data.get('skip_sent', False)
    user_count_limits = data.get('user_count_limits', {})
    proxy_ids = data.get('proxy_ids', {})
    sending_pattern = data.get('sending_pattern', '')

    logger.info(f"=== NEW SENDING REQUEST ===")
    logger.info(f"Accounts: {account_ids}")
    logger.info(f"Pattern: '{sending_pattern}'")
    logger.info(f"Skip sent: {skip_sent}")

    if not account_ids:
        return jsonify({'success': False, 'message': 'No accounts selected'}), 400

    if not message:
        return jsonify({'success': False, 'message': 'Message is required'}), 400

    # Parse and validate pattern
    try:
        stage_sizes = parse_sending_pattern(sending_pattern, len(account_ids))
        logger.info(f"Staging plan: {len(stage_sizes)} stages with sizes {stage_sizes}")
    except ValueError as e:
        return jsonify({'success': False, 'message': str(e)}), 400
    
    for account_id_str, proxy_id in proxy_ids.items():
        account_id = int(account_id_str)
        if account_id in account_ids:
            account = db.session.get(TelegramAccount, account_id)
            if account and proxy_id:
                proxy = db.session.get(Proxy, proxy_id)
                if proxy and proxy.is_active:
                    account.proxy_id = proxy_id
                    db.session.commit()
                    log_system('INFO', f'Account {account_id} assigned to proxy {proxy.host}:{proxy.port}', 'proxy_manager', account_id=account_id)
    
    session['streaming_account_ids'] = account_ids
    session['streaming_message'] = message
    session['streaming_skip_sent'] = skip_sent
    session['streaming_user_count_limits'] = user_count_limits
    
    import uuid
    session_id = str(uuid.uuid4())
    register_session_start(session_id)
    
    for account_id in account_ids:
        stop_sending_flag[account_id] = False
        
        account = db.session.get(TelegramAccount, account_id)
        account_name = account.account_name if account else f'Account {account_id}'
        user_count_limit = user_count_limits.get(str(account_id), 100)
        
        existing_task = ActiveTask.query.filter_by(account_id=account_id).first()
        if existing_task:
            db.session.delete(existing_task)
        
        new_task = ActiveTask(
            account_id=account_id,
            task_type='send_messages',
            account_name=account_name,
            started_at=datetime.now(),
            session_id=session_id,
            message=message,
            skip_sent=skip_sent,
            user_count_limit=user_count_limit
        )
        db.session.add(new_task)
        
        active_tasks[account_id] = {
            'active': True,
            'task_type': 'send_messages',
            'started_at': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            'account_name': account_name,
            'session_id': session_id
        }
    
    db.session.commit()
    
    from sqlalchemy.orm import scoped_session, sessionmaker
    session_factory = sessionmaker(bind=db.engine)
    ThreadSafeSession = scoped_session(session_factory)
    

    def account_worker_for_session(account_id, user_count_limit, session_id, message, skip_sent):
        worker_name = f"Worker-{session_id}-{account_id}"

        try:
            db_session = ThreadSafeSession()

            try:
                account = db_session.query(TelegramAccount).filter_by(id=account_id).first()

                if not account:
                    # Use broadcast_log
                    broadcast_log(session_id, {
                        'account_id': account_id,
                        'type': 'error',
                        'message': f'Account {account_id} not found'
                    })
                    return

                if account_id in active_tasks:
                    active_tasks[account_id]['account_name'] = account.account_name

                separator = '\n========================================\n'
                start_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                start_msg = f'{separator}🚀 ACCOUNT START\n   • Account: {account.account_name}\n   • Phone: {account.phone}\n   • Account ID: {account_id}\n   • Session ID: {session_id}\n   • Started at: {start_time}\n   • Message limit: {user_count_limit} users\n   • Skip sent: {"Yes" if skip_sent else "No"}{separator}'

                # Use broadcast_log
                broadcast_log(session_id, {
                    'account_id': account_id,
                    'account_name': account.account_name,
                    'type': 'info',
                    'message': start_msg
                })

                logger.info(f"Worker {worker_name}: Starting account {account.account_name} (ID: {account_id}, Session: {session_id}, Limit: {user_count_limit})")

                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)

                try:
                    async_gen = send_messages_to_users_streaming(account_id, message, skip_sent, user_count_limit, session_id)

                    message_count = 0
                    while True:
                        try:
                            # 🛑 Check stop from BOTH RAM and DATABASE
                            if check_stop_flag_from_db(account_id):
                                logger.warning(f"🛑 Stop signal detected for account {account_id}")
                                broadcast_log(session_id, {
                                    'account_id': account_id,
                                    'account_name': account.account_name,
                                    'type': 'warning',
                                    'message': '⚠️ Stop signal received. Stopping...'
                                })
                                break

                            log_data = loop.run_until_complete(async_gen.__anext__())

                            log_data['account_id'] = account_id
                            log_data['account_name'] = account.account_name

                            # Use broadcast_log
                            broadcast_log(session_id, log_data)

                            if log_data.get('type') == 'success':
                                message_count += 1

                            time.sleep(0.01)

                        except StopAsyncIteration:
                            break
                        except queue.Full:
                            time.sleep(0.1)
                        except Exception as e:
                            logger.error(f"{worker_name}: Error in loop: {str(e)}", exc_info=True)
                            # Use broadcast_log
                            broadcast_log(session_id, {
                                'account_id': account_id,
                                'account_name': account.account_name,
                                'type': 'error',
                                'message': f'Error: {str(e)}'
                            })
                            break

                    end_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                    complete_msg = f'\n========================================\n✅ ACCOUNT COMPLETED\n   • Account: {account.account_name}\n   • Account ID: {account_id}\n   • Session ID: {session_id}\n   • Completed at: {end_time}\n   • Total messages sent: {message_count}\n   • Status: {"Target reached" if message_count >= user_count_limit else "Completed early"}\n========================================\n'

                    # Mark account as completed
                    with session_threads_lock:
                        if session_id not in completed_accounts:
                            completed_accounts[session_id] = {}
                        completed_accounts[session_id][account_id] = True
                        logger.info(f"Marked account {account_id} as completed for session {session_id}")

                    # Use broadcast_log
                    broadcast_log(session_id, {
                        'account_id': account_id,
                        'account_name': account.account_name,
                        'type': 'info',
                        'message': complete_msg
                    })
                    # Send account completion signal to update UI button immediately
                    broadcast_log(session_id, {
                        'account_id': account_id,
                        'account_name': account.account_name,
                        'type': 'account_complete',
                        'message': f'Account {account.account_name} completed with {message_count} messages'
                    })

                    logger.info(f"Worker {worker_name}: Completed with {message_count} messages (Session: {session_id})")
                    
                finally:
                    try:
                        loop.close()
                    except:
                        pass
                
            finally:
                try:
                    db_session.close()
                except:
                    pass
                
        except Exception as e:
            logger.error(f"{worker_name}: Fatal error: {str(e)}", exc_info=True)
            log_queue.put({
                'account_id': account_id,
                'type': 'error',
                'message': f'Fatal error: {str(e)}'
            })
        finally:
            if account_id in active_tasks:
                active_tasks[account_id]['active'] = False

            try:
                # CRITICAL FIX: Don't delete from database, mark as completed
                # This persists completion status across server restarts
                db_session_cleanup = ThreadSafeSession()
                task_to_update = db_session_cleanup.query(ActiveTask).filter_by(account_id=account_id, task_type='send_messages').first()
                if task_to_update:
                    task_to_update.is_completed = True
                    task_to_update.completed_at = datetime.utcnow()
                    db_session_cleanup.commit()
                    logger.info(f"Marked ActiveTask as completed for account {account_id}")
                db_session_cleanup.close()
            except Exception as cleanup_error:
                logger.error(f"Error marking task as completed: {str(cleanup_error)}")
    
    # Split accounts into stages based on pattern
    account_stages = []
    account_index = 0
    for stage_num, stage_size in enumerate(stage_sizes, 1):
        stage_accounts = account_ids[account_index:account_index + stage_size]
        account_stages.append((stage_num, stage_accounts))
        account_index += stage_size
        logger.info(f"Stage {stage_num}: {len(stage_accounts)} accounts - {stage_accounts}")

    # Log stage plan to UI with detailed information
    plan_details = []
    for idx, size in enumerate(stage_sizes, 1):
        plan_details.append(f'   Stage {idx}: {size} accounts')

    start_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    # Use broadcast_log
    broadcast_log(session_id, {
        'account_id': 0,
        'type': 'info',
        'message': f'\n{"=" * 60}\n🚀 STAGED SENDING PLAN\n{"=" * 60}\n   • Total Stages: {len(stage_sizes)}\n   • Pattern: {":".join(map(str, stage_sizes))}\n   • Total Accounts: {len(account_ids)}\n   • Session ID: {session_id}\n   • Started at: {start_time}\n   • Skip sent messages: {"Enabled" if skip_sent else "Disabled"}\n\n   Stage Distribution:\n' + '\n'.join(plan_details) + f'\n{"=" * 60}\n'
    })

    # Create master coordinator thread that handles staged execution
    def staged_coordinator():
        coordinator_name = f"Coordinator-{session_id}"
        logger.info(f"{coordinator_name}: Starting staged execution")

        all_threads = []

        try:
            for stage_num, stage_account_ids in account_stages:
                # Check for global stop signal
                if any(stop_sending_flag.get(aid, False) for aid in account_ids):
                    logger.warning(f"{coordinator_name}: Stop signal detected, aborting remaining stages")
                    # Use broadcast_log
                    # Use broadcast_log
                    broadcast_log(session_id, {
                        'account_id': 0,
                        'type': 'warning',
                        'message': f'\n⚠️ STOP SIGNAL RECEIVED - Aborting remaining stages\n'
                    })

                    # CRITICAL: Wait for all started worker threads to finish before breaking
                    if all_threads:
                        logger.info(f"{coordinator_name}: Waiting for {len(all_threads)} worker threads to finish...")
                        broadcast_log(session_id, {
                            'account_id': 0,
                            'type': 'info',
                            'message': f'⏳ Waiting for {len(all_threads)} active workers to stop...'
                        })
                        for thread in all_threads:
                            try:
                                thread.join(timeout=30)
                                if thread.is_alive():
                                    logger.warning(f"{coordinator_name}: Thread {thread.name} still alive after timeout")
                            except Exception as e:
                                logger.error(f"{coordinator_name}: Error waiting for thread: {e}")
                        logger.info(f"{coordinator_name}: All worker threads stopped")
                    break

                # Log stage start with detailed information
                stage_start_time = datetime.now().strftime('%H:%M:%S')
                account_details = ', '.join([str(aid) for aid in stage_account_ids])
                stage_msg = f'\n{"=" * 60}\n📍 STAGE {stage_num}/{len(stage_sizes)} STARTING\n{"=" * 60}\n   • Accounts in this stage: {len(stage_account_ids)}\n   • Account IDs: {account_details}\n   • Stage started at: {stage_start_time}\n   • Session ID: {session_id}\n   • Processing mode: Parallel (all accounts in this stage run simultaneously)\n{"=" * 60}\n'
                # Use broadcast_log
                broadcast_log(session_id, {
                    'account_id': 0,
                    'type': 'info',
                    'message': stage_msg
                })
                logger.info(f"{coordinator_name}: Starting Stage {stage_num}/{len(stage_sizes)} with {len(stage_account_ids)} accounts at {stage_start_time}")

                # Start threads for this stage (parallel within stage)
                stage_threads = []
                for account_id in stage_account_ids:
                    user_limit = user_count_limits.get(str(account_id), 100)

                    thread = threading.Thread(
                        target=account_worker_for_session,
                        args=(account_id, user_limit, session_id, message, skip_sent),
                        name=f"SendWorker-S{stage_num}-{session_id}-{account_id}",
                        daemon=False
                    )
                    thread.start()
                    stage_threads.append(thread)
                    all_threads.append(thread)

                    # Add to running_threads for session restoration tracking
                    with session_threads_lock:
                        if session_id in running_threads:
                            running_threads[session_id].append(thread)

                    logger.info(f"{coordinator_name}: Started thread for account {account_id} in stage {stage_num}")

                # Wait for all threads in this stage to complete
                logger.info(f"{coordinator_name}: Waiting for stage {stage_num} to complete...")
                for thread in stage_threads:
                    thread.join()

                # Log stage completion with timing information
                stage_end_time = datetime.now().strftime('%H:%M:%S')
                stage_complete_msg = f'\n{"=" * 60}\n✅ STAGE {stage_num}/{len(stage_sizes)} COMPLETED\n{"=" * 60}\n   • Stage completed at: {stage_end_time}\n   • Accounts processed: {len(stage_account_ids)}\n   • All threads in this stage finished successfully\n   • Session ID: {session_id}\n{"=" * 60}\n'
                # Use broadcast_log
                broadcast_log(session_id, {
                    'account_id': 0,
                    'type': 'info',
                    'message': stage_complete_msg
                })
                logger.info(f"{coordinator_name}: Stage {stage_num}/{len(stage_sizes)} completed at {stage_end_time}")

                # Brief pause between stages
                if stage_num < len(stage_sizes):
                    pause_msg = f'\n⏸️  Pausing 3 seconds before next stage...\n'
                    # Use broadcast_log
                    # Use broadcast_log
                    broadcast_log(session_id, {
                        'account_id': 0,
                        'type': 'info',
                        'message': pause_msg
                    })

                    # Use interruptible sleep to respond to stop signal
                    for _ in range(3):
                        if any(stop_sending_flag.get(aid, False) for aid in account_ids):
                            logger.warning(f"{coordinator_name}: Stop signal detected during stage pause")
                            broadcast_log(session_id, {
                                'account_id': 0,
                                'type': 'warning',
                                'message': '⚠️ Stop signal received during stage pause'
                            })
                            break
                        time.sleep(1)

            # All stages completed
            final_msg = f'\n{"=" * 60}\n🎉 ALL STAGES COMPLETED\n{"=" * 60}\nTotal Stages: {len(stage_sizes)}\nTotal Accounts: {len(account_ids)}\n{"=" * 60}\n'
            # Use broadcast_log
            broadcast_log(session_id, {
                'account_id': 0,
                'type': 'info',
                'message': final_msg
            })
            # Send completion signal to close EventSource and update UI
            broadcast_log(session_id, {
                'account_id': 0,
                'type': 'complete',
                'message': f'All {len(account_ids)} accounts completed successfully!'
            })
            logger.info(f"{coordinator_name}: All stages completed successfully")

            # Clean up running_threads on normal completion
            with session_threads_lock:
                if session_id in running_threads:
                    del running_threads[session_id]
                    logger.info(f"{coordinator_name}: Cleaned up running_threads after normal completion")

        except Exception as e:
            logger.error(f"{coordinator_name}: Error in staged execution: {e}", exc_info=True)
            # Use broadcast_log
            broadcast_log(session_id, {
                'account_id': 0,
                'type': 'error',
                'message': f'\n❌ ERROR IN STAGED EXECUTION: {str(e)}\n'
            })

        finally:
            # DON'T delete running_threads here!
            # cleanup_session (triggered by /stop_messages) will handle cleanup
            # If we delete it here, cleanup_session won't find the threads to wait for
            # and will clear stop flags while workers are still running
            logger.info(f"{coordinator_name}: Coordinator thread finished")

    # Start the coordinator thread
    coordinator_thread = threading.Thread(
        target=staged_coordinator,
        name=f"Coordinator-{session_id}",
        daemon=False
    )
    coordinator_thread.start()

    with session_threads_lock:
        running_threads[session_id] = [coordinator_thread]

    log_activity('START_SENDING', f'Started staged sending: {len(stage_sizes)} stages, {len(account_ids)} accounts total, session={session_id}')

    return jsonify({
        'success': True,
        'message': f'Staged sending started: {len(stage_sizes)} stages',
        'session_id': session_id,
        'stages': len(stage_sizes),
        'pattern': stage_sizes
    })

@app.route('/stop_messages', methods=['POST'])
@login_required
def stop_messages():
    """
    🛑 STOP ALL MESSAGES - Database-Persisted Stop Mechanism

    This endpoint sets stop signals in BOTH RAM and DATABASE to ensure
    messages stop even if Railway restarts or connections drop.
    """
    try:
        # 1. Get all active tasks
        active_tasks_list = ActiveTask.query.filter_by(task_type='send_messages').all()

        if not active_tasks_list:
            return jsonify({'success': False, 'message': 'No active sending tasks found'})

        session_id = active_tasks_list[0].session_id
        account_ids = [task.account_id for task in active_tasks_list]

        logger.info(f"🛑 STOP REQUEST: Session {session_id}, {len(account_ids)} accounts")

        # 2. Set RAM flags (fast, but lost on restart)
        for account_id in account_ids:
            stop_sending_flag[account_id] = True
            logger.info(f"✓ Set RAM stop flag for account {account_id}")

        # 3. Set DATABASE flags - CRITICAL for Railway persistence!
        for task in active_tasks_list:
            task.stop_requested = True  # ← DATABASE PERSISTENCE!
            logger.info(f"✓ Set DB stop flag for account {task.account_id}")

        db.session.commit()
        logger.info(f"✓ Committed {len(active_tasks_list)} stop flags to DATABASE")

        # 4. Send UI notification
        broadcast_log(session_id, {
            'account_id': 0,
            'type': 'warning',
            'message': f'🛑 STOP SIGNAL SENT - Stopping {len(account_ids)} account(s)...'
        })

        # 5. Wait for threads to actually stop (max 60s)
        import time
        max_wait = 60
        start_wait = time.time()

        while time.time() - start_wait < max_wait:
            time.sleep(2)

            # Check database - works even if Railway restarts
            remaining = ActiveTask.query.filter_by(
                session_id=session_id,
                task_type='send_messages',
                is_completed=False
            ).count()

            if remaining == 0:
                logger.info(f"✓ All tasks stopped in {time.time() - start_wait:.1f}s")
                break

            logger.info(f"⏳ Waiting for stop... {remaining} tasks still running")

        # 6. Mark tasks as completed
        for task in active_tasks_list:
            task.is_completed = True
            task.completed_at = datetime.utcnow()

        db.session.commit()

        # 7. Send complete signal
        broadcast_log(session_id, {
            'account_id': 0,
            'type': 'complete',
            'message': f'✅ Stopped {len(account_ids)} account(s)'
        })

        # 8. Cleanup (async)
        def cleanup():
            time.sleep(2)
            with session_threads_lock:
                if session_id in running_threads:
                    del running_threads[session_id]
                if session_id in session_log_listeners:
                    del session_log_listeners[session_id]
                if session_id in completed_accounts:
                    del completed_accounts[session_id]

            for account_id in account_ids:
                if account_id in stop_sending_flag:
                    del stop_sending_flag[account_id]

            logger.info(f"✓ Cleanup completed for session {session_id}")

        cleanup_thread = threading.Thread(target=cleanup, daemon=True)
        cleanup_thread.start()

        log_activity('STOP_ALL', f'Stopped {len(account_ids)} accounts, session={session_id}')

        return jsonify({
            'success': True,
            'message': f'Stop signal sent successfully',
            'stopped_accounts': len(account_ids)
        })

    except Exception as e:
        logger.error(f"Error in stop_messages: {e}", exc_info=True)
        db.session.rollback()
        return jsonify({'success': False, 'message': str(e)})

@app.route('/stop_account/<int:account_id>', methods=['POST'])
@login_required
def stop_account(account_id):
    """
    🛑 STOP SINGLE ACCOUNT - Database-Persisted Stop

    Sets stop signal in BOTH RAM and DATABASE for reliability.
    """
    try:
        logger.info(f"🛑 STOP REQUEST for account {account_id}")

        # 1. Set RAM flag
        stop_sending_flag[account_id] = True

        # 2. Set DATABASE flag - CRITICAL!
        task = ActiveTask.query.filter_by(
            account_id=account_id,
            task_type='send_messages'
        ).first()

        if task:
            task.stop_requested = True  # ← DATABASE PERSISTENCE!
            session_id = task.session_id
            db.session.commit()
            logger.info(f"✓ Set stop flags (RAM + DB) for account {account_id}")

            # Send UI notification
            broadcast_log(session_id, {
                'account_id': account_id,
                'type': 'warning',
                'message': '🛑 Stop signal received. Stopping...'
            })

            # Wait a bit for the thread to actually stop
            import time
            time.sleep(3)

            # Mark as completed
            task.is_completed = True
            task.completed_at = datetime.utcnow()
            db.session.commit()
            logger.info(f"✓ Marked account {account_id} as completed")

            # Check if all accounts stopped
            remaining = ActiveTask.query.filter_by(
                session_id=session_id,
                task_type='send_messages',
                is_completed=False
            ).count()

            if remaining == 0:
                logger.info(f"✓ All accounts stopped for session {session_id}")
                broadcast_log(session_id, {
                    'account_id': 0,
                    'type': 'complete',
                    'message': 'All accounts stopped'
                })

                # Cleanup
                def cleanup():
                    time.sleep(2)
                    with session_threads_lock:
                        if session_id in running_threads:
                            del running_threads[session_id]
                        if session_id in session_log_listeners:
                            del session_log_listeners[session_id]

                    if account_id in stop_sending_flag:
                        del stop_sending_flag[account_id]

                threading.Thread(target=cleanup, daemon=True).start()

        log_activity('STOP_ACCOUNT', f'Stopped account {account_id}')

        return jsonify({'success': True, 'message': f'Stop signal sent to account {account_id}'})

    except Exception as e:
        logger.error(f"Error in stop_account: {e}", exc_info=True)
        db.session.rollback()
        return jsonify({'success': False, 'message': str(e)})

@app.route('/cleanup_session', methods=['POST'])
@login_required
def cleanup_session_route():
    """Clean up completed tasks from database - called by Clear Logs button"""
    try:
        # Find any completed session tasks
        completed_tasks = ActiveTask.query.filter_by(
            task_type='send_messages',
            is_completed=True
        ).all()
        
        if not completed_tasks:
            return jsonify({'success': True, 'message': 'No completed tasks to clean up', 'cleaned': 0})
        
        # Get session IDs
        session_ids = list(set(task.session_id for task in completed_tasks))
        
        total_cleaned = 0
        for session_id in session_ids:
            count = cleanup_completed_tasks(session_id)
            total_cleaned += count
        
        return jsonify({
            'success': True,
            'message': f'Cleaned up {total_cleaned} completed tasks',
            'cleaned': total_cleaned
        })
        
    except Exception as e:
        logger.error(f"Error in cleanup_session: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)})

@app.route('/stream_messages')
@login_required
def stream_messages():
    active_tasks_list = ActiveTask.query.filter_by(task_type='send_messages').all()
    
    if not active_tasks_list:
        return Response(
            json.dumps({'type': 'error', 'message': 'No active sending tasks found'}),
            mimetype='text/event-stream'
        )
    
    session_id = active_tasks_list[0].session_id
    
    if not session_id:
        return Response(
            json.dumps({'type': 'error', 'message': 'No session ID found'}),
            mimetype='text/event-stream'
        )
    
    def generate():
        logger.info(f"Client connected to session {session_id}")

        # Create a dedicated queue for this client connection
        my_queue = queue.Queue(maxsize=5000)
        
        with session_threads_lock:
            if session_id not in session_log_listeners:
                session_log_listeners[session_id] = []
            session_log_listeners[session_id].append(my_queue)
            
            # Get threads reference
            threads = running_threads.get(session_id, [])

        # 1. Send Log History first (Catch up)
        with session_threads_lock:
            history = session_log_history.get(session_id, [])
            for msg in history:
                 yield f"data: {json.dumps(msg)}\n\n"

        log_queue = my_queue # alias for the loop below

        # Send current session state for reconnecting clients
        try:
            with app.app_context():
                # Query accounts for this session to check state
                # We need all accounts initially to determine if session is completed
                all_session_tasks = ActiveTask.query.filter_by(
                    session_id=session_id, 
                    task_type='send_messages'
                ).all()
                
                # Filter for UI display: only show incomplete ones OR all if all are completed
                # If we show nothing, the user can't see the "Clear Logs" button
                is_session_fully_done = all(t.is_completed for t in all_session_tasks) if all_session_tasks else False
                
                if is_session_fully_done:
                    active_accounts = all_session_tasks
                    logger.info(f"Session {session_id} is fully done. Showing all {len(active_accounts)} tasks.")
                else:
                    active_accounts = [t for t in all_session_tasks if not t.is_completed]
                    logger.info(f"Session {session_id} is active. Showing {len(active_accounts)} incomplete tasks.")
                logger.info(f"Sending current state: {len(active_accounts)} accounts for session {session_id}")

                # Check if session is still active
                # Session is active if it exists in running_threads (managed by coordinator)
                with session_threads_lock:
                    session_exists = session_id in running_threads
                    threads = running_threads.get(session_id, [])
                    alive_threads = [t for t in threads if t.is_alive()] if threads else []
                    logger.info(f"Session {session_id} status: exists={session_exists}, total threads={len(threads)}, alive threads={len(alive_threads)}")

                # Check for incomplete tasks
                incomplete_tasks = [t for t in active_accounts if not t.is_completed]
                
                if not session_exists and incomplete_tasks:
                    logger.warning(f"Session {session_id} has {len(incomplete_tasks)} incomplete tasks but no worker threads - server was likely restarted")
                    # DISABLED AUTO-KILL: To prevent "All Done" on refresh if there's a race condition or worker config issue.
                    # Tasks will remain "Active" (but stalled) if threads are truly dead.
                    # For now, just warn the user.
                    yield f"data: {json.dumps({'type': 'warning', 'message': '⚠️ Connection to background process lost. Logs may stop updating.'})}\n\n"
             
                 # Check for global completion on reconnection
                # logic: if session exists in DB (active_accounts not empty) AND all are completed
                # Status message
                yield f"data: {json.dumps({'type': 'info', 'message': f'Syncing state for session {session_id}...'})}\n\n"

                # Debug log for queue status (Removed shared queue size check)
                if session_exists:
                    queue_size = my_queue.qsize()
                    logger.info(f"Stream debug: Session {session_id} exists. Queue size: {queue_size}")
                    # Send a debug message to frontend console (invisible to user but visible in console)
                    yield f"data: {json.dumps({'type': 'debug', 'message': f'Server state: Threads={len(threads)}, Locked={len(alive_threads)}, Queue={queue_size}'})}\n\n"

                for task in active_accounts:
                    # Read completion status from database (may have been updated above)
                    is_completed = task.is_completed or False

                    # Send account_info to recreate UI for each account
                    account_info = {
                        'account_id': task.account_id,
                        'account_name': task.account_name,
                        'type': 'account_info',
                        'message': f'Account {task.account_name} {"completed" if is_completed else "is active"}',
                        'started_at': task.started_at.strftime('%Y-%m-%d %H:%M:%S') if task.started_at else 'N/A',
                        'is_completed': is_completed  # From database, survives server restart!
                    }
                    yield f"data: {json.dumps(account_info)}\n\n"
                    # logger.info(f"Sent account_info for account {task.account_id} ({task.account_name}), completed={is_completed}")
                
                # REPLAY LOG HISTORY for this session
                # This ensures reconnecting clients see all previous logs
                with session_threads_lock:
                    if session_id in session_log_history:
                        history = session_log_history[session_id]
                        logger.info(f"Replaying {len(history)} log entries for session {session_id}")
                        for log_entry in history:
                            yield f"data: {json.dumps(log_entry)}\n\n"
                    else:
                        logger.info(f"No log history found for session {session_id}")
                
                # Check for global completion on reconnection AFTER sending info and history
                # logic: if all tasks for this session are completed
                if active_accounts and all(t.is_completed for t in active_accounts):
                     logger.info(f"Session {session_id} is fully completed (sync). Sending complete signal.")
                     yield f"data: {json.dumps({'type': 'complete', 'message': 'Session state restored. All tasks completed.'})}\n\n"
                        
        except Exception as e:
            logger.error(f"Error sending current session state: {str(e)}", exc_info=True)

        start_time = time.time()
        max_wait_time = 7200
        last_keepalive = time.time()
        keepalive_interval = 5  # Reduced to 5 seconds for faster stale connection detection

        while True:
            with session_threads_lock:
                threads = running_threads.get(session_id, [])

            all_finished = not any(t.is_alive() for t in threads) if threads else False

            try:
                # Reduced timeout to 0.1s for faster keepalive checks
                log_data = log_queue.get(timeout=0.1)
                yield f"data: {json.dumps(log_data)}\n\n"
                last_keepalive = time.time()
            except queue.Empty:
                if all_finished and threads:
                    logger.info(f"All threads finished for session {session_id}")
                    # Don't send complete signal here - coordinator will send it
                    break
                if time.time() - start_time > max_wait_time:
                    yield f"data: {json.dumps({'type': 'error', 'message': 'Timeout exceeded'})}\n\n"
                    break

                if time.time() - last_keepalive >= keepalive_interval:
                    yield f"data: {json.dumps({'type': 'keepalive'})}\n\n"
                    last_keepalive = time.time()

            except Exception as e:
                logger.error(f"Error in stream gen: {e}")
                break

        # Cleanup this client's queue
        with session_threads_lock:
            if session_id in session_log_listeners and my_queue in session_log_listeners[session_id]:
                session_log_listeners[session_id].remove(my_queue)
                
        logger.info(f"Client disconnected from connection pool {session_id}")
    
    response = Response(generate(), mimetype='text/event-stream')
    response.headers['Cache-Control'] = 'no-cache'
    response.headers['X-Accel-Buffering'] = 'no'
    return response

@app.route('/delete_account/<int:account_id>', methods=['DELETE'])
@login_required
def delete_account(account_id):
    try:
        account = TelegramAccount.query.filter_by(id=account_id).first()
        
        if not account:
            return jsonify({'success': False, 'message': 'Account not found'}), 404
        
        phone = account.phone
        session_path = os.path.join(SESSION_FOLDER, account.session_file)
        if os.path.exists(session_path):
            try:
                os.remove(session_path)
            except Exception as e:
                logger.warning(f"Could not delete session file: {str(e)}")
        
        db.session.delete(account)
        db.session.commit()
        
        log_activity('ACCOUNT_DELETE', f'Deleted account {phone}')
        log_system('INFO', f'Account deleted: {phone}', 'account_manager', account_id=account_id)
        
        return jsonify({'success': True, 'message': 'Account deleted successfully'})
    except Exception as e:
        logger.error(f"Error deleting account {account_id}: {str(e)}", exc_info=True)
        db.session.rollback()
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/delete_channel/<int:channel_id>', methods=['DELETE'])
@login_required
def delete_channel(channel_id):
    try:
        channel = Channel.query.filter_by(id=channel_id).first()
        
        if not channel:
            return jsonify({'success': False, 'message': 'Channel not found'}), 404
        
        channel_name = channel.channel_name
        db.session.delete(channel)
        db.session.commit()
        
        log_activity('CHANNEL_DELETE', f'Deleted channel {channel_name}')
        
        return jsonify({'success': True, 'message': 'Channel deleted successfully'})
    except Exception as e:
        logger.error(f"Error deleting channel {channel_id}: {str(e)}", exc_info=True)
        db.session.rollback()
        return jsonify({'success': False, 'message': str(e)}), 500

@app.route('/check_account_status/<int:account_id>', methods=['POST'])
@login_required
def check_account_status(account_id):
    try:
        account = TelegramAccount.query.filter_by(id=account_id).first()
        
        if not account:
            return jsonify({'success': False, 'message': 'Account not found'}), 404
        
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        result = loop.run_until_complete(verify_session_status(account))
        loop.close()
        
        account.session_status = result.get('status')
        account.last_session_check = datetime.utcnow()
        db.session.commit()
        
        log_activity('CHECK_STATUS', f'Checked status for {account.phone}: {result.get("status")}')
        
        return jsonify(result)
    except Exception as e:
        logger.error(f"Error checking account {account_id} status: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500


async def send_verification_code(phone, api_id, api_hash, proxy_id=None):
    proxy_dict = None
    if proxy_id:
        proxy_obj = db.session.get(Proxy, proxy_id)
        if proxy_obj and proxy_obj.is_active:
            import socks
            if proxy_obj.protocol == 'socks5':
                proxy_type = socks.SOCKS5
            elif proxy_obj.protocol == 'socks4':
                proxy_type = socks.SOCKS4
            else:
                proxy_type = socks.HTTP
            
            username = proxy_obj.username.strip() if proxy_obj.username and proxy_obj.username.strip() else None
            password = proxy_obj.password.strip() if proxy_obj.password and proxy_obj.password.strip() else None
            
            if username and password:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port, True, username, password)
                logger.info(f"Using proxy {proxy_obj.host}:{proxy_obj.port} with auth (user: {username}, pass_len: {len(password)})")
            else:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port)
                logger.info(f"Using proxy {proxy_obj.host}:{proxy_obj.port} without auth")
    
    client = TelegramClient(StringSession(), api_id, api_hash, proxy=proxy_dict)
    
    try:
        logger.info(f"Attempting to connect to Telegram for {phone}...")
        await client.connect()
        
        if not await client.is_user_authorized():
            result = await client.send_code_request(phone)
            temp_session = client.session.save()
            log_system('INFO', f'Verification code sent to {phone}', 'auth_manager')
            return {
                'success': True, 
                'message': 'Code sent successfully', 
                'needs_code': True,
                'phone_code_hash': result.phone_code_hash,
                'temp_session': temp_session
            }
        
        return {'success': True, 'message': 'Already authorized', 'needs_code': False}
        
    except ConnectionError as e:
        error_msg = str(e)
        logger.error(f"Connection error for {phone}: {error_msg}", exc_info=True)
        
        if proxy_dict:
            suggestion = "The proxy credentials appear to be incorrect. Please verify:\n"
            suggestion += f"1. Username: {username if username else 'None'}\n"
            suggestion += f"2. Password length: {len(password) if password else 0}\n"
            suggestion += "3. Contact your proxy provider to verify credentials\n"
            suggestion += "4. Check if your IP needs to be whitelisted"
            
            log_system('ERROR', f'Proxy authentication failed for {phone}', 'auth_manager', error_details=suggestion)
            return {'success': False, 'message': f'Proxy authentication failed. Please check credentials with your provider.'}
        
        log_system('ERROR', f'Failed to send code to {phone}', 'auth_manager', error_details=error_msg)
        return {'success': False, 'message': error_msg}
        
    except Exception as e:
        logger.error(f"Error sending verification code to {phone}: {str(e)}", exc_info=True)
        log_system('ERROR', f'Failed to send code to {phone}', 'auth_manager', error_details=str(e))
        return {'success': False, 'message': str(e)}
    finally:
        await client.disconnect()

async def create_telegram_session(phone, api_id, api_hash, phone_code_hash, temp_session=None, code=None, password=None, proxy_id=None):
    proxy_dict = None
    if proxy_id:
        proxy_obj = db.session.get(Proxy, proxy_id)
        if proxy_obj and proxy_obj.is_active:
            import socks
            if proxy_obj.protocol == 'socks5':
                proxy_type = socks.SOCKS5
            elif proxy_obj.protocol == 'socks4':
                proxy_type = socks.SOCKS4
            else:
                proxy_type = socks.HTTP
            
            username = proxy_obj.username.strip() if proxy_obj.username and proxy_obj.username.strip() else None
            password_str = proxy_obj.password.strip() if proxy_obj.password and proxy_obj.password.strip() else None
            
            if username and password_str:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port, True, username, password_str)
                logger.info(f"Using proxy {proxy_obj.host}:{proxy_obj.port} with auth (user: {username})")
            else:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port)
                logger.info(f"Using proxy {proxy_obj.host}:{proxy_obj.port} without auth")
    
    if temp_session:
        client = TelegramClient(StringSession(temp_session), api_id, api_hash, proxy=proxy_dict)
    else:
        client = TelegramClient(StringSession(), api_id, api_hash, proxy=proxy_dict)
    
    try:
        await client.connect()
        
        if not await client.is_user_authorized():
            if not code:
                return {'success': False, 'message': 'Code required', 'needs_code': True}
            
            try:
                await client.sign_in(phone, code, phone_code_hash=phone_code_hash)
            except SessionPasswordNeededError:
                if not password:
                    return {'success': False, 'message': '2FA password required', 'needs_password': True}
                await client.sign_in(password=password)
        
        me = await client.get_me()
        account_name = f"{me.first_name or ''} {me.last_name or ''}".strip() or phone
        
        session_string = client.session.save()
        log_system('INFO', f'Session created for {phone}', 'auth_manager')
        return {'success': True, 'session_string': session_string, 'account_name': account_name}
        
    except Exception as e:
        logger.error(f"Error creating session for {phone}: {str(e)}", exc_info=True)
        log_system('ERROR', f'Session creation failed for {phone}', 'auth_manager', error_details=str(e))
        return {'success': False, 'message': str(e)}
    finally:
        await client.disconnect()

async def verify_channel_admin(account, channel_id):
    session_string = load_session_string(account=account)
    if not session_string:
        return {'success': False, 'message': 'Session not found'}
    
    proxy_dict = None
    if hasattr(account, 'proxy_id') and account.proxy_id:
        proxy_obj = db.session.get(Proxy, account.proxy_id)
        if proxy_obj and proxy_obj.is_active:
            import socks
            if proxy_obj.protocol == 'socks5':
                proxy_type = socks.SOCKS5
            elif proxy_obj.protocol == 'socks4':
                proxy_type = socks.SOCKS4
            else:
                proxy_type = socks.HTTP
            
            username = proxy_obj.username.strip() if proxy_obj.username and proxy_obj.username.strip() else None
            password = proxy_obj.password.strip() if proxy_obj.password and proxy_obj.password.strip() else None
            
            if username and password:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port, True, username, password)
            else:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port)
    
    client = TelegramClient(StringSession(session_string), account.api_id, account.api_hash, proxy=proxy_dict)
    
    try:
        await client.connect()
        
        if not await client.is_user_authorized():
            return {'success': False, 'message': 'Session expired. Please re-add your account.'}
        
        try:
            channel_id_int = int(channel_id) if not channel_id.startswith('-100') else int(channel_id)
        except:
            channel_id_int = channel_id
        
        entity = await client.get_entity(channel_id_int)
        
        participant = await client.get_permissions(entity, 'me')
        
        if not participant.is_admin:
            return {'success': False, 'message': 'You are not an admin of this channel'}
        
        return {'success': True, 'channel_name': entity.title}
        
    except Exception as e:
        error_msg = str(e)
        if 'key is not registered' in error_msg.lower() or 'authkeyunregistered' in error_msg.lower():
            return {'success': False, 'message': 'Session expired. Please re-add your account.'}
        logger.error(f"Error verifying channel {channel_id}: {error_msg}", exc_info=True)
        return {'success': False, 'message': error_msg}
    finally:
        await client.disconnect()

async def get_join_requests(account):
    from telethon.tl.functions.messages import GetChatInviteImportersRequest
    from telethon.tl.types import InputPeerEmpty
    
    session_string = load_session_string(account=account)
    if not session_string:
        return {'success': False, 'message': 'Session not found'}
    
    client = TelegramClient(StringSession(session_string), account.api_id, account.api_hash)
    
    try:
        await client.connect()
        
        all_requests = []
        
        for channel in account.channels:
            try:
                channel_id_int = int(channel.channel_id) if not channel.channel_id.startswith('-100') else int(channel.channel_id)
                entity = await client.get_entity(channel_id_int)
                
                requests = []
                
                messaged_users = set()
                history = MessageHistory.query.filter_by(
                    account_id=account.id,
                    channel_id=channel.channel_id,
                    success=True
                ).all()
                for h in history:
                    messaged_users.add(h.user_id)
                
                try:
                    result = await client(GetChatInviteImportersRequest(
                        peer=entity,
                        requested=True,
                        link='',
                        q='',
                        offset_date=0,
                        offset_user=InputPeerEmpty(),
                        limit=100
                    ))
                    
                    for importer in result.importers:
                        user = None
                        for u in result.users:
                            if u.id == importer.user_id:
                                user = u
                                break
                        
                        if user:
                            requests.append({
                                'user_id': user.id,
                                'first_name': user.first_name or '',
                                'last_name': user.last_name or '',
                                'username': user.username or '',
                                'already_messaged': user.id in messaged_users
                            })
                    
                except Exception as e:
                    logger.error(f"Error getting join requests for channel {channel.channel_id}: {str(e)}", exc_info=True)
                
                all_requests.append({
                    'channel_id': channel.channel_id,
                    'channel_name': channel.channel_name,
                    'requests_count': len(requests),
                    'new_requests_count': len([r for r in requests if not r['already_messaged']]),
                    'requests': requests
                })
                
            except Exception as e:
                logger.error(f"Error processing channel {channel.channel_id}: {str(e)}", exc_info=True)
                all_requests.append({
                    'channel_id': channel.channel_id,
                    'channel_name': channel.channel_name,
                    'error': str(e)
                })
        
        return {'success': True, 'channels': all_requests}
        
    except Exception as e:
        logger.error(f"Error getting join requests: {str(e)}", exc_info=True)
        return {'success': False, 'message': str(e)}
    finally:
        await client.disconnect()

async def get_join_requests_from_channel(account, channel_id):
    from telethon.tl.functions.messages import GetChatInviteImportersRequest
    from telethon.tl import types
    
    session_string = load_session_string(account=account)
    if not session_string:
        return {'success': False, 'message': 'Session not found'}
    
    client = TelegramClient(StringSession(session_string), account.api_id, account.api_hash)
    
    try:
        await client.connect()
        
        channel_id_int = int(channel_id) if not channel_id.startswith('-100') else int(channel_id)
        entity = await client.get_entity(channel_id_int)
        
        messaged_users = set()
        history = MessageHistory.query.filter_by(
            account_id=account.id,
            channel_id=channel_id,
            success=True
        ).all()
        for h in history:
            messaged_users.add(h.user_id)
        
        all_importers = []
        all_users = []
        offset_date = None
        offset_user = types.InputUserEmpty()
        limit = 100
        
        while True:
            try:
                result = await client(GetChatInviteImportersRequest(
                    peer=entity,
                    requested=True,
                    offset_date=offset_date,
                    offset_user=offset_user,
                    limit=limit
                ))
                
                all_importers.extend(result.importers)
                all_users.extend(result.users)
                
                if not result.importers:
                    break
                
                offset_date = result.importers[-1].date
                offset_user = result.users[-1] if result.users else types.InputUserEmpty()
                
                await asyncio.sleep(random.uniform(2, 4))
                
            except FloodWaitError as fwe:
                logger.warning(f"FloodWait: {fwe.seconds}s. Waiting...")
                await asyncio.sleep(fwe.seconds)
                continue
            except Exception as e:
                logger.error(f"Error fetching batch for channel {channel_id}: {str(e)}", exc_info=True)
                break
        
        requests = []
        for importer in all_importers:
            user = None
            for u in all_users:
                if u.id == importer.user_id:
                    user = u
                    break
            
            if user:
                requests.append({
                    'user_id': user.id,
                    'first_name': user.first_name or '',
                    'last_name': user.last_name or '',
                    'username': user.username or '',
                    'already_messaged': user.id in messaged_users
                })
        
        return {
            'success': True,
            'channel_id': channel_id,
            'channel_name': entity.title if hasattr(entity, 'title') else '',
            'requests_count': len(requests),
            'new_requests_count': len([r for r in requests if not r['already_messaged']]),
            'requests': requests
        }
        
    except Exception as e:
        logger.error(f"Error getting join requests from channel: {str(e)}", exc_info=True)
        return {'success': False, 'message': str(e)}
    finally:
        await client.disconnect()

async def get_join_requests_from_channel_streaming(account, channel_id):
    from telethon.tl.functions.messages import GetChatInviteImportersRequest
    from telethon.tl import types
    
    session_string = load_session_string(account=account)
    if not session_string:
        yield {'type': 'error', 'message': 'Session not found'}
        return
    
    proxy_dict = None
    if hasattr(account, 'proxy_id') and account.proxy_id:
        proxy_obj = db.session.get(Proxy, account.proxy_id)
        if proxy_obj and proxy_obj.is_active:
            import socks
            if proxy_obj.protocol == 'socks5':
                proxy_type = socks.SOCKS5
            elif proxy_obj.protocol == 'socks4':
                proxy_type = socks.SOCKS4
            else:
                proxy_type = socks.HTTP
            
            username = proxy_obj.username.strip() if proxy_obj.username and proxy_obj.username.strip() else None
            password = proxy_obj.password.strip() if proxy_obj.password and proxy_obj.password.strip() else None
            
            if username and password:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port, True, username, password)
            else:
                proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port)
    
    client = TelegramClient(StringSession(session_string), account.api_id, account.api_hash, proxy=proxy_dict)
    
    try:
        await client.connect()
        
        if not await client.is_user_authorized():
            yield {'type': 'error', 'message': 'Session expired. Please re-add your account.'}
            return
        
        channel_id_int = int(channel_id) if not channel_id.startswith('-100') else int(channel_id)
        entity = await client.get_entity(channel_id_int)
        
        messaged_users = set()
        history = db.session.query(MessageHistory).filter_by(
            account_id=account.id,
            channel_id=channel_id,
            success=True
        ).all()
        for h in history:
            messaged_users.add(h.user_id)
        
        all_importers = []
        all_users = []
        offset_date = None
        offset_user = types.InputUserEmpty()
        limit = 100
        batch_num = 0
        
        while True:
            try:
                result = await client(GetChatInviteImportersRequest(
                    peer=entity,
                    requested=True,
                    offset_date=offset_date,
                    offset_user=offset_user,
                    limit=limit
                ))
                
                all_importers.extend(result.importers)
                all_users.extend(result.users)
                batch_num += 1
                
                yield {
                    'type': 'progress',
                    'channel_id': channel_id,
                    'channel_name': entity.title if hasattr(entity, 'title') else '',
                    'total_fetched': len(all_importers),
                    'batch': batch_num,
                    'message': f'Fetched {len(all_importers)} users...'
                }
                
                if not result.importers:
                    break
                
                offset_date = result.importers[-1].date
                offset_user = result.users[-1] if result.users else types.InputUserEmpty()
                
                await asyncio.sleep(random.uniform(2, 4))
                
            except FloodWaitError as fwe:
                yield {
                    'type': 'warning',
                    'channel_id': channel_id,
                    'message': f'FloodWait: {fwe.seconds}s. Waiting...'
                }
                await asyncio.sleep(fwe.seconds)
                continue
            except Exception as e:
                logger.error(f"Error fetching batch for channel {channel_id}: {str(e)}", exc_info=True)
                yield {
                    'type': 'error',
                    'channel_id': channel_id,
                    'message': f'Error: {str(e)[:100]}'
                }
                break
        
        requests = []
        for importer in all_importers:
            user = None
            for u in all_users:
                if u.id == importer.user_id:
                    user = u
                    break
            
            if user:
                requests.append({
                    'user_id': user.id,
                    'first_name': user.first_name or '',
                    'last_name': user.last_name or '',
                    'username': user.username or '',
                    'already_messaged': user.id in messaged_users
                })
        
        yield {
            'type': 'complete',
            'channel_id': channel_id,
            'channel_name': entity.title if hasattr(entity, 'title') else '',
            'requests_count': len(requests),
            'new_requests_count': len([r for r in requests if not r['already_messaged']]),
            'requests': requests
        }
        
    except Exception as e:
        error_msg = str(e)
        if 'key is not registered' in error_msg.lower() or 'authkeyunregistered' in error_msg.lower():
            logger.error(f"Session expired for account {account.id}: {error_msg}")
            yield {'type': 'error', 'message': 'Session expired. Please re-add your account to continue.'}
        else:
            logger.error(f"Error getting join requests from channel: {error_msg}", exc_info=True)
            yield {'type': 'error', 'message': error_msg}
    finally:
        await client.disconnect()

async def get_all_join_requests_streaming(account, db_session=None):
    from telethon.tl.functions.messages import GetChatInviteImportersRequest
    from telethon.tl import types
    
    session_string = load_session_string(account=account)
    if not session_string:
        yield {'type': 'error', 'message': 'Session not found'}
        return
    
    client = TelegramClient(StringSession(session_string), account.api_id, account.api_hash)
    
    try:
        await client.connect()
        
        if not await client.is_user_authorized():
            yield {'type': 'error', 'message': 'Session expired or unauthorized'}
            return
        
        for channel in account.channels:
            try:
                channel_id_int = int(channel.channel_id) if not channel.channel_id.startswith('-100') else int(channel.channel_id)
                entity = await client.get_entity(channel_id_int)
                
                yield {
                    'type': 'info',
                    'channel_id': channel.channel_id,
                    'channel_name': channel.channel_name or entity.title,
                    'message': f'Processing channel: {channel.channel_name or entity.title}'
                }
                
                messaged_users = set()
                if db_session:
                    history = db_session.query(MessageHistory).filter_by(
                        account_id=account.id,
                        channel_id=channel.channel_id,
                        success=True
                    ).all()
                    for h in history:
                        messaged_users.add(h.user_id)
                
                all_importers = []
                all_users = []
                offset_date = None
                offset_user = types.InputUserEmpty()
                limit = 100
                batch_num = 0
                
                while True:
                    try:
                        result = await client(GetChatInviteImportersRequest(
                            peer=entity,
                            requested=True,
                            offset_date=offset_date,
                            offset_user=offset_user,
                            limit=limit
                        ))
                        
                        all_importers.extend(result.importers)
                        all_users.extend(result.users)
                        batch_num += 1
                        
                        yield {
                            'type': 'progress',
                            'channel_id': channel.channel_id,
                            'channel_name': channel.channel_name,
                            'total_fetched': len(all_importers),
                            'batch': batch_num,
                            'message': f'Fetched {len(all_importers)} users...'
                        }
                        
                        if not result.importers:
                            break
                        
                        offset_date = result.importers[-1].date
                        offset_user = result.users[-1] if result.users else types.InputUserEmpty()
                        
                        pause_duration = random.uniform(2, 4)
                        steps = int(pause_duration)
                        for _ in range(steps):
                            await asyncio.sleep(1)
                            yield {
                                'type': 'keepalive',
                                'channel_id': channel.channel_id,
                                'message': 'Processing...'
                            }
                    
                    except FloodWaitError as fwe:
                        yield {
                            'type': 'warning',
                            'channel_id': channel.channel_id,
                            'message': f'FloodWait: {fwe.seconds}s. Waiting...'
                        }
                        await asyncio.sleep(fwe.seconds)
                        continue
                    except Exception as e:
                        yield {
                            'type': 'error',
                            'channel_id': channel.channel_id,
                            'message': f'Error fetching batch: {str(e)}'
                        }
                        break
                
                requests = []
                for importer in all_importers:
                    user = None
                    for u in all_users:
                        if u.id == importer.user_id:
                            user = u
                            break
                    
                    if user:
                        requests.append({
                            'user_id': user.id,
                            'first_name': user.first_name or '',
                            'last_name': user.last_name or '',
                            'username': user.username or '',
                            'already_messaged': user.id in messaged_users
                        })
                
                yield {
                    'type': 'complete',
                    'channel_id': channel.channel_id,
                    'channel_name': channel.channel_name,
                    'requests_count': len(requests),
                    'new_requests_count': len([r for r in requests if not r['already_messaged']]),
                    'requests': requests
                }
                
            except Exception as e:
                logger.error(f"Error processing channel {channel.channel_id}: {str(e)}", exc_info=True)
                yield {
                    'type': 'error',
                    'channel_id': channel.channel_id,
                    'channel_name': channel.channel_name,
                    'message': str(e)
                }
        
        yield {'type': 'finished', 'message': 'All channels processed'}
        
    except Exception as e:
        logger.error(f"Error in get_all_join_requests_streaming: {str(e)}", exc_info=True)
        yield {'type': 'error', 'message': str(e)}
    finally:
        await client.disconnect()

async def verify_session_status(account):
    session_string = load_session_string(account=account)
    if not session_string:
        return {'success': False, 'status': 'inactive', 'message': 'Session not found'}
    
    client = TelegramClient(StringSession(session_string), account.api_id, account.api_hash)
    
    try:
        await client.connect()
        
        if not await client.is_user_authorized():
            return {'success': True, 'status': 'inactive', 'message': 'Session expired or unauthorized'}
        
        me = await client.get_me()
        account_info = {
            'id': me.id,
            'first_name': me.first_name or '',
            'last_name': me.last_name or '',
            'username': me.username or '',
            'phone': me.phone or ''
        }
        
        return {
            'success': True, 
            'status': 'active', 
            'message': 'Session is active and working',
            'account_info': account_info
        }
        
    except Exception as e:
        logger.error(f"Error verifying session for {account.phone}: {str(e)}", exc_info=True)
        return {'success': True, 'status': 'error', 'message': str(e)}
    finally:
        await client.disconnect()

async def send_messages_to_users_streaming(account_id, message, skip_sent=False, user_count_limit=100, session_id=None):
    from telethon.tl.functions.messages import GetChatInviteImportersRequest
    from telethon.tl.types import InputPeerEmpty
    from sqlalchemy.orm import scoped_session, sessionmaker

    # 🛑 ENHANCED INTERRUPTIBLE SLEEP - Database-Persisted Stop Check
    async def interruptible_sleep(duration):
        """
        Sleep in 1-second chunks, checking stop signal from BOTH RAM and DATABASE.

        This is CRITICAL for Railway where:
        - RAM can be cleared on restart
        - Connections can drop
        - Stop signals must persist

        Checks database every 5 seconds to balance performance with reliability.
        """
        remaining = duration
        last_db_check = asyncio.get_event_loop().time()
        db_check_interval = 5  # Check database every 5 seconds

        while remaining > 0:
            current_time = asyncio.get_event_loop().time()

            # 1. Quick check: RAM flag (every iteration, fast)
            if stop_sending_flag.get(account_id, False):
                logger.info(f"🛑 [Account {account_id}] Stop detected from RAM during sleep")
                return True

            # 2. Reliable check: DATABASE flag (every 5 seconds, survives restarts)
            if current_time - last_db_check >= db_check_interval:
                if check_stop_flag_from_db(account_id):
                    logger.info(f"🛑 [Account {account_id}] Stop detected from DATABASE during sleep")
                    return True
                last_db_check = current_time

            # 3. Sleep for 1 second
            sleep_time = min(1.0, remaining)
            await asyncio.sleep(sleep_time)
            remaining -= sleep_time

        return False  # Completed normally, not stopped

    with app.app_context():
        session_factory = sessionmaker(bind=db.engine)
        db_session = scoped_session(session_factory)()
    
    try:
        account = db_session.query(TelegramAccount).filter_by(id=account_id).first()
        if not account:
            yield {'type': 'error', 'message': 'Account not found'}
            log_system('ERROR', 'Account not found', 'message_sender', account_id=account_id)
            return
        
        config = load_config()
        session_string = load_session_string(account=account)
        if not session_string:
            yield {'type': 'error', 'message': 'Session not found'}
            log_system('ERROR', 'Session not found', 'message_sender', account_id=account_id)
            return
        
        proxy_dict = None
        if hasattr(account, 'proxy_id') and account.proxy_id:
            proxy_obj = db_session.query(Proxy).filter_by(id=account.proxy_id).first()
            if proxy_obj and proxy_obj.is_active:
                import socks
                if proxy_obj.protocol == 'socks5':
                    proxy_type = socks.SOCKS5
                elif proxy_obj.protocol == 'socks4':
                    proxy_type = socks.SOCKS4
                else:
                    proxy_type = socks.HTTP
                
                username = proxy_obj.username.strip() if proxy_obj.username and proxy_obj.username.strip() else None
                password = proxy_obj.password.strip() if proxy_obj.password and proxy_obj.password.strip() else None
                
                if username and password:
                    proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port, True, username, password)
                    proxy_msg = f'Using proxy: {proxy_obj.host}:{proxy_obj.port} with auth (user: {username})'
                else:
                    proxy_dict = (proxy_type, proxy_obj.host, proxy_obj.port)
                    proxy_msg = f'Using proxy: {proxy_obj.host}:{proxy_obj.port} without auth'
                
                yield {'type': 'info', 'message': proxy_msg}
                logger.info(f"[Account {account_id}] {proxy_msg}")
                log_system('INFO', proxy_msg, 'message_sender', account_id=account_id)
        
        client = TelegramClient(StringSession(session_string), account.api_id, account.api_hash, proxy=proxy_dict)
        
        try:
            connection_retries = 0
            max_connection_retries = config['connection_retry_attempts']
            
            while connection_retries < max_connection_retries:
                try:
                    await client.connect()
                    break
                except Exception as conn_error:
                    connection_retries += 1
                    if connection_retries >= max_connection_retries:
                        raise conn_error
                    await asyncio.sleep(2 ** connection_retries)
            
            if not await client.is_user_authorized():
                yield {'type': 'error', 'message': 'Session expired. Please re-add account.'}
                log_system('ERROR', 'Session expired', 'message_sender', account_id=account_id)
                return
            
            connection_time = datetime.now().strftime('%H:%M:%S')
            start_msg = f'[{connection_time}] ✅ Connected to Telegram successfully'
            yield {'type': 'info', 'message': start_msg}
            logger.info(f"[Account {account_id}] {start_msg}")

            init_msg = f'📋 Initializing message sending process...\n   • User count limit: {user_count_limit} messages\n   • Skip sent: {"Enabled" if skip_sent else "Disabled"}\n   • Session ID: {session_id}'
            yield {'type': 'info', 'message': init_msg}
            logger.info(f"[Account {account_id}] User limit: {user_count_limit}, Skip sent: {skip_sent}, Session: {session_id}")
            
            log_system('INFO', f'Starting message sending: user_count_limit={user_count_limit}', 'message_sender', account_id=account_id)
            
            channels = db_session.query(Channel).filter_by(account_id=account_id).all()

            if not channels:
                yield {'type': 'warning', 'message': '⚠️ No channels found for this account. Please fetch join requests first.'}
                logger.warning(f"[Account {account_id}] No channels found")
                return

            channels_msg = f'📢 Found {len(channels)} channel(s) to process'
            yield {'type': 'info', 'message': channels_msg}
            logger.info(f"[Account {account_id}] {channels_msg}")
            
            for channel_idx, channel in enumerate(channels, 1):
                if stop_sending_flag.get(account_id, False):
                    yield {'type': 'warning', 'message': 'Stopped by user'}
                    log_system('INFO', 'Stopped by user', 'message_sender', account_id=account_id)
                    break
                
                try:
                    current_time = datetime.now().strftime('%H:%M:%S')
                    channel_msg = f'[{current_time}] Processing Channel {channel_idx}/{len(channels)}: {channel.channel_name}'
                    yield {'type': 'info', 'message': channel_msg}
                    logger.info(f"[Account {account_id}] {channel_msg}")
                    
                    channel_id_int = int(channel.channel_id) if not channel.channel_id.startswith('-100') else int(channel.channel_id)
                    
                    try:
                        entity = await client.get_entity(channel_id_int)
                    except Exception as e:
                        error_msg = f'Cannot access channel {channel.channel_name}: {str(e)}'
                        yield {'type': 'error', 'message': error_msg}
                        logger.error(f"[Account {account_id}] {error_msg}")
                        log_system('ERROR', f'Cannot access channel {channel.channel_id}', 'message_sender', account_id=account_id, error_details=str(e))
                        continue
                    
                    users = []

                    # ═══════════════════════════════════════════════════════════════
                    # 🛡️ EARLY FILTERING - Load messaged users from ALL accounts
                    # ═══════════════════════════════════════════════════════════════
                    messaged_user_ids = set()

                    # Clear cache if needed (prevent memory bloat)
                    clear_cache_if_needed()

                    # Query database for ALL accounts (not just this one)
                    history = db_session.query(MessageHistory.user_id).filter_by(
                        # account_id=account.id,  ← REMOVED! Now checks ALL accounts
                        channel_id=channel.channel_id,
                        success=True
                    ).all()
                    messaged_user_ids = {h.user_id for h in history}

                    # Add permanent blacklist users
                    messaged_user_ids.update(permanent_user_blacklist)

                    if messaged_user_ids:
                        yield {'type': 'info', 'message': f'🛡️ {len(messaged_user_ids)} users in skip list (from ALL accounts + blacklist)'}
                    
                    try:
                        all_fetched_users = []
                        offset_user = InputPeerEmpty()
                        offset_date = 0
                        max_fetch_attempts = 100
                        fetch_attempt = 0
                        consecutive_no_results = 0
                        consecutive_no_new_users = 0
                        seen_user_ids = set()
                        
                        while len(users) < max(user_count_limit * 2, 200) and fetch_attempt < max_fetch_attempts:
                            fetch_attempt += 1
                            
                            if fetch_attempt % 5 == 0:
                                yield {'type': 'info', 'message': f'Fetch attempt {fetch_attempt}: Collected {len(users)} users (fetched {len(all_fetched_users)} total)'}
                            
                            result = await client(GetChatInviteImportersRequest(
                                peer=entity,
                                requested=True,
                                link='',
                                q='',
                                offset_date=offset_date,
                                offset_user=offset_user,
                                limit=100
                            ))
                            
                            if not result.importers:
                                consecutive_no_results += 1
                                if consecutive_no_results >= 3:
                                    yield {'type': 'info', 'message': f'No more users available in channel. Collected {len(users)} users'}
                                    break
                                continue
                            else:
                                consecutive_no_results = 0
                            
                            batch_users = []
                            for importer in result.importers:
                                user = None
                                for u in result.users:
                                    if u.id == importer.user_id:
                                        user = u
                                        break
                                
                                if user:
                                    batch_users.append(user)
                                    all_fetched_users.append(user)
                            
                            new_in_batch = 0
                            for user in batch_users:
                                # IMPROVED: Always filter messaged users (not dependent on skip_sent)
                                if user.id in messaged_user_ids:
                                    continue

                                if user.id in seen_user_ids:
                                    continue
                                
                                users.append(user)
                                seen_user_ids.add(user.id)
                                new_in_batch += 1
                            
                            if new_in_batch == 0:
                                consecutive_no_new_users += 1
                                if consecutive_no_new_users >= 10:
                                    yield {'type': 'warning', 'message': f'Stopping: No new users found in last 10 batches. Total users: {len(users)}'}
                                    break
                            else:
                                consecutive_no_new_users = 0
                            
                            if result.importers:
                                last_importer = result.importers[-1]
                                offset_date = last_importer.date
                                for u in result.users:
                                    if u.id == last_importer.user_id:
                                        offset_user = u
                                        break
                        
                        found_msg = f'Collected {len(users)} users to message (fetched {len(all_fetched_users)} total, {len(messaged_user_ids)} in database skip list)'
                        yield {'type': 'info', 'message': found_msg}
                        logger.info(f"[Account {account_id}] {found_msg}")
                        
                    except Exception as e:
                        error_msg = f'Error getting join requests: {str(e)}'
                        yield {'type': 'error', 'message': error_msg}
                        logger.error(f"[Account {account_id}] {error_msg}")
                        log_system('ERROR', f'Failed to get join requests for channel {channel.channel_id}', 'message_sender', account_id=account_id, error_details=str(e))
                        continue
                    
                    if not users:
                        no_users_msg = 'No new users to message in this channel'
                        yield {'type': 'warning', 'message': no_users_msg}
                        logger.warning(f"[Account {account_id}] {no_users_msg}")
                        continue
                    
                    target_message_count = user_count_limit
                    sent_count = 0
                    failed_count = 0
                    skipped_count = 0
                    messages_this_session = 0
                    sent_in_this_session = set()
                    new_user_counter = 0
                    current_user_index = 0
                    
                    yield {'type': 'info', 'message': '========================================'}
                    start_send_msg = f'Target: {target_message_count} messages'
                    yield {'type': 'info', 'message': start_send_msg}
                    logger.info(f"[Account {account_id}] {start_send_msg}")
                    logger.info(f"[Account {account_id}] ========================================")
                    
                    while sent_count < target_message_count:
                        if stop_sending_flag.get(account_id, False):
                            stop_msg = 'Stopped by user'
                            yield {'type': 'warning', 'message': stop_msg}
                            logger.warning(f"[Account {account_id}] {stop_msg}")
                            break
                        
                        if current_user_index >= len(users):
                            remaining = target_message_count - sent_count
                            refetch_msg = f'Need {remaining} more messages. Fetching more users...'
                            yield {'type': 'info', 'message': refetch_msg}
                            logger.info(f"[Account {account_id}] {refetch_msg}")
                            
                            fetch_more_attempts = 0
                            max_refetch = 10
                            users_before = len(users)
                            
                            while current_user_index >= len(users) and fetch_more_attempts < max_refetch:
                                # Check stop flag during user fetching
                                if stop_sending_flag.get(account_id, False):
                                    yield {'type': 'warning', 'message': 'Stopped by user during user fetching'}
                                    logger.warning(f"[Account {account_id}] Stopped during user fetching")
                                    break

                                fetch_more_attempts += 1

                                try:
                                    result = await client(GetChatInviteImportersRequest(
                                        peer=entity,
                                        requested=True,
                                        link='',
                                        q='',
                                        offset_date=offset_date,
                                        offset_user=offset_user,
                                        limit=100
                                    ))
                                    
                                    if not result.importers:
                                        no_more_msg = f'No more users available. Sent {sent_count}/{target_message_count}'
                                        yield {'type': 'warning', 'message': no_more_msg}
                                        logger.warning(f"[Account {account_id}] {no_more_msg}")
                                        break
                                    
                                    batch_users = []
                                    for importer in result.importers:
                                        user = None
                                        for u in result.users:
                                            if u.id == importer.user_id:
                                                user = u
                                                break
                                        if user:
                                            batch_users.append(user)
                                            all_fetched_users.append(user)
                                    
                                    new_in_batch = 0
                                    for user in batch_users:
                                        # IMPROVED: Always filter messaged users (not dependent on skip_sent)
                                        if user.id in messaged_user_ids:
                                            continue
                                        if user.id in seen_user_ids:
                                            continue
                                        users.append(user)
                                        seen_user_ids.add(user.id)
                                        new_in_batch += 1
                                    
                                    if new_in_batch == 0:
                                        if fetch_more_attempts >= 3:
                                            break
                                        continue
                                    
                                    if result.importers:
                                        last_importer = result.importers[-1]
                                        offset_date = last_importer.date
                                        for u in result.users:
                                            if u.id == last_importer.user_id:
                                                offset_user = u
                                                break
                                    
                                    break
                                    
                                except Exception as e:
                                    error_msg = f'Error fetching more users: {str(e)[:100]}'
                                    yield {'type': 'error', 'message': error_msg}
                                    logger.error(f"[Account {account_id}] {error_msg}")
                                    break
                            
                            users_after = len(users)
                            new_users_found = users_after - users_before
                            
                            if new_users_found > 0:
                                yield {'type': 'success', 'message': f'Fetched {new_users_found} new users'}
                            else:
                                no_more_final = f'No more users. Completed with {sent_count}/{target_message_count} messages'
                                yield {'type': 'warning', 'message': no_more_final}
                                logger.warning(f"[Account {account_id}] {no_more_final}")
                                break
                        
                        if current_user_index >= len(users):
                            break
                        
                        user = users[current_user_index]
                        current_user_index += 1
                        
                        if messages_this_session >= config['session_break_after']:
                            current_time = datetime.now().strftime('%H:%M:%S')
                            break_duration = config['session_break_duration']
                            break_msg = f'[{current_time}] Session break: sent {messages_this_session} messages. Resting for {break_duration}s'
                            yield {'type': 'info', 'message': break_msg}
                            logger.info(f"[Account {account_id}] {break_msg}")
                            
                            break_start = asyncio.get_event_loop().time()
                            break_end = break_start + break_duration
                            keepalive_interval = 5
                            last_keepalive = break_start
                            telegram_ping_interval = 30
                            last_telegram_ping = break_start
                            
                            while asyncio.get_event_loop().time() < break_end:
                                current_loop_time = asyncio.get_event_loop().time()

                                if current_loop_time - last_telegram_ping >= telegram_ping_interval:
                                    try:
                                        await client.get_me()
                                        last_telegram_ping = current_loop_time
                                    except Exception as e:
                                        logger.warning(f"Telegram ping failed during break: {str(e)}")

                                if current_loop_time - last_keepalive >= keepalive_interval:
                                    remaining = int(break_end - current_loop_time)
                                    yield {'type': 'info', 'message': f'Break in progress... {remaining}s remaining'}
                                    last_keepalive = current_loop_time

                                # Use interruptible sleep during session break
                                sleep_duration = min(5, break_end - current_loop_time)
                                if await interruptible_sleep(sleep_duration):
                                    yield {'type': 'warning', 'message': '⚠️ Stopped during session break'}
                                    break
                            
                            messages_this_session = 0
                            resume_msg = 'Session break completed. Resuming...'
                            yield {'type': 'info', 'message': resume_msg}
                            logger.info(f"[Account {account_id}] {resume_msg}")
                        
                        if user.id in sent_in_this_session:
                            yield {'type': 'warning', 'message': f'Skipping duplicate user in list: {user.first_name or ""} {user.last_name or ""} (ID: {user.id})'}
                            continue
                        
                        if has_user_been_messaged(account.id, channel.channel_id, user.id):
                            user_name = f"{user.first_name or ''} {user.last_name or ''}".strip()
                            if not user_name:
                                user_name = f"User_{user.id}"
                            current_time = datetime.now().strftime('%H:%M:%S')
                            yield {'type': 'warning', 'message': f'[{current_time}] {user_name}: Previously messaged, skip.'}
                            skipped_count += 1
                            new_user_counter -= 1
                            continue
                        
                        new_user_counter += 1
                        retry_count = 0
                        success = False
                        user_name = f"{user.first_name or ''} {user.last_name or ''}".strip()
                        if not user_name:
                            user_name = f"User_{user.id}"
                        
                        # ═══════════════════════════════════════════════════════════════
                        # 🛡️ ULTIMATE DUPLICATE PREVENTION - CHAT HISTORY CHECK
                        # ═══════════════════════════════════════════════════════════════
                        # IMPROVED: Now works INDEPENDENTLY from skip_sent parameter!
                        # This is the STRONGEST protection - checks real chat history
                        # ═══════════════════════════════════════════════════════════════
                        try:
                            chat_messages = await client.get_messages(user, limit=1)
                            if chat_messages and len(chat_messages) > 0:
                                last_msg = chat_messages[0]
                                last_msg_text = last_msg.message if last_msg.message else "[Media/Sticker]"
                                if len(last_msg_text) > 50:
                                    last_msg_text = last_msg_text[:50] + "..."

                                # Get message direction (from us or from them)
                                msg_from_me = last_msg.out
                                direction = "sent by us" if msg_from_me else "received from them"

                                current_time = datetime.now().strftime('%H:%M:%S')
                                skip_reason = f'[{current_time}] 🚫 {user_name}: SKIP - Chat history exists. Last message ({direction}): {last_msg_text}'
                                yield {'type': 'warning', 'message': skip_reason}
                                logger.warning(f"[Account {account_id}] {skip_reason}")
                                log_system('INFO', f'Skipped user {user.id} - chat history exists', 'message_sender', account_id=account_id)

                                # Add to blacklist for future prevention
                                add_to_permanent_blacklist(user.id, channel.channel_id)

                                skipped_count += 1
                                new_user_counter -= 1
                                continue
                        except Exception as check_error:
                            logger.warning(f"[Account {account_id}] Error checking chat history for user {user.id}: {check_error}")
                            # Continue with other checks even if this fails
                            pass

                        # Check stop flag after chat history check
                        if stop_sending_flag.get(account_id, False):
                            yield {'type': 'warning', 'message': 'Stopped by user'}
                            logger.warning(f"[Account {account_id}] Stopped after chat history check")
                            break

                        can_send, reason = try_claim_user(session_id, user.id, account_id)
                        if not can_send:
                            current_time = datetime.now().strftime('%H:%M:%S')
                            if reason == "already_messaged_in_session":
                                yield {'type': 'warning', 'message': f'[{current_time}] {user_name}: Already messaged by another account in this session, skip.'}
                            else:
                                other_account = reason.split('_')[-1]
                                yield {'type': 'warning', 'message': f'[{current_time}] {user_name}: Currently being messaged by Account {other_account}, skip.'}
                            skipped_count += 1
                            new_user_counter -= 1
                            continue
                        
                        while retry_count < config['max_retries'] and not success:
                            try:
                                current_time = datetime.now().strftime('%H:%M:%S')
                                delay = random.uniform(config['min_delay'], config['max_delay'])

                                # Log delay
                                delay_msg = f'[{new_user_counter}/{target_message_count}] [{current_time}] ⏳ Waiting {delay:.1f}s before sending to {user_name}'
                                yield {'type': 'info', 'message': delay_msg}
                                logger.debug(f"[Account {account_id}] {delay_msg}")

                                # Interruptible sleep - stops immediately when stop flag is set
                                if await interruptible_sleep(delay):
                                    yield {'type': 'warning', 'message': '⚠️ Stopped by user during delay'}
                                    logger.warning(f"[Account {account_id}] Stopped during delay")
                                    break

                                # Typing indicator with logging
                                if config['enable_typing']:
                                    typing_duration = random.uniform(1, config['typing_duration'])
                                    try:
                                        typing_msg = f'[{current_time}] 💬 Simulating typing for {typing_duration:.1f}s...'
                                        yield {'type': 'info', 'message': typing_msg}
                                        logger.debug(f"[Account {account_id}] {typing_msg}")

                                        await client(SetTypingRequest(
                                            peer=user,
                                            action=SendMessageTypingAction()
                                        ))

                                        # Interruptible sleep for typing simulation
                                        if await interruptible_sleep(typing_duration):
                                            yield {'type': 'warning', 'message': '⚠️ Stopped by user during typing'}
                                            logger.warning(f"[Account {account_id}] Stopped during typing simulation")
                                            break
                                    except Exception as typing_error:
                                        logger.debug(f"[Account {account_id}] Typing action failed: {typing_error}")
                                        pass

                                # Check stop flag before sending
                                if stop_sending_flag.get(account_id, False):
                                    yield {'type': 'warning', 'message': 'Stopped by user'}
                                    logger.warning(f"[Account {account_id}] Stopped before sending message")
                                    break

                                # Process and send message
                                processed_msg = process_message(message, user_name)

                                # Log just before sending
                                logger.info(f"[Account {account_id}] 📤 Sending message to user {user.id} ({user_name})")
                                log_system('INFO', f'Attempting to send message to user {user.id}', 'message_sender', account_id=account.id, user_id=user.id)

                                await client.send_message(user, processed_msg, parse_mode='html')

                                sent_in_this_session.add(user.id)

                                # Add to permanent blacklist immediately after sending
                                add_to_permanent_blacklist(user.id, channel.channel_id)

                                sent_count += 1
                                messages_this_session += 1
                                success = True

                                current_time = datetime.now().strftime('%H:%M:%S')
                                username_display = f"@{user.username}" if user.username else "no_username"

                                # Detailed success message
                                success_msg = f'[{new_user_counter}/{target_message_count}] [{current_time}] ✅ SUCCESS: Sent to {user_name} ({username_display}) | Progress: {sent_count}/{target_message_count} | Session: {messages_this_session} msgs'
                                yield {'type': 'success', 'message': success_msg}
                                logger.info(f"[Account {account_id}] ✅ {success_msg}")
                                
                                try:
                                    history_entry = MessageHistory(
                                        account_id=account.id,
                                        channel_id=channel.channel_id,
                                        user_id=user.id,
                                        user_name=user_name,
                                        user_username=user.username,
                                        message_sent=processed_msg,
                                        success=True,
                                        retry_count=retry_count
                                    )
                                    db_session.add(history_entry)
                                    increment_daily_stats(account.id, success=True)
                                    
                                    db_session.commit()
                                        
                                    log_system('INFO', f'Message sent to user {user.id}', 'message_sender', account_id=account.id, user_id=user.id)
                                except Exception as db_error:
                                    logger.error(f"Database error for user {user.id}: {str(db_error)}", exc_info=True)
                                    db_session.rollback()
                                
                            except FloodWaitError as e:
                                current_time = datetime.now().strftime('%H:%M:%S')
                                wait_time = e.seconds + config['flood_wait_extra_time']
                                flood_msg = f'[{current_time}] ⚠️ FLOODWAIT: Telegram rate limit hit! Waiting {wait_time}s (original: {e.seconds}s + extra: {config["flood_wait_extra_time"]}s) | Retry {retry_count + 1}/{config["max_retries"]}'
                                yield {'type': 'warning', 'message': flood_msg}
                                logger.warning(f"[Account {account_id}] {flood_msg}")
                                log_system('WARNING', f'FloodWait {e.seconds}s for user {user.id}, waiting {wait_time}s', 'message_sender', account_id=account.id, user_id=user.id)

                                # Countdown during flood wait - use interruptible sleep
                                countdown_interval = min(30, wait_time // 3)
                                for elapsed in range(wait_time):
                                    remaining = wait_time - elapsed
                                    if remaining > 0 and elapsed % countdown_interval == 0:
                                        yield {'type': 'info', 'message': f'⏱️ FloodWait countdown: {remaining}s remaining...'}

                                    # Check stop every second
                                    if await interruptible_sleep(1):
                                        yield {'type': 'warning', 'message': '⚠️ Stopped during FloodWait'}
                                        logger.warning(f"[Account {account_id}] Stopped during FloodWait countdown")
                                        break

                                # Exit retry loop if stopped
                                if stop_sending_flag.get(account_id, False):
                                    break

                                retry_count += 1
                                logger.info(f"[Account {account_id}] FloodWait completed, resuming...")
                                
                            except (UserPrivacyRestrictedError, UserDeactivatedBanError, UserDeactivatedError, ChatWriteForbiddenError) as e:
                                current_time = datetime.now().strftime('%H:%M:%S')
                                error_type = type(e).__name__

                                # Map error types to user-friendly messages
                                error_explanations = {
                                    'UserPrivacyRestrictedError': 'User privacy settings prevent messaging',
                                    'UserDeactivatedBanError': 'User account is banned',
                                    'UserDeactivatedError': 'User account is deactivated',
                                    'ChatWriteForbiddenError': 'Cannot write to this chat'
                                }
                                explanation = error_explanations.get(error_type, error_type)

                                skip_msg = f'[{current_time}] ⛔ SKIP: {user_name} - {explanation}'
                                yield {'type': 'warning', 'message': skip_msg}
                                logger.warning(f"[Account {account_id}] {skip_msg}")
                                skipped_count += 1

                                try:
                                    history_entry = MessageHistory(
                                        account_id=account.id,
                                        channel_id=channel.channel_id,
                                        user_id=user.id,
                                        user_name=user_name,
                                        user_username=user.username,
                                        message_sent=message,
                                        success=False,
                                        error_message=f"{error_type}: {explanation}",
                                        retry_count=retry_count
                                    )
                                    db_session.add(history_entry)
                                    db_session.commit()
                                    log_system('WARNING', f'{error_type} for user {user.id}: {explanation}', 'message_sender', account_id=account.id, user_id=user.id)
                                    logger.info(f"[Account {account_id}] Saved error to database: {error_type}")
                                except Exception as db_error:
                                    logger.error(f"[Account {account_id}] Failed to save error to database: {db_error}")
                                    db_session.rollback()
                                break
                                
                            except Exception as e:
                                error_str = str(e).lower()

                                # Handle payment required error
                                if 'allow_payment_required' in error_str or 'rpcerror 406' in error_str:
                                    current_time = datetime.now().strftime('%H:%M:%S')
                                    payment_msg = f'[{current_time}] 💳 SKIP: {user_name} - Payment required to message'
                                    yield {'type': 'warning', 'message': payment_msg}
                                    logger.warning(f"[Account {account_id}] {payment_msg}")
                                    skipped_count += 1

                                    try:
                                        history_entry = MessageHistory(
                                            account_id=account.id,
                                            channel_id=channel.channel_id,
                                            user_id=user.id,
                                            user_name=user_name,
                                            user_username=user.username,
                                            message_sent=message,
                                            success=False,
                                            error_message="Payment required",
                                            retry_count=retry_count
                                        )
                                        db_session.add(history_entry)
                                        db_session.commit()
                                        logger.info(f"[Account {account_id}] Saved payment error to database")
                                    except Exception as db_err:
                                        logger.error(f"[Account {account_id}] DB error: {db_err}")
                                        db_session.rollback()
                                    break

                                # Generic error with retry logic
                                current_time = datetime.now().strftime('%H:%M:%S')
                                error_msg = str(e)[:100]
                                retry_msg = f'[{current_time}] ❌ ERROR: {user_name} - {error_msg} | Retry {retry_count + 1}/{config["max_retries"]}'
                                yield {'type': 'error', 'message': retry_msg}
                                logger.error(f"[Account {account_id}] {retry_msg}")
                                logger.error(f"[Account {account_id}] Full error trace: {str(e)}", exc_info=True)
                                log_system('ERROR', f'Error sending to user {user.id}: {str(e)}', 'message_sender', account_id=account.id, user_id=user.id, error_details=str(e))

                                retry_count += 1

                                if retry_count >= config['max_retries']:
                                    # Max retries reached
                                    failed_count += 1
                                    final_fail_msg = f'[{current_time}] 💥 FAILED: {user_name} - Max retries ({config["max_retries"]}) reached'
                                    yield {'type': 'error', 'message': final_fail_msg}
                                    logger.error(f"[Account {account_id}] {final_fail_msg}")

                                    try:
                                        increment_daily_stats(account.id, success=False)
                                        history_entry = MessageHistory(
                                            account_id=account.id,
                                            channel_id=channel.channel_id,
                                            user_id=user.id,
                                            user_name=user_name,
                                            user_username=user.username,
                                            message_sent=message,
                                            success=False,
                                            error_message=str(e)[:500],
                                            retry_count=retry_count
                                        )
                                        db_session.add(history_entry)
                                        db_session.commit()
                                        logger.info(f"[Account {account_id}] Saved failure to database")
                                    except Exception as db_err:
                                        logger.error(f"[Account {account_id}] DB error on failure save: {db_err}")
                                        db_session.rollback()
                                else:
                                    # Exponential backoff with interruptible sleep
                                    backoff_delay = config['retry_delay_multiplier'] ** retry_count
                                    backoff_msg = f'⏱️ Backing off {backoff_delay}s before retry...'
                                    yield {'type': 'info', 'message': backoff_msg}
                                    logger.info(f"[Account {account_id}] {backoff_msg}")

                                    if await interruptible_sleep(backoff_delay):
                                        yield {'type': 'warning', 'message': '⚠️ Stopped during retry backoff'}
                                        logger.warning(f"[Account {account_id}] Stopped during retry backoff")
                                        break

                        # Check if stopped after retry loop
                        if stop_sending_flag.get(account_id, False):
                            logger.warning(f"[Account {account_id}] Stopped, exiting message loop")
                            break

                        release_user(user.id, mark_as_sent=success, session_id=session_id)
                    
                    try:
                        db_session.commit()
                    except Exception as e:
                        db_session.rollback()
                    
                    current_time = datetime.now().strftime('%H:%M:%S')
                    yield {'type': 'info', 'message': '========================================'}
                    completed_msg = f'[{current_time}] Channel completed: {sent_count} sent, {skipped_count} skipped, {failed_count} failed'
                    yield {'type': 'success', 'message': completed_msg}
                    logger.info(f"[Account {account_id}] {completed_msg}")
                    logger.info(f"[Account {account_id}] ========================================")
                    
                    log_system('INFO', f'Channel completed: sent={sent_count}, skipped={skipped_count}, failed={failed_count}', 'message_sender', account_id=account.id)
                    
                    if skipped_count > 0:
                        skip_msg = f'{skipped_count} users skipped (blocked/deleted/payment)'
                        yield {'type': 'info', 'message': skip_msg}
                        logger.info(f"[Account {account_id}] {skip_msg}")
                    
                    if failed_count > 0:
                        fail_msg = f'{failed_count} messages failed'
                        yield {'type': 'warning', 'message': fail_msg}
                        logger.warning(f"[Account {account_id}] {fail_msg}")
                    
                    yield {'type': 'info', 'message': ' '}
                    
                except Exception as e:
                    error_msg = str(e)[:200]
                    channel_error = f'Channel error: {error_msg}'
                    yield {'type': 'error', 'message': channel_error}
                    logger.error(f"[Account {account_id}] {channel_error}")
                    log_system('ERROR', f'Channel error: {str(e)}', 'message_sender', account_id=account.id, error_details=str(e))
            
            current_time = datetime.now().strftime('%H:%M:%S')
            all_done_msg = f'[{current_time}] All channels completed!'
            yield {'type': 'success', 'message': all_done_msg}
            logger.info(f"[Account {account_id}] {all_done_msg}")
            
            log_system('INFO', f'All channels completed. Total sent: {sent_count}', 'message_sender', account_id=account.id)
            
        except Exception as e:
            error_msg = str(e)[:200]
            yield {'type': 'error', 'message': f'Fatal error: {error_msg}'}
            log_system('ERROR', f'Fatal error in message sender: {str(e)}', 'message_sender', account_id=account.id, error_details=str(e))
            
        finally:
            try:
                await client.disconnect()
            except Exception as e:
                logger.error(f"Error disconnecting client: {str(e)}")
    
    finally:
        try:
            db_session.close()
        except Exception as e:
            logger.error(f"Error closing DB session: {str(e)}")



async def check_proxy_health(proxy):
    try:
        import socket
        
        start_time = datetime.now()
        
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(5)
        result = sock.connect_ex((proxy.host, proxy.port))
        sock.close()
        
        end_time = datetime.now()
        response_time = (end_time - start_time).total_seconds()
        
        if result == 0:
            proxy.status = 'online'
            proxy.response_time = response_time
        else:
            proxy.status = 'offline'
            proxy.response_time = None
            
        proxy.last_checked = datetime.utcnow()
        
        return result == 0, response_time
        
    except Exception as e:
        proxy.status = 'offline'
        proxy.last_checked = datetime.utcnow()
        proxy.response_time = None
        return False, str(e)






async def get_ip_location(ip_address):
    services = [
        {
            'url': f'http://ip-api.com/json/{ip_address}?fields=status,country,countryCode,city,lat,lon,query',
            'parser': lambda data: {
                'location': f"{data.get('city', 'Unknown')}, {data.get('country', 'Unknown')}",
                'country': data.get('country'),
                'country_code': data.get('countryCode'),
                'city': data.get('city')
            } if data.get('status') == 'success' else None
        },
        {
            'url': f'https://ipapi.co/{ip_address}/json/',
            'parser': lambda data: {
                'location': f"{data.get('city', 'Unknown')}, {data.get('country_name', 'Unknown')}",
                'country': data.get('country_name'),
                'country_code': data.get('country_code'),
                'city': data.get('city')
            } if data.get('country_code') else None
        },
        {
            'url': f'https://ipwho.is/{ip_address}',
            'parser': lambda data: {
                'location': f"{data.get('city', 'Unknown')}, {data.get('country', 'Unknown')}",
                'country': data.get('country'),
                'country_code': data.get('country_code'),
                'city': data.get('city')
            } if data.get('success') else None
        }
    ]
    
    for service in services:
        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                response = await client.get(service['url'])
                if response.status_code == 200:
                    data = response.json()
                    result = service['parser'](data)
                    if result:
                        logger.info(f"Location found for {ip_address}: {result.get('location')}")
                        return result
        except Exception as e:
            logger.warning(f"Error with geolocation service: {str(e)}")
            continue
    
    logger.error(f"All geolocation services failed for {ip_address}")
    return None


async def get_proxy_real_ip(proxy):
    try:
        if proxy.protocol in ['socks5', 'socks4']:
            if proxy.username and proxy.password:
                proxy_url = f"{proxy.protocol}://{proxy.username}:{proxy.password}@{proxy.host}:{proxy.port}"
            else:
                proxy_url = f"{proxy.protocol}://{proxy.host}:{proxy.port}"
        else:
            if proxy.username and proxy.password:
                proxy_url = f"http://{proxy.username}:{proxy.password}@{proxy.host}:{proxy.port}"
            else:
                proxy_url = f"http://{proxy.host}:{proxy.port}"
        
        ip_check_services = [
            'https://api.ipify.org?format=json',
            'http://api.ipify.org?format=json'
        ]
        
        for service in ip_check_services:
            try:
                transport = httpx.AsyncHTTPTransport(proxy=proxy_url)
                async with httpx.AsyncClient(transport=transport, timeout=15.0) as client:
                    response = await client.get(service)
                    if response.status_code == 200:
                        if 'json' in service:
                            data = response.json()
                            real_ip = data.get('ip', '').strip()
                        else:
                            real_ip = response.text.strip()
                        
                        if real_ip and len(real_ip) > 6:
                            logger.info(f"Proxy {proxy.host}:{proxy.port} real IP: {real_ip}")
                            return real_ip
            except Exception as e:
                logger.debug(f"IP check via proxy failed with {service}: {str(e)}")
                continue
        
        logger.info(f"Could not get real IP via proxy, using proxy host: {proxy.host}")
        return proxy.host
        
    except Exception as e:
        logger.error(f"Error getting proxy real IP: {str(e)}")
        return proxy.host
    services = [
        {
            'url': f'http://ip-api.com/json/{ip_address}?fields=status,country,countryCode,city,lat,lon,query',
            'parser': lambda data: {
                'location': f"{data.get('city', 'Unknown')}, {data.get('country', 'Unknown')}",
                'country': data.get('country'),
                'country_code': data.get('countryCode'),
                'city': data.get('city')
            } if data.get('status') == 'success' else None
        },
        {
            'url': f'https://ipapi.co/{ip_address}/json/',
            'parser': lambda data: {
                'location': f"{data.get('city', 'Unknown')}, {data.get('country_name', 'Unknown')}",
                'country': data.get('country_name'),
                'country_code': data.get('country_code'),
                'city': data.get('city')
            } if data.get('country_code') else None
        },
        {
            'url': f'https://ipwho.is/{ip_address}',
            'parser': lambda data: {
                'location': f"{data.get('city', 'Unknown')}, {data.get('country', 'Unknown')}",
                'country': data.get('country'),
                'country_code': data.get('country_code'),
                'city': data.get('city')
            } if data.get('success') else None
        }
    ]
    
    for service in services:
        try:
            async with httpx.AsyncClient(timeout=10.0) as client:
                response = await client.get(service['url'])
                if response.status_code == 200:
                    data = response.json()
                    result = service['parser'](data)
                    if result:
                        logger.info(f"Location found for {ip_address}: {result.get('location')}")
                        return result
        except Exception as e:
            logger.warning(f"Error with geolocation service: {str(e)}")
            continue
    
    logger.error(f"All geolocation services failed for {ip_address}")
    return None



@app.route('/api/proxy/add', methods=['POST'])
@login_required
def add_proxy():
    try:
        data = request.json
        
        host = data.get('host', '').strip()
        port = data.get('port')
        username = data.get('username', '').strip() or None
        password = data.get('password', '').strip() or None
        protocols = data.get('protocols', ['socks5'])
        
        if not host or not port:
            return jsonify({'success': False, 'message': 'Host and port are required'}), 400
        
        try:
            port = int(port)
            if port < 1 or port > 65535:
                return jsonify({'success': False, 'message': 'Port must be in range 1-65535'}), 400
        except ValueError:
            return jsonify({'success': False, 'message': 'Port must be a number'}), 400
        
        if not isinstance(protocols, list) or len(protocols) == 0:
            protocols = ['socks5']
        
        valid_protocols = ['socks5', 'socks4', 'http', 'https']
        for protocol in protocols:
            if protocol not in valid_protocols:
                return jsonify({'success': False, 'message': f'Invalid protocol: {protocol}'}), 400
        
        added_proxies = []
        for protocol in protocols:
            existing = Proxy.query.filter_by(host=host, port=port, protocol=protocol).first()
            if existing:
                continue
            
            proxy = Proxy(
                host=host,
                port=port,
                username=username if username else None,
                password=password if password else None,
                protocol=protocol,
                status='checking'
            )
            
            db.session.add(proxy)
            db.session.flush()
            
            success, result = asyncio.run(check_proxy_health(proxy))
            
            if success:
                real_ip = asyncio.run(get_proxy_real_ip(proxy))
                location_info = asyncio.run(get_ip_location(real_ip))
                
                if location_info:
                    proxy.location = location_info.get('location')
                    proxy.country = location_info.get('country')
                    proxy.country_code = location_info.get('country_code')
                    proxy.city = location_info.get('city')
            
            added_proxies.append(proxy.to_dict())
        
        db.session.commit()
        
        if len(added_proxies) == 0:
            return jsonify({'success': False, 'message': 'All proxies already exist'}), 400
        
        proxy_list = ', '.join([f"{p['protocol'].upper()}" for p in added_proxies])
        log_activity('proxy_added', f'Proxy added: {host}:{port} ({proxy_list})', 'success')
        log_system('INFO', f'Proxy added: {host}:{port} ({proxy_list})', 'proxy_manager')
        
        return jsonify({
            'success': True,
            'message': f'Proxy added successfully',
            'proxies': added_proxies
        })
        
    except Exception as e:
        db.session.rollback()
        logger.error(f"Error adding proxy: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': f'Error: {str(e)}'}), 500


@app.route('/api/proxy/list', methods=['GET'])
@login_required
def list_proxies():
    try:
        proxies = Proxy.query.order_by(Proxy.created_at.desc()).all()
        return jsonify({
            'success': True,
            'proxies': [p.to_dict() for p in proxies]
        })
    except Exception as e:
        logger.error(f"Error listing proxies: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500


@app.route('/api/system/ip', methods=['GET'])
@login_required
def get_server_ip():
    try:
        import requests as req
        services = [
            'https://api.ipify.org',
            'https://icanhazip.com',
            'https://ifconfig.me/ip'
        ]
        
        for service in services:
            try:
                response = req.get(service, timeout=5)
                if response.status_code == 200:
                    ip = response.text.strip()
                    logger.info(f"Server IP detected: {ip}")
                    return jsonify({
                        'success': True,
                        'ip': ip,
                        'message': f'Server IP: {ip}',
                        'instructions': [
                            'Copy this IP address',
                            'Add it to your proxy provider whitelist',
                            'Wait 5-10 minutes',
                            'Try connecting again'
                        ]
                    })
            except:
                continue
        
        return jsonify({
            'success': False,
            'message': 'Could not detect server IP'
        }), 500
        
    except Exception as e:
        logger.error(f"Error getting server IP: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500


@app.route('/api/proxy/test/<int:proxy_id>', methods=['POST'])
@login_required
def test_proxy_connection(proxy_id):
    try:
        proxy = db.session.get(Proxy, proxy_id)
        if not proxy:
            return jsonify({'success': False, 'message': 'Proxy not found'}), 404
        
        import socks
        import socket
        
        if proxy.protocol == 'socks5':
            proxy_type = socks.SOCKS5
        elif proxy.protocol == 'socks4':
            proxy_type = socks.SOCKS4
        else:
            proxy_type = socks.HTTP
        
        username = proxy.username.strip() if proxy.username and proxy.username.strip() else None
        password = proxy.password.strip() if proxy.password and proxy.password.strip() else None
        
        test_results = []
        
        test_results.append({
            'test': 'Configuration',
            'status': 'info',
            'message': f'Testing {proxy.protocol.upper()} proxy {proxy.host}:{proxy.port}'
        })
        
        if username and password:
            test_results.append({
                'test': 'Auth Status',
                'status': 'info',
                'message': f'Using authentication (user: {username})'
            })
        else:
            test_results.append({
                'test': 'Auth Status',
                'status': 'info',
                'message': 'No authentication'
            })
        
        try:
            sock = socks.socksocket()
            
            if username and password:
                sock.set_proxy(proxy_type, proxy.host, proxy.port, True, username, password)
            else:
                sock.set_proxy(proxy_type, proxy.host, proxy.port)
            
            sock.settimeout(15)
            sock.connect(("telegram.org", 443))
            
            test_results.append({
                'test': 'Connection Test',
                'status': 'success',
                'message': 'Successfully connected to telegram.org:443'
            })
            
            sock.close()
            
            log_system('INFO', f'Proxy test successful: {proxy.host}:{proxy.port}', 'proxy_manager')
            
            return jsonify({
                'success': True,
                'message': 'Proxy is working correctly',
                'results': test_results
            })
            
        except socks.ProxyError as e:
            error_msg = str(e)
            test_results.append({
                'test': 'Connection Test',
                'status': 'error',
                'message': f'Proxy error: {error_msg}'
            })
            
            if "407" in error_msg:
                test_results.append({
                    'test': 'Diagnosis',
                    'status': 'warning',
                    'message': 'Authentication failed. Username or password is incorrect.'
                })
                test_results.append({
                    'test': 'Action Required',
                    'status': 'info',
                    'message': 'Contact proxy provider to verify credentials or check if IP needs to be whitelisted'
                })
            
            log_system('WARNING', f'Proxy test failed: {proxy.host}:{proxy.port} - {error_msg}', 'proxy_manager')
            
            return jsonify({
                'success': False,
                'message': 'Proxy connection failed',
                'results': test_results
            })
            
        except socket.timeout:
            test_results.append({
                'test': 'Connection Test',
                'status': 'error',
                'message': 'Connection timeout - proxy server not responding'
            })
            
            return jsonify({
                'success': False,
                'message': 'Connection timeout',
                'results': test_results
            })
            
        except Exception as e:
            test_results.append({
                'test': 'Connection Test',
                'status': 'error',
                'message': str(e)
            })
            
            return jsonify({
                'success': False,
                'message': 'Connection error',
                'results': test_results
            })
            
    except Exception as e:
        logger.error(f"Error testing proxy: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500


@app.route('/api/proxy/check/<int:proxy_id>', methods=['POST'])
@login_required
def check_proxy(proxy_id):
    try:
        proxy = db.session.get(Proxy, proxy_id)
        if not proxy:
            return jsonify({'success': False, 'message': 'Proxy not found'}), 404
        
        proxy.status = 'checking'
        db.session.commit()
        
        success, result = asyncio.run(check_proxy_health(proxy))
        
        if success:
            real_ip = asyncio.run(get_proxy_real_ip(proxy))
            location_info = asyncio.run(get_ip_location(real_ip))
            
            if location_info:
                proxy.location = location_info.get('location')
                proxy.country = location_info.get('country')
                proxy.country_code = location_info.get('country_code')
                proxy.city = location_info.get('city')
        
        db.session.commit()
        
        if success:
            log_system('INFO', f'Proxy checked: {proxy.host}:{proxy.port} - {proxy.status} ({proxy.location or "Unknown location"})', 'proxy_manager', account_id=None)
            return jsonify({
                'success': True,
                'message': f'Proxy {proxy.status}',
                'proxy': proxy.to_dict()
            })
        else:
            log_system('WARNING', f'Proxy check failed: {proxy.host}:{proxy.port}', 'proxy_manager', error_details=result)
            return jsonify({
                'success': True,
                'message': f'Proxy offline',
                'proxy': proxy.to_dict()
            })
            
    except Exception as e:
        db.session.rollback()
        logger.error(f"Error checking proxy: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500


@app.route('/api/proxy/delete/<int:proxy_id>', methods=['DELETE'])
@login_required
def delete_proxy(proxy_id):
    try:
        proxy = db.session.get(Proxy, proxy_id)
        if not proxy:
            return jsonify({'success': False, 'message': 'Proxy not found'}), 404
        
        accounts_using = TelegramAccount.query.filter_by(proxy_id=proxy_id).count()
        if accounts_using > 0:
            return jsonify({
                'success': False,
                'message': f'This proxy is used by {accounts_using} accounts. Please remove proxy from accounts first'
            }), 400
        
        host_port = f"{proxy.host}:{proxy.port}"
        db.session.delete(proxy)
        db.session.commit()
        
        log_activity('proxy_deleted', f'Proxy deleted: {host_port}', 'success')
        log_system('INFO', f'Proxy deleted: {host_port}', 'proxy_manager')
        
        return jsonify({'success': True, 'message': 'Proxy deleted'})
        
    except Exception as e:
        db.session.rollback()
        logger.error(f"Error deleting proxy: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500


@app.route('/api/proxy/toggle/<int:proxy_id>', methods=['POST'])
@login_required
def toggle_proxy(proxy_id):
    try:
        proxy = db.session.get(Proxy, proxy_id)
        if not proxy:
            return jsonify({'success': False, 'message': 'Proxy not found'}), 404
        
        proxy.is_active = not proxy.is_active
        db.session.commit()
        
        status = 'enabled' if proxy.is_active else 'disabled'
        log_activity('proxy_toggled', f'Proxy {status}: {proxy.host}:{proxy.port}', 'success')
        
        return jsonify({
            'success': True,
            'message': f'Proxy {status}',
            'proxy': proxy.to_dict()
        })
        
    except Exception as e:
        db.session.rollback()
        logger.error(f"Error toggling proxy: {str(e)}", exc_info=True)
        return jsonify({'success': False, 'message': str(e)}), 500

# ============================================================================
# 🛑 ORPHANED TASKS CLEANUP - Auto-Stop on Railway Restart
# ============================================================================

def cleanup_orphaned_tasks():
    """
    Railway restart bo'lganda qolgan task'larni tozalaydi.
    2 soatdan ortiq davom etgan task'larni to'xtatadi.

    Bu funksiya har 5 daqiqada background threadda ishga tushadi.
    """
    try:
        with app.app_context():
            cutoff_time = datetime.utcnow() - timedelta(hours=2)

            orphaned = ActiveTask.query.filter(
                ActiveTask.task_type == 'send_messages',
                ActiveTask.started_at < cutoff_time,
                ActiveTask.is_completed == False
            ).all()

            for task in orphaned:
                logger.warning(f"🧹 Cleaning up orphaned task: account {task.account_id}, started at {task.started_at}")
                task.is_completed = True
                task.stop_requested = True
                task.completed_at = datetime.utcnow()

            if orphaned:
                db.session.commit()
                logger.info(f"✅ Cleaned up {len(orphaned)} orphaned tasks")

    except Exception as e:
        logger.error(f"Error cleaning orphaned tasks: {e}")
        try:
            db.session.rollback()
        except:
            pass

def background_cleanup_worker():
    """
    Background thread - har 5 daqiqada orphaned tasks'ni tozalaydi.
    Railway restart bo'lganda qolgan task'larni avtomatik to'xtatadi.
    """
    import time
    while True:
        try:
            time.sleep(300)  # 5 daqiqa
            cleanup_orphaned_tasks()
        except Exception as e:
            logger.error(f"Error in background cleanup: {e}")

# Background cleanup thread'ni ishga tushiramiz
cleanup_bg_thread = threading.Thread(
    target=background_cleanup_worker,
    daemon=True,
    name="CleanupWorker"
)
cleanup_bg_thread.start()
logger.info("✅ Started background cleanup thread - orphaned tasks will be auto-cleaned every 5 minutes")

# ============================================================================

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5000))
    debug_mode = os.environ.get('FLASK_ENV', 'production') != 'production'
    
    logger.info("=" * 60)
    logger.info("Starting Telegram Channel Manager")
    logger.info(f"Port: {port}")
    logger.info(f"Debug mode: {debug_mode}")
    logger.info("=" * 60)
    
    with app.app_context():
        try:
            proxies = Proxy.query.all()
            updated_count = 0
            for proxy in proxies:
                changed = False
                if proxy.username is not None and not proxy.username.strip():
                    proxy.username = None
                    changed = True
                if proxy.password is not None and not proxy.password.strip():
                    proxy.password = None
                    changed = True
                if changed:
                    updated_count += 1
            
            if updated_count > 0:
                db.session.commit()
                logger.info(f"Cleaned up {updated_count} proxy credentials")
        except Exception as e:
            logger.warning(f"Could not clean proxy credentials: {str(e)}")
    
    log_system('INFO', 'Application started', 'system')
    
    try:
        app.run(debug=debug_mode, host='0.0.0.0', port=port)
    except KeyboardInterrupt:
        logger.info("Application stopped by user")
        log_system('INFO', 'Application stopped by user', 'system')
    except Exception as e:
        logger.error(f"Application error: {str(e)}", exc_info=True)
        log_system('ERROR', f'Application error: {str(e)}', 'system')
