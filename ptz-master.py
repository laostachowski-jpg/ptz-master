#!/usr/bin/env python3
# -*- coding: utf-8 -*-
VERSION = "9.0.34"
__doc__ = f"""
#--###========================================================###--#
# 🎥  Name:         PTZ Master - Professional IP Camera Control
#                   Designed for Linux systems 🎯 🛡️ 🎥 ✨ ▶️
# ⚙️  Version:      {VERSION}
# 👨‍💻  Author:       Leszek Ostachowski (with Claude, DeepSeek, Gemini AI assistance)
# 🎯  Purpose:      Interactive TUI for IP camera control via mpv
#                   Supports RTSP, V4L2, USB camera, play video files and SANE scanners
#
# 🚀  Usage:        python3 ptz-master.py
#                   ./ptz-master.py --help
#                   python3 ptz-master.py -r
#                   python3 ptz-master.py -p <video_file>
#                   python3 ptz-master.py -pl <video_files>  # playlist with loop
#
# 🔧  Dependencies: Python 3.6+, mpv, ffprobe, ffmpeg, sane-utils (scanimage), ImageMagick (convert)
#                   xdotool (X11 player positioning)
#                   kdotool (Wayland/KDE player positioning)
#
# 📄  License:      Free software. Modify and redistribute under GPL v2.
#                   Authors provide NO WARRANTY.
#
#-###====== End Info_data - 🎯 🛡 🎥 ✨ ↑/↓ ←/→ 🔄 🎮 ======###-#
"""
import hashlib
import base64
import datetime
import os
import requests
import time
import sys
try:
    import tty
    import termios
    _UNIX_TTY = True
except ImportError:
    _UNIX_TTY = False
import select
import json
import re
import subprocess
import unicodedata
import socket
import logging
import atexit
import shutil
import platform
import glob
import html
import threading
import shlex
import textwrap
from contextlib import contextmanager
from typing import Optional, Dict, List, Tuple
from enum import Enum
from concurrent.futures import ThreadPoolExecutor, as_completed
from requests.adapters import HTTPAdapter
try:
    from urllib3.util.retry import Retry
    RETRY_AVAILABLE = True
except ImportError:
    RETRY_AVAILABLE = False
# --- Inicjalizacja ścieżek i logowania ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOG_DIR  = os.path.join(BASE_DIR, "logs")
if not os.path.exists(LOG_DIR):
    try:
        os.makedirs(LOG_DIR)
    except Exception:
        LOG_DIR = "/tmp"
LOG_FILE = os.path.join(LOG_DIR, "ptz_master_debug.log")
REC_DIR  = os.path.join(BASE_DIR, "rec")
if not os.path.exists(REC_DIR):
    try:
        os.makedirs(REC_DIR)
    except Exception:
        REC_DIR = "/tmp"
SCAN_DIR = os.path.join(BASE_DIR, "scans")
if not os.path.exists(SCAN_DIR):
    try:
        os.makedirs(SCAN_DIR)
    except Exception:
        SCAN_DIR = "/tmp"
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(LOG_FILE, encoding='utf-8'),
    ]
)
DEFAULT_CONFIG = "ptz_master_config.json"

class Colors:
    GREEN = "\033[92m"
    RED = "\033[91m"
    YELLOW = "\033[93m"
    BLUE = "\033[94m"
    MAGENTA = "\033[95m"
    CYAN = "\033[96m"
    WHITE = "\033[97m"
    RESET = "\033[0m"
    DIM = "\033[2m"

GRN = Colors.GREEN
RED = Colors.RED
YLW = Colors.YELLOW
BLU = Colors.BLUE
MAG = Colors.MAGENTA
CYN = Colors.CYAN
WHT = Colors.WHITE
RST  = Colors.RESET
DIM  = Colors.DIM

# =============================================================================
# ARGUMENT PARSING
# =============================================================================

_VIDEO_MAGIC_SIGS = [
    (b'\x1a\x45\xdf\xa3', 4, None),
    (b'RIFF', 4, None),
    (b'\x30\x26\xb2\x75', 4, None),
    (b'FLV', 3, None),
    (b'OggS', 4, None),
    (b'\x00\x00\x01\xb3', 4, None),
    (b'\x00\x00\x01\xba', 4, None),
    (b'\x00\x00\x00', 4, lambda h: h[4:8] in (b'ftyp', b'mdat', b'moov')),
]

def _has_video_magic(path: str) -> bool:
    try:
        with open(path, 'rb') as f:
            header = f.read(16)
        for magic, n, extra in _VIDEO_MAGIC_SIGS:
            if header[:n] == magic[:n]:
                if extra is None or extra(header):
                    return True
        return False
    except OSError:
        return False

def parse_arguments() -> Tuple[str, bool, bool, str, str, list]:
    import glob as _glob

    def _is_video(path: str) -> bool:
        if not os.path.isfile(path):
            ext = os.path.splitext(path)[1].lower()
            return bool(ext) and ext not in {'.json', '.conf', '.cfg', '.ini', '.txt', '.yaml', '.yml'}
        
        video_exts = {'.mp4', '.avi', '.mkv', '.mov', '.wmv', '.flv', '.webm', 
                     '.m4v', '.mpg', '.mpeg', '.ts', '.m2ts', '.3gp', '.ogv', '.mp3'}
        
        ext = os.path.splitext(path)[1].lower()
        if ext in video_exts:
            return True
            
        try:
            result = subprocess.run(
                ['ffprobe', '-v', 'quiet',
                 '-select_streams', 'v:0',
                 '-show_entries', 'stream=codec_type',
                 '-of', 'csv=p=0', path],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=3
            )
            return 'video' in result.stdout.decode('utf-8', errors='replace').strip()
        except (FileNotFoundError, subprocess.TimeoutExpired, subprocess.CalledProcessError):
            return ext in video_exts

    config_file  = DEFAULT_CONFIG
    debug_mode   = False
    restore_mode = False
    start_index  = ""
    start_mac    = ""
    player_files = []

    args = sys.argv[1:]
    i = 0
    player_mode   = False
    playlist_mode = False
    while i < len(args):
        arg = args[i]
        if arg in ('--help', '-h'):
            print(__doc__)
            print(f"  Version: {VERSION}")
            print(f"\nOptions:")
            print(f"  -h, --help          Show this help")
            print(f"  -d, --debug         Enable debug logging")
            print(f"  -r, --restore       Restore last session")
            print(f"  -p, --player FILE   Play file(s) once (no loop)")
            print(f"  -pl, --player-loop  Loop: single file → loops file; multiple → loops playlist")
            print(f"  -c N                Start on camera N")
            print(f"  --mac MAC           Start on camera with MAC")
            print(f"  CONFIG              Use config file (default: {DEFAULT_CONFIG})")
            sys.exit(0)
        elif arg in ('--debug', '-d'):
            debug_mode = True
        elif arg in ('--restore', '-r'):
            restore_mode = True
        elif arg in ('-p', '--player'):
            player_mode = True
        elif arg in ('-pl', '--player-loop'):
            # Loop mode: 1 plik → zapętla plik (--loop-file=inf)
            #            lista  → zapętla listę (każdy plik raz, lista od nowa)
            player_mode   = True
            playlist_mode = True
        elif arg in ('-c', '--camera') and i + 1 < len(args):
            start_index = args[i + 1]; i += 1
        elif arg.startswith('-c') and len(arg) > 2:
            start_index = arg[2:]
        elif arg in ('--mac',) and i + 1 < len(args):
            start_mac = args[i + 1].upper(); i += 1
        elif not arg.startswith('-'):
            if player_mode or _is_video(arg):
                player_mode = True
                expanded = _glob.glob(arg)
                if expanded:
                    player_files.extend(sorted(expanded))
                else:
                    player_files.append(arg)
            else:
                config_file = arg
        i += 1

    return config_file, debug_mode, restore_mode, start_index, start_mac, player_files, playlist_mode

CONFIG_FILE, DEBUG_MODE, RESTORE_MODE, START_CAMERA, START_MAC, PLAYER_FILES, PLAYLIST_LOOP = parse_arguments()

# =============================================================================
# DATA STRUCTURES
# =============================================================================

class CameraType(Enum):
    AUTO = "AUTO"
    ONVIF = "ONVIF"
    DVRIP = "DVRIP"
    RTSP_ONLY = "RTSP_ONLY"
    V4L2 = "V4L2"
    FILE = "FILE"
    SCANNER = "SCANNER"
    UNKNOWN = "UNKNOWN"

class CameraPorts:
    def __init__(self, onvif: int = 80, rtsp: int = 554, dvrip: int = 34567):
        self.onvif = onvif
        self.rtsp = rtsp
        self.dvrip = dvrip
    
    def to_dict(self) -> dict:
        return {"onvif": self.onvif, "rtsp": self.rtsp, "dvrip": self.dvrip}
    
    @classmethod
    def from_dict(cls, data: dict) -> 'CameraPorts':
        return cls(
            onvif=data.get("onvif", 80),
            rtsp=data.get("rtsp", 554),
            dvrip=data.get("dvrip", 34567)
        )

class CameraProfile:
    def __init__(self, name: str = "", token: str = "", uri: str = "",
                 res: str = "N/A", pid: Optional[int] = None, channel: int = 0,
                 fps: int = 0, codec: str = ""):
        self.name = name
        self.token = token
        self.uri = uri
        self.res = res
        self.pid = pid
        self.channel = channel
        self.fps = fps
        self.codec = codec
        self.error = False
        self.ipc_path: Optional[str] = None

    def get_mpv(self) -> Optional['MpvController']:
        if self.ipc_path and self.pid and ProcessManager.is_running(self.pid):
            return MpvController(self.ipc_path)
        return None
    
    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "token": self.token,
            "uri": self.uri,
            "res": self.res,
            "pid": self.pid,
            "channel": self.channel,
            "fps": self.fps,
            "codec": self.codec
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'CameraProfile':
        return cls(
            name=data.get("name", "Unknown"),
            token=data.get("token", "unknown"),
            uri=data.get("uri", ""),
            res=data.get("res", "N/A"),
            pid=None,  # nie ładuj PID z pliku — przy starcie zawsze "not running"
            channel=data.get("channel", 0),
            fps=data.get("fps", 0),
            codec=data.get("codec", "")
        )

class PresetPosition:
    def __init__(self, pan: float = 0.0, tilt: float = 0.0, zoom: float = 0.0):
        self.pan = pan
        self.tilt = tilt
        self.zoom = zoom
    
    def to_dict(self) -> dict:
        return {"pan": self.pan, "tilt": self.tilt, "zoom": self.zoom}
    
    @classmethod
    def from_dict(cls, data: dict) -> 'PresetPosition':
        return cls(
            pan=data.get("pan", 0.0),
            tilt=data.get("tilt", 0.0),
            zoom=data.get("zoom", 0.0)
        )

class WindowLayout:
    def __init__(self, x: int = 100, y: int = 100, w: int = 640, h: int = 360):
        self.x = x
        self.y = y
        self.w = w
        self.h = h
    
    def to_dict(self) -> dict:
        return {"x": self.x, "y": self.y, "w": self.w, "h": self.h}
    
    @classmethod
    def from_dict(cls, data: dict) -> 'WindowLayout':
        return cls(
            x=data.get("x", 100),
            y=data.get("y", 100),
            w=data.get("w", 640),
            h=data.get("h", 360)
        )

class SessionState:
    def __init__(self, active_camera_index: int = 0, 
                 playing_cameras: Optional[List[Dict[str, int]]] = None, 
                 timestamp: str = ""):
        self.active_camera_index = active_camera_index
        self.playing_cameras = playing_cameras or []
        self.timestamp = timestamp
    
    def to_dict(self) -> dict:
        return {
            "active_camera_index": self.active_camera_index,
            "playing_cameras": self.playing_cameras,
            "timestamp": self.timestamp
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'SessionState':
        return cls(
            active_camera_index=data.get("active_camera_index", 0),
            playing_cameras=data.get("playing_cameras", []),
            timestamp=data.get("timestamp", "")
        )

class Camera:
    DEFAULT_IMAGE_PARAMS = {
        "brightness": 0, "contrast": 0, "saturation": 0,
        "gamma": 0, "hue": 0, "volume": 100, "mute": False, "speed": 1.0
    }

    def __init__(self, name: str = "New Camera", ip: str = "192.168.1.10",
                 mac: str = "UNKNOWN", ports: Optional[CameraPorts] = None,
                 user: str = "admin", password: str = "admin",
                 profiles: Optional[List[CameraProfile]] = None,
                 cam_type: Optional[CameraType] = None, active_profile: int = 0,
                 presets: Optional[Dict[str, PresetPosition]] = None,
                 speed: float = 0.5, duration: float = 0.4,
                 layout: Optional[WindowLayout] = None, device: str = "",
                 file_path: str = "", file_loop: bool = True,
                 file_speed: float = 1.0, file_start: float = 0.0,
                 image_params: Optional[dict] = None):
        self.name = name
        self.ip = ip
        self.mac = mac
        self.ports = ports or CameraPorts()
        self.user = user
        self.password = password
        self.profiles = profiles or []
        self.type = cam_type or CameraType.AUTO
        self.active_profile = active_profile
        self.presets = presets or {}
        self.speed = speed
        self.duration = duration
        self.layout = layout
        self.device = device
        self.file_path  = file_path
        self.file_loop  = file_loop
        self.file_speed = file_speed
        self.file_start = file_start
        self.image_params: dict = dict(self.DEFAULT_IMAGE_PARAMS)
        if image_params:
            self.image_params.update(image_params)
        # Scanner params (CameraType.SCANNER)
        self.scan_device  = ""            # SANE device string (dynamiczny, zmienia się po restarcie)
        self.scan_vidpid  = ""            # USB VID:PID np. "04a9:220e" — stały identyfikator
        self.scan_mode    = "gray"        # color | gray | lineart
        self.scan_dpi     = 300
        self.scan_area    = "0:0:215:297" # x:y:w:h mm
        self.scan_format  = "jpg"         # jpg | png | pdf | tiff
        self.scan_quality = 75
        self.scan_resize  = "1240x1754"   # WxH po konwersji
        self.scan_desc    = ""            # opis do nazwy pliku
        self.scan_dest    = SCAN_DIR      # katalog docelowy
        self.scan_viewer  = "mpv"         # przeglądarka: mpv|gwenview|xdg-open|eog|feh

    def to_dict(self) -> dict:
        result = {
            "name": self.name,
            "ip": self.ip,
            "mac": self.mac,
            "ports": self.ports.to_dict(),
            "user": self.user,
            "password": self.password,
            "profiles": [p.to_dict() for p in self.profiles],
            "type": self.type.value,
            "active_profile": self.active_profile,
            "presets": {k: v.to_dict() for k, v in self.presets.items()},
            "speed": self.speed,
            "duration": self.duration
        }
        if self.layout:
            result["layout"] = self.layout.to_dict()
        if self.device:
            result["device"] = self.device
        if self.type == CameraType.FILE:
            result["file_path"]  = self.file_path
            result["file_loop"]  = self.file_loop
            result["file_speed"] = self.file_speed
            result["file_start"] = self.file_start
        if self.image_params != self.DEFAULT_IMAGE_PARAMS:
            result["image_params"] = self.image_params
        if self.type == CameraType.SCANNER:
            result["scan_device"]  = self.scan_device
            result["scan_vidpid"]  = self.scan_vidpid
            result["scan_mode"]    = self.scan_mode
            result["scan_dpi"]     = self.scan_dpi
            result["scan_area"]    = self.scan_area
            result["scan_format"]  = self.scan_format
            result["scan_quality"] = self.scan_quality
            result["scan_resize"]  = self.scan_resize
            result["scan_desc"]    = self.scan_desc
            result["scan_dest"]    = self.scan_dest
            result["scan_viewer"]  = self.scan_viewer
        return result

    @classmethod
    def from_dict(cls, data: dict) -> 'Camera':
        ports = CameraPorts.from_dict(data.get("ports", {}))
        profiles = [CameraProfile.from_dict(p) for p in data.get("profiles", [])]
        type_str = data.get("type", "AUTO")
        try:
            cam_type = CameraType(type_str)
        except ValueError:
            cam_type = CameraType.AUTO
        presets = {}
        for k, v in data.get("presets", {}).items():
            presets[k] = PresetPosition.from_dict(v)
        layout = None
        if "layout" in data:
            layout = WindowLayout.from_dict(data["layout"])
        obj = cls(
            name=data.get("name", "New Camera"),
            ip=data.get("ip", "192.168.1.10"),
            mac=data.get("mac", "UNKNOWN"),
            ports=ports,
            user=data.get("user", "admin"),
            password=data.get("password", "admin"),
            profiles=profiles,
            cam_type=cam_type,
            active_profile=data.get("active_profile", 0),
            presets=presets,
            speed=data.get("speed", 0.5),
            duration=data.get("duration", 0.4),
            layout=layout,
            device=data.get("device", ""),
            file_path=data.get("file_path", ""),
            file_loop=data.get("file_loop", True),
            file_speed=data.get("file_speed", 1.0),
            file_start=data.get("file_start", 0.0),
            image_params=data.get("image_params", None),
        )
        if cam_type == CameraType.SCANNER:
            obj.scan_device  = data.get("scan_device",  "")
            obj.scan_vidpid  = data.get("scan_vidpid",  "")
            obj.scan_mode    = data.get("scan_mode",    "gray")
            obj.scan_dpi     = data.get("scan_dpi",     300)
            obj.scan_area    = data.get("scan_area",    "0:0:215:297")
            obj.scan_format  = data.get("scan_format",  "jpg")
            obj.scan_quality = data.get("scan_quality", 75)
            obj.scan_resize  = data.get("scan_resize",  "1240x1754")
            obj.scan_desc    = data.get("scan_desc",    "")
            obj.scan_dest    = data.get("scan_dest",    SCAN_DIR)
            obj.scan_viewer  = data.get("scan_viewer",  "mpv")
        return obj

MPV_DEFAULT_CMD = (
    "mpv --rtsp-transport=tcp --no-border "
    "--hwdec=vaapi-copy --hwdec-codecs=all "
    "--cache=yes --cache-secs=10 "
    "--video-sync=display-vdrop --framedrop=vo "
    "--network-timeout=10 --profile=fast"
)

def _migrate_player_cmd(cmd: str) -> str:
    if cmd.startswith('ffplay'):
        return MPV_DEFAULT_CMD
    while cmd.startswith('mpv mpv'):
        cmd = cmd[4:]
    return cmd.strip() or MPV_DEFAULT_CMD

# =============================================================================
# LOGGING
# =============================================================================

class Logger:
    _instance = None
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._setup()
        return cls._instance
    
    def _setup(self):
        self.logger = logging.getLogger("PTZMaster")
        self.logger.setLevel(logging.DEBUG if DEBUG_MODE else logging.INFO)
        # Nie dodawaj handlera jeśli już istnieje (zapobiega duplikatom)
        if not self.logger.handlers:
            file_handler = logging.FileHandler(LOG_FILE)
            file_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
            if DEBUG_MODE:
                file_handler.setLevel(logging.DEBUG)
            self.logger.addHandler(file_handler)
        # Wyłącz propagację do root loggera (który już loguje do tego samego pliku)
        self.logger.propagate = False
    
    def debug(self, msg, **kwargs):
        self.logger.debug(msg, **kwargs)

    def info(self, msg, **kwargs):
        self.logger.info(msg, **kwargs)

    def warning(self, msg, **kwargs):
        self.logger.warning(msg, **kwargs)

    def error(self, msg, **kwargs):
        self.logger.error(msg, **kwargs)

    def critical(self, msg, **kwargs):
        self.logger.critical(msg, **kwargs)

    def exception(self, msg, **kwargs):
        self.logger.exception(msg, **kwargs)

logger = Logger()

# =============================================================================
# DEPENDENCY CHECK
# =============================================================================

REQUIRED_CRITICAL = ['mpv', 'ffprobe']
REQUIRED_OPTIONAL = ['ping', 'ip', 'xdotool', 'wmctrl', 'v4l2-ctl', 'socat',
                     'ffmpeg', 'kdotool', 'fuser', 'scanimage', 'convert']

def _win_tool_available() -> bool:
    """Zwraca True jeśli dostępne narzędzie do zapisu/odczytu geometrii okien."""
    return any(shutil.which(t) for t in ('xdotool', 'kdotool'))

def _detect_distro() -> tuple:
    """Zwraca (os_id, pretty_name) na podstawie /etc/os-release."""
    os_id, pretty = "unknown", "Unknown Linux"
    try:
        with open('/etc/os-release') as f:
            info = {}
            for line in f:
                line = line.strip()
                if '=' in line:
                    k, v = line.split('=', 1)
                    info[k] = v.strip('"')
        # ID_LIKE daje rodzinę (np. "opensuse" dla Tumbleweed)
        os_id   = info.get('ID_LIKE', info.get('ID', 'unknown')).lower()
        pretty  = info.get('PRETTY_NAME', os_id)
    except Exception:
        pass
    return os_id, pretty

def check_dependencies() -> None:
    """Sprawdź zależności i wypisz instrukcje instalacji dla wykrytego distro."""
    os_id, pretty_name = _detect_distro()

    # Wykryj rodzinę dystrybucji
    is_debian = any(k in os_id for k in ('debian','ubuntu','mint','pop','kali','raspbian'))
    is_arch   = any(k in os_id for k in ('arch','manjaro','cachyos','endeavour','garuda','biglinux'))
    is_suse   = any(k in os_id for k in ('suse','opensuse'))
    is_fedora = any(k in os_id for k in ('fedora','rhel','centos','rocky','alma'))

    # Kolory dla distro — podświetl wykryte, przyciemnij pozostałe
    C_ACT = f"{YLW}\033[1m"   # aktywne — żółty bold
    C_DIM = f"{DIM}"           # nieaktywne — przyciemnione

    C_DEB = C_ACT if is_debian else C_DIM
    C_ARC = C_ACT if is_arch   else C_DIM
    C_SUS = C_ACT if is_suse   else C_DIM
    C_FED = C_ACT if is_fedora else C_DIM

    # Komendy instalacji dla każdego narzędzia
    INSTALL = {
        'mpv': {
            'desc': 'Media player (WYMAGANY)',
            'deb': 'sudo apt install mpv',
            'arc': 'sudo pacman -S mpv',
            'sus': 'sudo zypper install mpv',
            'fed': 'sudo dnf install mpv',
        },
        'ffprobe': {
            'desc': 'Analiza strumieni wideo (WYMAGANY — część ffmpeg)',
            'deb': 'sudo apt install ffmpeg',
            'arc': 'sudo pacman -S ffmpeg',
            'sus': 'sudo zypper install ffmpeg',
            'fed': 'sudo dnf install ffmpeg',
        },
        'ffmpeg': {
            'desc': 'Ekstrakcja klipów [R]EC',
            'deb': 'sudo apt install ffmpeg',
            'arc': 'sudo pacman -S ffmpeg',
            'sus': 'sudo zypper install ffmpeg',
            'fed': 'sudo dnf install ffmpeg',
        },
        'ping': {
            'desc': 'Test dostępności kamer w sieci',
            'deb': 'sudo apt install iputils-ping',
            'arc': 'sudo pacman -S iputils',
            'sus': 'sudo zypper install iputils',
            'fed': 'sudo dnf install iputils',
        },
        'ip': {
            'desc': 'Wykrywanie kamer (MAC→IP)',
            'deb': 'sudo apt install iproute2',
            'arc': 'sudo pacman -S iproute2',
            'sus': 'sudo zypper install iproute2',
            'fed': 'sudo dnf install iproute2',
        },
        'xdotool': {
            'desc': 'Pozycjonowanie okien mpv (X11)',
            'deb': 'sudo apt install xdotool',
            'arc': 'sudo pacman -S xdotool',
            'sus': 'sudo zypper install xdotool',
            'fed': 'sudo dnf install xdotool',
        },
        'wmctrl': {
            'desc': 'Zarządzanie oknami (X11, alternatywa)',
            'deb': 'sudo apt install wmctrl',
            'arc': 'sudo pacman -S wmctrl',
            'sus': 'sudo zypper install wmctrl',
            'fed': 'sudo dnf install wmctrl',
        },
        'kdotool': {
            'desc': 'Pozycjonowanie okien mpv (KDE/Wayland)',
            'deb': 'pip install kdotool',
            'arc': 'yay -S kdotool  # lub: pip install kdotool',
            'sus': 'pip install kdotool',
            'fed': 'pip install kdotool',
        },
        'v4l2-ctl': {
            'desc': 'Obsługa kamer V4L2/USB',
            'deb': 'sudo apt install v4l-utils',
            'arc': 'sudo pacman -S v4l-utils',
            'sus': 'sudo zypper install v4l2-utils',
            'fed': 'sudo dnf install v4l-utils',
        },
        'socat': {
            'desc': 'Diagnostyka połączeń sieciowych',
            'deb': 'sudo apt install socat',
            'arc': 'sudo pacman -S socat',
            'sus': 'sudo zypper install socat',
            'fed': 'sudo dnf install socat',
        },
    }

    missing_critical = [c for c in REQUIRED_CRITICAL if not shutil.which(c)]

    # Narzędzia do zarządzania oknami mpv:
    # — xdotool lub kdotool potrzebne do ZAPISU pozycji (getwindowgeometry)
    # — wmctrl tylko do sterowania (nie umie czytać geometrii przez PID)
    _geom_tools   = ['xdotool', 'kdotool']   # do zapisu layoutu
    _geom_missing = all(not shutil.which(t) for t in _geom_tools)
    _win_report   = ['xdotool'] if _geom_missing else []   # reprezentant grupy

    missing_optional = _win_report + [
        c for c in REQUIRED_OPTIONAL
        if c not in REQUIRED_CRITICAL
        and c not in _geom_tools + ['wmctrl']
        and not shutil.which(c)
    ]

    # Nic nie brakuje — cicho
    if not missing_critical and not missing_optional:
        return

    W = 72
    def _bar(ch='═'): print(f"{BLU}{'═'*W}{RST}")

    _bar()
    print(f"{BLU}  PTZ Master — sprawdzanie zależności{RST}"
          f"  {DIM}{pretty_name}{RST}")
    _bar()

    def _install_row(cmd):
        info  = INSTALL.get(cmd, {})
        desc  = info.get('desc', '')
        # Specjalny przypadek: xdotool jako reprezentant grupy narzędzi okienkowych
        if cmd == 'xdotool' and _geom_missing:
            print(f"\n  {YLW}▸ Narzędzia do pozycjonowania okien mpv{RST}"
                  f"  {DIM}(brak xdotool / wmctrl / kdotool){RST}")
            print(f"    {C_DEB}Debian/Ubuntu : sudo apt install xdotool{RST}")
            print(f"    {C_ARC}Arch/CachyOS  : sudo pacman -S xdotool  {DIM}lub{RST}{C_ARC}  yay -S kdotool{RST}")
            print(f"    {C_SUS}openSUSE      : sudo zypper install xdotool  {DIM}lub{RST}{C_SUS}  kdotool (AUR/pip){RST}")
            print(f"    {C_FED}Fedora/RHEL   : sudo dnf install xdotool{RST}")
            print(f"    {DIM}KDE/Wayland   : pip install kdotool  {GRN}(najlepsza opcja na KWin){RST}")
            return
        print(f"\n  {YLW}▸ {cmd}{RST}  {DIM}{desc}{RST}")
        if info:
            print(f"    {C_DEB}Debian/Ubuntu : {info['deb']}{RST}")
            print(f"    {C_ARC}Arch/CachyOS  : {info['arc']}{RST}")
            print(f"    {C_SUS}openSUSE      : {info['sus']}{RST}")
            print(f"    {C_FED}Fedora/RHEL   : {info['fed']}{RST}")

    if missing_critical:
        print(f"\n  {RED}✗ BRAKUJĄCE WYMAGANE — program nie uruchomi się:{RST}")
        for cmd in missing_critical:
            _install_row(cmd)
        _bar()
        print(f"\n{RED}Zainstaluj brakujące programy i uruchom ponownie.{RST}\n")
        sys.exit(1)

    if missing_optional:
        print(f"\n  {YLW}○ Opcjonalne — niektóre funkcje będą niedostępne:{RST}")
        for cmd in missing_optional:
            _install_row(cmd)
        _bar()
        print(f"  {DIM}Naciśnij ENTER aby kontynuować...{RST}", end='', flush=True)
        try:
            input()
        except (EOFError, KeyboardInterrupt):
            pass
        print()


# =============================================================================
# READLINE SUPPORT
# =============================================================================

try:
    import readline
    READLINE_AVAILABLE = True
except ImportError:
    READLINE_AVAILABLE = False

def rl_prompt(s: str) -> str:
    return re.sub(r'(\033\[[0-9;]*m)', r'\001\1\002', s)

def rlinput(prompt: str, default: str = '') -> str:
    fd = sys.stdin.fileno()
    old_settings = None
    try:
        old_settings = termios.tcgetattr(fd)
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)

        safe_prompt = rl_prompt(prompt)

        if READLINE_AVAILABLE and default:
            readline.set_startup_hook(lambda: readline.insert_text(str(default)))
            try:
                result = input(safe_prompt)
                if result:
                    readline.add_history(result)
                return result
            finally:
                readline.set_startup_hook()
        else:
            return input(safe_prompt)
    finally:
        if old_settings is not None:
            termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)

# =============================================================================
# HELPERS
# =============================================================================

def _is_wayland() -> bool:
    """Zwraca True jeśli sesja działa na Wayland."""
    return (os.environ.get('WAYLAND_DISPLAY') is not None or
            os.environ.get('XDG_SESSION_TYPE', '').lower() == 'wayland')

def _wayland_compositor() -> str:
    """Wykryj compositor Wayland: 'hyprland', 'sway', 'wlroots', 'kwin', 'unknown'."""
    if os.environ.get('HYPRLAND_INSTANCE_SIGNATURE'):  return 'hyprland'
    if os.environ.get('SWAYSOCK'):                      return 'sway'
    if shutil.which('swaymsg'):                         return 'sway'
    if shutil.which('hyprctl'):                         return 'hyprland'
    if shutil.which('kwin_wayland') or shutil.which('kwin_x11'): return 'kwin'
    return 'unknown'

class Terminal:
    _window_id = None
    _win_tool  = None   # 'xdotool' lub 'kdotool'

    @classmethod
    def _get_win_tool(cls) -> Optional[str]:
        """Zwraca dostępne narzędzie do zarządzania oknami."""
        if cls._win_tool:
            return cls._win_tool
        for t in ('xdotool', 'kdotool'):
            if shutil.which(t):
                cls._win_tool = t
                return t
        return None

    @classmethod
    def capture_window_id(cls):
        tool = cls._get_win_tool()
        if not tool or platform.system() != "Linux":
            return
        # xdotool wymaga DISPLAY, kdotool działa też na Wayland
        if tool == 'xdotool' and not os.environ.get('DISPLAY'):
            return
        try:
            cmd = ["xdotool", "getactivewindow"] if tool == 'xdotool' else \
                  ["kdotool", "getactivewindow"]
            cls._window_id = subprocess.check_output(
                cmd, universal_newlines=True,
                stderr=subprocess.DEVNULL, timeout=1).strip()
            logger.info(f"Terminal window ID: {cls._window_id} (via {tool})")
        except Exception as e:
            logger.warning(f"Could not capture terminal window ID: {e}")

    @classmethod
    def reposition_mpv_window(cls, title: str, layout: 'WindowLayout',
                               max_wait: float = 5.0) -> bool:
        """Po starcie mpv wymuś pozycję/rozmiar przez xdotool lub kdotool.
        Czeka aż okno się pojawi (max max_wait sekund).
        Zwraca True jeśli udało się ustawić pozycję.
        """
        tool = cls._get_win_tool()
        if not tool:
            return False
        x, y, w, h = str(layout.x), str(layout.y), str(layout.w), str(layout.h)
        deadline = time.time() + max_wait
        while time.time() < deadline:
            try:
                # Jedna komenda: search + move + size (atomowa)
                result = subprocess.run(
                    [tool, 'search', '--name', title,
                     'windowmove', x, y,
                     'windowsize', w, h],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL, timeout=3)
                if result.returncode == 0:
                    logger.debug(
                        f"reposition '{title}' → {x},{y} {w}x{h} via {tool}")
                    return True
            except Exception as e:
                logger.debug(f"reposition '{title}': {e}")
            time.sleep(0.3)
        logger.debug(f"reposition '{title}': window not found after {max_wait}s")
        return False

    @classmethod
    def restore_focus(cls, mpv_pid: int = 0,
                      mpv_pids: Optional[List[int]] = None) -> bool:
        tool = cls._get_win_tool()
        if not cls._window_id or not tool:
            return False

        def _wait_for_pid(pid: int, deadline: float) -> None:
            while time.time() < deadline:
                try:
                    r = subprocess.run(
                        [tool, "search", "--pid", str(pid)],
                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                        timeout=1.0)
                    if r.returncode == 0 and r.stdout.strip():
                        return
                except Exception:
                    pass
                time.sleep(0.1)

        try:
            pids = mpv_pids if mpv_pids else ([mpv_pid] if mpv_pid else [])
            if pids:
                deadline = time.time() + 5.0
                for pid in pids:
                    _wait_for_pid(pid, deadline)
                time.sleep(0.15)

            subprocess.run(
                [tool, "windowactivate", "--sync", str(cls._window_id)],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                timeout=2.0
            )
            logger.debug(f"restore_focus: OK → wid={cls._window_id} pids={pids}")
            return True
        except Exception as e:
            logger.debug(f"restore_focus: {e}")
            return False
    
    @classmethod
    def setup_layout(cls, cfg: 'Config', fast: bool = False):
        tool = cls._get_win_tool()
        if not tool:
            return
        # xdotool wymaga DISPLAY; kdotool działa bez
        if tool == 'xdotool' and (platform.system() != "Linux" or not os.environ.get('DISPLAY')):
            return

        if fast:
            cls.restore_focus()
            return

        if not cls._window_id:
            return
        
        layout = cfg.layout.get("terminal", WindowLayout())
        
        try:
            subprocess.run(
                [tool, "windowactivate", cls._window_id],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=0.5
            )
            
            subprocess.run(
                [tool, "windowmove", cls._window_id, str(layout.x), str(layout.y)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=0.5
            )
            
            subprocess.run(
                [tool, "windowsize", cls._window_id, str(layout.w), str(layout.h)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=0.5
            )
            
            logger.info(f"Terminal positioned: ({layout.x},{layout.y}) {layout.w}x{layout.h}")
        except Exception as e:
            logger.debug(f"Error positioning terminal: {e}")

def get_cpu_usage() -> str:
    """Zwraca procent użycia CPU z /proc/stat."""
    try:
        with open('/proc/stat', 'r') as f:
            line = f.readline()
        parts = line.split()
        user, nice, system, idle = int(parts[1]), int(parts[2]), int(parts[3]), int(parts[4])
        total = user + nice + system + idle
        if not hasattr(get_cpu_usage, '_prev'):
            get_cpu_usage._prev = (total, idle)
            return "0%"
        prev_total, prev_idle = get_cpu_usage._prev
        get_cpu_usage._prev = (total, idle)
        d_total = total - prev_total
        d_idle  = idle  - prev_idle
        usage = 100 * (d_total - d_idle) / d_total if d_total > 0 else 0
        return f"{usage:.0f}%"
    except Exception:
        return "??%"


def get_free_space_percent(path: str = "/") -> int:
    """Zwraca procent wolnego miejsca na dysku."""
    try:
        import shutil as _shutil
        stat = _shutil.disk_usage(path)
        return int(100 * stat.free / stat.total)
    except Exception:
        return 0


def _is_keyframe_aligned(filepath: str, time_sec: float) -> bool:
    """Sprawdza czy czas jest wyrównany do klatki kluczowej."""
    try:
        result = subprocess.run(
            ['ffprobe', '-v', 'quiet', '-select_streams', 'v:0',
             '-show_frames', '-read_intervals', '%+1',
             '-of', 'compact=p=0', '-i', filepath,
             '-ss', str(time_sec)],
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, timeout=5
        )
        return b'key_frame=1' in result.stdout
    except Exception:
        return False


def _extract_clip(filepath: str, start: float, end: float,
                  brightness: int = 0, contrast: int = 0,
                  saturation: int = 0, gamma: int = 0, hue: int = 0,
                  output_name: str = None, vcodec_override: str = None,
                  crf: int = 23, extra_vf: str = None) -> bool:
    """Wyciąga fragment wideo z obecnymi filtrami obrazu (ffmpeg w tle)."""
    if not filepath or not os.path.isfile(filepath):
        logger.error(f"_extract_clip: plik nie istnieje: {filepath!r}")
        return False
    if start >= end:
        logger.error(f"_extract_clip: start={start} >= end={end}")
        return False
    vf_filters = []
    if extra_vf:
        vf_filters.append(extra_vf)
    eq_parts = []
    if brightness != 0: eq_parts.append(f"brightness={brightness/100:.2f}")
    if contrast   != 0: eq_parts.append(f"contrast={1 + contrast/100:.2f}")
    if saturation != 0: eq_parts.append(f"saturation={1 + saturation/100:.2f}")
    if gamma      != 0: eq_parts.append(f"gamma={1 + gamma/100:.2f}")
    if hue        != 0: eq_parts.append(f"hue={hue/100:.2f}")
    if eq_parts:
        vf_filters.append("eq=" + ":".join(eq_parts))
    filter_str = ",".join(vf_filters) if vf_filters else None
    if not output_name:
        base = os.path.splitext(filepath)[0]
        output_name = f"{base}_clip_{int(start)}_{int(end)}.mp4"
    if vcodec_override:
        vcodec = vcodec_override
    elif not filter_str and _is_keyframe_aligned(filepath, start):
        vcodec = "copy"
    else:
        vcodec = "libx264"
    if vcodec == "copy":
        cmd = ["ffmpeg", "-y", "-i", filepath,
               "-ss", str(start), "-to", str(end),
               "-c", "copy", output_name]
    else:
        cmd = ["ffmpeg", "-y", "-i", filepath,
               "-ss", str(start), "-to", str(end)]
        if filter_str:
            cmd += ["-vf", filter_str]
        cmd += ["-c:v", vcodec, "-preset", "fast", "-crf", str(crf),
                "-c:a", "aac", "-b:a", "128k", output_name]
    logger.info(f"_extract_clip CMD: {' '.join(cmd)}")
    logger.info(f"_extract_clip vcodec={vcodec} filter={filter_str!r} extra_vf={extra_vf!r}")
    try:
        ffmpeg_log = output_name + ".ffmpeg.log"
        with open(ffmpeg_log, "w") as _flog:
            proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=_flog)
        logger.info(f"_extract_clip PID={proc.pid}  ffmpeg_log={ffmpeg_log}")
        # Usuń log w tle po zakończeniu ffmpeg
        def _rm_log():
            try:
                proc.wait(timeout=600)
                if os.path.exists(ffmpeg_log):
                    os.unlink(ffmpeg_log)
            except Exception:
                pass
        import threading as _thr_ec
        _thr_ec.Thread(target=_rm_log, daemon=True).start()
        return True
    except Exception as e:
        logger.error(f"_extract_clip Popen failed: {e}")
        return False


def ansilen(s: str) -> int:
    """Dokładne liczenie długości dla pozycjonowania myszy"""
    # Używamy standardowego ciągu znaków (bez 'r'), aby \x1b zostało zinterpretowane jako znak Escape.
    clean = re.sub('\x1b\\[[0-9;]*[a-zA-Z]', '', s)
    total = 0
    for c in clean:
        cp = ord(c)
        # Emoji i symbole (większość zajmuje 2 pozycje)
        if cp >= 0x1F000:
            total += 2
        # Znaki CJK (chiński, japoński, koreański)
        elif unicodedata.east_asian_width(c) in ('W', 'F'):
            total += 2
        # Specjalne znaki ramek (║, ═, █, ░)
        elif c in '║═╔╗╚╝╠╣╤╧╪╫╬▀▄█▌▐░▒▓■□▪▫▬▲►▼◄◀►':
            total += 1
        # Zwykłe znaki
        else:
            total += 1
    return total

def pad(text: str, length: int) -> str:
    return text + (" " * max(0, length - ansilen(text)))

def btn_pos(text: str, offset: int = 0) -> dict:
    """Oblicz pozycje przycisków [X] w tekście (bez kolorów ANSI).
    Zwraca {label: (col_start, col_end)} 1-indexed, z opcjonalnym offset.
    Złożone etykiety jak [Q/ESC] są mapowane pod każdym kluczem osobno.
    """
    clean = re.sub(r'\x1b\[[0-9;]*[a-zA-Z]', '', text)
    positions = {}
    for m in re.finditer(r'\[([^\]]+)\]', clean):
        span = (m.start() + 1 + offset, m.end() + offset)
        for key in m.group(1).split('/'):
            positions[key] = span
            positions[key.lower()] = span
    return positions

@contextmanager
def _cooked_input(fd: int):
    """Context manager: przełącz terminal na cooked+echo, wyłącz mysz.
    Użycie:
        with _cooked_input(fd) as _:
            result = input()
    Przywraca raw mode i mysz po wyjściu niezależnie od wyjątków.
    """
    import tty as _tty_cm
    old = termios.tcgetattr(fd)
    try:
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        yield fd
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)
        _tty_cm.setraw(fd)
        sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
        sys.stdout.flush()


def mouse_off():
    sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
    sys.stdout.flush()
    try:
        termios.tcflush(sys.stdin.fileno(), termios.TCIFLUSH)
    except Exception:
        pass

def mouse_on():
    sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
    sys.stdout.flush()

def print_progress_bar(iteration: int, total: int, prefix: str = '', 
                       suffix: str = '', length: int = 30, fill: str = '█'):
    pct = (iteration / total) * 100
    filled = int(length * iteration // total)
    bar = fill * filled + '░' * (length - filled)
    sys.stdout.write(f'\r{prefix} |{bar}| {pct:.1f}% {suffix}'.ljust(80))
    sys.stdout.flush()

def format_progress_line(percent: float, width: int = 20, label: str = "", subnet: str = "") -> str:
    """
    Tworzy linię statusu z paskiem postępu.
    Przykład: "Auto-check: [████████░░░░░░░░░░░░]  40%  192.168.1.0/24"
    """
    filled = int(percent / 100 * width)
    bar = '█' * filled + '░' * (width - filled)
    label_part = f"{label}: " if label else ""
    subnet_part = f"  {subnet}" if subnet else ""
    return f"{label_part}[{bar}] {percent:3.0f}%{subnet_part}"

def print_header(text: str):
    width = 59
    print(f"\n{YLW}╔{'═' * (width-2)}╗{RST}")
    print(f"{YLW}║{RST}{BLU}{text.center(width-2)}{RST}{YLW}║{RST}")
    print(f"{YLW}╚{'═' * (width-2)}╝{RST}\n")

def validate_ip(ip: str) -> bool:
    pattern = r'^(\d{1,3}\.){3}\d{1,3}$'
    if not re.match(pattern, ip):
        return False
    try:
        return all(0 <= int(x) <= 255 for x in ip.split('.'))
    except ValueError:
        return False

def validate_port(port: str) -> bool:
    try:
        p = int(port)
        return 1 <= p <= 65535
    except ValueError:
        return False

def notify(message: str, level: str = "info"):
    NotificationManager().add(message, level)

# =============================================================================
# NOTIFICATIONS
# =============================================================================

class NotificationManager:
    _instance = None
    _queue = []
    _max_notifications = 5
    _lifetime = 3.0
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance
    
    def add(self, message: str, level: str = "info"):
        colors = {"info": GRN, "warning": YLW, "error": RED}
        color = colors.get(level, WHT)
        self._queue.append((message, color, time.time()))
        logger.debug(f"Notification: {message} ({level})")
        
        if len(self._queue) > self._max_notifications:
            self._queue.pop(0)
    
    def get_active(self) -> List[str]:
        now = time.time()
        self._queue = [(msg, col, ts) for msg, col, ts in self._queue 
                      if now - ts < self._lifetime]
        return [f"{col}▸ {msg}{RST}" for msg, col, _ in self._queue]

_CODEC_MAP = {
    "h264": "H.264", "hevc": "H.265", "h265": "H.265",
    "vp8": "VP8", "vp9": "VP9", "av1": "AV1",
    "mpeg4": "MPEG-4", "mpeg2video": "MPEG-2",
    "mjpeg": "MJPEG", "theora": "Theora",
    "wmv3": "WMV3", "wmv2": "WMV2", "wmv1": "WMV1",
    "vc1": "VC-1", "flv1": "FLV", "rv40": "RealVideo",
    "divx": "DivX", "xvid": "Xvid",
    "aac": "AAC", "mp3": "MP3", "mp2": "MP2",
    "ac3": "AC3", "eac3": "E-AC3", "dts": "DTS",
    "flac": "FLAC", "vorbis": "Vorbis", "opus": "Opus",
    "wmav2": "WMA2", "wmav1": "WMA1", "wmapro": "WMA Pro",
    "pcm_s16le": "PCM", "pcm_s24le": "PCM",
    "truehd": "TrueHD", "alac": "ALAC", "speex": "Speex",
    "google vp9": "VP9",
    "windows media video 9": "WMV9",
    "windows media video 8": "WMV8",
    "windows media video 7": "WMV7",
    "windows media audio 2": "WMA2",
}

def _codec_name(raw: str) -> str:
    if not raw or raw == "—":
        return "—"
    key = raw.lower().strip()
    if key in _CODEC_MAP:
        return _CODEC_MAP[key]
    short = raw.split(" /")[0].split(" (")[0].strip()
    key2 = short.lower()
    if key2 in _CODEC_MAP:
        return _CODEC_MAP[key2]
    return short[:10] if len(short) > 10 else short

# =============================================================================
# KEY HANDLING
# =============================================================================

class Key:
    UP = 'UP'
    DOWN = 'DW'
    LEFT = 'LE'
    RIGHT = 'RI'
    ENTER = 'ENTER'
    SPACE = 'SPACE'
    BACKSPACE = 'BACKSPACE'
    TAB = 'TAB'
    ESC = 'ESC'
    ESC_ESC = 'ESC_ESC'
    HOME = 'HOME'
    END = 'END'
    INSERT = 'INS'
    DELETE = 'DEL'
    PAGE_UP = 'PGUP'
    PAGE_DOWN = 'PGDN'
    F1 = 'F1'
    F2 = 'F2'
    F3 = 'F3'
    F4 = 'F4'
    F5 = 'F5'
    F6 = 'F6'
    F7 = 'F7'
    F8 = 'F8'
    F9 = 'F9'
    F10 = 'F10'
    F11 = 'F11'
    F12 = 'F12'
    TIMEOUT = 'TIMEOUT'
    MOUSE_CLICK  = 'MOUSE_CLICK'
    MOUSE_SCROLL_UP   = 'MOUSE_SCROLL_UP'
    MOUSE_SCROLL_DOWN = 'MOUSE_SCROLL_DOWN'

class MouseEvent:
    def __init__(self, btn: int, col: int, row: int, release: bool = False):
        self.btn     = btn
        self.col     = col
        self.row     = row
        self.release = release
    def __repr__(self):
        return f"MouseEvent(btn={self.btn},col={self.col},row={self.row},release={self.release})"

class KeyReader:
    _ESC_SEQUENCES = {
        '[A': Key.UP, '[B': Key.DOWN, '[C': Key.RIGHT, '[D': Key.LEFT,
        '[1~': Key.HOME, '[H': Key.HOME,
        '[4~': Key.END, '[F': Key.END,
        '[2~': Key.INSERT,
        '[3~': Key.DELETE,
        '[5~': Key.PAGE_UP,
        '[6~': Key.PAGE_DOWN,
        'OP': Key.F1, 'OQ': Key.F2, 'OR': Key.F3, 'OS': Key.F4,
        '[11~': Key.F1, '[12~': Key.F2, '[13~': Key.F3, '[14~': Key.F4,
        '[15~': Key.F5, '[17~': Key.F6, '[18~': Key.F7, '[19~': Key.F8,
        '[20~': Key.F9, '[21~': Key.F10, '[23~': Key.F11, '[24~': Key.F12,
    }
    
    @classmethod
    @contextmanager
    def _raw_mode(cls):
        fd = sys.stdin.fileno()
        old = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            yield
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
    
    @classmethod
    def _read_byte(cls, timeout: Optional[float] = None) -> Optional[str]:
        fd = sys.stdin.fileno()
        if timeout is not None:
            ready, _, _ = select.select([fd], [], [], timeout)
            if not ready:
                return None
        try:
            return os.read(fd, 1).decode('utf-8', errors='replace')
        except OSError:
            return None
    
    @classmethod
    def get_key(cls, timeout: float = -1) -> str:
        with cls._raw_mode():
            ch = cls._read_byte(timeout if timeout >= 0 else None)
            if ch is None:
                return Key.TIMEOUT
            
            if ch == '\x1b':
                seq = ''
                for _ in range(32):
                    c = cls._read_byte(0.15)
                    if c is None:
                        break
                    if c == '\x1b':
                        return Key.ESC_ESC
                    seq += c
                    if seq in cls._ESC_SEQUENCES:
                        return cls._ESC_SEQUENCES[seq]
                    if seq.endswith('~'):
                        break
                    if seq.startswith('[<') and seq[-1:] in ('M', 'm'):
                        try:
                            parts = seq[2:-1].split(';')
                            btn, col, row = int(parts[0]), int(parts[1]), int(parts[2])
                            release = seq[-1] == 'm'
                            if btn == 64: return Key.MOUSE_SCROLL_UP
                            if btn == 65: return Key.MOUSE_SCROLL_DOWN
                            return MouseEvent(btn, col, row, release)
                        except Exception:
                            pass
                    if seq == '[M':
                        b = cls._read_byte(0.1)
                        x = cls._read_byte(0.1)
                        y = cls._read_byte(0.1)
                        if b and x and y:
                            btn = ord(b) - 32
                            col = ord(x) - 32
                            row = ord(y) - 32
                            if btn == 96: return Key.MOUSE_SCROLL_UP
                            if btn == 97: return Key.MOUSE_SCROLL_DOWN
                            return MouseEvent(btn & 3, col, row)
                        break

                return cls._ESC_SEQUENCES.get(seq, Key.ESC)
            
            if ch in ('\x0a', '\x0d'): return Key.ENTER
            if ch == '\x7f': return Key.BACKSPACE
            if ch == '\x09': return Key.TAB
            if ch == '\x20': return Key.SPACE
            
            return ch

get_key = KeyReader.get_key

# =============================================================================
# MENU SELECTION
# =============================================================================

def select_menu(items: list, selected: int = 0,
                title: str = "Select", W: int = 57,
                page_size: int = 0,
                extra_keys: tuple = ()) -> int:
    import shutil as _sh

    DIGIT_TIMEOUT = 0.6

    if page_size <= 0:
        term_h = _sh.get_terminal_size((24, 80)).lines
        page_size = max(3, term_h - 8)

    n = len(items)
    page_size = min(page_size, n)

    def _page_offset(sel, offset):
        if sel < offset:
            return sel
        if sel >= offset + page_size:
            return sel - page_size + 1
        return offset

    def _draw(sel, offset, num_buf=""):
        sys.stdout.write('\033[2J\033[H')
        sys.stdout.flush()
        t = f" {title} "
        sp = max(0, (W - ansilen(t)) // 2)
        print(f"{YLW}╔{'═'*W}╗{RST}")
        print(f"{YLW}║{RST}{BLU}{' '*sp}{t}{' '*max(0,W-ansilen(t)-sp)}{RST}{YLW}║{RST}")
        if n > page_size:
            pg_info = f" {offset+1}-{min(offset+page_size,n)}/{n} "
            pg_len  = len(pg_info)
            left    = (W - pg_len) // 2
            right   = W - pg_len - left
            sep = f"{YLW}╠{'═'*left}{RST}{DIM}{pg_info}{RST}{YLW}{'═'*right}╣{RST}"
        else:
            sep = f"{YLW}╠{'═'*W}╣{RST}"
        print(sep)
        for i in range(offset, min(offset + page_size, n)):
            active = (i == sel)
            marker = f"\033[5m{GRN}▶{RST}" if active else " "
            bg     = "\033[48;5;234m" if active else ""
            line   = f" {i+1:3}) {marker} {bg}{items[i]}{RST}"
            print(f"{YLW}║{RST}{pad(line, W)}{YLW}║{RST}")
        up_arrow   = f" {DIM}↑ more{RST}" if offset > 0 else ""
        down_arrow = f" {DIM}↓ more{RST}" if offset + page_size < n else ""
        print(f"{YLW}╚{'═'*W}╝{RST}")
        hint_plain = " ↑↓ navigate"
        if n > page_size:
            hint_plain += "  PgUp/PgDn page  Home/End"
        hint_plain += "   ENTER select   (Q) exit"
        hint_cols = {}
        hint_cols['\r'] = hint_plain.index('ENTER') + 1
        hint_cols['q']   = hint_plain.index('(Q) exit') + 1
        if extra_keys:
            for k in extra_keys:
                hint_plain += f"   ({k.upper()})"
                hint_cols[k] = hint_plain.rindex(f'({k.upper()})') + 1

        hint_colored = (f"{DIM} ↑↓ navigate"
                        + (f"  PgUp/PgDn page  Home/End" if n > page_size else "")
                        + f"   {RST}{YLW}ENTER{RST}{DIM} select"
                        + f"   {RST}{YLW}(Q){RST}{DIM} exit{RST}")
        if extra_keys:
            for k in extra_keys:
                hint_colored += f"{DIM}   {RST}{YLW}({k.upper()}){RST}"

        hint = hint_colored
        if num_buf:
            hint += f"  {YLW}# {num_buf}_{RST}"
        print(hint)
        if up_arrow or down_arrow:
            print(f"{up_arrow}  {down_arrow}")

    fd = sys.stdin.fileno()
    old_term = termios.tcgetattr(fd)
    sel    = max(0, min(selected, n - 1))
    offset = _page_offset(sel, 0)
    num_buf      = ""
    last_digit_t = 0

    HEADER_ROWS = 3

    hint_cols = {}
    hint_row  = [0]

    def _hint_row():
        return HEADER_ROWS + min(page_size, n) + 2

    def _row_to_idx(row):
        item_row = row - HEADER_ROWS
        if 1 <= item_row <= page_size:
            return offset + item_row - 1
        return -1

    try:
        tty.setcbreak(fd)
        sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
        sys.stdout.flush()
        _draw(sel, offset)
        while True:
            if num_buf and (time.time() - last_digit_t) >= DIGIT_TIMEOUT:
                idx = int(num_buf) - 1
                num_buf = ""
                if 0 <= idx < n:
                    return idx
                _draw(sel, offset)
                continue

            key = get_key(DIGIT_TIMEOUT / 2)
            if key == Key.TIMEOUT:
                continue

            if isinstance(key, MouseEvent):
                if not key.release:
                    if key.row == _hint_row() and hint_cols:
                        for k, col in hint_cols.items():
                            if abs(key.col - col) <= 3:
                                if k == '\r':
                                    return sel
                                elif k == 'q':
                                    return -1
                                elif extra_keys and k in extra_keys:
                                    return (sel, k)
                                break
                    else:
                        item_idx = _row_to_idx(key.row)
                        if 0 <= item_idx < n:
                            if item_idx == sel:
                                return sel
                            sel = item_idx
                            offset = _page_offset(sel, offset)
                            _draw(sel, offset)
                continue
            if key == Key.MOUSE_SCROLL_UP:
                if sel > 0:
                    num_buf = ""; sel -= 1
                    offset = _page_offset(sel, offset); _draw(sel, offset)
                continue
            if key == Key.MOUSE_SCROLL_DOWN:
                if sel < n - 1:
                    num_buf = ""; sel += 1
                    offset = _page_offset(sel, offset); _draw(sel, offset)
                continue

            if key == Key.UP and sel > 0:
                num_buf = ""; sel -= 1
                offset = _page_offset(sel, offset); _draw(sel, offset)
            elif key == Key.DOWN and sel < n - 1:
                num_buf = ""; sel += 1
                offset = _page_offset(sel, offset); _draw(sel, offset)
            elif key in (Key.PAGE_UP,) and sel > 0:
                num_buf = ""; sel = max(0, sel - page_size)
                offset = _page_offset(sel, offset); _draw(sel, offset)
            elif key in (Key.PAGE_DOWN,) and sel < n - 1:
                num_buf = ""; sel = min(n - 1, sel + page_size)
                offset = _page_offset(sel, offset); _draw(sel, offset)
            elif key == Key.HOME:
                num_buf = ""; sel = 0; offset = 0; _draw(sel, offset)
            elif key == Key.END:
                num_buf = ""; sel = n - 1
                offset = _page_offset(sel, 0); _draw(sel, offset)
            elif key in ('\r', '\n', Key.ENTER):
                if num_buf:
                    idx = int(num_buf) - 1
                    num_buf = ""
                    if 0 <= idx < n:
                        return idx
                else:
                    return sel
            elif key in ('q', 'Q', '\x1b'):
                return -1
            elif extra_keys and isinstance(key, str) and key.lower() in extra_keys:
                return (sel, key.lower())
            elif key.isdigit():
                num_buf += key
                last_digit_t = time.time()
                tentative = int(num_buf) - 1
                if 0 <= tentative < n:
                    sel = tentative
                    offset = _page_offset(sel, offset)
                _draw(sel, offset, num_buf)
    finally:
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        termios.tcsetattr(fd, termios.TCSADRAIN, old_term)

# =============================================================================
# CONFIGURATION - LOAD/SAVE
# =============================================================================

class Config:
    def __init__(self, cameras: Optional[List[Camera]] = None,
                 player_cmd: str = MPV_DEFAULT_CMD,
                 layout: Optional[Dict[str, WindowLayout]] = None,
                 auto_check_ip_changes: bool = True,
                 auto_check_interval: int = 300,
                 session_state: Optional[SessionState] = None,
                 default_image_params: Optional[dict] = None,
                 global_mute: bool = False):
        self.cameras = cameras or []
        self.player_cmd = player_cmd
        self.layout = layout or {
            "terminal": WindowLayout(x=100, y=580, w=800, h=450),
            "mpv_default": WindowLayout(x=100, y=100, w=640, h=360)
        }
        self.auto_check_ip_changes = auto_check_ip_changes
        self.auto_check_interval = auto_check_interval
        self.session_state = session_state
        self.global_mute = global_mute
        # Domyślne parametry obrazu dla nowych plików
        if default_image_params:
            self.default_image_params = default_image_params
            Camera.DEFAULT_IMAGE_PARAMS = default_image_params.copy()
    
    def to_dict(self) -> dict:
        result = {
            "PLAYER_CMD": self.player_cmd,
            "LAYOUT": {
                "TERMINAL": self.layout["terminal"].to_dict(),
                "MPV_DEFAULT": self.layout["mpv_default"].to_dict()
            },
            "AUTO_CHECK_IP_CHANGES": self.auto_check_ip_changes,
            "AUTO_CHECK_INTERVAL": self.auto_check_interval,
            "GLOBAL_MUTE": self.global_mute,
            "CAMERAS": [c.to_dict() for c in self.cameras]
        }
        # Zapisz domyślne parametry jeśli różnią się od fabrycznych
        dip = getattr(self, 'default_image_params', None)
        if dip and dip != {"brightness": 0, "contrast": 0, "saturation": 0,
                           "gamma": 0, "hue": 0, "volume": 100, "mute": False, "speed": 1.0}:
            result["DEFAULT_IMAGE_PARAMS"] = dip
        if self.session_state:
            result["SESSION_STATE"] = self.session_state.to_dict()
        return result
    
    @classmethod
    def from_dict(cls, data: dict) -> 'Config':
        cameras = [Camera.from_dict(c) for c in data.get("CAMERAS", [])]
        
        layout_data = data.get("LAYOUT", {})
        layout = {
            "terminal": WindowLayout.from_dict(layout_data.get("TERMINAL", {})),
            "mpv_default": WindowLayout.from_dict(layout_data.get("MPV_DEFAULT", layout_data.get("FFPLAY_DEFAULT", {})))
        }
        
        session_state = None
        if "SESSION_STATE" in data:
            session_state = SessionState.from_dict(data["SESSION_STATE"])
        
        return cls(
            cameras=cameras,
            player_cmd=_migrate_player_cmd(data.get("PLAYER_CMD", MPV_DEFAULT_CMD)),
            layout=layout,
            auto_check_ip_changes=data.get("AUTO_CHECK_IP_CHANGES", True),
            auto_check_interval=data.get("AUTO_CHECK_INTERVAL", 300),
            session_state=session_state,
            default_image_params=data.get("DEFAULT_IMAGE_PARAMS"),
            global_mute=data.get("GLOBAL_MUTE", False)
        )

class ConfigManager:
    def __init__(self, filename: str):
        self.filename = filename
        self.config = self._load()
    
    def _load(self) -> Config:
        if not os.path.exists(self.filename):
            logger.warning(f"Config file {self.filename} not found, creating new")
            return Config()

        def _try_load(path: str) -> Config:
            with open(path, 'r') as f:
                content = f.read().strip()
            if not content:
                raise ValueError("File is empty")
            data = json.loads(content)
            return self._from_dict(data)

        try:
            cfg = _try_load(self.filename)
            logger.debug(f"Loaded configuration from {self.filename}")
            return cfg
        except Exception as e:
            logger.error(f"Error loading configuration: {e}")
            backup = self.filename + ".backup"
            if os.path.exists(backup):
                try:
                    cfg = _try_load(backup)
                    logger.warning(f"Loaded from backup: {backup}")
                    notify("Config loaded from backup!", "warning")
                    return cfg
                except Exception as e2:
                    logger.error(f"Backup also failed: {e2}")
            return Config()
    
    def save(self, create_backup: bool = True) -> bool:
        if os.path.exists(self.filename) and _has_video_magic(self.filename):
            logger.error(f"Config save ABORTED — target looks like a video file: {self.filename}")
            notify("Save error: target is a video file!", "error")
            return False
        try:
            data = json.dumps(self._to_dict(), indent=4)
        except Exception as e:
            logger.error(f"Error saving configuration: {e}")
            notify(f"Save error: {e}", "error")
            return False

        tmp = self.filename + ".tmp"
        try:
            with open(tmp, 'w') as f:
                f.write(data)
                f.flush()
                os.fsync(f.fileno())
            if create_backup and os.path.exists(self.filename):
                backup_name = f"{self.filename}.backup"
                shutil.copy2(self.filename, backup_name)
                logger.debug(f"Created backup: {backup_name}")
            os.replace(tmp, self.filename)
            logger.info(f"Saved configuration to {self.filename}")
            notify("Config saved!")
            return True
        except Exception as e:
            logger.error(f"Error saving configuration: {e}")
            notify(f"Save error: {e}", "error")
            return False
        finally:
            # Ten blok zawsze się wykona. Jeśli plik .tmp nadal istnieje, bezpiecznie go usuwamy.
            if os.path.exists(tmp):
                try:
                    os.unlink(tmp)
                    logger.debug(f"Cleaned up temporary file: {tmp}")
                except OSError:
                    pass
    
    def _to_dict(self) -> dict:
        return self.config.to_dict()
    
    def _from_dict(self, data: dict) -> Config:
        if "CAMERAS" in data:
            for cam_data in data["CAMERAS"]:
                if "PORT" in cam_data or "DVRIP_PORT" in cam_data:
                    logger.info(f"Migrating old format for {cam_data.get('IP', 'unknown')}")
                    ports = {}
                    if "PORT" in cam_data:
                        ports["onvif"] = int(cam_data["PORT"])
                    if "DVRIP_PORT" in cam_data:
                        ports["dvrip"] = cam_data["DVRIP_PORT"]
                    cam_data["ports"] = ports
        
        return Config.from_dict(data)

# =============================================================================
# NETWORK FUNCTIONS
# =============================================================================

class NetworkUtils:
    @staticmethod
    def get_local_prefix() -> str:
        if shutil.which('ip'):
            try:
                out = subprocess.check_output(
                    ["ip", "route", "show", "default"],
                    universal_newlines=True,
                    timeout=2,
                    stderr=subprocess.DEVNULL
                )
                src_match = re.search(r'src\s+(\d+\.\d+\.\d+\.\d+)', out)
                if src_match:
                    ip = src_match.group(1)
                    prefix = ".".join(ip.split('.')[:-1]) + "."
                    logger.debug(f"Local prefix from ip route: {prefix}")
                    return prefix
                via_match = re.search(r'via\s+(\d+\.\d+\.\d+)\.\d+', out)
                if via_match:
                    prefix = via_match.group(1) + "."
                    logger.debug(f"Local prefix from gateway: {prefix}")
                    return prefix
            except Exception as e:
                logger.debug(f"ip route failed: {e}")

        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.settimeout(0)
            s.connect(("192.0.2.1", 80))
            ip = s.getsockname()[0]
            s.close()
            if ip and not ip.startswith("0."):
                prefix = ".".join(ip.split('.')[:-1]) + "."
                logger.debug(f"Local prefix from socket: {prefix}")
                return prefix
        except Exception as e:
            logger.debug(f"Socket method failed: {e}")

        if shutil.which('ip'):
            try:
                out = subprocess.check_output(
                    ["ip", "-4", "addr", "show"],
                    universal_newlines=True,
                    timeout=2,
                    stderr=subprocess.DEVNULL
                )
                for line in out.splitlines():
                    if 'inet ' in line and 'scope global' in line:
                        parts = line.strip().split()
                        if len(parts) >= 2:
                            ip = parts[1].split('/')[0]
                            if not ip.startswith('127.'):
                                prefix = ".".join(ip.split('.')[:-1]) + "."
                                logger.debug(f"Local prefix from ip addr: {prefix}")
                                return prefix
            except Exception as e:
                logger.debug(f"ip addr failed: {e}")

        logger.warning("Could not determine local prefix, using default 192.168.1.")
        return "192.168.1."
    
    @staticmethod
    def get_mac_from_ip(ip: str) -> str:
        if not shutil.which('ip'):
            return "UNKNOWN"
        
        try:
            out = subprocess.check_output(
                ["ip", "neigh", "show", ip],
                stderr=subprocess.DEVNULL,
                timeout=2,
                universal_newlines=True
            )
            match = re.search(r'lladdr\s+([0-9a-fA-F:]+)', out)
            if match:
                mac = match.group(1).upper()
                logger.debug(f"Found MAC for {ip}: {mac}")
                return mac
        except Exception as e:
            logger.debug(f"Error getting MAC for {ip}: {e}")
        
        return "UNKNOWN"
    
    @staticmethod
    def get_ip_from_mac(mac: str) -> Optional[str]:
        if not mac or mac == "UNKNOWN" or not shutil.which('ip'):
            return None
        
        try:
            out = subprocess.check_output(
                ["ip", "neigh", "show"],
                stderr=subprocess.DEVNULL,
                timeout=2,
                universal_newlines=True
            )
            for line in out.splitlines():
                if mac.lower() in line.lower():
                    parts = line.split()
                    if parts:
                        ip = parts[0]
                        logger.debug(f"Found IP for MAC {mac}: {ip}")
                        return ip
        except Exception as e:
            logger.debug(f"Error getting IP for MAC {mac}: {e}")
        
        return None

    @staticmethod
    def resolve_ip(cam) -> bool:
        if cam.type in (CameraType.V4L2, CameraType.FILE, CameraType.SCANNER):
            return False
        if not cam.mac or cam.mac in ("UNKNOWN", "V4L2", "FILE", "SCANNER", ""):
            return False
        new_ip = NetworkUtils.get_ip_from_mac(cam.mac)
        if not new_ip:
            return False

        changed = False

        if new_ip != cam.ip:
            old_ip = cam.ip
            cam.ip = new_ip
            for prof in cam.profiles:
                if old_ip in prof.uri:
                    prof.uri = prof.uri.replace(old_ip, new_ip)
            logger.info(f"resolve_ip: {cam.name} {old_ip} → {new_ip}")
            changed = True

        for prof in cam.profiles:
            if prof.uri and "rtsp://" in prof.uri:
                m = re.search(r'@([\d.]+)[:/]', prof.uri)
                if m:
                    uri_ip = m.group(1)
                    if uri_ip != new_ip:
                        prof.uri = prof.uri.replace(uri_ip, new_ip)
                        logger.info(f"resolve_ip: fixed URI for {cam.name}: {uri_ip} → {new_ip}")
                        changed = True

        return changed

    @staticmethod
    def ping_host(ip: str, timeout: float = 1.0) -> bool:
        if not shutil.which('ping'):
            return False
        
        wait_sec = str(max(1, round(timeout)))
        
        try:
            result = subprocess.run(
                ["ping", "-c", "2", "-W", wait_sec, ip],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=timeout + 1.5
            )
            return result.returncode == 0
        except (subprocess.TimeoutExpired, OSError):
            return False
    
    @staticmethod
    def scan_subnet(prefix: str, max_workers: int = 20,
                    progress_cb=None) -> List[str]:
        active = []
        total = 254

        logger.info(f"Starting subnet scan {prefix}0/24")
        if progress_cb:
            progress_cb(0, 0, total, f"Scanning {prefix}0/24")

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {}
            for i in range(1, 255):
                ip = f"{prefix}{i}"
                futures[executor.submit(NetworkUtils.ping_host, ip, 1.0)] = ip

            for i, future in enumerate(as_completed(futures), 1):
                ip = futures[future]
                if future.result():
                    active.append(ip)
                    logger.debug(f"Active host: {ip}")

                if progress_cb and (i % 20 == 0 or i == 254):
                    pct = int((i / total) * 100)
                    bar_len = 20
                    filled = int(bar_len * i / total)
                    bar = '█' * filled + '░' * (bar_len - filled)
                    progress_cb(pct, i, total, f"[{bar}] {pct}%  {prefix}0/24")

        logger.info(f"Found {len(active)} active hosts")
        return active
    
    @staticmethod
    def check_port(ip: str, port: int, timeout: float = 1.2) -> bool:
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.settimeout(timeout)
                result = s.connect_ex((ip, port)) == 0
                if result:
                    logger.debug(f"Port {port} open on {ip}")
                return result
        except Exception as e:
            logger.debug(f"Error checking port {port} on {ip}: {e}")
            return False

# =============================================================================
# CAMERA TYPE DETECTION
# =============================================================================

class CameraDetector:
    PORTS = {
        554: "RTSP",
        34567: "DVRIP",
        80: "HTTP",
        8899: "ONVIF-Alt",
        8000: "ONVIF-Hik",
        8080: "ONVIF-Misc"
    }
    
    @classmethod
    def detect(cls, cam: Camera, show_progress: bool = False) -> Tuple[CameraType, Optional[int]]:
        if cam.type in (CameraType.V4L2, CameraType.FILE, CameraType.SCANNER):
            return cam.type, None
        
        if not cam.ip:
            return CameraType.UNKNOWN, None
        
        ip = cam.ip
        logger.info(f"Detecting type for {ip}")
        
        if show_progress:
            print(f"\n{CYN}--- Testing: {ip} ---{RST}")
        
        open_ports = {}
        first_output = True
        
        for port, name in cls.PORTS.items():
            is_open = NetworkUtils.check_port(ip, port)
            open_ports[port] = is_open
            
            if show_progress and is_open:
                if first_output:
                    print()
                    first_output = False
                print(f"  [Port] {port:<5} -> {GRN}OPEN{RST} ({name})")
            
            logger.debug(f"Port {ip}:{port} ({name}) -> {'OPEN' if is_open else 'CLOSED'}")
        
        if not any(open_ports.values()):
            logger.warning(f"All ports closed for {ip}, retrying...")
            if show_progress:
                print(f"  {YLW}[Retry]{RST} All ports closed, retrying...")
            time.sleep(1)
            
            for port in cls.PORTS:
                open_ports[port] = NetworkUtils.check_port(ip, port, timeout=1.5)
                if show_progress and open_ports[port]:
                    print(f"  [Port] {port:<5} -> {GRN}OPEN{RST} (retry)")
        
        if not open_ports.get(554) and not open_ports.get(34567):
            if show_progress:
                print(f"  {RED}[Result]{RST} No video ports - not a camera")
            return CameraType.UNKNOWN, None
        
        if open_ports.get(34567):
            if show_progress:
                print(f"{GRN}✓ DVRIP detected (port 34567){RST}")
            logger.info(f"DVRIP detected on {ip}")
            return CameraType.DVRIP, 34567
        
        onvif_ports = [80, 8899, 8000, 8080]
        found_port = next((p for p in onvif_ports if open_ports.get(p)), None)
        
        if found_port:
            port = found_port
            if cls._verify_onvif(ip, port):
                if show_progress:
                    print(f"{GRN}✓ ONVIF detected on port {port}{RST}")
                logger.info(f"ONVIF detected on {ip}:{port}")
                return CameraType.ONVIF, port
            elif open_ports.get(554):
                if show_progress:
                    print(f"{YLW}✓ ONVIF detected (heuristic: RTSP+HTTP on port {port}){RST}")
                logger.info(f"ONVIF detected (heuristic) on {ip}:{port}")
                return CameraType.ONVIF, port
        
        if open_ports.get(554):
            if show_progress:
                print(f"{YLW}✓ RTSP_ONLY detected (only port 554){RST}")
            logger.info(f"RTSP_ONLY detected on {ip}")
            return CameraType.RTSP_ONLY, 554
        
        logger.info(f"Unknown camera type for {ip}")
        return CameraType.UNKNOWN, None
    
    @classmethod
    def _verify_onvif(cls, ip: str, port: int) -> bool:
        try:
            soap = '<?xml version="1.0"?><s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope"><s:Body/></s:Envelope>'
            url = f"http://{ip}:{port}/onvif/device_service"
            logger.debug(f"Verifying ONVIF via SOAP POST to {url}")
            
            r = requests.post(
                url,
                data=soap,
                timeout=1.5,
                allow_redirects=False
            )
            
            logger.debug(f"SOAP response: HTTP {r.status_code}")
            if r.status_code in [200, 400, 401, 403, 405, 500]:
                return True
        
        except requests.exceptions.ConnectionError as e:
            logger.debug(f"Connection error during ONVIF verify: {e}")
            if any(x in str(e) for x in ["RemoteDisconnected", "aborted"]):
                logger.debug("Connection closed - indicates ONVIF")
                return True
            return False
        
        except requests.exceptions.Timeout:
            logger.debug("ONVIF verify timeout")
            return False
        
        except Exception as e:
            logger.debug(f"SOAP exception: {e}")
        
        return False

# =============================================================================
# ONVIF COMMUNICATION
# =============================================================================

class ONVIFClient:
    def __init__(self, cam: Camera):
        self.cam = cam
        NetworkUtils.resolve_ip(cam)
        self._session: Optional[requests.Session] = None
    
    def _get_auth_header(self) -> str:
        nonce = os.urandom(16)
        nonce_b64 = base64.b64encode(nonce).decode()
        created = datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
        
        sha = hashlib.sha1()
        sha.update(nonce + created.encode() + self.cam.password.encode())
        digest = base64.b64encode(sha.digest()).decode()
        
        logger.debug(f"Generating auth header for {self.cam.user}")
        
        return f'''<wsse:Security xmlns:wsse="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-secext-1.0.xsd" xmlns:wsu="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-utility-1.0.xsd">
<wsse:UsernameToken>
<wsse:Username>{self.cam.user}</wsse:Username>
<wsse:Password Type="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-secext-1.0.xsd#PasswordDigest">{digest}</wsse:Password>
<wsse:Nonce EncodingType="http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-secext-1.0.xsd#Base64Binary">{nonce_b64}</wsse:Nonce>
<wsu:Created>{created}</wsu:Created>
</wsse:UsernameToken>
</wsse:Security>'''
    
    def _get_session(self) -> requests.Session:
        if self._session is not None:
            return self._session
        
        session = requests.Session()
        if RETRY_AVAILABLE:
            try:
                retry = Retry(total=2, read=2, connect=2, backoff_factor=0.3)
                adapter = HTTPAdapter(max_retries=retry)
                session.mount('http://', adapter)
                logger.debug("ONVIF session with Retry adapter")
            except Exception as e:
                logger.debug(f"Could not configure Retry: {e}")
        else:
            logger.debug("ONVIF session without Retry (urllib3 too old)")
        
        self._session = session
        return self._session

    def _send_onvif_request(self, url: str, body: str, timeout: tuple = (1.5, 3.5)) -> Optional[str]:
        """
        Bezpieczne wysyłanie żądania SOAP do kamery ONVIF z rozdzielonym timeoutem.

        Args:
            url: Pełny adres URL endpointu ONVIF
            body: Treść żądania SOAP (XML)
            timeout: Krotka (connect_timeout, read_timeout) w sekundach

        Returns:
            Odpowiedź serwera jako string lub None w przypadku błędu
        """
        try:
            session = self._get_session()
            # Używamy krotki (connect, read) – szybko wykrywamy niedostępne kamery
            response = session.post(url, data=body, timeout=timeout)

            # Akceptujemy również kody 400, 401, 500 – często oznaczają one, że kamera
            # odpowiedziała, ale wymaga autoryzacji lub ma błąd w zapytaniu
            if response.status_code in (200, 400, 401, 403, 405, 500):
                logger.debug(f"ONVIF response HTTP {response.status_code} from {url}")
                return response.text
            else:
                logger.warning(f"ONVIF unexpected status {response.status_code} from {url}")
                return None

        except requests.exceptions.ConnectTimeout:
            logger.warning(f"ONVIF connection timeout – camera {self.cam.ip}:{self.cam.ports.onvif} unreachable")
            return None

        except requests.exceptions.ReadTimeout:
            logger.warning(f"ONVIF read timeout – camera {self.cam.ip} connected but not responding")
            return None

        except requests.exceptions.ConnectionError as e:
            logger.debug(f"ONVIF connection error for {self.cam.ip}: {e}")
            return None

        except requests.exceptions.RequestException as e:
            logger.error(f"ONVIF request failed for {self.cam.ip}: {e}")
            return None

        except Exception as e:
            logger.exception(f"Unexpected error in ONVIF request to {url}: {e}")
            return None

    
    def get_profiles(self) -> Tuple[List[CameraProfile], str]:
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/Media"
        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:trt="http://www.onvif.org/ver10/media/wsdl">
<s:Header>{self._get_auth_header()}</s:Header>
<s:Body><trt:GetProfiles/></s:Body>
</s:Envelope>'''

        logger.info(f"Getting ONVIF profiles from {url}")

        # Używamy nowej, bezpiecznej metody z rozdzielonym timeoutem
        xml = self._send_onvif_request(url, body, timeout=(1.5, 3.5))
        if xml is None:
            # Błąd został już zalogowany wewnątrz _send_onvif_request
            return ([], "")

        logger.debug(f"XML response (first 200 chars): {xml[:200]}")

        profiles = []
        blocks = re.findall(r'<trt:Profiles[^>]*token="([^"]+)"[^>]*>(.*?)</trt:Profiles>', xml, re.DOTALL)
        logger.debug(f"Found {len(blocks)} profile blocks")

        for token, block in blocks:
            name_match = re.search(r'<tt:Name>([^<]+)</tt:Name>', block)
            name = name_match.group(1) if name_match else "Unknown"

            uri = self._get_stream_uri(token)

            res = "N/A"
            v_enc = re.search(r'<tt:VideoEncoderConfiguration[^>]*>(.*?)</tt:VideoEncoderConfiguration>', block, re.DOTALL)
            if v_enc:
                w = re.search(r'<tt:Width>(\d+)</tt:Width>', v_enc.group(1))
                h = re.search(r'<tt:Height>(\d+)</tt:Height>', v_enc.group(1))
                if w and h:
                    res = f"{w.group(1)}x{h.group(1)}"

            if res in ["640x360", "N/A", ""] and uri and shutil.which('ffprobe'):
                logger.debug(f"Verifying resolution for {name} with ffprobe...")
                try:
                    verify_uri = uri

                    args = [
                        'ffprobe',
                        '-v', 'error',
                        '-select_streams', 'v:0',
                        '-show_entries', 'stream=width,height',
                        '-of', 'csv=s=x:p=0',
                        '-rtsp_transport', 'tcp',
                        '-timeout', '3000000',
                        verify_uri
                    ]

                    real_res = subprocess.check_output(
                        args,
                        timeout=4,
                        stderr=subprocess.DEVNULL,
                        universal_newlines=True
                    ).strip()

                    if "x" in real_res and real_res != res:
                        logger.info(f"FFprobe detected different resolution for {name}: {res} -> {real_res}")
                        res = real_res
                    elif "x" in real_res:
                        logger.debug(f"FFprobe confirmed resolution: {real_res}")

                except subprocess.TimeoutExpired:
                    logger.warning(f"FFprobe timeout for {name}")
                except subprocess.CalledProcessError as e:
                    logger.debug(f"FFprobe error for {name}: {e}")
                except Exception as e:
                    logger.error(f"FFprobe unexpected error for {name}: {e}")

            logger.debug(f"Profile: {name}, token={token}, res={res}, uri={uri[:50]}...")

            profiles.append(CameraProfile(
                name=name,
                token=token,
                uri=uri,
                res=res
            ))

        logger.info(f"Retrieved {len(profiles)} profiles")
        return (profiles, xml)
    
    def _get_stream_uri(self, token: str) -> str:
        token = html.escape(token)
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/Media"
        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:trt="http://www.onvif.org/ver10/media/wsdl" xmlns:tt="http://www.onvif.org/ver10/schema">
<s:Header>{self._get_auth_header()}</s:Header>
<s:Body>
<trt:GetStreamUri>
<trt:StreamSetup>
<tt:Stream>RTP-Unicast</tt:Stream>
<tt:Transport><tt:Protocol>RTSP</tt:Protocol></tt:Transport>
</trt:StreamSetup>
<trt:ProfileToken>{token}</trt:ProfileToken>
</trt:GetStreamUri>
</s:Body>
</s:Envelope>'''

        logger.debug(f"Getting URI for token {token}")

        xml = self._send_onvif_request(url, body, timeout=(1.5, 3.5))
        if xml is None:
            return ""

        if '<tt:Uri>' in xml:
            uri = xml.split('<tt:Uri>')[1].split('</tt:Uri>')[0].strip()
            if "://" in uri:
                proto, rest = uri.split('://', 1)
                host_part = rest.split('/')[0].split('@')[-1]
                host_only = host_part.split(':')[0]

                bad_hosts = ('', '0.0.0.0', '127.0.0.1', 'localhost')
                if host_only in bad_hosts:
                    if host_part and ':' in host_part:
                        port_str = host_part.split(':', 1)[1]
                        good_host = f"{self.cam.ip}:{port_str}"
                    else:
                        good_host = self.cam.ip
                    if rest.startswith('/'):
                        rest = good_host + rest
                    else:
                        rest = rest.replace(host_part, good_host, 1)
                    logger.debug(f"URI bad host '{host_part}' -> '{good_host}'")

                uri = f"{proto}://{rest}"
                auth_uri = f"{proto}://{self.cam.user}:{self.cam.password}@{rest}"
                safe_uri = re.sub(r'(://)[^:]+:[^@]+(@)', r'\1*:*\2', auth_uri)
                logger.debug(f"URI with auth: {safe_uri[:60]}...")
                return auth_uri
            logger.debug(f"URI without protocol: {uri}")
            return uri

        logger.warning(f"GetStreamUri response missing <tt:Uri>")
        return ""
    
    def move_continuous(self, token: str, pan: float, tilt: float, zoom: float) -> bool:
        token = html.escape(token)
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/PTZ"
        body = f'''<tptz:ContinuousMove xmlns:tptz="http://www.onvif.org/ver20/ptz/wsdl" xmlns:tt="http://www.onvif.org/ver10/schema">
<tptz:ProfileToken>{token}</tptz:ProfileToken>
<tptz:Velocity>
<tt:PanTilt x="{pan:.2f}" y="{tilt:.2f}"/>
<tt:Zoom x="{zoom:.2f}"/>
</tptz:Velocity>
</tptz:ContinuousMove>'''

        envelope = f'<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope"><s:Header>{self._get_auth_header()}</s:Header><s:Body>{body}</s:Body></s:Envelope>'

        xml = self._send_onvif_request(url, envelope, timeout=(1.0, 2.0))
        return xml is not None
    
    def stop(self, token: str) -> bool:
        token = html.escape(token)
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/PTZ"
        body = f'''<tptz:Stop xmlns:tptz="http://www.onvif.org/ver20/ptz/wsdl">
<tptz:ProfileToken>{token}</tptz:ProfileToken>
<tptz:PanTilt>true</tptz:PanTilt>
<tptz:Zoom>true</tptz:Zoom>
</tptz:Stop>'''

        envelope = f'<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope"><s:Header>{self._get_auth_header()}</s:Header><s:Body>{body}</s:Body></s:Envelope>'

        xml = self._send_onvif_request(url, envelope, timeout=(1.0, 2.0))
        return xml is not None
    
    def get_position(self, token: str) -> Optional[PresetPosition]:
        token = html.escape(token)
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/PTZ"
        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tptz="http://www.onvif.org/ver20/ptz/wsdl">
<s:Header>{self._get_auth_header()}</s:Header>
<s:Body>
<tptz:GetStatus>
<tptz:ProfileToken>{token}</tptz:ProfileToken>
</tptz:GetStatus>
</s:Body>
</s:Envelope>'''

        xml = self._send_onvif_request(url, body, timeout=(1.5, 2.5))
        if xml is None:
            return None

        pan_tilt = re.search(
            r'<tt:PanTilt[^/]* x="([^"]+)"[^/]* y="([^"]+)"',
            xml
        )
        zoom_tag = re.search(
            r'<tt:Zoom[^/]* x="([^"]+)"',
            xml
        )

        if pan_tilt:
            pos = PresetPosition(
                pan=float(pan_tilt.group(1)),
                tilt=float(pan_tilt.group(2)),
                zoom=float(zoom_tag.group(1)) if zoom_tag else 0.0
            )
            logger.debug(f"Position: P={pos.pan:.2f}, T={pos.tilt:.2f}, Z={pos.zoom:.2f}")
            return pos

        return None
    
    def absolute_move(self, token: str, pos: PresetPosition) -> bool:
        token = html.escape(token)
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/PTZ"
        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tptz="http://www.onvif.org/ver20/ptz/wsdl" xmlns:tt="http://www.onvif.org/ver10/schema">
<s:Header>{self._get_auth_header()}</s:Header>
<s:Body>
<tptz:AbsoluteMove>
<tptz:ProfileToken>{token}</tptz:ProfileToken>
<tptz:Position>
<tt:PanTilt x="{pos.pan}" y="{pos.tilt}"/>
<tt:Zoom x="{pos.zoom}"/>
</tptz:Position>
</tptz:AbsoluteMove>
</s:Body>
</s:Envelope>'''

        xml = self._send_onvif_request(url, body, timeout=(1.5, 3.0))
        return xml is not None

    def _get_video_source_tokens(self) -> list:
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/Media"
        body = (
            f'<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope"'
            f' xmlns:trt="http://www.onvif.org/ver10/media/wsdl">'
            f'<s:Header>{self._get_auth_header()}</s:Header>'
            f'<s:Body><trt:GetVideoSources/></s:Body></s:Envelope>'
        )

        xml = self._send_onvif_request(url, body, timeout=(1.5, 3.0))
        if xml is None:
            return ["VideoSource_1", "VideoSourceToken_1", "000", "0", "1"]

        tokens = re.findall(r'<trt:VideoSources[^>]*token="([^"]+)"', xml)
        if not tokens:
            tokens = re.findall(r'token="([^"]+)"', xml)
        if tokens:
            logger.debug(f"VideoSource tokens: {tokens}")
            return tokens

        return ["VideoSource_1", "VideoSourceToken_1", "000", "0", "1"]

    def _imaging_endpoint(self) -> str:
        candidates = [
            f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/imaging",
            f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/Imaging",
            f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/device_service",
        ]
        import socket as _socket
        for url in candidates:
            try:
                host = self.cam.ip
                port = self.cam.ports.onvif
                with _socket.create_connection((host, port), timeout=1):
                    pass
                return url
            except OSError:
                pass
        return ""

    def get_imaging_settings(self) -> dict:
        import socket as _socket
        try:
            with _socket.create_connection(
                (self.cam.ip, self.cam.ports.onvif), timeout=1
            ):
                pass
        except OSError:
            logger.debug(f"Imaging: camera {self.cam.ip}:{self.cam.ports.onvif} unreachable")
            return {}

        vs_tokens = self._get_video_source_tokens()
        endpoints = [
            f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/imaging",
            f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/Imaging",
            f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/device_service",
        ]
        namespaces = [
            "http://www.onvif.org/ver20/imaging/wsdl",
            "http://www.onvif.org/ver10/imaging/wsdl",
        ]
        dead_endpoints = set()

        for url in endpoints:
            if url in dead_endpoints:
                continue
            for vs_token in vs_tokens:
                if url in dead_endpoints:
                    break
                for ns in namespaces:
                    body = (
                        f'<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:timg="{ns}">'
                        f'<s:Header>{self._get_auth_header()}</s:Header>'
                        f'<s:Body><timg:GetImagingSettings>'
                        f'<timg:VideoSourceToken>{vs_token}</timg:VideoSourceToken>'
                        f'</timg:GetImagingSettings></s:Body></s:Envelope>'
                    )

                    xml = self._send_onvif_request(url, body, timeout=(1.5, 2.5))
                    if xml is None:
                        if "ConnectionError" in str(xml) or "ConnectTimeout" in str(xml):
                            dead_endpoints.add(url)
                            break
                        continue

                    if "Brightness" in xml or "Contrast" in xml:
                        xml_clean = xml.replace("\n", "").replace("\r", "")

                        brightness = "N/A"
                        contrast = "N/A"
                        saturation = "N/A"
                        sharpness = "N/A"

                        b_match = re.search(r'<tt:Brightness>([^<]+)</tt:Brightness>', xml_clean)
                        if b_match:
                            brightness = b_match.group(1)

                        c_match = re.search(r'<tt:Contrast>([^<]+)</tt:Contrast>', xml_clean)
                        if c_match:
                            contrast = c_match.group(1)

                        s_match = re.search(r'<tt:ColorSaturation>([^<]+)</tt:ColorSaturation>', xml_clean)
                        if s_match:
                            saturation = s_match.group(1)

                        sh_match = re.search(r'<tt:Sharpness>([^<]+)</tt:Sharpness>', xml_clean)
                        if sh_match:
                            sharpness = sh_match.group(1)

                        logger.debug(f"Imaging OK: token={vs_token} url={url}")
                        return {
                            "brightness": brightness,
                            "contrast":   contrast,
                            "saturation": saturation,
                            "sharpness":  sharpness,
                            "vs_token":   vs_token,
                            "endpoint":   url,
                            "ns":         "v2.0" if "ver20" in ns else "v1.0",
                        }
        return {}

    def get_snapshot_uri(self, token: str) -> str:
        token = html.escape(token)
        url = f"http://{self.cam.ip}:{self.cam.ports.onvif}/onvif/Media"
        body = (
            f'<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:trt="http://www.onvif.org/ver10/media/wsdl">'
            f'<s:Header>{self._get_auth_header()}</s:Header>'
            f'<s:Body><trt:GetSnapshotUri>'
            f'<trt:ProfileToken>{token}</trt:ProfileToken>'
            f'</trt:GetSnapshotUri></s:Body></s:Envelope>'
        )

        xml = self._send_onvif_request(url, body, timeout=(1.5, 3.0))
        if xml is None:
            return ""

        m = re.search(r'<tt:Uri>([^<]+)</tt:Uri>', xml)
        if m:
            return m.group(1).strip()
        return ""

# =============================================================================
# DVRIP COMMUNICATION
# =============================================================================

try:
    from dvrip import DVRIPCam
    DVRIP_AVAILABLE = True
except ImportError:
    DVRIP_AVAILABLE = False
    DVRIPCam = None

class DVRIPClient:
    def __init__(self, cam: Camera):
        self.cam = cam
        self._device     = None
        self._stop_timer = None
    
    def _get_device(self):
        if not DVRIP_AVAILABLE:
            notify("DVRIP module not installed!", "error")
            return None
        
        if self._device is not None:
            return self._device
        
        try:
            device = DVRIPCam(
                self.cam.ip,
                user=self.cam.user,
                password=self.cam.password,
                port=self.cam.ports.dvrip
            )
            if not device.login():
                logger.error(f"DVRIP login failed for {self.cam.ip}")
                notify("DVRIP login failed!", "error")
                return None
            self._device = device
            logger.debug(f"DVRIP connected to {self.cam.ip}")
            return self._device
        except Exception as e:
            logger.error(f"DVRIP connect error: {e}")
            return None
    
    def close(self):
        if self._stop_timer:
            self._stop_timer.cancel()
            self._stop_timer = None
        if self._device is not None:
            try:
                self._device.logout()
                logger.debug("DVRIP logout")
            except Exception:
                pass
            self._device = None
    
    def move(self, direction: str, speed: int, duration: float) -> bool:
        cmd_map = {
            "U": "UP", "D": "DOWN", "L": "LEFT", "R": "RIGHT",
            "Z+": "ZOOM_ADD", "Z-": "ZOOM_DEC", "C": "STOP"
        }

        if direction not in cmd_map:
            logger.warning(f"Unknown direction: {direction}")
            return False

        logger.info(f"DVRIP move: {direction} (speed={speed}, duration={duration}s)")

        device = self._get_device()
        if device is None:
            return False

        try:
            cmd = cmd_map[direction]

            if cmd == "STOP":
                if self._stop_timer is not None:
                    self._stop_timer.cancel()
                    self._stop_timer = None
                device.ptz(cmd, 0, False)
                logger.debug("DVRIP stop")
            else:
                if self._stop_timer is not None:
                    self._stop_timer.cancel()
                    self._stop_timer = None
                logger.debug(f"DVRIP start {cmd}")
                device.ptz(cmd, speed, True)

                def _stop_after():
                    try:
                        if device:
                            device.ptz("STOP", 0, False)
                            logger.debug("DVRIP stop after time")
                    except Exception as e:
                        logger.error(f"DVRIP stop error: {e}")
                    finally:
                        self._stop_timer = None

                import threading as _thr
                self._stop_timer = _thr.Timer(duration, _stop_after)
                self._stop_timer.daemon = True
                self._stop_timer.start()

            return True

        except Exception as e:
            logger.error(f"DVRIP PTZ error: {e}")
            self._device = None
            return False

# =============================================================================
# RTSP SCANNER
# =============================================================================

COMMON_RTSP_PATHS = [
    "/stream=0.sdp", "/stream=1.sdp",
    "/streamtype=0", "/streamtype=1",
    "/0/av0", "/0/av1",
    "/0/video0", "/0/video1",
    "/0/audio",
    "/", "/live", "/live/ch0", "/live/ch1",
    "/live/main", "/live/sub",
    "/stream", "/stream1", "/stream2",
    "/video", "/main", "/sub",
    "/cam", "/camera",
    "/onvif/profile.0/media.ssp", "/onvif1", "/onvif2",
    "/Streaming/Channels/101", "/Streaming/Channels/102", "/Streaming/Channels/201",
    "/cam/realmonitor?channel=1&subtype=0", "/cam/realmonitor?channel=1&subtype=1",
    "/11", "/12", "/ch0", "/ch1", "/ch0_0.264", "/live0.264",
    "/av0_0", "/av0_1", "/1/av0", "/2/av0",
    "/h264", "/h265", "/h264/ch1/main/av_stream", "/h264_stream", "/mjpeg_stream",
    "/videoMain", "/videoSub",
    "/axis-media/media.amp", "/axis-media/media.amp?videocodec=h264",
    "/axis-cgi/mjpg/video.cgi",
    "/profile0", "/profile1", "/profile100", "/profile101",
    "/media/video1", "/media.amp", "/media.mp4", "/live.sdp", "/ipcam.sdp",
    "/defaultPrimary?streamType=u", "/MediaInput/h264", "/trackID=1",
    "/video.mjpg", "/mjpg/video.mjpg", "/img/video.asf", "/videostream.asf",
    "/cgi-bin/mjpg/video.cgi", "/cgi-bin/viewer/video.jpg",
    "/cgi-bin/nphMotionJpeg", "/nphMotionJpeg", "/mpeg4",
]

class RTSPScanner:
    def __init__(self, cam: Camera):
        self.cam = cam

    def scan(self) -> List[CameraProfile]:
        rtsp_port = self.cam.ports.rtsp
        base_url = f"rtsp://{self.cam.user}:{self.cam.password}@{self.cam.ip}:{rtsp_port}"

        logger.info(f"Starting RTSP scan for {self.cam.ip}:{rtsp_port}")

        print(f"\n{CYN}Scanning RTSP on port {rtsp_port}...{RST}")
        print(f"{YLW}Press 'q' to stop (no Enter needed){RST}\n")

        valid = []
        total = len(COMMON_RTSP_PATHS)

        fd = sys.stdin.fileno()
        old_settings = None
        try:
            old_settings = termios.tcgetattr(fd)
            tty.setraw(fd)

            for i, path in enumerate(COMMON_RTSP_PATHS, 1):
                if select.select([sys.stdin], [], [], 0)[0]:
                    ch = sys.stdin.read(1)
                    if ch.lower() == 'q':
                        sys.stdout.write('\r' + ' ' * 80 + '\r')
                        print(f"{YLW}Scan interrupted by user{RST}")
                        logger.info("Scan interrupted by user")
                        break

                uri = base_url + path

                print_progress_bar(i, total, prefix='📹', suffix=f"Testing {path[:25]}")
                logger.debug(f"Testing: {uri}")

                info = self._test_path(uri)
                if info:
                    sys.stdout.write('\r' + ' ' * 80 + '\r')

                    print(f"{GRN}✅ Found:{RST}\r")
                    print(f"            ┌─> mpv {uri}\r")

                    video_line = f"            ├─ 📹 V: {info.get('res', '?')} : {info.get('fps', '?')}fps : {info.get('codec', '?')}\r"
                    print(video_line)

                    if info.get('audio_codec'):
                        audio_line = f"            └─ 🔊 A: {info.get('audio_codec')} : {info.get('audio_sample_rate', '?')}Hz : Ch:{info.get('audio_channels', '?')}\r"
                    else:
                        audio_line = f"            └─ 🔇 No audio\r"
                    print(audio_line)

                    print(f"{YLW}{'─' * 80}{RST}")

                    logger.info(f"Found working stream: {path} - {info.get('res', 'Unknown')}")
                    valid.append((path, uri, info.get('res', 'Unknown')))

        finally:
            if old_settings:
                termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)

        sys.stdout.write('\r' + ' ' * 80 + '\r')
        print_progress_bar(total, total, prefix='📹', suffix="Complete!")

        if not valid:
            print(f"\n{RED}No working RTSP streams found{RST}")
            logger.warning("No working RTSP streams found")
            return []

        logger.info(f"Found {len(valid)} working streams")
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        return self._select_streams(valid, base_url)


    def _manual_entry(self, base_url: str) -> List[CameraProfile]:
        print(f"\n{CYN}Enter RTSP path (e.g., /live/ch0):{RST}")
        path = rlinput("> ", "/").strip()

        if not path.startswith('/'):
            path = '/' + path

        uri = base_url + path
        logger.info(f"Manual testing path: {path}")

        info = self._test_path(uri)

        if info:
            print(f"{GRN}✓ Stream works!{RST}")
            print(f"            ┌─> mpv {uri}")
            print(f"            ├─ 📹 V: {info.get('res', '?')} : {info.get('fps', '?')}fps : {info.get('codec', '?')}")
            if info.get('audio_codec'):
                print(f"            └─ 🔊 A: {info.get('audio_codec')} : {info.get('audio_sample_rate', '?')}Hz : Ch:{info.get('audio_channels', '?')}")
            else:
                print(f"            └─ 🔇 No audio")
            print(f"{YLW}{'─' * 80}{RST}")

            profile = CameraProfile(
                name=f"RTSP_{path.replace('/', '_')}",
                token=f"rtsp_001",
                uri=uri,
                res=info.get('res', 'Unknown'),
                fps=int(info.get('fps', 0)),
                codec=info.get('codec', '')
            )
            logger.info(f"Manually added profile: {path} - {info.get('res', 'Unknown')}")
            return [profile]
        else:
            print(f"{RED}✗ Stream does not work{RST}")
            logger.warning(f"Manually entered path does not work: {path}")
            return []

    def _test_path(self, uri: str) -> Optional[Dict[str, str]]:
        if not shutil.which('ffprobe'):
            logger.warning("ffprobe not available - cannot test paths")
            return None

        try:
            logger.debug(f"Running ffprobe for {uri[:50]}...")

            result = subprocess.run(
                [
                    'ffprobe',
                    '-v', 'quiet',
                    '-rtsp_transport', 'tcp',
                    '-timeout', '3000000',
                    '-probesize', '1000000',
                    '-analyzeduration', '1000000',
                    '-show_streams',
                    '-of', 'flat',
                    '-i', uri
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                timeout=4
            )

            if result.returncode != 0 or not result.stdout:
                logger.debug(f"ffprobe failed (code {result.returncode})")
                return None

            info = {}
            for line in result.stdout.split('\n'):
                if '=' in line:
                    k, v = line.split('=', 1)
                    info[k] = v.strip('"')

            v_idx = None
            a_idx = None
            for i in range(5):
                if info.get(f'streams.stream.{i}.codec_type') == 'video':
                    v_idx = str(i)
                elif info.get(f'streams.stream.{i}.codec_type') == 'audio':
                    a_idx = str(i)

            if v_idx is None:
                logger.debug("No video stream found")
                return None

            width = info.get(f'streams.stream.{v_idx}.width', '?')
            height = info.get(f'streams.stream.{v_idx}.height', '?')
            codec = info.get(f'streams.stream.{v_idx}.codec_name', 'unknown')
            raw_fps = info.get(f'streams.stream.{v_idx}.r_frame_rate', '0/0')

            fps = '?'
            if '/' in raw_fps:
                try:
                    num, den = raw_fps.split('/')
                    fps = str(int(num) // int(den)) if int(den) > 0 else '?'
                except (ValueError, ZeroDivisionError):
                    pass

            res = f"{width}x{height}" if width != '?' and height != '?' else "Unknown"

            result_dict = {
                'res': res,
                'fps': fps,
                'codec': codec.upper()
            }

            if a_idx:
                a_codec = info.get(f'streams.stream.{a_idx}.codec_name', 'unknown')
                sample_rate = info.get(f'streams.stream.{a_idx}.sample_rate', '?')
                channels = info.get(f'streams.stream.{a_idx}.channels', '0')

                result_dict['audio_codec'] = a_codec.upper()
                result_dict['audio_sample_rate'] = sample_rate
                result_dict['audio_channels'] = channels

            logger.debug(f"Found stream: {res}, {fps}fps, {codec}")
            if a_idx:
                logger.debug(f"Audio: {a_codec}, {sample_rate}Hz, {channels}ch")

            return result_dict

        except subprocess.TimeoutExpired:
            logger.debug("ffprobe timeout")
        except Exception as e:
            logger.debug(f"ffprobe exception: {e}")

        return None

    def _select_streams(self, paths: List[tuple], base_url: str) -> List[CameraProfile]:
        if not paths:
            return []

        items = [f"{path:<32} {res}" for path, uri, res in paths]

        while True:
            result = select_menu(
                items,
                selected=0,
                title=f"🎥 Found {len(paths)} streams",
                extra_keys=('s', 'a'),
                W=57
            )

            if isinstance(result, tuple):
                idx, key = result
                if key == 's':
                    logger.info(f"Saved selected stream: {paths[idx][0]}")
                    return [self._path_to_profile(paths[idx])]
                if key == 'a':
                    logger.info(f"Saved all {len(paths)} streams")
                    return [self._path_to_profile(p) for p in paths]

            elif result == -1:
                logger.info("Stream selection cancelled")
                return []

            else:
                path, uri, res = paths[result]
                mouse_off()
                print(f"\n{CYN}Testing stream: {path} {res}{RST}")
                logger.info(f"Testing selected stream: {path}")
                subprocess.run(
                    ['mpv', '--rtsp-transport=tcp', uri],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                )
                mouse_on(); get_key(); mouse_off()

    def _path_to_profile(self, path_data: tuple) -> CameraProfile:
        path, uri, res = path_data
        clean = path.replace('/', '').replace('?', '_').replace('&', '_')
        if not clean:
            clean = "root"

        return CameraProfile(
            name=f"RTSP_{clean}",
            token=f"rtsp_001",
            uri=uri,
            res=res
        )

# =============================================================================
# PROCESS MANAGEMENT
# =============================================================================

class MpvController:
    def __init__(self, socket_path: str):
        self.socket_path = socket_path

    def _send(self, command: list) -> Optional[dict]:
        import socket as _sock
        payload = json.dumps({"command": command}).encode() + b'\n'
        logger.debug(f"IPC → {self.socket_path}  CMD: {json.dumps(command)}")
        try:
            with _sock.socket(_sock.AF_UNIX, _sock.SOCK_STREAM) as s:
                s.settimeout(1.0)
                s.connect(self.socket_path)
                s.sendall(payload)
                buf = b""
                while True:
                    try:
                        chunk = s.recv(4096)
                    except _sock.timeout:
                        break
                    if not chunk:
                        break
                    buf += chunk
                    lines = buf.split(b'\n')
                    for line in lines[:-1]:
                        line = line.strip()
                        if not line:
                            continue
                        try:
                            obj = json.loads(line)
                            if "event" in obj:
                                logger.debug(f"IPC ← EVENT: {line.decode()}")
                            elif "error" in obj:
                                logger.debug(f"IPC ← RESP:  {line.decode()}")
                                return obj
                            else:
                                logger.debug(f"IPC ← OTHER: {line.decode()}")
                        except json.JSONDecodeError:
                            logger.debug(f"IPC ← INVALID JSON: {line!r}")
                            continue
                    buf = lines[-1]
                    s.settimeout(0.5)
                if buf.strip():
                    try:
                        obj = json.loads(buf.strip())
                        if "error" in obj:
                            logger.debug(f"IPC ← RESP(final): {buf.strip().decode()}")
                            return obj
                    except Exception:
                        pass
        except Exception as e:
            logger.info(f"IPC ✗ {command}: {e}")
        logger.info(f"IPC ← None (no response found) for {command}")
        return None

    def set_property(self, prop: str, value) -> bool:
        r = self._send(["set_property", prop, value])
        ok = r is not None and r.get("error") == "success"
        if prop == "pause":
            logger.info(f"IPC set_property({prop!r}, {value!r}) → {'OK' if ok else 'FAIL'} raw={r}")
        else:
            logger.debug(f"IPC set_property({prop!r}, {value!r}) → {'OK' if ok else 'FAIL'} raw={r}")
        return ok

    def get_property(self, prop: str):
        r = self._send(["get_property", prop])
        if r and r.get("error") == "success":
            val = r.get("data")
            logger.debug(f"IPC get_property({prop!r}) → {val!r}")
            return val
        logger.debug(f"IPC get_property({prop!r}) → None raw={r}")
        return None

    def show_osd(self, text: str, duration_ms: int = 3000):
        self._send(["show-text", text, duration_ms])

    def pause(self):   self.set_property("pause", True)
    def resume(self):  self.set_property("pause", False)

    def set_brightness(self, val: int):   self.set_property("brightness", max(-100, min(100, val)))
    def set_contrast(self,   val: int):   self.set_property("contrast",   max(-100, min(100, val)))
    def set_saturation(self, val: int):   self.set_property("saturation", max(-100, min(100, val)))
    def set_gamma(self,      val: int):   self.set_property("gamma",      max(-100, min(100, val)))
    def set_hue(self,        val: int):   self.set_property("hue",        max(-100, min(100, val)))
    def set_speed(self,      val: float): self.set_property("speed",      max(0.1, min(10.0, val)))

    def is_alive(self) -> bool:
        return self.get_property("pid") is not None

    def quit(self):
        self._send(["quit"])

    @staticmethod
    def socket_path_for(cam_name: str, pid: int) -> str:
        safe = cam_name.replace(' ', '_').replace('/', '_')
        return f"/tmp/mpv-{safe}-{pid}"


class PlayerWatchdog:
    POLL_INTERVAL   = 2
    FREEZE_TIMEOUT  = 45
    CONNECT_TIMEOUT = 30
    MAX_RESTARTS    = 10
    CRASH_TIMEOUT   = 5

    _instances: dict = {}
    _lock = threading.Lock()
    _restart_counts: dict = {}

    def __init__(self, proc: 'subprocess.Popen', cam: 'Camera',
                 profile: 'CameraProfile', restart_fn, stderr_fd: int = -1,
                 eof_stops: bool = False):
        self.proc       = proc
        self.cam        = cam
        self.profile    = profile
        self.restart_fn = restart_fn
        self.eof_stops  = eof_stops  # FILE: normalny koniec != crash
        self._stop      = threading.Event()
        self._last_pts  = None
        self._last_adv  = time.time()
        self._stderr_fd = stderr_fd
        self._thread    = threading.Thread(
            target=self._run, daemon=True, name=f"watchdog-{proc.pid}")
        self._thread.start()
        with PlayerWatchdog._lock:
            PlayerWatchdog._instances[proc.pid] = self
        logger.debug(f"Watchdog started for PID {proc.pid} ({cam.name})")

    def stop(self):
        self._stop.set()
        with PlayerWatchdog._lock:
            PlayerWatchdog._instances.pop(self.proc.pid, None)
        if self._stderr_fd >= 0:
            try:
                os.close(self._stderr_fd)
            except OSError:
                pass
            self._stderr_fd = -1

    @staticmethod
    def stop_for_pid(pid: int):
        with PlayerWatchdog._lock:
            wd = PlayerWatchdog._instances.pop(pid, None)
        if wd:
            wd.stop()

    @classmethod
    def _get_restart_count(cls, name: str) -> int:
        return cls._restart_counts.get(name, 0)

    @classmethod
    def _inc_restart_count(cls, name: str) -> int:
        cls._restart_counts[name] = cls._restart_counts.get(name, 0) + 1
        return cls._restart_counts[name]

    @classmethod
    def reset_restart_count(cls, name: str):
        cls._restart_counts.pop(name, None)

    def _run(self):
        import socket as _socket
        import json as _json

        start_time = time.time()
        self._last_adv = start_time
        ipc_path = self.profile.ipc_path

        time.sleep(10)
        logger.info(f"Watchdog timer started for {self.cam.name} (PID {self.proc.pid})")

        def _ipc_query(path: str) -> Optional[float]:
            try:
                with _socket.socket(_socket.AF_UNIX, _socket.SOCK_STREAM) as s:
                    s.settimeout(2.0)
                    s.connect(path)
                    cmd = b'{"command": ["get_property", "playback-time"]}\n'
                    s.sendall(cmd)
                    data = s.recv(256)
                resp = _json.loads(data.decode())
                if resp.get("error") == "success":
                    return float(resp["data"])
            except Exception:
                pass
            return None

        connected_once = False
        while not self._stop.is_set():
            time.sleep(self.POLL_INTERVAL)
            if self._stop.is_set():
                break

            now = time.time()

            if self.proc.poll() is not None:
                alive_time = now - start_time
                if alive_time < self.CRASH_TIMEOUT:
                    logger.error(f"Watchdog: {self.cam.name} crashed after {alive_time:.1f}s")
                    self.profile.error = True
                    self.profile.pid = None
                    notify(f"{self.cam.name}: stream error – check IP/URI", "error")
                    if not self._stop.is_set():
                        self._restart()
                elif self.eof_stops:
                    # Normalny koniec pliku (EOF) — nie restartuj, zatrzymaj watchdog
                    logger.info(f"Watchdog: {self.cam.name} EOF — stop (no restart)")
                    self.stop()
                else:
                    if not self._stop.is_set():
                        self._restart()
                return

            if not ipc_path:
                continue

            pts = _ipc_query(ipc_path)

            if pts is None:
                if not connected_once:
                    elapsed = now - start_time
                    if elapsed > self.CONNECT_TIMEOUT + 10:
                        logger.warning(
                            f"Watchdog: {self.cam.name} IPC not responding for {elapsed:.0f}s – restarting")
                        self._restart()
                        return
                else:
                    freeze = now - self._last_adv
                    if freeze > self.FREEZE_TIMEOUT:
                        logger.warning(
                            f"Watchdog: {self.cam.name} IPC freeze {freeze:.0f}s – restarting")
                        self._restart()
                        return
                continue

            if not connected_once:
                connected_once = True
                PlayerWatchdog.reset_restart_count(self.cam.name)
                logger.info(f"Watchdog: {self.cam.name} streaming OK, reset restart counter")
                ip = getattr(self.cam, 'image_params', None)
                if ip and ip != Camera.DEFAULT_IMAGE_PARAMS:
                    try:
                        ctrl = MpvController(self.profile.ipc_path)
                        PROP_MAP = {
                            "brightness": "brightness", "contrast": "contrast",
                            "saturation": "saturation", "gamma": "gamma", "hue": "hue",
                        }
                        for key, prop in PROP_MAP.items():
                            if key in ip:
                                ctrl.set_property(prop, ip[key])
                        if "volume" in ip: ctrl.set_property("volume", ip["volume"])
                        if "mute"   in ip: ctrl.set_property("mute",   ip["mute"])
                        if "speed"  in ip: ctrl.set_property("speed",  ip["speed"])
                        logger.info(f"Watchdog: applied image_params for {self.cam.name}")
                    except Exception as e:
                        logger.warning(f"Watchdog: image_params apply failed: {e}")

            if self._last_pts is None or pts > self._last_pts + 0.01:
                self._last_pts = pts
                self._last_adv = now
            elif self._last_pts is not None and pts < self._last_pts - 0.5:
                # pts cofnął się — seek lub ab-loop, reset freeze timer
                logger.debug(f"Watchdog: {self.cam.name} seek back {self._last_pts:.1f}→{pts:.1f}s — freeze reset")
                self._last_pts = pts
                self._last_adv = now
            else:
                def _is_paused(path: str) -> bool:
                    try:
                        with _socket.socket(_socket.AF_UNIX, _socket.SOCK_STREAM) as s:
                            s.settimeout(2.0)
                            s.connect(path)
                            s.sendall(b'{"command": ["get_property", "pause"]}\n')
                            data = s.recv(256)
                        resp = _json.loads(data.decode())
                        return resp.get("error") == "success" and resp.get("data") is True
                    except Exception:
                        return False

                if _is_paused(ipc_path):
                    self._last_adv = now
                    logger.debug(f"Watchdog: {self.cam.name} paused — freeze timer reset")
                else:
                    freeze = now - self._last_adv
                    if freeze > self.FREEZE_TIMEOUT:
                        logger.warning(
                            f"Watchdog: {self.cam.name} pts frozen at {pts:.2f}s for {freeze:.0f}s – restarting")
                        self._restart()
                        return

        self.stop()

    def _restart(self):
        count = PlayerWatchdog._inc_restart_count(self.cam.name)
        if count > PlayerWatchdog.MAX_RESTARTS:
            logger.error(
                f"Watchdog: {self.cam.name} – too many restarts ({count-1}), giving up")
            notify(f"{self.cam.name}: watchdog gave up after {count-1} restarts", "error")
            self.stop()
            return
        self.stop()
        try:
            self.proc.kill()
        except Exception:
            pass
        delay = [1.0, 5.0, 15.0][min(count - 1, 2)]
        logger.info(
            f"Watchdog restarting player for {self.cam.name} "
            f"(attempt {count}/{PlayerWatchdog.MAX_RESTARTS}, delay {delay:.0f}s)")
        notify(f"{self.cam.name}: watchdog restart {count}/{PlayerWatchdog.MAX_RESTARTS}", "warning")
        time.sleep(delay)
        self.restart_fn(self.cam, self.profile)


class ProcessManager:
    @staticmethod
    def is_running(pid: Optional[int]) -> bool:
        if pid is None:
            return False
        try:
            os.kill(pid, 0)
            return True
        except OSError:
            return False
    
    @staticmethod
    def wait_for_start(pid: int, timeout: float = 2.0) -> bool:
        start = time.time()
        while time.time() - start < timeout:
            if ProcessManager.is_running(pid):
                time.sleep(0.2)
                logger.debug(f"Process {pid} confirmed after {time.time()-start:.2f}s")
                return True
            time.sleep(0.05)
        logger.warning(f"Process {pid} not detected after {timeout}s")
        return False
    
    @staticmethod
    def kill(pid: int, force: bool = False) -> bool:
        PlayerWatchdog.stop_for_pid(pid)
        try:
            if force:
                os.kill(pid, 9)
            else:
                os.kill(pid, 15)
                time.sleep(0.1)
                if ProcessManager.is_running(pid):
                    os.kill(pid, 9)
            logger.debug(f"Killed process {pid} (force={force})")
            return True
        except OSError as e:
            logger.debug(f"Error killing process {pid}: {e}")
            return False
    
    @staticmethod
    def kill_all(cameras: List[Camera]) -> int:
        killed = 0
        for cam in cameras:
            for prof in cam.profiles:
                if prof.pid and ProcessManager.is_running(prof.pid):
                    if ProcessManager.kill(prof.pid):
                        prof.pid = None
                        killed += 1
        if killed > 0:
            logger.info(f"Killed {killed} processes")
        return killed

# =============================================================================
# RESOLUTION TYPE MAPPING for V4L2
# =============================================================================

RESOLUTION_TYPES = {
    (3840, 2160): "4K",
    (2560, 1440): "2K",
    (1920, 1080): "Full HD",
    (1280, 720): "HD",
    (854, 480): "WVGA",
    (720, 576): "SD PAL",
    (720, 480): "SD NTSC",
    (640, 480): "VGA",
    (640, 360): "nHD",
    (480, 320): "HVGA",
    (320, 240): "QVGA",
    (160, 120): "QQVGA"
}

def get_resolution_type(res: str) -> str:
    if 'x' not in res:
        return res
    
    try:
        w, h = map(int, res.split('x'))
        
        for (rw, rh), name in RESOLUTION_TYPES.items():
            if w == rw and h == rh:
                return name
        
        if w >= 1920 and h >= 1080:
            return "Full HD"
        elif w >= 1280 and h >= 720:
            return "HD"
        elif w >= 720 and h >= 480:
            return "SD"
        else:
            return "Low Res"
    except (ValueError, AttributeError) as e:
        logger.debug(f"get_resolution_type parse error: {e}")
        return res

# =============================================================================
# V4L2 DEVICES
# =============================================================================

class V4L2Scanner:
    @staticmethod
    def scan() -> List[Camera]:
        devices = []
        
        logger.info("Scanning V4L2 devices")
        
        for dev_path in sorted(glob.glob('/dev/video*')):
            if 'm' in os.path.basename(dev_path).replace('video', ''):
                continue
            
            dev_name = os.path.basename(dev_path)
            logger.debug(f"Found device: {dev_path}")
            
            card = f"V4L2 Device {dev_name}"
            driver = "unknown"
            formats = []
            
            if shutil.which('v4l2-ctl'):
                try:
                    logger.debug(f"Getting info from v4l2-ctl for {dev_path}")
                    
                    result = subprocess.run(
                        ['v4l2-ctl', '-d', dev_path, '--info'],
                        stdout=subprocess.PIPE,
                        stderr=subprocess.DEVNULL,
                        universal_newlines=True,
                        timeout=2
                    )
                    for line in result.stdout.split('\n'):
                        if 'Driver name' in line:
                            driver = line.split(':')[1].strip()
                        elif 'Card type' in line:
                            card = line.split(':')[1].strip()
                    
                    result = subprocess.run(
                        ['v4l2-ctl', '-d', dev_path, '--list-formats-ext'],
                        stdout=subprocess.PIPE,
                        stderr=subprocess.DEVNULL,
                        universal_newlines=True,
                        timeout=3
                    )
                    
                    for line in result.stdout.split('\n'):
                        if 'Size:' in line:
                            parts = line.split()
                            for part in parts:
                                if 'x' in part and part.replace('x', '').isdigit():
                                    if part not in formats:
                                        formats.append(part)
                                        logger.debug(f"Found format: {part}")
                                    break
                except Exception as e:
                    logger.debug(f"Error running v4l2-ctl for {dev_path}: {e}")
            
            profiles = []
            if formats:
                try:
                    formats.sort(key=lambda r: int(r.split('x')[0]) * int(r.split('x')[1]), reverse=True)
                except Exception as e:
                    logger.debug(f"Format sort error: {e}")
                
                for i, res in enumerate(formats[:5]):
                    res_type = get_resolution_type(res)
                    profile_name = f"{res_type} ({res})" if res_type != res else res
                    
                    profiles.append(CameraProfile(
                        name=profile_name,
                        token=f"{dev_name}_{res}",
                        uri=dev_path,
                        res=res,
                        fps=30,
                        channel=0
                    ))
            
            if not profiles:
                logger.debug(f"No formats found for {dev_path}, adding default")
                profiles.append(CameraProfile(
                    name="VGA (640x480)",
                    token=dev_name,
                    uri=dev_path,
                    res="640x480",
                    fps=30
                ))
            
            cam = Camera(
                name=card[:30],
                ip="localhost",
                mac="V4L2",
                user="",
                password="",
                profiles=profiles,
                cam_type=CameraType.V4L2,
                device=dev_path
            )
            
            devices.append(cam)
            logger.info(f"Added V4L2 device: {dev_path} - {card[:30]}")
        
        return devices

# =============================================================================
# PLAYER
# =============================================================================

class Player:
    @staticmethod
    def play(cam: Camera, profile: CameraProfile, player_cmd: str, layout: WindowLayout,
             skip_focus: bool = False, global_mute: bool = False) -> bool:
        if not shutil.which('mpv'):
            notify("mpv not found!", "error")
            return False

        logger.info(f"Starting player for {cam.name}")

        try:
            if cam.type == CameraType.V4L2:
                return Player._play_v4l2(cam, profile, layout, player_cmd,
                                         skip_focus=skip_focus, global_mute=global_mute)
            elif cam.type == CameraType.FILE:
                return Player._play_file(cam, layout, skip_focus=skip_focus,
                                         global_mute=global_mute)
            elif cam.type == CameraType.SCANNER:
                return Player._play_scanner(cam, skip_focus=skip_focus)
            else:
                return Player._play_rtsp(cam, profile, player_cmd, layout,
                                         skip_focus=skip_focus, global_mute=global_mute)
        except Exception as e:
            logger.error(f"Error starting player: {e}")
            notify(f"Player error: {str(e)[:30]}", "error")
            return False

    @staticmethod
    def _play_file(cam: Camera, layout: WindowLayout,
                   _watchdog_restart: bool = False,
                   skip_focus: bool = False,
                   global_mute: bool = False) -> bool:
        if not cam.file_path or not os.path.isfile(cam.file_path):
            notify(f"FILE: file not found: {cam.file_path}", "error")
            return False

        name_safe = cam.name.replace(' ', '_')
        ipc_path  = MpvController.socket_path_for(cam.name, os.getpid())
        try:
            os.unlink(ipc_path)
        except FileNotFoundError:
            pass

        # Wykryj plik audio (brak video) — dodaj wizualizację oscilloscope
        _AUDIO_EXTS = {'.mp3', '.flac', '.ogg', '.opus', '.m4a',
                       '.aac', '.wav', '.wma', '.ape', '.mka'}
        _ext = os.path.splitext(cam.file_path)[1].lower()
        _is_audio_only = _ext in _AUDIO_EXTS

        args = [
            'mpv',
            cam.file_path,
            f'--geometry={layout.w}x{layout.h}+{layout.x}+{layout.y}',
            f'--title=FILE:{name_safe}',
            '--no-border',
            f'--input-ipc-server={ipc_path}',
            f'--speed={cam.image_params.get("speed", cam.file_speed):.2f}',
        ]
        if _is_audio_only:
            # Oscyloskop / wizualizacja audio przez lavfi
            _vis_size = f"{layout.w}x{layout.h}"
            args += [
                f'--lavfi-complex=[aid1]asplit=2[ao][a1];[a1]avectorscope=s={_vis_size}:zoom=1.5:rc=0:gc=200:bc=0:rf=1:gf=8:bf=7[vo]',
                '--no-audio-display',
            ]
        # Zastosuj image_params bezpośrednio w komendzie mpv — bez czekania na IPC
        ip = cam.image_params
        if ip.get("brightness", 0) != 0: args.append(f'--brightness={int(ip["brightness"])}')
        if ip.get("contrast",   0) != 0: args.append(f'--contrast={int(ip["contrast"])}')
        if ip.get("saturation", 0) != 0: args.append(f'--saturation={int(ip["saturation"])}')
        if ip.get("gamma",      0) != 0: args.append(f'--gamma={int(ip["gamma"])}')
        if ip.get("hue",        0) != 0: args.append(f'--hue={int(ip["hue"])}')
        vol = ip.get("volume", 100)
        if vol != 100: args.append(f'--volume={int(vol)}')
        if ip.get("mute", False) or global_mute: args.append('--mute=yes')
        if cam.file_loop:
            args.append('--loop-file=inf')
        if cam.file_start > 0:
            args.append(f'--start={cam.file_start:.1f}')

        logger.info(f"FILE mpv command: {' '.join(args)}")

        profile = cam.profiles[cam.active_profile] if cam.profiles else None

        proc = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if profile:
            profile.pid      = proc.pid
            profile.ipc_path = ipc_path
        logger.info(f"FILE player PID: {proc.pid}")

        def _restart(c, p):
            Player._play_file(c, layout, _watchdog_restart=True,
                              global_mute=global_mute)

        if not _watchdog_restart:
            PlayerWatchdog.reset_restart_count(cam.name)

        if not ProcessManager.wait_for_start(proc.pid):
            if profile:
                profile.error = True
                profile.pid   = None
            logger.error(f"FILE player for {cam.name} failed to start")
            notify(f"{cam.name}: cannot start player", "error")
            return False

        PlayerWatchdog(proc, cam, profile or CameraProfile(), _restart,
                       eof_stops=(cam.type == CameraType.FILE))

        if not skip_focus:
            Terminal.restore_focus(mpv_pid=proc.pid)

        # Wymuś pozycję przez kdotool/xdotool w tle
        if _win_tool_available() and cam.layout:
            _title = f"FILE:{cam.name.replace(' ', '_')}"
            threading.Thread(
                target=Terminal.reposition_mpv_window,
                args=(_title, layout), daemon=True).start()

        return True

    @staticmethod
    def _play_v4l2(cam: Camera, profile: CameraProfile, layout: WindowLayout,
                    player_cmd: str = "", _watchdog_restart: bool = False,
                    skip_focus: bool = False, global_mute: bool = False) -> bool:
        name_safe = cam.name.replace(' ', '_')
        dev_short = cam.device.split('/')[-1] if cam.device else "video"

        if cam.device:
            try:
                r = subprocess.run(
                    ["fuser", cam.device],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE
                )
                if r.returncode == 0:
                    pids = r.stdout.decode().split()
                    my_pid = str(os.getpid())
                    known_pid = str(profile.pid or 0)
                    for p in pids:
                        clean_pid = "".join(filter(str.isdigit, p))
                        if not clean_pid or clean_pid == my_pid:
                            continue
                        try:
                            import signal as _sig
                            os.kill(int(clean_pid), _sig.SIGTERM)
                            logger.info(f"V4L2 {cam.device}: released PID {clean_pid} before restart")
                        except (ProcessLookupError, ValueError):
                            pass
                    time.sleep(0.3)
            except FileNotFoundError:
                pass

        ipc_path = MpvController.socket_path_for(cam.name, os.getpid())
        try:
            os.unlink(ipc_path)
        except FileNotFoundError:
            pass

        lavf_opts = [f'framerate={profile.fps or 30}']
        if 'x' in profile.res:
            lavf_opts.insert(0, f'video_size={profile.res}')

        args = [
            'mpv',
            f'av://v4l2:{cam.device}',
            '--demuxer-lavf-analyzeduration=0.5',
            f'--demuxer-lavf-o={",".join(lavf_opts)}',
            f'--geometry={layout.w}x{layout.h}+{layout.x}+{layout.y}',
            f'--title=LIVE:{name_safe}[{dev_short}]',
            f'--input-ipc-server={ipc_path}',
        ]
        if global_mute:
            args.append('--mute=yes')
        if '--no-border' in (player_cmd or ''):
            args.insert(1, '--no-border')

        cmd_str = ' '.join(args)
        logger.info(f"V4L2 mpv command: {cmd_str}")

        proc = subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        profile.pid = proc.pid
        profile.ipc_path = ipc_path
        logger.info(f"V4L2 player PID: {proc.pid}")

        def _restart(cam, profile):
            Player._play_v4l2(cam, profile, layout, player_cmd, _watchdog_restart=True,
                              global_mute=global_mute)

        if not _watchdog_restart:
            PlayerWatchdog.reset_restart_count(cam.name)

        if not ProcessManager.wait_for_start(proc.pid):
            profile.error = True
            profile.pid = None
            logger.error(f"Player for {cam.name} failed to start")
            notify(f"{cam.name}: failed to start player", "error")
            return True

        PlayerWatchdog(proc, cam, profile, _restart)

        if not skip_focus:
            Terminal.restore_focus(mpv_pid=proc.pid)

        # Wymuś pozycję przez kdotool/xdotool w tle
        if _win_tool_available() and cam.layout:
            _title = f"LIVE:{cam.name.replace(' ', '_')}"
            threading.Thread(
                target=Terminal.reposition_mpv_window,
                args=(_title, layout), daemon=True).start()

        return True

    @staticmethod
    def _play_rtsp(cam: Camera, profile: CameraProfile, player_cmd: str, layout: WindowLayout, _watchdog_restart: bool = False, skip_focus: bool = False, global_mute: bool = False) -> bool:
        if not _watchdog_restart:
            NetworkUtils.resolve_ip(cam)
        name_safe = cam.name.replace(' ', '_')

        args = shlex.split(player_cmd)
        if args and args[0] in ('mpv', 'ffplay'):
            args = args[1:]

        ipc_path = MpvController.socket_path_for(cam.name, os.getpid())
        try:
            os.unlink(ipc_path)
        except FileNotFoundError:
            pass

        full_args = [
            'mpv',
            *args,
            f'--geometry={layout.w}x{layout.h}+{layout.x}+{layout.y}',
            f'--title=LIVE:{name_safe}',
            f'--input-ipc-server={ipc_path}',
        ]
        if global_mute: full_args.append('--mute=yes')
        full_args.append(profile.uri)

        cmd_str = ' '.join(f'"{a}"' if ' ' in a else a for a in full_args)
        logger.info(f"RTSP mpv command: {cmd_str}")

        proc = subprocess.Popen(full_args, stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL)
        profile.pid = proc.pid
        profile.ipc_path = ipc_path
        logger.info(f"RTSP player PID: {proc.pid}")

        def _restart(cam, profile):
            Player._play_rtsp(cam, profile, player_cmd, layout, _watchdog_restart=True,
                              global_mute=global_mute)

        if not _watchdog_restart:
            PlayerWatchdog.reset_restart_count(cam.name)

        if not ProcessManager.wait_for_start(proc.pid):
            profile.error = True
            profile.pid = None
            logger.error(f"Player for {cam.name} failed to start")
            notify(f"{cam.name}: failed to start player", "error")
            return False

        PlayerWatchdog(proc, cam, profile, _restart)

        if not skip_focus:
            Terminal.restore_focus(mpv_pid=proc.pid)

        # Wymuś pozycję przez kdotool/xdotool w tle (Wayland ignoruje --geometry)
        if _win_tool_available() and cam.layout:
            _title = f"LIVE:{name_safe}"
            threading.Thread(
                target=Terminal.reposition_mpv_window,
                args=(_title, layout), daemon=True).start()

        return True

    @staticmethod
    def _play_scanner(cam: 'Camera', skip_focus: bool = False,
                      progress_callback=None) -> bool:
        """Perform scan using scanimage + convert (stable temporary file version).
        If progress_callback is provided, it will be called with percentage (0-100)
        based on scanimage --progress output.
        """
        if not shutil.which('scanimage'):
            notify("scanimage not found! Install: sane-utils", "error")
            return False

        import datetime as _dt
        import tempfile as _tmp
        import select
        import re

        # --- Parameters ---
        mode    = cam.scan_mode
        dpi     = cam.scan_dpi
        area    = cam.scan_area          # "x:y:w:h"
        fmt     = cam.scan_format
        quality = cam.scan_quality
        resize  = cam.scan_resize
        desc    = cam.scan_desc
        dest    = cam.scan_dest

        device = cam.scan_device
        if cam.scan_vidpid:
            resolved = PTZMasterApp._resolve_scanner_device(cam.scan_vidpid)
            if resolved:
                device = resolved
                cam.scan_device = resolved
            elif not device:
                notify(f"Scanner VID:PID={cam.scan_vidpid} not found on USB", "error")
                return False

        # Parse area
        try:
            xl, yt, wd, ht = area.split(":")
        except Exception:
            xl, yt, wd, ht = "0", "0", "215", "297"

        # Create destination directory
        try:
            os.makedirs(dest, exist_ok=True)
        except Exception as e:
            notify(f"Scan dest error: {e}", "error")
            return False

        # Generate filename
        today = _dt.date.today().strftime("%Y-%m-%d")
        desc_part = f"_{desc}" if desc else ""
        pattern = f"{today}{desc_part}_*.{fmt}"

        import glob as _gl
        existing = _gl.glob(os.path.join(dest, pattern))
        nums = []
        for f in existing:
            bn = os.path.basename(f)
            try:
                n = int(bn.split("_")[-1].split(".")[0])
                nums.append(n)
            except Exception:
                pass
        next_num = max(nums, default=0) + 1
        fname = f"{today}{desc_part}_{next_num:03d}.{fmt}"
        dest_file = os.path.join(dest, fname)

        # Raw file handling
        raw_file = os.path.join(dest, f"{today}{desc_part}_{next_num:03d}_raw.tiff")
        out_file = dest_file

        profile = cam.profiles[cam.active_profile] if cam.profiles else None
        if profile:
            profile.pid = -1
            profile.ipc_path = dest_file

        # POPRAWKA: Wymuszamy dużą literę dla sterownika SANE (Gray, Color, Lineart)
        sane_mode = mode.capitalize() if mode else "Gray"

        logger.info(f"Scan START: {sane_mode} {dpi}DPI → {dest_file}")
        notify(f"Scanning... {sane_mode} {dpi}DPI", "info")

        try:
            # 1. scanimage -> raw TIFF file
            scan_cmd = [
                'scanimage',
                '--progress',                     # <-- WŁĄCZAMY RAPORTOWANIE POSTĘPU
                '--mode', sane_mode,
                '-l', xl, '-t', yt,
                '-x', wd, '-y', ht,
                '--resolution', str(dpi),
                '--format', 'tiff',               # Zawsze TIFF na tym etapie
                '--output-file', raw_file
            ]
            if device:
                scan_cmd += ['--device-name', device]

            logger.info(f"scanimage cmd: {' '.join(scan_cmd)}")

            # Uruchamiamy proces i monitorujemy stderr dla postępu
            proc = subprocess.Popen(
                scan_cmd,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                bufsize=1
            )

            start_time = time.time()
            timeout = 120  # sekund

            # Odczytuj stderr linia po linii, parsuj postęp
            while proc.poll() is None:
                if time.time() - start_time > timeout:
                    proc.kill()
                    raise subprocess.TimeoutExpired(scan_cmd, timeout)

                # Czekaj na dane na stderr (maks. 0.3s)
                rlist, _, _ = select.select([proc.stderr], [], [], 0.3)
                if proc.stderr in rlist:
                    line = proc.stderr.readline()
                    if not line:
                        continue
                    # Szukaj "Progress: 45.2%"
                    match = re.search(r'Progress:\s*(\d+(?:\.\d+)?)%', line)
                    if match and progress_callback:
                        percent = int(float(match.group(1)))
                        progress_callback(percent)
                    else:
                        logger.debug(f"scanimage stderr: {line.strip()}")

            # Odczytaj ewentualne pozostałe dane
            remaining = proc.stderr.read()
            if remaining:
                logger.debug(f"scanimage stderr (remaining): {remaining}")

            returncode = proc.returncode

            if returncode != 0:
                logger.error(f"scanimage failed with code {returncode}")
                notify(f"Scan failed (code {returncode})", "error")
                return False

            if not os.path.isfile(raw_file) or os.path.getsize(raw_file) == 0:
                notify("Scan empty — check scanner", "error")
                return False

            # 2. convert (ImageMagick)
            if shutil.which('convert'):
                conv_cmd = [
                    'convert', raw_file,
                    '-sharpen', '0x1.0',
                    '-resize', resize,
                    '-quality', str(quality),
                    '-strip', out_file
                ]
                logger.info(f"convert cmd: {' '.join(conv_cmd)}")
                conv_proc = subprocess.run(
                    conv_cmd,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                    timeout=120
                )
                if conv_proc.returncode != 0:
                    err = conv_proc.stderr.decode('utf-8', errors='replace')[:200]
                    logger.error(f"convert failed: {err}")
                    notify(f"Convert error, saving raw TIFF", "warning")
                    src = raw_file
                else:
                    src = out_file
            else:
                src = raw_file
                notify("Raw TIFF saved (no convert)", "warning")

            # 3. Move to destination
            if src != dest_file:
                shutil.copy2(src, dest_file)

            logger.info(f"Scan saved: {dest_file}")
            notify(f"Scan saved: {fname}", "info")

            if profile:
                profile.pid = None
                profile.ipc_path = dest_file

            # 4. Open viewer
            viewer = cam.scan_viewer or "mpv"
            if shutil.which(viewer):
                subprocess.Popen(
                    [viewer, dest_file],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                )
            elif shutil.which('xdg-open'):
                subprocess.Popen(
                    ['xdg-open', dest_file],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                )

            return True

        except subprocess.TimeoutExpired:
            notify("Scan timeout (>120s)", "error")
            return False
        except Exception as e:
            import traceback
            logger.error(f"_play_scanner exception: {e}\n{traceback.format_exc()}")
            notify(f"Scan error: {str(e)[:50]}", "error")
            return False
        finally:
            if raw_file and os.path.isfile(raw_file):
                if dest_file and os.path.isfile(dest_file) and raw_file != dest_file:
                    try: os.unlink(raw_file)
                    except OSError: pass
# =============================================================================
# UI - MAIN INTERFACE
# =============================================================================

class UI:
    def __init__(self, config: Config):
        self.config = config
        self.current_idx = 0
        self.active_dir = None
        self.progress = 0
        self._scan_status = ""
    
    @property
    def current_camera(self) -> Optional[Camera]:
        if not self.config.cameras:
            return None
        return self.config.cameras[self.current_idx]
    
    @property
    def current_profile(self) -> CameraProfile:
        cam = self.current_camera
        if not cam or not cam.profiles:
            return CameraProfile(name="None", token="None", res="N/A")
        idx = min(cam.active_profile, len(cam.profiles) - 1)
        return cam.profiles[idx]
    
    def draw(self):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        cam = self.current_camera

        if not cam:
            print(f"{YLW}No cameras in configuration.{RST}")
            print(f"{YLW}Press 'a' to add camera or F2 to discover.{RST}")
            return

        prof = self.current_profile
        W  = 57
        LW = 19

        sym = {
            "U": "▲", "D": "▼", "L": "◄", "R": "►",
            "C": "■", "Z+": "+", "Z-": "-"
        }
        dir_sym = {
            k: (f"{RED}█{RST}" if self.active_dir == k else f"{GRN}{v}{RST}")
            for k, v in sym.items()
        }

        if getattr(prof, 'error', False):
            p_status = f"{RED}[ERR]{RST}"
        elif ProcessManager.is_running(prof.pid):
            p_status = f"{GRN}[ON]{RST}"
        else:
            p_status = f"{RED}[OFF]{RST}"
        p_view = f"[{'#' * int(self.progress * 10)}{'-' * (10 - int(self.progress * 10))}]"

        type_short = {
            CameraType.ONVIF:     "ONV",
            CameraType.DVRIP:     "XM ",
            CameraType.RTSP_ONLY: "RTS",
            CameraType.V4L2:      "V4L",
            CameraType.FILE:      "FIL",
            CameraType.SCANNER:   "SCN",
            CameraType.AUTO:      "?  ",
        }
        ts = type_short.get(cam.type, "?  ")

        cameras = self.config.cameras
        total   = len(cameras)

        cam_rows = []
        for idx, c in enumerate(cameras):
            max_name = LW - 6
            cname    = c.name[:max_name]
            num      = f"{idx + 1}"
            if idx == self.current_idx:
                row = f" {YLW}►{RST} {YLW}{num}{RST} {GRN}{cname}{RST}"
            else:
                row = f"  {DIM}{num}{RST} {WHT}{cname}{RST}"
            cam_rows.append(pad(row, LW))

        rlines = []

        l1 = f" {YLW}F1{RST} Help {YLW}(c){RST} Config: {GRN}{CONFIG_FILE[:16]}{RST}"
        r1 = f"{YLW}(e){RST} Edit {YLW}(w){RST} {RED}Save{RST} "
        rlines.append(("top",    f"┬" + "─" * W + "┐"))
        rlines.append(("normal", f"│{pad(l1, W - ansilen(r1))}{r1}│"))
        rlines.append(("sep",    f"├" + "─" * W + "┤"))

        if cam.type == CameraType.V4L2:
            l2 = f" {YLW}(i){RST} IP: {GRN}{cam.device}{RST}"
            r2 = f"{YLW}(I){RST} MAC: {BLU}V4L2{RST} "
        elif cam.type == CameraType.FILE:
            fname = os.path.basename(cam.file_path) if cam.file_path else "—"
            l2 = f" {YLW}(i){RST} FILE: {GRN}{fname[:30]}{RST}"
            r2 = f"{MAG}x{cam.file_speed:.2f}{RST} {'🔁' if cam.file_loop else '▶'} "
        elif cam.type == CameraType.SCANNER:
            _dev = cam.scan_device or "(default)"
            l2 = f" {YLW}(i){RST} DEV: {GRN}{_dev[:28]}{RST}"
            r2 = f"{CYN}{cam.scan_mode} {cam.scan_dpi}DPI{RST} "
        else:
            port = cam.ports.onvif
            if cam.type == CameraType.DVRIP:
                port = cam.ports.dvrip
            elif cam.type == CameraType.RTSP_ONLY:
                port = cam.ports.rtsp
            l2 = f" {YLW}(i){RST} IP: {GRN}{cam.ip}{RST}:{YLW}{port}{RST}"
            r2 = f"{YLW}(I){RST} MAC: {BLU}{cam.mac[:18]}{RST} "
        rlines.append(("normal", f"│{pad(l2, W - ansilen(r2))}{r2}│"))

        l3 = f" {YLW}(u){RST} USER: {GRN}{cam.user}{RST}"
        pass_stars = ('*' * min(5, len(cam.password))).ljust(5)
        r3 = f"{YLW}(h){RST} PASS: {GRN}{pass_stars}{RST} {YLW}(?){RST} {MAG}{ts.strip():<3}{RST} {YLW}(g){RST} {MAG}Sync{RST} "
        if cam.type == CameraType.FILE:
            l3 = f" {MAG}Start:{RST} {GRN}{cam.file_start:.1f}s{RST}"
            r3 = f"{YLW}(h){RST} PASS: {GRN}{pass_stars}{RST} {YLW}(?){RST} {MAG}{ts.strip():<3}{RST} {YLW}(g){RST} {MAG}Sync{RST} "
        elif cam.type == CameraType.SCANNER:
            _dest_short = str(cam.scan_dest)[-28:]
            l3 = f" {YLW}(x){RST} {GRN}{cam.scan_format.upper():<4}{RST} q:{GRN}{cam.scan_quality}{RST} → {DIM}{_dest_short}{RST}"
            r3 = f"{MAG}{ts.strip():<3}{RST} {YLW}(g){RST} {MAG}Sync{RST} "
        rlines.append(("normal", f"│{pad(l3, W - ansilen(r3))}{r3}│"))
        rlines.append(("sep",    f"├" + "─" * W + "┤"))

        preset_count = len(cam.presets)
        preset_info  = f" {CYN}[{preset_count}P]{RST}" if preset_count > 0 else ""
        if cam.type in (CameraType.V4L2, CameraType.FILE):
            display_name = prof.name
            res_display  = ""
        elif cam.type == CameraType.SCANNER:
            display_name = "🖨  Scanner"
            res_display  = f" [{cam.scan_resize}] "
        else:
            display_name = prof.name
            res_display  = f" [{prof.res}]"
        l4     = f" 📺 {BLU}{display_name[:20]}{RST}{res_display}{preset_info}"
        t_info = f" {YLW}(t){RST} Token: {BLU}{prof.token[:10]}{RST}"
        rlines.append(("normal", f"│{pad(l4, W - ansilen(t_info))}{t_info}│"))
        rlines.append(("sep",    f"├" + "─" * W + "┤"))

        player_short = self.config.player_cmd[:13]
        if cam.type == CameraType.SCANNER:
            l5 = f" {YLW}(p){RST} Scan {YLW}(x){RST} Config  {DIM}viewer: {cam.scan_viewer}{RST}"
            r5 = f"{YLW}(k){RST} Kill {p_status} "
        else:
            l5 = f" {YLW}(p){RST} Play {YLW}(x){RST} mpv ▶ {YLW}(o){RST} {GRN}{player_short}{RST}"
            r5 = f"{YLW}(k){RST} Kill {p_status} "
        rlines.append(("normal", f"│{pad(l5, W - ansilen(r5))}{r5}│"))

        # For SCANNER, display scanner info instead of URI
        if cam.type == CameraType.SCANNER:
            scan_info = f" {YLW}(r){RST} SCAN: {cam.scan_mode} {cam.scan_dpi}DPI → {cam.scan_dest}"
            rlines.append(("normal", f"│{pad(scan_info, W)}│"))
        else:
            max_uri  = W - len(" (r) URI: ")
            uri      = prof.uri or "N/A"
            if len(uri) > max_uri:
                uri = uri[:max_uri - 1] + "…"
            uri_line = f" {YLW}(r){RST} URI: {BLU}{uri}{RST}"
            rlines.append(("normal", f"│{pad(uri_line, W)}│"))

        rlines.append(("bot_join", f"┴" + "─" * W + "┤"))

        LEFT_CONTENT = len(rlines) - 2

        print("┌" + "─" * LW + rlines[0][1])

        content_count = len(rlines) - 2
        visible_slots = content_count - 1
        offset = max(0, min(self.current_idx - visible_slots + 1,
                            len(cameras) - visible_slots))
        add_del_str = pad(f' {YLW}(,.) (a){RST}Add {YLW}(d){RST}Del', LW)
        for i in range(1, len(rlines) - 1):
            row_i = i - 1
            is_last_row = (i == content_count)
            if is_last_row:
                left_cell = add_del_str
            else:
                cam_idx = offset + row_i
                if cam_idx < len(cam_rows):
                    left_cell = cam_rows[cam_idx]
                else:
                    left_cell = ' ' * LW
            print(f'│{left_cell}{rlines[i][1]}')

        FW = LW + 1 + W
        print('├' + '─' * LW + rlines[-1][1])
        dsU=dir_sym["U"]; dsD=dir_sym["D"]; dsL=dir_sym["L"]; dsR=dir_sym["R"]; dsC=dir_sym["C"]; dsZP=dir_sym["Z+"]; dsZM=dir_sym["Z-"]
        print('│'+pad(f'    {dsU}    │ Progress: {p_view}', 33)+'│'+pad(f' {YLW}(m/l){RST} Dur: {GRN}{cam.duration:4.1f}s{RST} ', FW-34)+'│')
        print('│'+pad(f'  {dsL} {dsC} {dsR}  │  Zoom: [{dsZP}] [{dsZM}]', 33)+'│'+pad(f' {YLW}(s/f){RST} Speed: {GRN}{cam.speed:3.1f}{RST} ', FW-34)+'│')
        print('│'+pad(f'    {dsD}    │', 33)+'│'+pad(f' {YLW}(z){RST} Reset {YLW}F4{RST} Recall {YLW}F5{RST} Save', FW-34)+'│')
        cam_nav      = f"({self.current_idx + 1}/{total})"
        _gm = self.config.global_mute
        _mute_icon = f"{RED}🔇{RST}" if _gm else f"{DIM}🔊{RST}"
        footer_left  = f" {YLW}F2{RST} Discovery {YLW}F3{RST} Batch {YLW}1-9{RST} Cam {YLW}{cam_nav}{RST} {_mute_icon}{YLW}(F6){RST}"
        footer_right = f"{CYN}v{VERSION}{RST} {YLW}(ESC){RST} Quit "
        print(f"├" + "─" * FW + "┤")
        print(f"│{pad(footer_left, FW - ansilen(footer_right))}{footer_right}│")

        scan = getattr(self, '_scan_status', '')
        notifs = NotificationManager().get_active()
        status_line = scan if scan else (notifs[-1] if notifs else None)
        if status_line:
            print(f"├" + "─" * FW + "┤")
            print(f"│ {status_line}{' ' * (FW - ansilen(status_line) - 1)}│")

        print(f"└" + "─" * FW + "┘")

    def set_scan_status(self, msg: str):
        self._scan_status = msg

    def set_active_dir(self, dir: Optional[str]):
        self.active_dir = dir
    
    def set_progress(self, progress: float):
        self.progress = progress

# =============================================================================
# MAIN CAMERA CONTROL SCREEN (PTZMasterApp) Start
# =============================================================================

class PTZMasterApp:
    def __init__(self, config_file: str, restore_mode: bool = False, 
                 start_camera: str = "", start_mac: str = ""):
        self.config_file = config_file
        self.config_mgr = ConfigManager(config_file)
        self.config = self.config_mgr.config
        self.ui = UI(self.config)
        self.last_key = None
        self.restore_mode = restore_mode
        self.start_camera = start_camera
        self.start_mac = start_mac
        
        atexit.register(self.cleanup)
    
    def cleanup(self, save_session: bool = False):
        logger.info("Cleaning up before exit...")
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        
        if save_session:
            logger.info("Saving session state...")
            self._save_session_state()
            self.config_mgr.save(create_backup=False)
        else:
            logger.info("Exiting without saving session")
        
        ProcessManager.kill_all(self.config.cameras)
    
    def _save_session_state(self):
        playing = []
        
        for i, cam in enumerate(self.config.cameras):
            if cam.profiles and cam.active_profile < len(cam.profiles):
                prof = cam.profiles[cam.active_profile]
                if prof.pid and ProcessManager.is_running(prof.pid):
                    playing.append({
                        "camera": i,
                        "profile": cam.active_profile
                    })
        
        import datetime
        self.config.session_state = SessionState(
            active_camera_index=self.ui.current_idx,
            playing_cameras=playing,
            timestamp=datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        )
        
        logger.info(f"Session state saved: {len(playing)} playing cameras")
    
    def _restore_session(self):
        if not self.config.session_state:
            notify("No saved session", "warning")
            return
        
        ss = self.config.session_state
        
        print(f"\n{CYN}Restoring session from {ss.timestamp}...{RST}\n")
        
        restored = 0
        started_pids = []
        for play in ss.playing_cameras:
            cam_idx = play.get("camera", 0)
            prof_idx = play.get("profile", 0)

            if cam_idx >= len(self.config.cameras):
                continue

            cam = self.config.cameras[cam_idx]
            if prof_idx >= len(cam.profiles):
                continue

            cam.active_profile = prof_idx
            prof = cam.profiles[prof_idx]

            layout = cam.layout or self.config.layout["mpv_default"]
            if Player.play(cam, prof, self.config.player_cmd, layout,
                           skip_focus=True,
                           global_mute=self.config.global_mute):
                print(f"  {GRN}✓{RST} {cam.name}")
                if prof.pid:
                    started_pids.append(prof.pid)
                restored += 1
                time.sleep(0.3)

        if 0 <= ss.active_camera_index < len(self.config.cameras):
            self.ui.current_idx = ss.active_camera_index

        print(f"\n{GRN}Restored {restored} camera(s){RST}")
        notify(f"Restored {restored} cam(s)", "info")
        Terminal.restore_focus(mpv_pids=started_pids)
    
    def _mouse_off(self): 
        mouse_off()
    
    def _mouse_on(self):  
        mouse_on()

    def _wait_click_or_key(self):
        import termios as _t, time as _time
        fd = sys.stdin.fileno()
        old_settings = _t.tcgetattr(fd)
        try:
            _t.tcflush(fd, _t.TCIFLUSH)
        except Exception:
            pass
        _time.sleep(0.05)
        self._mouse_on()
        try:
            while True:
                key = get_key()
                if isinstance(key, MouseEvent):
                    if not key.release:
                        break
                elif key not in (Key.TIMEOUT,):
                    break
        finally:
            self._mouse_off()
            _t.tcsetattr(fd, _t.TCSADRAIN, old_settings)

    def _handle_mouse_click(self, ev: 'MouseEvent'):
        r, c = ev.row, ev.col
        cam = self.ui.current_camera
        LW = 19
        S  = LW + 2

        # For SCANNER, ignore PTZ area clicks (rows 12-14, columns related to PTZ)
        if cam and cam.type == CameraType.SCANNER:
            # If click in PTZ area (rows 12,13,14 and relevant columns), just return
            if r in (12, 13, 14):
                # Allow only maybe the progress bar or other non-PTZ elements? Better to ignore.
                return

        if 1 <= c <= LW + 1 and r <= 9:
            cameras = self.ui.config.cameras
            total = len(cameras)
            visible_slots = 8
            offset = max(0, min(self.ui.current_idx - visible_slots + 1,
                                total - visible_slots))
            cam_idx = offset + (r - 2)
            if 0 <= cam_idx < total:
                self.ui.current_idx = cam_idx
                self._sync_network(cameras[self.ui.current_idx])
                self.ui.draw()
            return

        if r == 2:
            if S+2 <= c <= S+3:
                self._mouse_off(); self._show_help(); self._mouse_on(); self.ui.draw(); return
            if S+10 <= c <= S+12:
                self._mouse_off()
                new_file = self._edit_param("CONFIG FILE", self.config_file)
                self._mouse_on()
                if new_file != self.config_file:
                    self.config_file = new_file
                    self.config_mgr = ConfigManager(self.config_file)
                    self.config = self.config_mgr.config
                    self.ui.config = self.config
                    self.ui.current_idx = 0
                self.ui.draw(); return
            if S+40 <= c <= S+42:
                self._mouse_off(); self._edit_camera_all(); self._mouse_on(); self.ui.draw(); return
            if S+50 <= c <= S+52:
                self.config_mgr.save(); notify("Saved", "info"); self.ui.draw(); return

        if r == 4:
            if S+2 <= c <= S+3:
                self._mouse_off(); self._edit_camera_ip(); self._mouse_on(); self.ui.draw(); return
            if S+31 <= c:
                self._mouse_off(); self._show_imaging(); self._mouse_on(); self.ui.draw(); return

        if r == 5:
            if S+2 <= c <= S+3 and cam:
                self._mouse_off()
                cam.user = self._edit_param("USER", cam.user)
                self._mouse_on(); self.ui.draw(); return
            if S+25 <= c <= S+27 and cam:
                self._mouse_off()
                cam.password = self._edit_param("PASS", cam.password)
                self._mouse_on(); self.ui.draw(); return
            if S+42 <= c <= S+44:
                self._mouse_off(); self._change_camera_type(); self._mouse_on(); self.ui.draw(); return
            if S+49 <= c <= S+51:
                self._mouse_off(); self._sync_profiles(); self._mouse_on(); self.ui.draw(); return

        if r == 7 and cam and cam.profiles:
            cam.active_profile = (cam.active_profile + 1) % len(cam.profiles)
            self.ui.draw(); return

        if r == 9:
            if S+1 <= c <= S+3:
                self._mouse_off(); self._play_stream(); self._mouse_on(); self.ui.draw(); return
            if S+10 <= c <= S+12:
                self._mouse_off()
                cam = self.ui.current_camera
                if cam and cam.type == CameraType.SCANNER:
                    self._scanner_control_screen()
                else:
                    self._mpv_control_screen_cam()
                self._mouse_on(); self.ui.draw(); return
            if S+20 <= c <= S+22:
                self._mouse_off()
                self.config.player_cmd = self._edit_param("PLAYER CMD", self.config.player_cmd)
                self._mouse_on(); self.ui.draw(); return
            if S+44 <= c <= S+46 and cam:
                ProcessManager.kill_all([cam]); self.ui.draw(); return

        if r == 10:
            if c <= LW + 1:
                cameras = self.ui.config.cameras
                if 3 <= c <= 4 and cameras:
                    self.ui.current_idx = (self.ui.current_idx - 1) % len(cameras)
                    self._sync_network(cameras[self.ui.current_idx]); self.ui.draw(); return
                if 5 <= c <= 6 and cameras:
                    self.ui.current_idx = (self.ui.current_idx + 1) % len(cameras)
                    self._sync_network(cameras[self.ui.current_idx]); self.ui.draw(); return
                if 8 <= c <= 10:
                    new_cam = Camera()
                    cameras.append(new_cam)
                    self.ui.current_idx = len(cameras) - 1
                    self.ui.draw(); return
                if 15 <= c <= 17 and cam:
                    ProcessManager.kill_all([cam])
                    cameras.pop(self.ui.current_idx)
                    self.ui.current_idx = max(0, self.ui.current_idx - 1)
                    notify(f"Deleted {cam.name}", "info"); self.ui.draw(); return
            else:
                if c >= S+2:
                    self._mouse_off(); self._uri_menu(); self._mouse_on(); self.ui.draw(); return

        if r == 12:
            if c == 6:
                self._move_timed(0.0, 1.0, 0.0, "U"); self.ui.draw(); return
            if 37 <= c <= 38 and cam:
                cam.duration = round(cam.duration + 0.1, 1); self.ui.draw(); return
            if 40 <= c <= 41 and cam:
                cam.duration = max(0.1, round(cam.duration - 0.1, 1)); self.ui.draw(); return

        if r == 13:
            if c == 4:    self._move_timed(-1.0, 0.0, 0.0, "L"); self.ui.draw(); return
            if c == 6:    self._move_timed( 0.0, 0.0, 0.0, "C"); self.ui.draw(); return
            if c == 8:    self._move_timed( 1.0, 0.0, 0.0, "R"); self.ui.draw(); return
            if 20 <= c <= 22: self._move_timed(0.0, 0.0,  1.0, "Z+"); self.ui.draw(); return
            if 24 <= c <= 26: self._move_timed(0.0, 0.0, -1.0, "Z-"); self.ui.draw(); return
            if 37 <= c <= 38 and cam:
                cam.speed = max(0.1, round(cam.speed - 0.1, 1)); self.ui.draw(); return
            if 40 <= c <= 41 and cam:
                cam.speed = min(1.0, round(cam.speed + 0.1, 1)); self.ui.draw(); return

        if r == 14:
            if c == 6:
                self._move_timed(0.0, -1.0, 0.0, "D"); self.ui.draw(); return
            if 35 <= c <= 43 and cam:
                cam.speed = 0.5; cam.duration = 0.4
                notify("Reset to defaults", "info"); self.ui.draw(); return
            if 47 <= c <= 48:
                self._mouse_off(); self._recall_preset(); self._mouse_on(); self.ui.draw(); return
            if 57 <= c <= 58:
                self._mouse_off(); self._save_preset(); self._mouse_on(); self.ui.draw(); return

        if r == 16:
            # === Nawigacja po kamerach (oryginalne, działające zakresy) ===
            if c == 25 or c == 27:
                cameras = self.ui.config.cameras
                if cameras:
                    self.ui.current_idx = (self.ui.current_idx + (1 if c == 27 else -1)) % len(cameras)
                    self._sync_network(cameras[self.ui.current_idx])
                    self.ui.draw()
                return
            if 33 <= c <= 34 or 36 <= c <= 37:
                cameras = self.ui.config.cameras
                if cameras:
                    self.ui.current_idx = (self.ui.current_idx + (1 if c >= 36 else -1)) % len(cameras)
                    self._sync_network(cameras[self.ui.current_idx])
                    self.ui.draw()
                return

            # === Przyciski funkcyjne (stałe zakresy) ===
            if 3 <= c <= 4:                     # F2 Discovery
                self._mouse_off()
                self._discover_cameras()
                self._mouse_on()
                self.ui.draw()
                return
            if 16 <= c <= 17:                   # F3 Batch
                self._mouse_off()
                self._batch_menu()
                self._mouse_on()
                self.ui.draw()
                return
            if 39 <= c <= 44:
                self._mouse_off()
                self.config.global_mute = not self.config.global_mute
                _gm = self.config.global_mute
                for _cam in self.config.cameras:
                    for _prof in _cam.profiles:
                        if _prof.pid and ProcessManager.is_running(_prof.pid):
                            _ctrl = _prof.get_mpv()
                            if _ctrl and _ctrl.is_alive():
                                _ctrl.set_property("mute", _gm)
                self.config_mgr.save()
                notify(f"🔇 Global mute {'ON' if _gm else 'OFF'}",
                       "warning" if _gm else "info")
                self._mouse_on()
                self.ui.draw()
                return

            if 70 <= c <= 73:                   # (ESC) Quit
                self._mouse_off()
                self._confirm_exit()
                self._mouse_on()
                return

    def _confirm_exit(self, quick_exit: bool = False):
        if quick_exit:
            print(f"\n{GRN}⚡ Quick exit - saving session...{RST}")
            time.sleep(0.3)
            self.cleanup(save_session=True)
            sys.exit(0)
        
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        W = 57
        
        playing = 0
        for cam in self.config.cameras:
            for prof in cam.profiles:
                if prof.pid and ProcessManager.is_running(prof.pid):
                    playing += 1
        
        current_cam_name = self.ui.current_camera.name if self.ui.current_camera else "None"
        
        print(f"{YLW}┌" + "─" * W + f"┐{RST}")
        print(f"{YLW}│{pad(' EXIT CONFIRMATION', W)}│{RST}")
        print(f"{YLW}├" + "─" * W + f"┤{RST}")
        print(f"{YLW}│{pad(f' 📷 Active camera: {self.ui.current_idx+1}. {current_cam_name[:30]}', W)}│{RST}")
        print(f"{YLW}│{pad(f' 📺 Playing streams: {playing}', W)}│{RST}")
        print(f"{YLW}│{pad('', W)}│{RST}")
        print(f"{YLW}│{pad(' Options:', W)}│{RST}")
        print(f"{YLW}│{pad('  [s] 💾 Save session and exit', W)}│{RST}")
        print(f"{YLW}│{pad('  [q] 🚪 Exit without saving', W)}│{RST}")
        print(f"{YLW}│{pad('  [c/ESC] 🔄 Cancel and return', W)}│{RST}")
        print(f"{YLW}├" + "─" * W + f"┤{RST}")
        print(f"{YLW}│{pad(' ⏱️  Auto-exit without saving in 10s...', W)}│{RST}")
        print(f"{YLW}└" + "─" * W + f"┘{RST}")
        
        fd = sys.stdin.fileno()
        old_settings = termios.tcgetattr(fd)
        try:
            tty.setraw(fd)
            time.sleep(0.05)
            import select as _sel_flush
            while _sel_flush.select([fd], [], [], 0)[0]:
                try: os.read(fd, 256)
                except OSError: break
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()

            key = None
            deadline = time.time() + 10
            time.sleep(0.2)  # krótki debounce
            while key is None:
                remaining = deadline - time.time()
                if remaining <= 0:
                    break
                # get_key z timeoutem 1s — nie blokuje, odświeża odliczanie
                ch = get_key(min(remaining, 1.0))
                if ch == Key.TIMEOUT:
                    continue
                if isinstance(ch, MouseEvent):
                    if not ch.release and ch.btn == 0:
                        r, c = ch.row, ch.col
                        if   r == 8  and 4 <= c <= 6: key = 's'
                        elif r == 9  and 4 <= c <= 6: key = 'q'
                        elif r == 10 and 4 <= c <= 6: key = 'c'
                        else: key = 'c'
                    continue
                # ESC = anuluj (wróć do programu)
                if ch in (Key.ESC, Key.ESC_ESC):
                    key = 'c'
                elif ch.lower() in ('s', 'q', 'c'):
                    key = ch.lower()

            sys.stdout.write('\r' + ' ' * 80 + '\r')
            sys.stdout.flush()

        finally:
            sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
            sys.stdout.flush()
            termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)
            import select as _sel2
            while _sel2.select([fd], [], [], 0)[0]:
                try: os.read(fd, 256)
                except OSError: break
        
        if key == 's':
            print(f"\n{GRN}💾 Saving session and exiting...{RST}")
            time.sleep(0.5)
            self.cleanup(save_session=True)
            sys.exit(0)
        
        elif key == 'q' or key is None:
            if key is None:
                print(f"\n{YLW}⏱️  Timeout - exiting without saving...{RST}")
            else:
                print(f"\n{YLW}🚪 Exiting without saving...{RST}")
            time.sleep(0.5)
            self.cleanup(save_session=False)
            sys.exit(0)
        
        else:
            print(f"\n{GRN}🔄 Cancelled - returning to application...{RST}")
            time.sleep(1)
            self.ui.draw()
            return
    
    def _get_recent_values(self, label: str) -> List[str]:
        values = set()
        for cam in self.config.cameras:
            if label == "IP" and cam.ip != "localhost":
                values.add(cam.ip)
            elif label == "USER" and cam.user:
                values.add(cam.user)
            elif "PORT" in label:
                values.add(str(cam.ports.onvif))
                values.add(str(cam.ports.dvrip))
                values.add(str(cam.ports.rtsp))
            elif label == "NAME" and cam.name:
                values.add(cam.name)
        return sorted(list(values))[-5:]
    
    def _get_hint_for_label(self, label: str, cam: Optional[Camera] = None) -> str:
        port_status = ""
        if cam and "PORT" in label and cam.ip and cam.ip != "localhost":
            test_port = cam.ports.onvif
            if "DVRIP" in label:
                test_port = cam.ports.dvrip
            elif "RTSP" in label:
                test_port = cam.ports.rtsp
            
            if NetworkUtils.check_port(cam.ip, test_port, timeout=0.5):
                port_status = f" {GRN}● OPEN{RST}"
            else:
                port_status = f" {RED}○ CLOSED{RST}"
        
        hints = {
            "IP": f"🌐 Network: {NetworkUtils.get_local_prefix()}xxx  Current: {cam.ip if cam else 'unknown'}",
            "PORT": "🔌 Common ports: ONVIF:80,8080,8899 | DVRIP:34567 | RTSP:554",
            "ONVIF PORT": f"🔌 ONVIF: 80,8080,8899,8000  Current: {cam.ports.onvif if cam else '?'}{port_status}",
            "DVRIP PORT": f"🔌 XM/iCSee: 34567  Current: {cam.ports.dvrip if cam else '?'}{port_status}",
            "RTSP PORT": f"🔌 RTSP: 554  Current: {cam.ports.rtsp if cam else '?'}{port_status}",
            "USER": f"👤 Username: admin, root, operator  Current: {cam.user if cam else 'admin'}",
            "PASS": f"🔐 Password: admin, 12345, (empty)  Current: {'•' * len(cam.password) if cam and cam.password else 'empty'}",
            "NAME": "📷 Camera name: max 30 chars, avoid special chars",
            "DEVICE PATH": "🎥 V4L2 device: /dev/video0, /dev/video1  (auto-detect available)",
            "RTSP PATH": "📡 RTSP path: /live/ch0, /stream1, /0/av0  (use 'r' to scan)",
            "PLAYER CMD": (
                f"🎬 V4L2: mpv av://v4l2:/dev/videoX  "
                f"({'✅ --no-border' if '--no-border' in self.config.player_cmd else '❌ no --no-border'})"
                if cam and cam.type == CameraType.V4L2
                else f"🎬 RTSP cmd: {self.config.player_cmd[:45]}..."
            ) if hasattr(self, 'config') else "🎬 Player command for mpv",
            "CONFIG FILE": f"📁 Config: JSON file  (default: {DEFAULT_CONFIG})",
            "PRESET NAME": "📍 Preset: name for PTZ position  (max 20 chars)",
        }
        
        if cam:
            if label == "IP":
                ping_status = f"{GRN}OK{RST}" if NetworkUtils.ping_host(cam.ip) else f"{RED}FAIL{RST}"
                return f"🌐 Current: {cam.ip}  Network: {NetworkUtils.get_local_prefix()}xxx  Ping: {ping_status}"
            
            if label == "USER":
                return f"👤 Current: {cam.user}  Default: admin"
            
            if label == "PASS":
                return f"🔐 Current: {'•' * len(cam.password)}  Default: admin"
        
        return hints.get(label, f"📝 Enter value or press Enter to keep current")
    
    def _edit_param(self, label: str, current: str, validator=None) -> str:
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        W = 57

        hint = self._get_hint_for_label(label, self.ui.current_camera)

        icons = {
            "IP": "🌐", "PORT": "🔌", "ONVIF PORT": "🔌", "DVRIP PORT": "🔌", "RTSP PORT": "🔌",
            "USER": "👤", "PASS": "🔐", "NAME": "📷", "PLAYER CMD": "🎬",
            "PRESET NAME": "📍", "CONFIG FILE": "📁", "DEVICE PATH": "🎥", "RTSP PATH": "📡"
        }
        icon = icons.get(label.split()[0] if " " in label else label, "📝")

        print(f"{YLW}┌" + "─" * W + f"┐{RST}")

        title = f" {icon}  {MAG}{label}{RST} "
        title_padded = pad(title, W)
        print(f"{YLW}│{RST}{title_padded}{YLW}│{RST}")

        print(f"{YLW}├" + "─" * W + f"┤{RST}")

        if len(hint) > W - 4:
            lines = textwrap.wrap(hint, width=W-4)
            for line in lines:
                print(f"{YLW}│{RST} {BLU}{pad(line, W-2)}{RST} {YLW}│{RST}")
        else:
            print(f"{YLW}│{RST} {BLU}{pad(hint, W-2)}{RST} {YLW}│{RST}")

        base_label = label.split()[0] if " " in label else label
        tips = {
            "IP": [
                "💡 Use Tab to auto-complete from history",
                "💡 Common prefixes: 192.168., 10.0., 172.16.",
                "💡 Press '.' to keep current value"
            ],
            "PORT": [
                "💡 ONVIF: 80, 8080, 8899, 8000",
                "💡 DVRIP (XM): 34567",
                "💡 RTSP: 554"
            ],
            "USER": [
                "💡 Default: admin, root, operator",
                "💡 Case sensitive!",
                "💡 Some cameras use empty user"
            ],
            "PASS": [
                "💡 Default: admin, 12345, 888888",
                "💡 Some cameras have no password",
                "💡 Characters are hidden for security"
            ],
            "NAME": [
                "💡 Use descriptive names (e.g., 'Living Room')",
                "💡 Max 30 characters",
                "💡 Avoid special characters"
            ],
            "RTSP PATH": [
                "💡 Common paths: /live/ch0, /stream1, /0/av0",
                "💡 Use 'r' key to scan automatically"
            ]
        }

        if base_label in tips:
            print(f"{YLW}├" + "─" * W + f"┤{RST}")
            for tip in tips[base_label]:
                tip_line = f" {YLW}{tip}{RST}"
                print(f"{YLW}│{RST}{pad(tip_line, W)}{YLW}│{RST}")

        recent = self._get_recent_values(label)
        if recent:
            print(f"{YLW}├" + "─" * W + f"┤{RST}")
            prefix = f" {CYN}Recent:{RST} "
            prefix_vis = len(" Recent:  ")
            available = W - prefix_vis - 2

            parts = []
            used = 0
            for val in recent:
                entry = val + "  "
                if used + len(entry) > available:
                    if not parts:
                        parts.append(val[:available - 4] + "…")
                    else:
                        parts.append("…")
                    break
                parts.append(val)
                used += len(entry)

            recent_str = prefix + "  ".join(parts)
            print(f"{YLW}│{RST}{pad(recent_str, W)}{YLW}│{RST}")

        print(f"{YLW}└" + "─" * W + f"┘{RST}")

        print(f"\n{YLW}Current:{RST} ", end='')
        if current:
            if label == "PASS":
                print(f"{GRN}{'•' * len(current)}{RST}")
            else:
                print(f"{GRN}{current}{RST}")
        else:
            print(f"{YLW}<empty>{RST}")

        examples = {
            "IP": "192.168.1.100",
            "ONVIF PORT": "80",
            "DVRIP PORT": "34567",
            "RTSP PORT": "554",
            "USER": "admin",
            "PASS": "••••••",
            "NAME": "Living Room Cam",
            "RTSP PATH": "/live/ch0",
            "DEVICE PATH": "/dev/video0",
        }

        example = ""
        for key, val in examples.items():
            if key in label or label in key:
                example = val
                break

        if example:
            prompt_str = f"{CYN}New {label}{RST} {YLW}(e.g. {example}){RST} {CYN}:>{RST} "
        else:
            prompt_str = f"{CYN}New {label}{RST} {CYN}:>{RST} "

        while True:
            try:
                new_val = rlinput(prompt_str, current).strip()
            except EOFError:
                new_val = ""

            if not new_val:
                print(f"{YLW}  Keeping current value{RST}")
                time.sleep(0.3)
                return current

            if validator and not validator(new_val):
                print(f"{RED}  ✗ Invalid!{RST} {YLW}Try again{RST}")
                continue

            print(f"{GRN}  ✓ Updated{RST}")
            time.sleep(0.2)
            return new_val
    
    def run(self):
        Terminal.capture_window_id()
        Terminal.setup_layout(self.config)
        
        if self.config.cameras:
            self._sync_network(self.config.cameras[0])
        
        if self.restore_mode and self.config.session_state:
            self._restore_session()

        if self.start_camera:
            try:
                idx = int(self.start_camera) - 1
                if 0 <= idx < len(self.config.cameras):
                    self.ui.current_idx = idx
                    logger.info(f"Start camera set by -c: index {idx}")
            except ValueError:
                logger.warning(f"Invalid -c value: {self.start_camera}")
        elif self.start_mac:
            for idx, cam in enumerate(self.config.cameras):
                if cam.mac.upper() == self.start_mac:
                    self.ui.current_idx = idx
                    logger.info(f"Start camera set by --mac: {self.start_mac}")
                    break
            else:
                logger.warning(f"Camera with MAC {self.start_mac} not found")
        
        self.ui.draw()
        self._start_auto_check_timer()
        self.last_key = None

        sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
        sys.stdout.flush()

        try:
            while True:
                key = get_key()

                if isinstance(key, MouseEvent):
                    if not key.release:
                        self._handle_mouse_click(key)
                    continue
                if key == Key.MOUSE_SCROLL_UP or key == Key.MOUSE_SCROLL_DOWN:
                    continue

                if DEBUG_MODE and key not in [Key.UP, Key.DOWN, Key.LEFT, Key.RIGHT]:
                    logger.debug(f"Key: {key}")

                # --------------------------------------------------------------
                # SCANNER: block unavailable actions
                # --------------------------------------------------------------
                cam = self.ui.current_camera
                if cam and cam.type == CameraType.SCANNER:
                    # Keys PTZ, sync, URI, player edit, credentials, speed/duration, zoom, preset, profile
                    if key in (Key.UP, Key.DOWN, Key.LEFT, Key.RIGHT,
                               '+', '=', '-', Key.SPACE,
                               'g', 'r', 'o', 'u', 'h', 's', 'f', 'm', 'l',
                               'z', 't', 'i', 'I', '?', '\\'):
                        notify("SCANNER: operation not available", "warning")
                        self.ui.draw()
                        continue
                    # Keys p, x, e, a, d, w, c, ,, ., 1-9, F1-F6, q work normally

                if key in (Key.ESC, Key.ESC_ESC):
                    # ESC = wróć / anuluj (identycznie jak q)
                    logger.info("ESC pressed - confirm exit")
                    self._mouse_off(); self._confirm_exit(); self._mouse_on()
                    continue

                if key.lower() == 'q':
                    if self.last_key and self.last_key.lower() == 'q':
                        logger.info("Double q detected - quick exit")
                        self._mouse_off(); self._confirm_exit(quick_exit=True); self._mouse_on()
                    else:
                        logger.info("Exit requested, asking for confirmation...")
                        self.last_key = 'q'
                        self._mouse_off(); self._confirm_exit(); self._mouse_on()
                        self.last_key = None
                    continue
                
                if key.lower() != 'q':
                    self.last_key = None
                
                if key == Key.F1:
                    self._mouse_off(); self._show_help(); self._mouse_on()
                    self.ui.draw()
                
                elif key == Key.F2:
                    self._mouse_off(); self._discover_cameras(); self._mouse_on()
                    self.ui.draw()
                
                elif key == Key.F3:
                    self._mouse_off(); self._batch_menu(); self._mouse_on()
                    self.ui.draw()
                
                elif key in (Key.F4, '4'):
                    if self.config.cameras:
                        logger.info(f"Recalling preset for {self.ui.current_camera.name}")
                        self._mouse_off(); self._recall_preset(); self._mouse_on()
                    self.ui.draw()
                
                elif key in (Key.F5, '5'):
                    if self.config.cameras:
                        logger.info(f"Saving preset for {self.ui.current_camera.name}")
                        self._mouse_off(); self._save_preset(); self._mouse_on()
                    self.ui.draw()
                
                elif key.lower() == 'a':
                    new_cam = Camera()
                    self.config.cameras.append(new_cam)
                    self.ui.current_idx = len(self.config.cameras) - 1
                    logger.info(f"Added new camera: {new_cam.name}")
                    self.ui.draw()
                
                elif key.lower() == 'c':
                    self._mouse_off(); new_file = self._edit_param("CONFIG FILE", self.config_file); self._mouse_on()
                    if new_file != self.config_file:
                        logger.info(f"Config file changed: {self.config_file} -> {new_file}")
                        self.config_file = new_file
                        self.config_mgr = ConfigManager(self.config_file)
                        self.config = self.config_mgr.config
                        self.ui.config = self.config
                        self.ui.current_idx = 0
                    self.ui.draw()
                
                elif key.isdigit() and key != '0':
                    idx = int(key) - 1
                    if 0 <= idx < len(self.config.cameras):
                        self.ui.current_idx = idx
                        self._sync_network(self.config.cameras[idx])
                        notify(f"Camera {key}: {self.config.cameras[idx].name}", "info")
                        logger.info(f"Switched to camera {idx+1}: {self.config.cameras[idx].name}")
                    else:
                        notify(f"Camera {key} not found", "warning")
                    self.ui.draw()
                
                elif not self.config.cameras:
                    self.ui.draw()
                    continue
                
                elif key == Key.UP:
                    self._move_timed(0.0, 1.0, 0.0, "U")
                elif key == Key.DOWN:
                    self._move_timed(0.0, -1.0, 0.0, "D")
                elif key == Key.LEFT:
                    self._move_timed(-1.0, 0.0, 0.0, "L")
                elif key == Key.RIGHT:
                    self._move_timed(1.0, 0.0, 0.0, "R")
                elif key in ['+', '=']:
                    self._move_timed(0.0, 0.0, 1.0, "Z+")
                elif key == '-':
                    self._move_timed(0.0, 0.0, -1.0, "Z-")
                elif key == Key.SPACE:
                    self._move_timed(0.0, 0.0, 0.0, "C")
                
                elif key == '.':
                    if self.config.cameras:
                        self.ui.current_idx = (self.ui.current_idx + 1) % len(self.config.cameras)
                        self._sync_network(self.config.cameras[self.ui.current_idx])
                        logger.info(f"Next camera: {self.ui.current_idx+1}")
                    self.ui.draw()
                elif key == ',':
                    if self.config.cameras:
                        self.ui.current_idx = (self.ui.current_idx - 1) % len(self.config.cameras)
                        self._sync_network(self.config.cameras[self.ui.current_idx])
                        logger.info(f"Previous camera: {self.ui.current_idx-1}")
                    self.ui.draw()
                
                elif key.lower() == 'g':
                    logger.info(f"Syncing profiles for {self.ui.current_camera.name}")
                    self._mouse_off(); self._sync_profiles(); self._mouse_on()
                    self.ui.draw()
                
                elif key.lower() == 't':
                    cam = self.ui.current_camera
                    if cam and cam.profiles:
                        cam.active_profile = (cam.active_profile + 1) % len(cam.profiles)
                        logger.info(f"Switched to profile {cam.active_profile+1}: {cam.profiles[cam.active_profile].name}")
                    self.ui.draw()
                
                elif key.lower() == 'p':
                    logger.info(f"Playing stream for {self.ui.current_camera.name}")
                    self._mouse_off(); self._play_stream(); self._mouse_on()
                    self.ui.draw()
                elif key.lower() == 'x':
                    cam = self.ui.current_camera
                    if cam and cam.type == CameraType.SCANNER:
                        self._mouse_off()
                        self._scanner_control_screen()
                        self._mouse_on()
                    else:
                        prof = self.ui.current_profile
                        player_running = prof and ProcessManager.is_running(prof.pid or 0)
                        if not player_running:
                            logger.info(f"Auto-starting stream for {cam.name} before control screen")
                            self._play_stream()
                            time.sleep(0.5)  # short pause for IPC socket creation
                        self._mouse_off()
                        self._mpv_control_screen_cam()
                        self._mouse_on()
                    self.ui.draw()
                elif key.lower() == 'k':
                    cam = self.ui.current_camera
                    if cam:
                        logger.info(f"Killing player for {cam.name}")
                        ProcessManager.kill_all([cam])
                    self.ui.draw()
                
                elif key.lower() == 'w':
                    logger.info("Manual config save")
                    self.config_mgr.save()
                    self.ui.draw()
                
                elif key.lower() == 'd':
                    cam = self.ui.current_camera
                    if cam:
                        logger.info(f"Deleting camera: {cam.name}")
                        ProcessManager.kill_all([cam])
                        self.config.cameras.pop(self.ui.current_idx)
                        self.ui.current_idx = max(0, self.ui.current_idx - 1)
                        notify(f"Deleted {cam.name}", "info")
                    self.ui.draw()
                
                elif key.lower() == 'e':
                    logger.info(f"Editing all parameters for {self.ui.current_camera.name}")
                    self._mouse_off(); self._edit_camera_all(); self._mouse_on()
                    self.ui.draw()
                elif key.lower() == 'i':
                    if key == 'I':
                        cam = self.ui.current_camera
                        if cam:
                            logger.info(f"Showing imaging settings for {cam.name}")
                            self._mouse_off(); self._show_imaging(); self._mouse_on()
                            self.ui.draw()
                    else:
                        logger.info(f"Editing IP for {self.ui.current_camera.name}")
                        self._mouse_off(); self._edit_camera_ip(); self._mouse_on()
                        self.ui.draw()
                elif key.lower() == 'u':
                    cam = self.ui.current_camera
                    if cam:
                        if cam.type == CameraType.V4L2:
                            notify("V4L2: no credentials", "warning")
                        else:
                            old = cam.user
                            self._mouse_off(); cam.user = self._edit_param("USER", cam.user); self._mouse_on()
                            logger.info(f"Username changed: {old} -> {cam.user}")
                    self.ui.draw()
                elif key.lower() == 'h':
                    cam = self.ui.current_camera
                    if cam:
                        if cam.type == CameraType.V4L2:
                            notify("V4L2: no credentials", "warning")
                        else:
                            logger.info(f"Password changed for {cam.name}")
                            self._mouse_off(); cam.password = self._edit_param("PASS", cam.password); self._mouse_on()
                    self.ui.draw()
                
                elif key == '?':
                    logger.info(f"Changing camera type for {self.ui.current_camera.name}")
                    self._mouse_off(); self._change_camera_type(); self._mouse_on()
                    self.ui.draw()
                
                elif key.lower() == 'o':
                    old = self.config.player_cmd
                    self._mouse_off(); self.config.player_cmd = self._edit_param("PLAYER CMD", self.config.player_cmd); self._mouse_on()
                    logger.info(f"Player command changed: {old} -> {self.config.player_cmd}")
                    self.ui.draw()
                
                elif key.lower() == 'r':
                    logger.info(f"Editing URI for {self.ui.current_camera.name}")
                    self._mouse_off(); self._uri_menu(); self._mouse_on()
                    self.ui.draw()
                
                elif key.lower() == 'f':
                    cam = self.ui.current_camera
                    if cam:
                        old = cam.speed
                        cam.speed = min(1.0, round(cam.speed + 0.1, 1))
                        logger.debug(f"Speed changed: {old} -> {cam.speed}")
                    self.ui.draw()
                elif key.lower() == 's':
                    cam = self.ui.current_camera
                    if cam:
                        old = cam.speed
                        cam.speed = max(0.1, round(cam.speed - 0.1, 1))
                        logger.debug(f"Speed changed: {old} -> {cam.speed}")
                    self.ui.draw()
                elif key.lower() == 'm':
                    cam = self.ui.current_camera
                    if cam:
                        old = cam.duration
                        cam.duration = round(cam.duration + 0.1, 1)
                        logger.debug(f"Duration changed: {old} -> {cam.duration}")
                    self.ui.draw()
                elif key.lower() == 'l':
                    cam = self.ui.current_camera
                    if cam:
                        old = cam.duration
                        cam.duration = max(0.1, round(cam.duration - 0.1, 1))
                        logger.debug(f"Duration changed: {old} -> {cam.duration}")
                    self.ui.draw()
                elif key in (Key.F6, '\\'):
                    # Global mute toggle — działa niezależnie od aktywnej kamery
                    self.config.global_mute = not self.config.global_mute
                    _gm = self.config.global_mute
                    # Zastosuj natychmiast do wszystkich grających instancji mpv
                    for _cam in self.config.cameras:
                        for _prof in _cam.profiles:
                            if _prof.pid and ProcessManager.is_running(_prof.pid):
                                _ctrl = _prof.get_mpv()
                                if _ctrl and _ctrl.is_alive():
                                    _ctrl.set_property("mute", _gm)
                    self.config_mgr.save()
                    notify(f"🔇 Global mute {'ON' if _gm else 'OFF'}",
                           "warning" if _gm else "info")
                    logger.info(f"Global mute toggled: {_gm}")
                    self.ui.draw()
                elif key.lower() == 'z':
                    cam = self.ui.current_camera
                    if cam:
                        cam.speed = 0.5
                        cam.duration = 0.4
                        notify("Reset to defaults", "info")
                        logger.info("Reset speed/duration to defaults")
                    self.ui.draw()
                
        except KeyboardInterrupt:
            logger.info("Interrupted by user")
            self._mouse_off(); self._confirm_exit(); self._mouse_on()
    
    def _sync_network(self, cam: Camera) -> bool:
        if cam.type in (CameraType.V4L2, CameraType.FILE, CameraType.SCANNER):
            return False

        # --- Tymczasowe wyłączenie myszy, aby uniknąć wycieków escape'ów ---
        self._mouse_off()
        try:
            NetworkUtils.resolve_ip(cam)

            if shutil.which('ping'):
                try:
                    subprocess.run(
                        ["ping", "-c", "1", "-W", "1", cam.ip],
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                        timeout=2
                    )
                except (subprocess.TimeoutExpired, OSError):
                    pass

            if cam.mac in [None, "", "UNKNOWN"]:
                mac = NetworkUtils.get_mac_from_ip(cam.ip)
                if mac and mac != "UNKNOWN":
                    cam.mac = mac
                    notify(f"MAC found: {mac[:12]}", "info")
                    return True

            return False
        finally:
            # Zawsze przywracamy mysz po zakończeniu (nawet po błędzie)
            self._mouse_on()
    
    def _sync_profiles(self):
        cam = self.ui.current_camera

        if not cam:
            return

        if cam.type == CameraType.V4L2:
            notify("V4L2: local device, no profiles to sync", "warning")
            return
        if cam.type == CameraType.FILE:
            notify("FILE: local file, no profiles to sync", "warning")
            return
        if cam.type == CameraType.SCANNER:
            notify("SCANNER: use (x) to configure", "warning")
            return

        # --- Zabezpieczenie stanu terminala na czas całej metody ---
        fd = sys.stdin.fileno()
        old_termios = termios.tcgetattr(fd)
        try:
            # Upewniamy się, że mysz jest włączona (na wypadek wcześniejszych błędów)
            self._mouse_on()

            if cam.type == CameraType.AUTO:
                print(f"\n{CYN}Detecting camera type...{RST}")
                new_type, port = CameraDetector.detect(cam, show_progress=True)
                cam.type = new_type

                if port:
                    if new_type == CameraType.DVRIP:
                        cam.ports.dvrip = port
                    else:
                        cam.ports.onvif = port

                notify(f"TYPE detected: {new_type.value}", "info")
                time.sleep(1)

            if cam.type == CameraType.DVRIP:
                print(f"\n{MAG}DVRIP camera - manual profile configuration{RST}")
                print("Use 'r' to scan RTSP paths")
                print("\nPress any key to continue...")
                self._wait_click_or_key()
                return

            if cam.type == CameraType.RTSP_ONLY:
                scanner = RTSPScanner(cam)
                profiles = scanner.scan()
                if profiles:
                    cam.profiles = profiles
                    cam.active_profile = 0
                    self.config_mgr.save()
                    notify(f"Found {len(profiles)} RTSP streams", "info")
                return

            if cam.type == CameraType.ONVIF:
                print(f"\n{CYN}ONVIF sync...{RST}")
                raw_xml = ""
                key_pressed = None

                try:
                    client = ONVIFClient(cam)
                    profiles, raw_xml = client.get_profiles()

                    if profiles:
                        cam.profiles = profiles
                        cam.active_profile = 0
                        notify(f"Synced {len(profiles)} profiles", "info")
                        self.config_mgr.save()

                        print(f"\n{GRN}Found {len(profiles)} profiles:{RST}")
                        for i, p in enumerate(profiles, 1):
                            try:
                                if "x" in p.res:
                                    width = int(p.res.split('x')[0])
                                    res_color = GRN if width >= 1920 else YLW
                                else:
                                    res_color = WHT
                            except Exception as e:
                                logger.debug(f"Resolution parse error: {e}")
                                res_color = WHT

                            print(f"  {i}. {p.name} - {res_color}{p.res}{RST}")

                        print(f"\n{GRN}✓ Sync completed successfully!{RST}")

                        print(f"\n{YLW}─── Debugging info ───{RST}")
                        print(f"{BLU}• RAW XML response:{RST} {len(raw_xml)} bytes")
                        print(f"{BLU}• Profiles found:{RST} {len(profiles)}")
                        print(f"{BLU}• Camera type:{RST} {cam.type.value}")
                        print(f"{BLU}• ONVIF port:{RST} {cam.ports.onvif}")

                        if "http://www.onvif.org/ver10/profile/wsdl" in raw_xml:
                            print(f"{BLU}• Profile version:{RST} Ver10")
                        if "InvalidArgVal" in raw_xml:
                            print(f"{YLW}• Warning:{RST} Invalid arguments in response")

                        print(f"\n{YLW}🔍 Debug options:{RST}")
                        print(f"  {GRN}1.{RST} Run with {CYN}--debug{RST} flag for verbose logging")
                        print(f"  {GRN}2.{RST} Press {CYN}d{RST} now to view RAW XML response")
                        print(f"  {GRN}3.{RST} Check {CYN}{LOG_FILE}{RST} for detailed logs")
                        print(f"  {GRN}4.{RST} Use {CYN}F1{RST} for help with camera configuration")

                        print(f"\n{YLW}Press 'd' for XML debug, any other key to continue (auto-continue in 10s)...{RST}")

                        # Bezpieczne oczekiwanie na klawisz z timeoutem
                        start_time = time.time()
                        key_pressed = None
                        while time.time() - start_time < 10:
                            k = get_key(timeout=0.2)
                            if k and k != Key.TIMEOUT:
                                if isinstance(k, str):
                                    key_pressed = k
                                    break
                                elif isinstance(k, MouseEvent) and not k.release:
                                    # kliknięcie myszy - kontynuuj
                                    break

                        if key_pressed and key_pressed.lower() == 'd':
                            self._show_debug_xml(raw_xml)
                        else:
                            if key_pressed is None:
                                print(f"\n{GRN}Timeout - continuing...{RST}")
                            else:
                                print(f"\n{GRN}Continuing...{RST}")
                            time.sleep(0.5)

                    else:
                        notify("No profiles found - check credentials", "error")
                        print(f"\n{RED}No profiles found.{RST}")
                        print(f"{YLW}Check:{RST}")
                        print(f"  • Username: {BLU}{cam.user}{RST}")
                        print(f"  • Password: {BLU}{'*' * len(cam.password)}{RST}")
                        print(f"  • ONVIF port: {BLU}{cam.ports.onvif}{RST}")
                        print(f"  • Camera IP: {BLU}{cam.ip}{RST}")

                        print(f"\n{YLW}🔍 Debug tips:{RST}")
                        print(f"  {GRN}•{RST} Try different ONVIF ports: 80, 8080, 8899, 8000")
                        print(f"  {GRN}•{RST} Check if camera supports ONVIF (try '?' to change type)")
                        print(f"  {GRN}•{RST} Run with {CYN}--debug{RST} for detailed logs")
                        print(f"  {GRN}•{RST} Test with VLC: {CYN}vlc rtsp://{cam.user}:{cam.password}@{cam.ip}:{cam.ports.rtsp}{RST}")

                        if raw_xml:
                            print(f"  {GRN}•{RST} Press {CYN}d{RST} to view RAW response (may contain clues)")
                            print(f"\n{YLW}Press 'd' for XML debug, any other key to continue...{RST}")

                            key_pressed = get_key()
                            if key_pressed.lower() == 'd':
                                self._show_debug_xml(raw_xml)
                        else:
                            print(f"\n{YLW}Press any key to continue...{RST}")
                            self._wait_click_or_key()

                except requests.exceptions.ConnectionError as e:
                    logger.error(f"ONVIF connection error: {e}")
                    notify("Camera offline", "error")
                    print(f"\n{RED}🚫 Connection refused - camera offline?{RST}")
                    print(f"\n{YLW}🔍 Debug:{RST}")
                    print(f"  {GRN}•{RST} Ping camera: {CYN}ping {cam.ip}{RST}")
                    print(f"  {GRN}•{RST} Check port: {CYN}nc -zv {cam.ip} {cam.ports.onvif}{RST}")
                    print(f"  {GRN}•{RST} Verify network connectivity")
                    print(f"  {GRN}•{RST} Check if firewall is blocking port {cam.ports.onvif}")

                    if "Connection refused" in str(e):
                        print(f"\n{YLW}💡 Hint: Camera may be on different port. Common ONVIF ports:{RST}")
                        print(f"    80, 8080, 8899, 8000, 5000")

                    print(f"\n{YLW}Press any key to continue...{RST}")
                    self._wait_click_or_key()

                except requests.exceptions.Timeout:
                    logger.error(f"ONVIF timeout for {cam.ip}")
                    notify("Camera timeout", "error")
                    print(f"\n{RED}⏱️ Timeout - camera not responding{RST}")
                    print(f"\n{YLW}🔍 Debug:{RST}")
                    print(f"  {GRN}•{RST} Camera may be overloaded - try again later")
                    print(f"  {GRN}•{RST} Check if {cam.ip} is correct")
                    print(f"  {GRN}•{RST} Try increasing timeout in code")
                    print(f"  {GRN}•{RST} Test with browser: {CYN}http://{cam.ip}:{cam.ports.onvif}{RST}")
                    print(f"\n{YLW}Press any key to continue...{RST}")
                    self._wait_click_or_key()

                except requests.exceptions.HTTPError as e:
                    logger.error(f"ONVIF HTTP error: {e}")
                    status_code = e.response.status_code if hasattr(e, 'response') else 'N/A'

                    if status_code == 401:
                        notify("Authentication failed", "error")
                        print(f"\n{RED}🔐 Authentication failed (HTTP 401){RST}")
                        print(f"\n{YLW}🔍 Debug:{RST}")
                        print(f"  {GRN}•{RST} Current user: {BLU}{cam.user}{RST}")
                        print(f"  {GRN}•{RST} Current pass: {BLU}{'*' * len(cam.password)}{RST}")
                        print(f"  {GRN}•{RST} Try default credentials: admin/admin, admin/12345, admin/888888")
                        print(f"  {GRN}•{RST} Some cameras use empty password")
                    else:
                        notify(f"HTTP error {status_code}", "error")
                        print(f"\n{RED}❌ HTTP error {status_code}{RST}")
                        print(f"\n{YLW}🔍 Debug:{RST}")
                        print(f"  {GRN}•{RST} HTTP Status: {status_code}")
                        if raw_xml:
                            print(f"  {GRN}•{RST} Press {CYN}d{RST} to view RAW response")
                            print(f"\n{YLW}Press 'd' for XML debug, any other key to continue...{RST}")

                            key_pressed = get_key()
                            if key_pressed.lower() == 'd':
                                self._show_debug_xml(raw_xml)
                        else:
                            print(f"\n{YLW}Press any key to continue...{RST}")
                            self._wait_click_or_key()

                except Exception as e:
                    if DEBUG_MODE:
                        logger.exception(f"ONVIF sync error: {e}")
                    else:
                        logger.error(f"ONVIF sync error: {e}")
                    notify(f"ONVIF error: {str(e)[:30]}", "error")
                    print(f"\n{RED}Unexpected error: {type(e).__name__}{RST}")
                    print(f"{RED}{e}{RST}")
                    print(f"\n{YLW}🔍 Debug:{RST}")
                    print(f"  {GRN}•{RST} Run with {CYN}--debug{RST} for full stack trace")
                    print(f"  {GRN}•{RST} Check {CYN}{LOG_FILE}{RST} for details")
                    print(f"  {GRN}•{RST} Try manual RTSP scan with {CYN}'r'{RST}")
                    print(f"  {GRN}•{RST} Verify camera model supports ONVIF")
                    print(f"\n{YLW}Press any key to continue...{RST}")
                    self._wait_click_or_key()

        finally:
            # Przywrócenie oryginalnych ustawień terminala i myszy
            termios.tcsetattr(fd, termios.TCSADRAIN, old_termios)
            self._mouse_on()
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()

    # --------------------------------------------------------------------------
    # MPV LIVE CONTROL SCREEN  (key: x)  - wrapper dla trybu kamer
    # --------------------------------------------------------------------------
    def _mpv_control_screen_cam(self):
        """Unified player TUI for cameras — uses _mpv_control_screen_player in cam_mode."""
        cameras = self.config.cameras
        if not cameras:
            notify("No cameras", "warning")
            return

        idx = self.ui.current_idx
        cam = cameras[idx]
        prof = self.ui.current_profile

        # Safety check: if still not running, show error and exit
        if not prof or not ProcessManager.is_running(prof.pid or 0):
            notify("mpv is not running – cannot open control screen", "error")
            return

        while 0 <= idx < len(cameras):
            cam  = cameras[idx]
            prof = cam.profiles[cam.active_profile] if cam.profiles else None
            if not prof:
                break

            result, _ = _mpv_control_screen_player(
                cam, prof,
                files=cameras,
                current_idx=idx,
                save_as_camera_fn=None,
                config_mgr=self.config_mgr,
                loop_mode=False,
                cam_mode=True,
                all_cameras=cameras,
            )
            if isinstance(result, tuple) and result[0] == "goto":
                idx = result[1]
                self.ui.current_idx = idx
            elif result == "next":
                idx = (idx + 1) % len(cameras)
                self.ui.current_idx = idx
            elif result == "prev":
                idx = (idx - 1) % len(cameras)
                self.ui.current_idx = idx
            else:
                break


    def _play_stream(self):
        cam = self.ui.current_camera
        prof = self.ui.current_profile
        
        if not cam or not prof:
            return
        
        # For SCANNER, skip URI check and directly call Player.play
        if cam.type == CameraType.SCANNER:
            if ProcessManager.is_running(prof.pid):
                notify("Already scanning?", "warning")
                return
            layout = cam.layout or self.config.layout["mpv_default"]
            Player.play(cam, prof, self.config.player_cmd, layout,
                        global_mute=self.config.global_mute)
            return
        
        if ProcessManager.is_running(prof.pid):
            notify("Already playing", "warning")
            return

        prof.error = False
        if not prof.uri and cam.type not in (CameraType.V4L2, CameraType.FILE):
            notify("No URI configured", "error")
            return
        
        layout = cam.layout or self.config.layout["mpv_default"]
        Player.play(cam, prof, self.config.player_cmd, layout,
                    global_mute=self.config.global_mute)
    
    def _show_debug_xml(self, xml: str):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        print(f"{BLU}{'='*57}")
        print(f"DEBUG: RAW XML RESPONSE")
        print(f"{'='*57}{RST}\n")
        
        lines = xml.split('\n')
        for line in lines[:50]:
            print(line)
        
        if len(lines) > 50:
            print(f"\n{YLW}... (response truncated, full log in {LOG_FILE}){RST}")
        
        print(f"\n{BLU}{'='*57}")
        print(f"END DEBUG LOG")
        print(f"{'='*57}{RST}")
        print("\nPress any key to return...")
        self._wait_click_or_key()
    
    def _edit_camera_all(self):
        cam = self.ui.current_camera
        if not cam:
            return

        if cam.type == CameraType.V4L2:
            cam.name = self._edit_param("NAME", cam.name)
            old_dev = cam.device
            cam.device = self._edit_param("DEVICE PATH", cam.device)
            if cam.device != old_dev:
                cam.profiles = []
                notify("Device changed – rescan profiles with (g)", "info")
            return

        if cam.type == CameraType.FILE:
            cam.name = self._edit_param("NAME", cam.name)
            path = self._edit_param("FILE PATH", cam.file_path).strip("'\"")
            if path and os.path.isfile(path):
                cam.file_path = path
                cam.profiles = [CameraProfile(
                    name=os.path.basename(path), token="file_0", uri=path)]
                cam.active_profile = 0
            elif path:
                notify(f"File not found: {path}", "warning")
            loop_ans = self._edit_param("LOOP (y/n)", "y" if cam.file_loop else "n").strip().lower()
            cam.file_loop = loop_ans not in ("n", "no", "0", "false")
            spd = self._edit_param("SPEED (0.25-4.0)", f"{cam.file_speed:.2f}")
            try:
                cam.file_speed = max(0.1, min(4.0, float(spd)))
            except ValueError:
                pass
            start = self._edit_param("START (seconds)", f"{cam.file_start:.1f}")
            try:
                cam.file_start = max(0.0, float(start))
            except ValueError:
                pass
            self.config_mgr.save()
            return

        if cam.type == CameraType.SCANNER:
            cam.name = self._edit_param("NAME", cam.name)
            cam.scan_device = self._edit_param("SCAN DEVICE (empty=default)", cam.scan_device)
            cam.scan_mode = self._edit_param("Mode (gray|color|lineart)", cam.scan_mode)
            dpi = self._edit_param("DPI", str(cam.scan_dpi))
            try: cam.scan_dpi = max(50, min(2400, int(dpi)))
            except: pass
            cam.scan_format = self._edit_param("Format (jpg|png|pdf|tiff)", cam.scan_format)
            q = self._edit_param("Quality (0-100)", str(cam.scan_quality))
            try: cam.scan_quality = max(0, min(100, int(q)))
            except: pass
            cam.scan_resize = self._edit_param("Resize (WxH)", cam.scan_resize)
            cam.scan_desc = self._edit_param("Description (for filename)", cam.scan_desc)
            cam.scan_dest = self._edit_param("Destination dir", str(cam.scan_dest))
            cam.scan_viewer = self._edit_param("Viewer (mpv|gwenview|xdg-open|eog|feh)", cam.scan_viewer)
            self.config_mgr.save()
            return

        old_ip = cam.ip

        cam.name = self._edit_param("NAME", cam.name)
        cam.ip = self._edit_param("IP", cam.ip, validate_ip)

        if cam.type == CameraType.DVRIP:
            port_label = "DVRIP PORT"
            current_port = str(cam.ports.dvrip)
        elif cam.type == CameraType.RTSP_ONLY:
            port_label = "RTSP PORT"
            current_port = str(cam.ports.rtsp)
        else:
            port_label = "ONVIF PORT"
            current_port = str(cam.ports.onvif)

        new_port = self._edit_param(port_label, current_port, validate_port)
        try:
            new_port_int = int(new_port)
        except ValueError:
            notify("Invalid port format!", "error")
            return
        else:
            if cam.type == CameraType.DVRIP:
                cam.ports.dvrip = new_port_int
            elif cam.type == CameraType.RTSP_ONLY:
                cam.ports.rtsp = new_port_int
            else:
                cam.ports.onvif = new_port_int

        cam.user = self._edit_param("USER", cam.user)
        cam.password = self._edit_param("PASS", cam.password)

        if cam.ip != old_ip:
            cam.mac = "UNKNOWN"
            notify("IP changed - MAC reset", "info")

        self._sync_network(cam)
    
    def _edit_camera_ip(self):
        cam = self.ui.current_camera
        if not cam:
            return

        if cam.type == CameraType.V4L2:
            notify("V4L2: no IP/port – use (e) to edit device path", "warning")
            return
        if cam.type == CameraType.FILE:
            notify("FILE: use (e) to edit file path and settings", "warning")
            return
        if cam.type == CameraType.SCANNER:
            notify("SCANNER: use (e) to edit scanner settings", "warning")
            return
        
        old_ip = cam.ip
        cam.ip = self._edit_param("IP", cam.ip, validate_ip)
        
        if cam.type == CameraType.DVRIP:
            port_label = "DVRIP PORT"
            current_port = str(cam.ports.dvrip)
        elif cam.type == CameraType.RTSP_ONLY:
            port_label = "RTSP PORT"
            current_port = str(cam.ports.rtsp)
        else:
            port_label = "ONVIF PORT"
            current_port = str(cam.ports.onvif)
        
        new_port = self._edit_param(port_label, current_port, validate_port)
        try:
            new_port_int = int(new_port)
        except ValueError:
            notify("Invalid port format!", "error")
            return
        else:
            if cam.type == CameraType.DVRIP:
                cam.ports.dvrip = new_port_int
            elif cam.type == CameraType.RTSP_ONLY:
                cam.ports.rtsp = new_port_int
            else:
                cam.ports.onvif = new_port_int
        
        if cam.ip != old_ip:
            cam.mac = "UNKNOWN"
            notify("IP changed - MAC reset", "info")
        
        self._sync_network(cam)
    
    def _uri_menu(self):
        cam  = self.ui.current_camera
        prof = self.ui.current_profile
        if not cam:
            return

        uri = prof.uri if prof else ""

        choice = select_menu(
            ["✏  Edit URI",
             "🔍 Scan common paths",
             "📋 Copy to clipboard",
             "🎬 Edit player command",
             "✖  Cancel"],
            title="📡 RTSP Configuration",
            W=57
        )

        if choice == 0:
            if not cam.ip:
                notify("No IP set for this camera", "error"); return
            scanner = RTSPScanner(cam)
            rtsp_port = cam.ports.rtsp
            base_url = f"rtsp://{cam.user}:{cam.password}@{cam.ip}:{rtsp_port}"
            profiles = scanner._manual_entry(base_url)
            if profiles:
                cam.profiles = profiles
                cam.active_profile = 0
                cam.type = CameraType.RTSP_ONLY
                self.config_mgr.save()

        elif choice == 1:
            if not cam.ip:
                notify("No IP set for this camera", "error"); return
            scanner = RTSPScanner(cam)
            profiles = scanner.scan()
            if profiles:
                cam.profiles = profiles
                cam.active_profile = 0
                self.config_mgr.save()

        elif choice == 2:
            if not uri:
                notify("No URI to copy", "error"); return
            copied = False
            for tool in (['xclip', '-selection', 'clipboard'],
                         ['xsel', '--clipboard', '--input'],
                         ['wl-copy']):
                try:
                    p = subprocess.Popen(tool, stdin=subprocess.PIPE,
                                         stdout=subprocess.DEVNULL,
                                         stderr=subprocess.DEVNULL)
                    p.communicate(uri.encode())
                    if p.returncode == 0:
                        copied = True; break
                except FileNotFoundError:
                    continue
            notify("Copied to clipboard!" if copied else "xclip/xsel/wl-copy not found",
                   "info" if copied else "error")

        elif choice == 3:
            self.config.player_cmd = self._edit_param("PLAYER CMD", self.config.player_cmd)

    
    def _change_camera_type(self):
        cam = self.ui.current_camera
        if not cam:
            return
        
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        W = 57
        
        type_order = [CameraType.AUTO, CameraType.ONVIF, CameraType.DVRIP,
                      CameraType.RTSP_ONLY, CameraType.V4L2, CameraType.FILE, CameraType.SCANNER]
        cur = type_order.index(cam.type) if cam.type in type_order else 0

        items = [
            "🔍 AUTO      – Auto-detect",
            "📷 ONVIF     – Force ONVIF PTZ",
            "🔧  DVRIP     – Force XM/iCSee PTZ",
            "📡 RTSP_ONLY – Stream only",
            "🎥 V4L2      – Local USB device",
            "📁  FILE      – Local video file",
            "🖨️  SCANNER   – Sane scanner",
        ]

        idx = select_menu(items, selected=cur,
                          title=f"🔧 Camera Type – {cam.name}  [{cam.type.value}]")

        if idx == -1:
            return

        changed = True
        if idx == 0:
            new_type, port = CameraDetector.detect(cam, show_progress=True)
            cam.type = new_type
            if port:
                if new_type == CameraType.DVRIP:
                    cam.ports.dvrip = port
                else:
                    cam.ports.onvif = port
            notify(f"Detected: {new_type.value}", "info")
        elif idx == 1:
            cam.type = CameraType.ONVIF
        elif idx == 2:
            cam.type = CameraType.DVRIP
        elif idx == 3:
            cam.type = CameraType.RTSP_ONLY
        elif idx == 4:
            cam.type = CameraType.V4L2
            dev = rlinput(f"{CYN}Device path:{RST} ", cam.device or "/dev/video0").strip()
            if dev.startswith("/dev/video"):
                cam.device = dev
                cam.ip = "localhost"
                cam.mac = "V4L2"
                cam.ports = CameraPorts()
                cam.profiles = []
        elif idx == 5:
            cam.type = CameraType.FILE
            cam.ip   = "localhost"
            cam.mac  = "FILE"
            cam.ports = CameraPorts()
            path = rlinput(f"{CYN}Path to video file:{RST} ", cam.file_path or "").strip().strip("'\"")
            if path and os.path.isfile(path):
                cam.file_path = path
                if cam.name in ("New Camera", ""):
                    cam.name = os.path.splitext(os.path.basename(path))[0][:30]
            elif path:
                notify(f"File not found: {path}", "warning")
            loop_ans = rlinput(f"{CYN}Loop (y/n):{RST} ", "y" if cam.file_loop else "n").strip().lower()
            cam.file_loop = loop_ans not in ("n", "no", "0", "false")
            spd = rlinput(f"{CYN}Playback speed (0.25–4.0):{RST} ", f"{cam.file_speed:.2f}").strip()
            try:
                cam.file_speed = max(0.1, min(4.0, float(spd)))
            except ValueError:
                pass
            start = rlinput(f"{CYN}Start at second:{RST} ", f"{cam.file_start:.1f}").strip()
            try:
                cam.file_start = max(0.0, float(start))
            except ValueError:
                pass
            cam.profiles = [CameraProfile(
                name=os.path.basename(cam.file_path or "file"),
                token="file_0", uri=cam.file_path)]
            cam.active_profile = 0
        elif idx == 6:
            cam.type = CameraType.SCANNER
            cam.ip = ""
            cam.mac = "SCANNER"
            cam.ports = CameraPorts()
            cam.profiles = [CameraProfile(name="scan", token="", res="A4")]
            if not cam.scan_device:
                cam.scan_device = ""
            if not cam.scan_dest:
                cam.scan_dest = SCAN_DIR
        else:
            changed = False

        if changed:
            self.config_mgr.save()
            notify(f"Type set to: {cam.type.value}", "info")
            time.sleep(0.8)
    
    def _save_preset(self):
        cam = self.ui.current_camera
        prof = self.ui.current_profile
        
        if not cam or prof.token == "None":
            notify("No active profile!", "error")
            return
        
        if cam.type != CameraType.ONVIF:
            notify("Presets only for ONVIF cameras", "warning")
            return
        
        name = self._edit_param("PRESET NAME", f"Preset_{len(cam.presets) + 1}")
        
        client = ONVIFClient(cam)
        pos = client.get_position(prof.token)
        
        if pos:
            cam.presets[name] = pos
            notify(f"Preset '{name}' saved!", "info")
        else:
            notify("Failed to read position!", "error")
    
    def _recall_preset(self):
        cam = self.ui.current_camera
        prof = self.ui.current_profile
        
        if not cam or prof.token == "None":
            notify("No active profile!", "error")
            return
        
        if not cam.presets:
            notify("No presets saved!", "warning")
            return
        
        if cam.type != CameraType.ONVIF:
            notify("Presets only for ONVIF cameras", "warning")
            return
        
        names = list(cam.presets.keys())
        items = []
        for name in names:
            pos = cam.presets[name]
            items.append(f"📍 {name:<20} P:{pos.pan:+.2f} T:{pos.tilt:+.2f} Z:{pos.zoom:.2f}")
        items.append("🗑  Delete a preset...")

        idx = select_menu(items, selected=0,
                          title=f"📌 Recall Preset – {cam.name}")

        if idx == -1:
            return

        if idx == len(names):
            del_items = [f"❌ {n}" for n in names] + ["✖  Cancel"]
            didx = select_menu(del_items, selected=0, title="🗑  Delete Preset")
            if didx != -1 and 0 <= didx < len(names):
                del cam.presets[names[didx]]
                self.config_mgr.save()
                notify(f"Deleted '{names[didx]}'", "info")
            return

        name = names[idx]
        pos  = cam.presets[name]
        client = ONVIFClient(cam)
        if client.absolute_move(prof.token, pos):
            notify(f"Recalled '{name}'", "info")
        else:
            notify("Recall failed!", "error")
    
    def _move_timed(self, x: float, y: float, z: float = 0.0, label: str = "C"):
        if not isinstance(x, (int, float)):
            logger.error(f"x is not a number: {x} (type: {type(x)})")
            x = 0.0
        if not isinstance(y, (int, float)):
            logger.error(f"y is not a number: {y} (type: {type(y)})")
            y = 0.0
        if not isinstance(z, (int, float)):
            logger.error(f"z is not a number: {z} (type: {type(z)})")
            z = 0.0
        
        x = float(x)
        y = float(y)
        z = float(z)
        
        cam = self.ui.current_camera
        prof = self.ui.current_profile
        
        if not cam or not prof or prof.token == "None":
            notify("No active profile!", "error")
            self.ui.draw(); return
        
        speed = cam.speed
        duration = cam.duration
        
        logger.debug(f"_move_timed: x={x}, y={y}, z={z}, label={label}, speed={speed}, duration={duration}")
        
        if cam.type == CameraType.AUTO:
            notify("TYPE=AUTO - use 'g' Sync or '?' to set", "warning")
            self.ui.draw(); return
        elif cam.type == CameraType.RTSP_ONLY:
            notify("No PTZ - RTSP only camera", "warning")
            self.ui.draw(); return
        elif cam.type == CameraType.V4L2:
            notify("V4L2 PTZ not supported", "warning")
            self.ui.draw(); return
        elif cam.type == CameraType.FILE:
            notify("FILE: PTZ not supported", "warning")
            self.ui.draw(); return
        elif cam.type == CameraType.SCANNER:
            notify("SCANNER: no PTZ", "warning")
            self.ui.draw(); return
        
        if cam.type == CameraType.DVRIP:
            if prof.channel != 0:
                notify(f"PTZ only for Ch 0 (current: Ch {prof.channel})", "warning")
                return
            
            ptz_speed = int(speed * 8)
            steps = 10
            client = None

            # Start movement only once
            client = DVRIPClient(cam)
            client.move(label, ptz_speed, duration)
            
            try:
                for i in range(steps + 1):
                    self.ui.set_active_dir(label)
                    self.ui.set_progress(i / steps)
                    self.ui.draw()

                    if select.select([sys.stdin], [], [], 0)[0]:
                        ch = sys.stdin.read(1)
                        if ch == ' ':
                            logger.debug("Movement interrupted by space")
                            if client:
                                client.move("C", 0, 0)
                            break

                    time.sleep(duration / steps)
            finally:
                if client:
                    client.close()
            
            self.ui.set_active_dir(None)
            self.ui.set_progress(0)
            self.ui.draw()
            return
        
        if cam.type == CameraType.ONVIF:
            client = ONVIFClient(cam)
            
            pan = x * speed
            tilt = y * speed
            zoom = z * speed
            
            logger.debug(f"ONVIF move: pan={pan:.2f}, tilt={tilt:.2f}, zoom={zoom:.2f}")
            
            try:
                client.move_continuous(prof.token, pan, tilt, zoom)
                
                steps = 10
                for i in range(steps + 1):
                    self.ui.set_active_dir(label)
                    self.ui.set_progress(i / steps)
                    self.ui.draw()
                    
                    if select.select([sys.stdin], [], [], 0)[0]:
                        if sys.stdin.read(1) == ' ':
                            logger.debug("Movement interrupted by space")
                            break
                    
                    time.sleep(duration / steps)
            finally:
                client.stop(prof.token)
            
            self.ui.set_active_dir(None)
            self.ui.set_progress(0)
            self.ui.draw()

# --------------------------------------------------------------------------
# Scanner configuration TUI (x) start
# --------------------------------------------------------------------------
    def _scanner_control_screen(self):
        """Scanner configuration TUI – aligned columns, ESC to quit."""
        cam = self.ui.current_camera
        if not cam or cam.type != CameraType.SCANNER:
            notify("No scanner selected", "warning")
            return

        # --- Available options ---
        MODES   = ["gray", "color", "lineart"]
        FORMATS = ["jpg", "png", "pdf", "tiff"]
        VIEWERS = ["mpv", "gwenview", "xdg-open", "eog", "feh"]
        DPIS    = [75, 100, 150, 200, 300, 600, 1200]

        AREAS = {
            "A4"     : "0:0:215:297",
            "A5"     : "0:0:148:210",
            "Letter" : "0:0:216:279",
            "Custom" : cam.scan_area,
        }
        RESIZES = {
            "A4@150": "1240x1754",
            "A4@300": "2480x3508",
            "A4@100": "827x1169",
            "A4@75" : "620x877",
            "Custom": cam.scan_resize,
        }

        # Number padding: 0 = none (0d), 2 = two digits (2d), 3 = three digits (3d)
        num_padding = 3
        date_format = 0   # 0 = YYYY-MM-DD, 1 = DD-MM-YYYY
        override_num = None

        def _cycled(lst, val):
            try:
                return lst[(lst.index(val) + 1) % len(lst)]
            except ValueError:
                return lst[0]

        def _get_next_number():
            if override_num is not None:
                return override_num
            import glob as _gl
            today = datetime.date.today().strftime("%Y-%m-%d")
            desc_part = f"_{cam.scan_desc}" if cam.scan_desc else ""
            pattern = f"{today}{desc_part}_*.{cam.scan_format}"
            existing = _gl.glob(os.path.join(cam.scan_dest, pattern))
            nums = []
            for f in existing:
                bn = os.path.basename(f)
                try:
                    n = int(bn.split("_")[-1].split(".")[0])
                    nums.append(n)
                except Exception:
                    pass
            return max(nums, default=0) + 1

        def _format_number(num):
            if num_padding == 0:
                return str(num)
            elif num_padding == 2:
                return f"{num:02d}"
            else:
                return f"{num:03d}"

        def _draw():
            sys.stdout.write('\033[2J\033[H')
            sys.stdout.flush()
            W = 76
            def line(txt=""):
                print(f"║ {pad(txt, W-2)} ║")

            # Header – fixed length to ensure right border alignment
            header = f"{CYN} 🖨  Scanner: {YLW}{cam.name}{RST}{CYN}   device: {DIM}{cam.scan_device or '(default)'}{RST}"
            header_visual_len = ansilen(header) + 1
            if header_visual_len < W:
                header += ' ' * (W - header_visual_len)
            print(f"╔{'═'*W}╗")
            line(header)
            print(f"╠{'═'*W}╣")

            def _pad_field(txt, width):
                cur = ansilen(txt)
                if cur < width:
                    txt += ' ' * (width - cur)
                return txt

            c1w = (W - 2 - 4) // 3
            c2w = (W - 2 - 4) // 3
            c3w =  W - 2 - 4 - c1w - c2w

            def row3col(a, b, c):
                return _pad_field(a, c1w) + "  " + _pad_field(b, c2w) + "  " + _pad_field(c, c3w)

            row1 = row3col(
                f" {YLW}(m){RST} Mode  : {GRN}{cam.scan_mode}{RST}",
                f" {YLW}(d){RST} DPI   : {GRN}{cam.scan_dpi}{RST}",
                f" {YLW}(a){RST} Area  : {GRN}{cam.scan_area}{RST}",
            )
            row2 = row3col(
                f" {YLW}(f){RST} Format: {GRN}{cam.scan_format}{RST}",
                f" {YLW}(r){RST} Resize: {GRN}{cam.scan_resize}{RST}",
                f" {YLW}(c){RST} Compression: {GRN}{cam.scan_quality}{RST}",
            )
            today = datetime.date.today()
            date_str = today.strftime("%Y-%m-%d") if date_format == 0 else today.strftime("%d-%m-%Y")
            next_num = _get_next_number()
            num_str = _format_number(next_num)
            pad_indicator = {0:"0d", 2:"2d", 3:"3d"}[num_padding]
            row3 = row3col(
                f" {YLW}(h){RST} Date  : {GRN}{date_str}{RST}",
                f" {YLW}(n){RST} Desc  : {GRN}{cam.scan_desc or '(none)'}{RST}",
                f" {YLW}(x){RST} Number: {GRN}{num_str} [{pad_indicator}](y){RST}",
            )
            dest_str = str(cam.scan_dest)
            row4 = f" {YLW}(v){RST} Viewer: {GRN}{cam.scan_viewer:<10}{RST}" + \
                   f"   {YLW}(t){RST} Dest  : {GRN}{dest_str}{RST}"

            for r in (row1, row2, row3, row4):
                cur_len = ansilen(r)
                if cur_len < W-2:
                    r += ' ' * (W-2 - cur_len)
                elif cur_len > W-2:
                    r = r[:W-2]
                line(r)

            print(f"╠{'═'*W}╣")
            ver_esc = f"{DIM}v{VERSION}{RST} {YLW}(?){RST} Help {YLW}(ESC){RST} Quit"
            scan_btn = f" {YLW}(p){RST} Scan"
            footer_row = scan_btn + ' ' * (W-2 - ansilen(scan_btn) - ansilen(ver_esc)) + ver_esc
            line(footer_row)
            print(f"╚{'═'*W}╝")

        sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
        sys.stdout.flush()
        running = True
        try:
            while running:
              _draw()
              key = get_key()
              _mk = key  # domyślnie: klawisz z klawiatury

              if _mk == 'm':
                  cam.scan_mode = _cycled(MODES, cam.scan_mode)
                  self.config_mgr.save()
              elif _mk == 'd':
                  try:
                      idx = DPIS.index(cam.scan_dpi)
                  except ValueError:
                      idx = 4
                  cam.scan_dpi = DPIS[(idx + 1) % len(DPIS)]
                  self.config_mgr.save()
              elif _mk == 'f':
                  cam.scan_format = _cycled(FORMATS, cam.scan_format)
                  self.config_mgr.save()
              elif _mk == 'a':
                  items = list(AREAS.keys())
                  ai = select_menu(items, selected=0, title="Scan area")
                  if ai >= 0:
                      key_ = items[ai]
                      if key_ == "Custom":
                          new_area = self._edit_param("Area (x:y:w:h mm)", cam.scan_area)
                          if new_area:
                              cam.scan_area = new_area
                      else:
                          cam.scan_area = AREAS[key_]
                      self.config_mgr.save()
              elif _mk == 'r':
                  items = list(RESIZES.keys())
                  ri = select_menu(items, selected=0, title="Output resize")
                  if ri >= 0:
                      key_ = items[ri]
                      if key_ == "Custom":
                          new_resize = self._edit_param("Resize (WxH)", cam.scan_resize)
                          if new_resize:
                              cam.scan_resize = new_resize
                      else:
                          cam.scan_resize = RESIZES[key_]
                      self.config_mgr.save()
              elif _mk == 'c':
                  val = self._edit_param("Compression (0-100)", str(cam.scan_quality))
                  try:
                      cam.scan_quality = max(0, min(100, int(val)))
                      self.config_mgr.save()
                  except ValueError:
                      pass
              elif _mk == 'v':
                  cam.scan_viewer = _cycled(VIEWERS, cam.scan_viewer)
                  self.config_mgr.save()
              elif _mk == 't':
                  new_dest = self._edit_param("Destination directory", str(cam.scan_dest))
                  if new_dest:
                      cam.scan_dest = new_dest
                      self.config_mgr.save()
              elif _mk == 'n':
                  new_desc = self._edit_param("Description (added to filename)", cam.scan_desc)
                  if new_desc is not None:
                      cam.scan_desc = new_desc
                      self.config_mgr.save()
              elif _mk == 'h':
                  date_format = 1 - date_format
              elif _mk == 'x':
                  if num_padding == 0:
                      num_padding = 2
                  elif num_padding == 2:
                      num_padding = 3
                  else:
                      num_padding = 0
                  self.config_mgr.save()
              elif _mk == 'y':
                  val = self._edit_param("Next file number (1-999)", str(_get_next_number()))
                  try:
                      num = int(val)
                      if 1 <= num <= 999:
                          override_num = num
                      else:
                          notify("Number must be 1-999", "warning")
                  except ValueError:
                      pass

              elif _mk == 'p':
                  self.config_mgr.save()
                  _draw()

                  fd = sys.stdin.fileno()
                  old_termios = termios.tcgetattr(fd)

                  # Disable mouse tracking during scanning
                  sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
                  sys.stdout.flush()

                  term_height = shutil.get_terminal_size().lines
                  sys.stdout.write(f'\033[{term_height-1};1H\033[2K')
                  sys.stdout.write("🖨️ Preparing scan...")
                  sys.stdout.flush()

                  scan_done = threading.Event()
                  scan_ok = [False]

                  def update_progress(pct):
                      # Called from the scanner thread – safe to write to terminal
                      term_h = shutil.get_terminal_size().lines
                      sys.stdout.write(f'\033[{term_h-1};1H\033[2K')
                      bar_len = 20
                      filled = int(pct / 100 * bar_len)
                      bar = '█' * filled + '░' * (bar_len - filled)
                      sys.stdout.write(f"🖨️ Scanning... {pct:3d}% [{bar}]")
                      sys.stdout.flush()

                  def scan_task():
                      try:
                          ok = Player._play_scanner(cam, progress_callback=update_progress)
                          scan_ok[0] = ok
                      finally:
                          scan_done.set()

                  threading.Thread(target=scan_task, daemon=True).start()

                  # Wait for scan to complete, ignoring all input
                  while not scan_done.is_set():
                      time.sleep(0.05)

                  # Clear progress line
                  term_h = shutil.get_terminal_size().lines
                  sys.stdout.write(f'\033[{term_h-1};1H\033[2K')
                  sys.stdout.flush()

                  # Restore terminal state and redraw interface
                  sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
                  sys.stdout.flush()
                  termios.tcsetattr(fd, termios.TCSADRAIN, old_termios)

                  sys.stdout.write('\033[2J\033[H')
                  sys.stdout.flush()
                  _draw()

                  if scan_ok[0]:
                      notify("Scan saved successfully", "info")
                  else:
                      notify("Scan failed", "error")

              elif _mk == '?':
                  self._show_scanner_help()
                  _draw()
              elif key in ('q', 'Q'):
                  running = False
              elif isinstance(key, MouseEvent) and not key.release:
                  r, c = key.row, key.col
                  _C1 = c <= 26; _C2 = 27 <= c <= 52; _C3 = c >= 53
                  _mk = None  # mapped key
                  if r == 4:
                      if _C1: _mk = 'm'
                      elif _C2: _mk = 'd'
                      elif _C3: _mk = 'a'
                  elif r == 5:
                      if _C1: _mk = 'f'
                      elif _C2: _mk = 'r'
                      elif _C3: _mk = 'c'
                  elif r == 6:
                      if _C1: _mk = 'h'
                      elif _C2: _mk = 'n'
                      elif _C3: _mk = 'x'
                  elif r == 7:
                      _mk = 'v' if c <= 40 else 't'
                  elif r == 9:
                      if c <= 10: _mk = 'p'
                      elif 11 <= c <= 20: _mk = '?'
                      else: running = False; continue
              elif _mk == Key.ESC:
                  running = False
        finally:
            sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
            sys.stdout.flush()

# --------------------------------------------------------------------------
# Scanner configuration TUI (x) end
# --------------------------------------------------------------------------

    def _discover_cameras(self):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        W = 57
        
        has_nmap = bool(shutil.which('nmap'))
        nmap_note = "" if has_nmap else f" {RED}(nmap not installed){RST}"
        
        nmap_label = f"🔍 Scan Network - nmap (thorough){nmap_note}"
        items = [
            "📡 Scan Network - ping sweep (fast)",
            "🎥 Scan V4L2 Devices (USB/local)",
            nmap_label,
            "📂 Add File Camera (local video file)",
            "🖨️ Add Scanner (SANE)",
            "✖  Cancel",
        ]
        idx = select_menu(items, selected=0, title="📷 Camera Discovery")

        if idx == -1:
            return
        elif idx == 0:
            self._discover_network()
        elif idx == 1:
            self._discover_v4l2()
        elif idx == 2:
            if has_nmap:
                self._discover_network_nmap()
            else:
                notify("nmap not installed! Install: sudo apt install nmap", "error")
                time.sleep(2)
        elif idx == 3:
            self._add_file_camera()
        elif idx == 4:
            self._add_scanner_camera()
    

    @staticmethod
    def _discover_scanners_usb() -> list:
        """Wykryj skanery SANE z VID:PID przez scanimage -f + udevadm.
        Zwraca listę słowników:
          {vendor, model, sane_type, device, vidpid, display}
        device = aktualny device string (zmienia się przy hot-plug)
        vidpid = VID:PID np. "04a9:220e" (stały)
        """
        import re as _re
        found = []

        if not shutil.which('scanimage'):
            return found

        # --- Krok 1: scanimage -f — strukturalne pola ---
        try:
            r = subprocess.run(
                ['scanimage', '-f', '%v|%m|%t|%d\n'],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                universal_newlines=True, timeout=15
            )
            lines = r.stdout.strip().splitlines()
        except Exception as e:
            logger.warning(f"scanimage -f failed: {e}")
            # Fallback do -L
            try:
                r = subprocess.run(['scanimage', '-L'],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    universal_newlines=True, timeout=15)
                lines = []
                for ln in r.stdout.splitlines():
                    m = _re.match(r"device `([^']+)' is (.+)", ln)
                    if m:
                        d, desc = m.group(1), m.group(2)
                        lines.append(f"?|{desc}|scanner|{d}")
            except Exception:
                return found

        for line in lines:
            parts = line.strip().split('|')
            if len(parts) < 4:
                continue
            vendor, model, sane_type, device = (p.strip() for p in parts[:4])
            if not device:
                continue

            # --- Krok 2: wyciągnij VID:PID przez udevadm ---
            vidpid = ""
            # device string: "backend:libusb:BUS:DEV" np. plustek:libusb:001:006
            m = _re.search(r'libusb:(\d+):(\d+)', device)
            if m:
                bus, dev = m.group(1).zfill(3), m.group(2).zfill(3)
                usb_path = f"/dev/bus/usb/{bus}/{dev}"
                try:
                    ud = subprocess.run(
                        ['udevadm', 'info', '--query=property', '--name', usb_path],
                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                        universal_newlines=True, timeout=3
                    )
                    props = dict(ln.split('=', 1) for ln in ud.stdout.splitlines() if '=' in ln)
                    vid = props.get('ID_VENDOR_ID', '')
                    pid = props.get('ID_MODEL_ID', '')
                    if vid and pid:
                        vidpid = f"{vid}:{pid}"
                        # Uzupełnij vendor/model z udev jeśli SANE nie podał
                        if vendor in ('?', ''):
                            vendor = props.get('ID_VENDOR_ENC', props.get('ID_VENDOR', vendor)).replace('\\x20', ' ')
                        if model in ('?', ''):
                            model  = props.get('ID_MODEL_ENC',  props.get('ID_MODEL',  model )).replace('\\x20', ' ')
                except Exception as e:
                    logger.debug(f"udevadm for {usb_path}: {e}")

            # Wyczyść prefix "a " i suffix "flatbed scanner" z typu
            import re as _re2
            clean_type = _re2.sub(r'^(a|an)\s+', '', sane_type, flags=_re2.IGNORECASE)
            clean_type = _re2.sub(r'\s+(flatbed|scanner).*$', '', clean_type, flags=_re2.IGNORECASE)

            display = f"{vendor} {model}".strip() or device
            found.append({
                'vendor':    vendor,
                'model':     model,
                'sane_type': clean_type,
                'device':    device,
                'vidpid':    vidpid,
                'display':   display,
            })
            logger.info(f"Scanner found: {display}  device={device}  VID:PID={vidpid or 'unknown'}")

        return found

    @staticmethod
    def _resolve_scanner_device(vidpid: str) -> str:
        """Znajdź aktualny device string SANE dla danego VID:PID.
        Wywołuje scanimage -f przy każdym skanie — adresuje hot-plug.
        Zwraca device string lub "" jeśli nie znaleziono.
        """
        if not vidpid:
            return ""
        scanners = PTZMasterApp._discover_scanners_usb()
        for s in scanners:
            if s['vidpid'] == vidpid:
                return s['device']
        return ""

    def _add_scanner_camera(self):
        """Wykryj skanery SANE z VID:PID (stały identyfikator USB)."""
        print_header("SCANNER DISCOVERY")
        if not shutil.which('scanimage'):
            notify("scanimage not found! Install: sane-utils", "error")
            print(f"  {RED}scanimage not found{RST}")
            print(f"  {DIM}sudo apt install sane-utils{RST}")
            time.sleep(3)
            return

        print(f"  {CYN}Searching for scanners (scanimage -f)...{RST}")
        scanners = PTZMasterApp._discover_scanners_usb()

        if not scanners:
            print(f"  {YLW}No scanners found.{RST}")

        for s in scanners:
            vidpid_str = f"  {DIM}VID:PID={s['vidpid']}{RST}" if s['vidpid'] else ""
            print(f"  {GRN}✓{RST} {s['display']:<30}  {DIM}{s['device']}{RST}{vidpid_str}")

        items = []
        for s in scanners:
            disp = s['display'][:26]
            vp   = f" [{s['vidpid']}]" if s['vidpid'] else ""
            items.append(f" [SCN] {disp:<26}{DIM}{vp}{RST}")
        items += [" [ + ] Add manually (enter VID:PID)", " [ x ] Cancel"]

        idx = select_menu(items, selected=0, title="Add Scanner (SANE)")
        if idx == -1 or idx == len(items) - 1:
            return

        if idx == len(items) - 2:
            vidpid_str  = self._edit_param("USB VID:PID (e.g. 04a9:220e)", "")
            device_str  = self._edit_param("SANE device (leave empty = auto)", "")
            name        = self._edit_param("Name", "Scanner")
        else:
            s           = scanners[idx]
            vidpid_str  = s['vidpid']
            device_str  = s['device']
            default_name = s['display'][:20].replace(" ", "_").replace("/", "-")
            name = self._edit_param("Name", default_name)

        if vidpid_str and any(c.type == CameraType.SCANNER and c.scan_vidpid == vidpid_str
               for c in self.config.cameras):
            notify("Scanner VID:PID already in list", "warning")
            return

        cam = Camera(name=name, cam_type=CameraType.SCANNER, ip="", mac="UNKNOWN")
        cam.scan_vidpid = vidpid_str
        cam.scan_device = device_str
        cam.scan_dest   = SCAN_DIR
        cam.profiles    = [CameraProfile(name="scan", token="", res="A4")]
        self.config.cameras.append(cam)
        self.config_mgr.save()
        notify(f"Added scanner: {name}  VID:PID={vidpid_str or 'unknown'}", "info")
        logger.info(f"Added scanner: {name} vidpid={vidpid_str} device={device_str}")

    def _show_scanner_help(self):
        """Display scanner help with right edge fixed at column 78."""
        mouse_off()
        fd = sys.stdin.fileno()
        old_term = termios.tcgetattr(fd)

        import signal
        resized = [False]
        def handle_winch(sig, frame):
            resized[0] = True

        old_winch = None # Inicjalizujemy pustą zmienną

        try:
            # Przypisujemy sygnał dopiero wewnątrz bloku try
            old_winch = signal.signal(signal.SIGWINCH, handle_winch)

            tty.setraw(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()

            RIGHT_EDGE = 78
            footer_label = f"v{VERSION}  (ESC) Quit "
            footer_len = len(footer_label)

            while True:
                resized[0] = False
                total_lines = 0
                # Czyścimy ekran i ustawiamy kursor na 1,1
                sys.stdout.write('\033[2J\033[H')

                def line(content=""):
                    nonlocal total_lines
                    # Dodajemy \r\n na końcu dla trybu RAW
                    sys.stdout.write(f"{YLW}║{RST} {content}\033[{RIGHT_EDGE}G{YLW}║{RST}\r\n")
                    total_lines += 1

                def sep():
                    nonlocal total_lines
                    sys.stdout.write(f"{YLW}╠{'═'*(RIGHT_EDGE-2)}╣{RST}\r\n")
                    total_lines += 1

                # 1. Górna ramka
                sys.stdout.write(f"{YLW}╔{'═'*(RIGHT_EDGE-2)}╗{RST}\r\n")
                total_lines += 1

                # 2. Nagłówek
                title = "📐 SCANNER GEOMETRY & 🖼️ IMAGE WORKFLOW REFERENCE"
                line(f"{BLU}{title.center(75)}{RST}")
                sep()

                # 3. Treść sekcji
                line(f"{WHT}STANDARD PAPER SIZES (Width x Height in mm):{RST}")
                line("   • A4            : 210.0 x 297.0 (International)")
                line("   • Letter (US)   : 215.9 x 279.4 (8.5 x 11 in)")
                line("   • Legal (US)    : 215.9 x 355.6 (8.5 x 14 in)")
                line("   • Ledger (US)   : 279.4 x 431.8 (11 x 17 in)")
                line(f"   {DIM}(Scanner width is typically max 215-216 mm){RST}")
                line()

                line(f"{WHT}DPI TO PIXELS (For A4 @ 210x297 mm):{RST}")
                line("   • 600 DPI : 4960 x 7016 (Master/Archive)")
                line("   • 300 DPI : 2480 x 3508 (OCR/Translation)")
                line("   • 150 DPI : 1240 x 1754 (Web/Screen)")
                line("   • 100 DPI :  827 x 1169 (Fast preview)")
                line("   •  75 DPI :  620 x  877 (Thumbnail)")
                line()

                line(f"{WHT}⚙️  RECOMMENDED WORKFLOW (High Quality):{RST}")
                line("   1. Scan → TIFF @ 600 DPI (Raw data)")
                line("   2. Save to /tmp/ (Use RAM disk for speed)")
                line("   3. Process with ImageMagick (convert):")
                line(f"      {DIM}-sharpen 0x1.0 -resize 2480x3508 -quality 85%{RST}")
                line("   4. Send to Google Translate / Tesseract OCR")
                line()

                line(f"{WHT}🌐 ISO 639-1 LANGUAGE CODES (for OCR/Translation):{RST}")
                line(f"   {GRN}pl{RST} Polish    {GRN}en{RST} English   {GRN}de{RST} German    {GRN}fr{RST} French")
                line(f"   {GRN}es{RST} Spanish   {GRN}it{RST} Italian   {GRN}uk{RST} Ukrainian {GRN}ru{RST} Russian")
                line()

                sep()

                # 4. Stopka (interaktywna)
                footer_content = f"{CYN}v{VERSION}{RST}  {YLW}(ESC){RST} Quit "
                sys.stdout.write(f"{YLW}║{RST}")
                # Pozycjonujemy tekst stopki do prawej krawędzi
                sys.stdout.write(f"\033[{RIGHT_EDGE - footer_len - 1}G")
                sys.stdout.write(f"{footer_content}\033[{RIGHT_EDGE}G{YLW}║{RST}\r\n")
                total_lines += 1

                # 5. Dolna ramka
                sys.stdout.write(f"{YLW}╚{'═'*(RIGHT_EDGE-2)}╝{RST}\r\n")
                total_lines += 1

                sys.stdout.flush()

                # Indeks rzędu stopki dla obsługi myszy
                footer_row = total_lines - 1 # W setraw() rzędy w MouseEvent mogą być od 1 lub 0

                # Pętla oczekiwania na klawisz lub zmianę rozmiaru
                while not resized[0]:
                    key = get_key(timeout=0.2)
                    if key == Key.TIMEOUT:
                        continue
                    if key in (Key.ESC, 'q', 'Q'):
                        return

                    # Obsługa myszy
                    if isinstance(key, MouseEvent) and not key.release:
                        # Sprawdzamy czy kliknięto w rzędzie stopki
                        if key.row == footer_row:
                            btn_start = RIGHT_EDGE - footer_len
                            if btn_start <= key.col <= RIGHT_EDGE:
                                return

        finally:
            # Przywracanie ustawień terminala i sygnałów – teraz w 100% bezpieczne
            if old_winch is not None:
                signal.signal(signal.SIGWINCH, old_winch)
            sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
            sys.stdout.flush()
            termios.tcsetattr(fd, termios.TCSADRAIN, old_term)
            mouse_on()

    def _discover_network(self):
        print_header("NETWORK CAMERA DISCOVERY")

        prefix = NetworkUtils.get_local_prefix()
        logger.info(f"Scanning network {prefix}0/24")

        print(f"  Scanning {prefix}0/24...")
        def _disc_progress(pct, i, total, msg):
            # Aktualizuj linię statusu w głównym UI
            self.ui.set_scan_status(
                format_progress_line(pct, width=25, label="📡 Scanning", subnet=prefix+"0/24")
            )
            # Odśwież ekran, aby pokazać zmieniony status
            self.ui.draw()

        active = NetworkUtils.scan_subnet(prefix, progress_cb=_disc_progress)
        self.ui.set_scan_status("")  # Wyczyść linię statusu po zakończeniu
        self.ui.draw()

        print()
        if not active:
            print(f"\n{RED}No active hosts found.{RST}")
            time.sleep(2)
            return

        logger.info(f"Found {len(active)} active hosts")

        print(f"\n{CYN}Phase 2: Deep Scan...{RST}")
        found = []

        for i, ip in enumerate(active, 1):
            cam = Camera(ip=ip)
            cam_type, port = CameraDetector.detect(cam, show_progress=False)

            if cam_type != CameraType.UNKNOWN:
                mac = NetworkUtils.get_mac_from_ip(ip)
                found.append({
                    "ip": ip,
                    "type": cam_type,
                    "port": port,
                    "mac": mac
                })

        if not found:
            print(f"\n{RED}No cameras found.{RST}")
            time.sleep(2)
            return

        to_add = self._pick_scan_results(found)
        if to_add is None:
            return

        added = 0
        for cam_data in to_add:
            _mac = cam_data["mac"]
            _ip  = cam_data["ip"]
            # Sprawdź duplikat po IP lub po MAC (MAC jest pewniejszy po zmianie IP)
            _dup_ip  = any(c.ip == _ip for c in self.config.cameras)
            _dup_mac = (_mac not in ("", "UNKNOWN") and
                        any(c.mac == _mac for c in self.config.cameras))
            if _dup_ip:
                print(f"  {YLW}Skipping {_ip} (IP already in list){RST}")
                continue
            if _dup_mac:
                # Kamera istnieje pod innym IP — zaktualizuj zamiast dodawać
                existing = next(c for c in self.config.cameras if c.mac == _mac)
                if existing.ip != _ip:
                    old_ip = existing.ip
                    NetworkUtils.resolve_ip(existing)  # aktualizuje IP i URI
                    print(f"  {YLW}Updated {existing.name}: {old_ip} → {existing.ip}{RST}")
                else:
                    print(f"  {YLW}Skipping {_ip} (MAC already in list){RST}")
                continue

            ports = CameraPorts()
            if cam_data["type"] == CameraType.DVRIP:
                ports.dvrip = cam_data["port"] or 34567
            elif cam_data["type"] == CameraType.RTSP_ONLY:
                ports.rtsp = cam_data["port"] or 554
            else:
                ports.onvif = cam_data["port"] or 80

            cam = Camera(
                name=f"Cam_{_ip.split('.')[-1]}",
                ip=_ip,
                mac=_mac,
                ports=ports,
                cam_type=cam_data["type"]
            )

            self.config.cameras.append(cam)
            added += 1
            logger.info(f"Added camera: {_ip} ({cam_data['type'].value}) MAC={_mac}")

        if added > 0:
            self.config_mgr.save()
            print(f"\n{GRN}Added {added} cameras to config{RST}")
            time.sleep(2)
    
    def _discover_v4l2(self):
        print_header("V4L2 DEVICE DISCOVERY")
        
        devices = V4L2Scanner.scan()
        
        if not devices:
            print(f"\n{RED}No V4L2 devices found.{RST}")
            print(f"{YLW}Install v4l-utils: sudo apt install v4l-utils{RST}")
            time.sleep(2)
            return
        
        items = []
        for dev in devices:
            exists = any(c.device == dev.device for c in self.config.cameras
                         if c.type == CameraType.V4L2)
            tag = f"{GRN}E{RST}" if exists else f"{RED}N{RST}"
            items.append(f"{dev.device:<12} {tag} {dev.name[:30]}")
        items.append(f"── Add ALL {len(devices)} devices ──")

        idx = select_menu(items, selected=0,
                          title=f"🎥 V4L2 Devices – {len(devices)} found   ENTER=add  Q=cancel")

        to_add = []
        if idx == -1:
            return
        elif idx == len(devices):
            to_add = devices
        elif 0 <= idx < len(devices):
            to_add = [devices[idx]]
        else:
            return
        
        added = 0
        for dev in to_add:
            if any(c.device == dev.device for c in self.config.cameras if c.type == CameraType.V4L2):
                print(f"  {YLW}Skipping {dev.device} (already exists){RST}")
                continue
            
            self.config.cameras.append(dev)
            added += 1
            logger.info(f"Added V4L2 device: {dev.device}")
        
        if added > 0:
            self.config_mgr.save()
            print(f"\n{GRN}Added {added} V4L2 devices{RST}")
        else:
            print(f"\n{YLW}All selected devices already exist{RST}")
        
        time.sleep(2)

    def _add_file_camera(self):
        print_header("ADD FILE CAMERA")

        path = rlinput(f"{CYN}Path to video file:{RST} ", "").strip()
        if not path:
            return
        if not os.path.isfile(path):
            print(f"{RED}File not found: {path}{RST}")
            time.sleep(2)
            return

        name_default = os.path.splitext(os.path.basename(path))[0][:30]
        name = rlinput(f"{CYN}Camera name:{RST} ", name_default).strip() or name_default

        loop_ans = rlinput(f"{CYN}Loop (y/n):{RST} ", "y").strip().lower()
        file_loop = loop_ans not in ("n", "no", "0", "false")

        spd = rlinput(f"{CYN}Speed (0.25–4.0):{RST} ", "1.0").strip()
        try:
            file_speed = max(0.1, min(4.0, float(spd)))
        except ValueError:
            file_speed = 1.0

        start = rlinput(f"{CYN}Start at second:{RST} ", "0.0").strip()
        try:
            file_start = max(0.0, float(start))
        except ValueError:
            file_start = 0.0

        cam = Camera(
            name=name,
            ip="localhost",
            mac="FILE",
            cam_type=CameraType.FILE,
            file_path=path,
            file_loop=file_loop,
            file_speed=file_speed,
            file_start=file_start,
            profiles=[CameraProfile(
                name=os.path.basename(path), token="file_0", uri=path)],
        )
        self.config.cameras.append(cam)
        self.config_mgr.save()
        print(f"\n{GRN}Added FILE camera: {name}{RST}")
        logger.info(f"Added FILE camera: {name} → {path}")
        time.sleep(1.5)

    def _discover_network_nmap(self):
        print_header("NMAP NETWORK DISCOVERY")

        prefix = NetworkUtils.get_local_prefix()
        subnet = f"{prefix}0/24"

        print(f"{CYN}Running nmap host discovery on {subnet}...{RST}")
        print(f"{YLW}This may take 10-30 seconds{RST}\n")
        logger.info(f"nmap discovery: {subnet}")

        # Ustaw status w UI na czas działania nmap
        self.ui.set_scan_status(f"{CYN}🔍 nmap scanning {subnet}... (this may take a while){RST}")
        self.ui.draw()

        try:
            result = subprocess.run(
                ["nmap", "-sn", "--open", "-T4", subnet],
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                universal_newlines=True,
                timeout=60
            )
            output = result.stdout
        except subprocess.TimeoutExpired:
            self.ui.set_scan_status(f"{RED}nmap timed out{RST}")
            self.ui.draw()
            print(f"{RED}nmap timed out{RST}")
            time.sleep(2)
            self.ui.set_scan_status("")
            return
        except OSError as e:
            self.ui.set_scan_status(f"{RED}nmap error: {e}{RST}")
            self.ui.draw()
            print(f"{RED}nmap error: {e}{RST}")
            time.sleep(2)
            self.ui.set_scan_status("")
            return

        active = re.findall(r'Nmap scan report for (?:\S+ \()?(\d+\.\d+\.\d+\.\d+)\)?', output)

        if not active:
            self.ui.set_scan_status(f"{RED}nmap found no active hosts.{RST}")
            self.ui.draw()
            print(f"\n{RED}nmap found no active hosts.{RST}")
            time.sleep(2)
            self.ui.set_scan_status("")
            return

        print(f"{GRN}nmap found {len(active)} active hosts{RST}")
        print(f"\n{CYN}Phase 2: Deep scan (port check + type detect)...{RST}")

        # Deep scan z paskiem postępu
        found = []
        total = len(active)
        for i, ip in enumerate(active, 1):
            # Aktualizuj status co kilka hostów, żeby nie migało za często
            if i % 5 == 0 or i == total:
                pct = (i / total) * 100
                self.ui.set_scan_status(
                    format_progress_line(pct, width=20, label="🔍 Deep scan", subnet=f"{i}/{total} hosts")
                )
                self.ui.draw()

            cam = Camera(ip=ip)
            cam_type, port = CameraDetector.detect(cam, show_progress=False)
            if cam_type != CameraType.UNKNOWN:
                mac = NetworkUtils.get_mac_from_ip(ip)
                found.append({"ip": ip, "type": cam_type, "port": port, "mac": mac})

        self.ui.set_scan_status("")
        self.ui.draw()

        if not found:
            print(f"\n{RED}No cameras detected.{RST}")
            time.sleep(2)
            return

        to_add = self._pick_scan_results(found)
        if to_add is None:
            return

        added = 0
        for cam_data in to_add:
            _mac = cam_data["mac"]
            _ip  = cam_data["ip"]
            _mac_known = _mac not in ("", "UNKNOWN")
            if _mac_known:
                _by_mac = next((c for c in self.config.cameras if c.mac == _mac), None)
                if _by_mac:
                    if _by_mac.ip != _ip:
                        _old_ip = _by_mac.ip
                        NetworkUtils.resolve_ip(_by_mac)
                        print(f"  {GRN}Updated {_by_mac.name}: {_old_ip} → {_by_mac.ip}{RST}")
                    else:
                        print(f"  {DIM}Skipping {_ip} — known camera (MAC){RST}")
                    continue
            if any(c.ip == _ip for c in self.config.cameras):
                print(f"  {DIM}Skipping {_ip} — known camera (IP){RST}")
                continue

            ports = CameraPorts()
            if cam_data["type"] == CameraType.DVRIP:
                ports.dvrip = cam_data["port"] or 34567
            elif cam_data["type"] == CameraType.RTSP_ONLY:
                ports.rtsp = cam_data["port"] or 554
            else:
                ports.onvif = cam_data["port"] or 80

            cam = Camera(
                name=f"Cam_{_ip.split('.')[-1]}",
                ip=_ip,
                mac=_mac,
                ports=ports,
                cam_type=cam_data["type"]
            )
            self.config.cameras.append(cam)
            added += 1
            logger.info(f"Added camera: {_ip} ({cam_data['type'].value}) MAC={_mac}")

        if added > 0:
            self.config_mgr.save()
            print(f"\n{GRN}Added {added} cameras to config{RST}")
            time.sleep(2)
    
    def _save_session(self):
        self._save_session_state()
        self.config_mgr.save()
        
        print(f"\n{GRN}Session state saved!{RST}")
        cam = self.ui.current_camera
        if cam:
            print(f"{WHT}Active camera: {self.ui.current_idx+1}. {cam.name}{RST}")
        print(f"{WHT}Playing cameras: {len(self.config.session_state.playing_cameras) if self.config.session_state else 0}{RST}")
        print(f"\n{YLW}Press any key...{RST}")
        self._wait_click_or_key()
    
    def _save_window_layout(self):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        print(f"{CYN}╔══════════════════════════════════════════════════════════╗{RST}")
        print(f"{CYN}║              SAVE WINDOW LAYOUT                          ║{RST}")
        print(f"{CYN}╚══════════════════════════════════════════════════════════╝\n{RST}")

        wayland = _is_wayland()
        compositor = _wayland_compositor() if wayland else 'x11'
        print(f"  Session: {YLW}{'Wayland/' + compositor if wayland else 'X11'}{RST}")

        def _geom_via_ipc(prof) -> dict:
            """Pobierz rozmiar z IPC + pozycję przez xdotool/window-pos."""
            try:
                ctrl = prof.get_mpv()
                if not ctrl or not ctrl.is_alive(): return {}
                w = ctrl.get_property("osd-width")
                h = ctrl.get_property("osd-height")
                if not w or not h or int(w) <= 0: return {}
                w, h = int(w), int(h)
                # Pozycja przez window-pos-x/y (nowsze mpv)
                x = ctrl.get_property("window-pos-x")
                y = ctrl.get_property("window-pos-y")
                if x is not None and y is not None:
                    logger.debug(f"IPC window-pos: {x},{y} {w}x{h}")
                    return {"X": int(x), "Y": int(y), "WIDTH": w, "HEIGHT": h}
                # Pozycja przez xdotool (X11 + XWayland)
                if shutil.which("xdotool"):
                    import os as _os
                    env = dict(_os.environ)
                    if not env.get("DISPLAY"): env["DISPLAY"] = ":0"
                    # Kolejność prób: nazwa okna → PID → ^LIVE:
                    cam_title = None
                    if prof.ipc_path:
                        try:
                            part = prof.ipc_path.split("mpv-")[1].rsplit("-", 1)[0]
                            cam_title = f"LIVE:{part}"
                        except Exception:
                            pass
                    searches = []
                    if cam_title: searches.append(["--name", cam_title])
                    searches.append(["--pid", str(prof.pid)])
                    searches.append(["--name", "^LIVE:"])
                    for sarg in searches:
                        try:
                            wids = subprocess.check_output(
                                ["xdotool", "search"] + sarg,
                                universal_newlines=True, timeout=2,
                                stderr=subprocess.DEVNULL, env=env).strip().split()
                            if not wids: continue
                            go = subprocess.check_output(
                                ["xdotool", "getwindowgeometry", "--shell", wids[0]],
                                universal_newlines=True, timeout=1, env=env)
                            gd = {}
                            for line in go.split("\n"):
                                if "=" in line:
                                    k, v = line.split("=", 1)
                                    try: gd[k] = int(v)
                                    except ValueError: pass
                            if "X" in gd and "Y" in gd:
                                logger.debug(f"xdotool {sarg}: {gd['X']},{gd['Y']} {w}x{h}")
                                return {"X": gd["X"], "Y": gd["Y"], "WIDTH": w, "HEIGHT": h}
                        except Exception as e:
                            logger.debug(f"xdotool {sarg}: {e}")
                logger.debug(f"IPC: size {w}x{h} OK but position unknown")
            except Exception as e:
                logger.debug(f"IPC geom error: {e}")
            return {}


        def _geom_kwin(pid) -> dict:
            """KWin/Plasma: kdotool, qdbus, xdotool/XWayland."""
            # Próba 0: kdotool (xdotool dla KDE Wayland)
            # pip install kdotool  lub  yay -S kdotool (AUR)
            if shutil.which('kdotool'):
                try:
                    import re as _re
                    # Szukaj po dokładnym tytule okna (LIVE:Cam_101 itp.)
                    # ipc_path: /tmp/mpv-Cam_101-7262 → cam_name = Cam_101
                    cam_name = None
                    if prof.ipc_path:
                        m = _re.search(r'mpv-(.+)-\d+$', prof.ipc_path)
                        if m: cam_name = m[1]
                    searches = []
                    if cam_name: searches.append(f'LIVE:{cam_name}')
                    searches.append('LIVE:')  # fallback — weź pierwszy
                    for title in searches:
                        try:
                            wids = subprocess.check_output(
                                ['kdotool', 'search', '--name', title],
                                universal_newlines=True, timeout=3,
                                stderr=subprocess.DEVNULL).strip().split()
                            if not wids: continue
                            go = subprocess.check_output(
                                ['kdotool', 'getwindowgeometry', wids[0]],
                                universal_newlines=True, timeout=2)
                            # Format:
                            # Window {uuid}
                            # Position: 340.23,68.49
                            # Geometry: 768x864
                            m_pos  = _re.search(r'Position:\s*([\d.]+),([\d.]+)', go)
                            m_size = _re.search(r'Geometry:\s*(\d+)x(\d+)', go)
                            if m_pos and m_size:
                                logger.debug(f"kdotool '{title}': {go.strip()}")
                                return {"X": int(float(m_pos[1])), "Y": int(float(m_pos[2])),
                                        "WIDTH": int(m_size[1]), "HEIGHT": int(m_size[2])}
                        except Exception as e:
                            logger.debug(f"kdotool '{title}': {e}")
                except Exception as e:
                    logger.debug(f"kdotool error: {e}")
            # Próba 1: qdbus/qdbus6 (KDE Plasma)
            for qdbus in ('qdbus6', 'qdbus'):
                if not shutil.which(qdbus): continue
                try:
                    # Pobierz listę okien przez KWin scripting
                    out = subprocess.check_output(
                        [qdbus, 'org.kde.KWin', '/KWin', 'queryWindowInfo'],
                        universal_newlines=True, timeout=2, stderr=subprocess.DEVNULL)
                    logger.debug(f"qdbus queryWindowInfo: {out[:200]}")
                except Exception as e:
                    logger.debug(f"{qdbus} error: {e}")
            # Próba 2: xdotool przez XWayland (KDE często ma XWayland)
            if shutil.which('xdotool'):
                try:
                    import os as _os
                    env = dict(_os.environ)
                    if not env.get('DISPLAY'): env['DISPLAY'] = ':0'
                    # Szukaj przez PID
                    wids = subprocess.check_output(
                        ["xdotool", "search", "--pid", str(pid)],
                        universal_newlines=True, timeout=2,
                        stderr=subprocess.DEVNULL, env=env).strip().split()
                    # Fallback: szukaj przez tytuł okna LIVE:*
                    if not wids:
                        wids = subprocess.check_output(
                            ["xdotool", "search", "--name", "^LIVE:"],
                            universal_newlines=True, timeout=2,
                            stderr=subprocess.DEVNULL, env=env).strip().split()
                        logger.debug(f"xdotool search --name LIVE: found {wids}")
                    if wids:
                        geom_out = subprocess.check_output(
                            ["xdotool", "getwindowgeometry", "--shell", wids[0]],
                            universal_newlines=True, timeout=1, env=env)
                        geom = {}
                        for line in geom_out.split("\n"):
                            if "=" in line:
                                k, v = line.split("=", 1)
                                try: geom[k] = int(v)
                                except ValueError: pass
                        logger.debug(f"xdotool geom for pid={pid}: {geom}")
                        if all(k in geom for k in ["X","Y","WIDTH","HEIGHT"]):
                            return geom
                except Exception as e:
                    logger.debug(f"xdotool/XWayland error: {e}")
            # Próba 3: wmctrl (może działać przez XWayland)
            if shutil.which('wmctrl'):
                try:
                    out = subprocess.check_output(
                        ["wmctrl", "-lGp"], universal_newlines=True, timeout=2)
                    for line in out.splitlines():
                        parts = line.split()
                        if len(parts) >= 7 and parts[2] == str(pid):
                            return {"X": int(parts[3]), "Y": int(parts[4]),
                                    "WIDTH": int(parts[5]), "HEIGHT": int(parts[6])}
                except Exception as e:
                    logger.debug(f"wmctrl error: {e}")
            return {}

        def _geom_xdotool(wid) -> dict:
            try:
                geom_out = subprocess.check_output(
                    ["xdotool", "getwindowgeometry", "--shell", wid],
                    universal_newlines=True, timeout=1)
                geom = {}
                for line in geom_out.split("\n"):
                    if "=" in line:
                        k, v = line.split("=", 1)
                        try: geom[k] = int(v)
                        except ValueError: pass
                return geom
            except Exception:
                return {}

        def _geom_hyprland(pid) -> dict:
            """Pobierz geometrię okna przez hyprctl clients."""
            try:
                import json as _j
                out = subprocess.check_output(
                    ["hyprctl", "clients", "-j"],
                    universal_newlines=True, timeout=2)
                clients = _j.loads(out)
                for cl in clients:
                    if cl.get("pid") == pid:
                        at = cl.get("at", [0,0])
                        sz = cl.get("size", [640,360])
                        return {"X": at[0], "Y": at[1], "WIDTH": sz[0], "HEIGHT": sz[1]}
            except Exception as e:
                logger.debug(f"hyprctl error: {e}")
            return {}

        def _geom_sway(pid) -> dict:
            """Pobierz geometrię okna przez swaymsg."""
            try:
                import json as _j
                out = subprocess.check_output(
                    ["swaymsg", "-t", "get_tree"],
                    universal_newlines=True, timeout=2)
                def _find(node):
                    if node.get("pid") == pid:
                        r = node.get("rect", {})
                        return {"X": r.get("x",0), "Y": r.get("y",0),
                                "WIDTH": r.get("width",640), "HEIGHT": r.get("height",360)}
                    for ch in node.get("nodes", []) + node.get("floating_nodes", []):
                        res = _find(ch)
                        if res: return res
                    return None
                return _find(_j.loads(out)) or {}
            except Exception as e:
                logger.debug(f"swaymsg error: {e}")
            return {}

        saved = 0
        for cam in self.config.cameras:
            for prof in cam.profiles:
                if not prof.pid or not ProcessManager.is_running(prof.pid):
                    continue
                # Próbuj w kolejności: IPC → compositor-specific → kdotool → xdotool (X11)
                geom = _geom_via_ipc(prof)
                if not geom and compositor == 'hyprland' and shutil.which('hyprctl'):
                    geom = _geom_hyprland(prof.pid)
                if not geom and compositor == 'sway' and shutil.which('swaymsg'):
                    geom = _geom_sway(prof.pid)
                if not geom and compositor == 'kwin':
                    geom = _geom_kwin(prof.pid)
                if not geom and shutil.which('kdotool'):
                    # kdotool działa na X11 i Wayland/KDE — próbuj zawsze gdy dostępne
                    geom = _geom_kwin(prof.pid)
                if not geom and not wayland and shutil.which('xdotool'):
                    # X11 fallback przez xdotool search --pid
                    try:
                        wids = subprocess.check_output(
                            ["xdotool", "search", "--pid", str(prof.pid)],
                            universal_newlines=True, timeout=2).strip().split()
                        if wids:
                            geom = _geom_xdotool(wids[0])
                    except Exception:
                        pass
                if geom and all(k in geom for k in ["X","Y","WIDTH","HEIGHT"]):
                    cam.layout = WindowLayout(
                        x=geom["X"], y=geom["Y"],
                        w=geom["WIDTH"], h=geom["HEIGHT"])
                    print(f"  {GRN}✓{RST} {cam.name}  {geom['X']},{geom['Y']} {geom['WIDTH']}x{geom['HEIGHT']}")
                    saved += 1
                else:
                    # Pokaż co udało się zebrać
                    ctrl = prof.get_mpv()
                    ipc_ok = ctrl and ctrl.is_alive()
                    print(f"  {YLW}?{RST} {cam.name} [{prof.name}] pid={prof.pid}"
                          f" ipc={'✓' if ipc_ok else '✗'} — geometria niedostępna")

        if saved == 0 and wayland:
            # Na Wayland automatyczna detekcja niemożliwa — zaproponuj ręczne wpisanie
            print(f"\n{YLW}Wayland: automatyczna detekcja pozycji okien niedostępna.{RST}")
            print(f"{DIM}Aby włączyć automatyczny zapis na KDE/KWin zainstaluj kdotool:{RST}")
            print(f"{DIM}  pip install kdotool   lub   yay -S kdotool{RST}")
            print(f"{DIM}Możesz wpisać pozycje ręcznie (x y) lub ENTER aby pominąć.{RST}")
            print(f"{DIM}Wskazówka: PPM na tytuł okna mpv → Więcej → Geometria.{RST}\n")
            import termios as _termios2
            _fd2 = sys.stdin.fileno()
            _old2 = _termios2.tcgetattr(_fd2)
            # Wyłącz raportowanie myszy — bez tego ruch myszy generuje śmieci w input()
            sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
            sys.stdout.flush()
            try:
                cooked = _termios2.tcgetattr(_fd2)
                cooked[3] |= _termios2.ECHO | _termios2.ICANON
                _termios2.tcsetattr(_fd2, _termios2.TCSADRAIN, cooked)
                for cam in self.config.cameras:
                    for prof in cam.profiles:
                        if not prof.pid or not ProcessManager.is_running(prof.pid):
                            continue
                        ctrl = prof.get_mpv()
                        w = h = None
                        if ctrl and ctrl.is_alive():
                            w = ctrl.get_property("osd-width")
                            h = ctrl.get_property("osd-height")
                        w = int(w) if w else (cam.layout.w if cam.layout else 640)
                        h = int(h) if h else (cam.layout.h if cam.layout else 360)
                        print(f"  {CYN}{cam.name}{RST} [{prof.name}]"
                              f"  rozmiar={w}x{h}"
                              f"  obecna_poz={cam.layout.x},{cam.layout.y if cam.layout else '?'}")
                        try:
                            ans = input(f"    Wpisz 'x y' lub ENTER aby zachować obecną: ").strip()
                            if ans:
                                parts = ans.split()
                                if len(parts) >= 2:
                                    nx, ny = int(parts[0]), int(parts[1])
                                    cam.layout = WindowLayout(x=nx, y=ny, w=w, h=h)
                                    print(f"    {GRN}✓{RST} Zapisano {nx},{ny} {w}x{h}")
                                    saved += 1
                        except (ValueError, EOFError):
                            pass
            finally:
                _termios2.tcsetattr(_fd2, _termios2.TCSADRAIN, _old2)
                # Przywróć raportowanie myszy
                sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
                sys.stdout.flush()
        elif saved == 0:
            print(f"\n{YLW}Nie znaleziono aktywnych okien mpv.{RST}")

        if saved > 0 or True:  # zawsze próbuj zapisać terminal
            # Zapisz pozycję okna terminala
            term_geom = {}
            if Terminal._window_id:
                tool = Terminal._get_win_tool()
                if tool:
                    try:
                        go = subprocess.check_output(
                            [tool, 'getwindowgeometry' if tool == 'xdotool' else 'getwindowgeometry',
                             Terminal._window_id],
                            universal_newlines=True, timeout=2,
                            stderr=subprocess.DEVNULL)
                        import re as _re2
                        if tool == 'xdotool':
                            # FORMAT: Position: X,Y\nGeometry: WxH
                            mp = _re2.search(r'Position:\s*(\d+),(\d+)', go)
                            ms = _re2.search(r'Geometry:\s*(\d+)x(\d+)', go)
                        else:  # kdotool
                            mp = _re2.search(r'Position:\s*([\d.]+),([\d.]+)', go)
                            ms = _re2.search(r'Geometry:\s*(\d+)x(\d+)', go)
                        if mp and ms:
                            term_geom = {"X": int(float(mp[1])), "Y": int(float(mp[2])),
                                         "WIDTH": int(ms[1]), "HEIGHT": int(ms[2])}
                    except Exception as e:
                        logger.debug(f"terminal geom error: {e}")

            if term_geom:
                self.config.layout["terminal"] = WindowLayout(
                    x=term_geom["X"], y=term_geom["Y"],
                    w=term_geom["WIDTH"], h=term_geom["HEIGHT"])
                print(f"  {GRN}✓{RST} Terminal  "
                      f"{term_geom['X']},{term_geom['Y']} "
                      f"{term_geom['WIDTH']}x{term_geom['HEIGHT']}")
                saved += 1
            else:
                print(f"  {DIM}? Terminal — pozycja niedostępna{RST}")

        if saved > 0:
            self.config_mgr.save()
            print(f"\n{GRN}Zapisano {saved} layout(ów).{RST}")

        print(f"\n{YLW}Press any key...{RST}")
        self._wait_click_or_key()

    def _batch_menu(self):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        W = 57
        
        items = [
            "🔄 Sync all cameras (network)",
            "💀 Kill all players",
            "🔌 Test connections",
            "📤 Export configuration",
            "📥 Import configuration",
            "🔎 Find moved cameras (by MAC)",
            "🎯 Detect camera types",
            "💾 Save window layout",
            "♻️  Restore saved session",
            "✖  Cancel",
        ]
        idx = select_menu(items, selected=0, title="⚙️  Batch Operations")

        if idx == -1:
            return
        if idx == 0:
            sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
            print(f"{CYN}Syncing all cameras...{RST}\n")
            for cam in self.config.cameras:
                print(f"  {cam.name} ({cam.ip})...")
                self._sync_network(cam)
            print(f"\n{GRN}Sync completed!{RST}")
            time.sleep(1.5)
        
        elif idx == 1:
            killed = ProcessManager.kill_all(self.config.cameras)
            notify(f"Killed {killed} player(s)", "info")
        
        elif idx == 2:
            sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
            print(f"{CYN}Testing connections...{RST}\n")
            print(f"  {WHT}CAMERA{pad('', 20)} | STATUS{RST}")
            print(f"  " + "-" * 40)
            
            for cam in self.config.cameras:
                if cam.type == CameraType.V4L2:
                    status = f"{GRN}LOCAL{RST}"
                else:
                    ok = NetworkUtils.ping_host(cam.ip)
                    status = f"{GRN}OK{RST}" if ok else f"{RED}FAIL{RST}"
                
                print(f"  {pad(cam.name[:25], 25)} | {status}")
            
            print(f"\n{YLW}Press any key...{RST}")
            self._wait_click_or_key()
        
        elif idx == 3:
            exp = f"{self.config_file}.export.json"
            try:
                with open(exp, 'w') as f:
                    json.dump(self.config_mgr._to_dict(), f, indent=4)
                notify(f"Exported to {exp}", "info")
            except Exception as e:
                notify(f"Export failed: {e}", "error")
            time.sleep(1.5)
        
        elif idx == 4:
            default_import = f"{self.config_file}.export.json"
            imp = rlinput(f"Import file: ", default_import).strip()
            if not imp:
                imp = default_import
            if os.path.exists(imp):
                try:
                    with open(imp, 'r') as f:
                        data = json.load(f)
                    self.config = Config.from_dict(data)
                    self.config_mgr.config = self.config
                    self.ui.config = self.config
                    notify("Imported", "info")
                except Exception as e:
                    notify(f"Import failed: {e}", "error")
            else:
                notify("File not found!", "error")
            time.sleep(1.5)
        
        elif idx == 5:
            self._find_moved_cameras()
        
        elif idx == 6:
            self._detect_all_types()
        
        elif idx == 7:
            self._save_window_layout()
        
        elif idx == 8:
            self._restore_session()

    def _start_auto_check_timer(self):
        if not self.config.auto_check_ip_changes:
            return
        interval = self.config.auto_check_interval
        def _tick():
            while True:
                time.sleep(interval)
                try:
                    self._auto_check_cameras()
                except Exception as e:
                    logger.error(f"Auto-check error: {e}")
        t = threading.Thread(target=_tick, daemon=True, name="auto-check-ip")
        t.start()
        logger.info(f"Auto-check IP timer started (every {interval}s)")

    def _auto_check_cameras(self):
        logger.info("Auto-check: scanning network for moved cameras...")

        subnets = []
        try:
            out = subprocess.check_output(
                ["ip", "-4", "addr", "show"],
                universal_newlines=True, timeout=5
            )
            for line in out.splitlines():
                if 'inet ' in line and 'scope global' in line:
                    parts = line.strip().split()
                    if len(parts) >= 2:
                        ip = parts[1].split('/')[0]
                        if not ip.startswith('127.'):
                            prefix = '.'.join(ip.split('.')[:-1]) + '.'
                            if prefix not in subnets:
                                subnets.append(prefix)
        except Exception as e:
            logger.error(f"Auto-check: subnet detection error: {e}")
            return

        if not subnets:
            logger.warning("Auto-check: no active subnets found")
            return

        def _auto_progress(pct, i, total, msg):
            # Ładnie sformatowany pasek postępu w linii statusu
            self.ui._scan_status = format_progress_line(
                pct, width=20, label=f"{CYN}Auto-check{RST}", subnet=msg
            )

        for subnet in subnets:
            logger.info(f"Auto-check: scanning {subnet}0/24")
            NetworkUtils.scan_subnet(subnet, max_workers=30,
                                     progress_cb=_auto_progress)
        self.ui._scan_status = ''

        changes = []
        for cam in self.config.cameras:
            if cam.type in (CameraType.V4L2, CameraType.FILE, CameraType.SCANNER) or cam.mac in ("UNKNOWN", "V4L2", "FILE", "SCANNER", ""):
                continue
            new_ip = NetworkUtils.get_ip_from_mac(cam.mac)
            if new_ip and new_ip != cam.ip:
                logger.info(f"Auto-check: {cam.name} moved {cam.ip} → {new_ip}")
                changes.append((cam, cam.ip, new_ip))

        if not changes:
            logger.info("Auto-check: all cameras at correct IP")
            notify("Auto-check: OK", "info")
            return

        for cam, old_ip, new_ip in changes:
            cam.ip = new_ip
            for prof in cam.profiles:
                if old_ip in prof.uri:
                    prof.uri = prof.uri.replace(old_ip, new_ip)
                    logger.info(f"Auto-check: updated URI for {cam.name}: {prof.uri}")

        self.config_mgr.save()
        logger.info(f"Auto-check: updated {len(changes)} camera(s)")

        for cam, old_ip, new_ip in changes:
            prof_idx = cam.active_profile
            if not cam.profiles or prof_idx >= len(cam.profiles):
                continue
            prof = cam.profiles[prof_idx]
            if ProcessManager.is_running(prof.pid):
                logger.info(f"Auto-check: restarting stream for {cam.name} ({old_ip} → {new_ip})")
                ProcessManager.kill(prof.pid)
                time.sleep(0.5)
                layout = cam.layout or self.config.layout.get("mpv_default", WindowLayout())
                Player._play_rtsp(cam, prof, self.config.player_cmd, layout,
                                  global_mute=self.config.global_mute)

        notify(f"Auto-check: {len(changes)} camera(s) changed IP", "info")

    def _find_moved_cameras(self):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        print(f"{CYN}╔══════════════════════════════════════════════════════════╗{RST}")
        print(f"{CYN}║             FIND CAMERAS THAT MOVED (BY MAC)             ║{RST}")
        print(f"{CYN}╚══════════════════════════════════════════════════════════╝{RST}\n")
        
        print(f"{CYN}Detecting subnets...{RST}")
        subnets = []
        
        try:
            out = subprocess.check_output(
                ["ip", "-4", "addr", "show"],
                universal_newlines=True,
                timeout=5
            )
            for line in out.splitlines():
                if 'inet ' in line and 'scope global' in line:
                    parts = line.strip().split()
                    if len(parts) >= 2:
                        cidr = parts[1]
                        ip = cidr.split('/')[0]
                        if not ip.startswith('127.'):
                            prefix = '.'.join(ip.split('.')[:-1]) + '.'
                            if prefix not in subnets:
                                subnets.append(prefix)
                                print(f"  {GRN}✓{RST} {prefix}0/24")
        except Exception as e:
            logger.error(f"Error detecting subnets: {e}")
        
        if not subnets:
            print(f"{RED}No active subnets found{RST}")
            time.sleep(2)
            return
        
        print(f"\n{CYN}Scanning networks...{RST}\n")
        
        for subnet in subnets:
            print(f"  Scanning {subnet}0/24...")
            NetworkUtils.scan_subnet(subnet, max_workers=30)
        
        print(f"\n{GRN}ARP table populated{RST}\n")
        
        print(f"  {WHT}CAMERA{pad('', 20)} | OLD IP{pad('', 8)} | NEW IP{pad('', 8)} | MAC{RST}")
        print(f"  " + "-" * 70)
        
        changes = []
        for cam in self.config.cameras:
            if cam.type in (CameraType.V4L2, CameraType.FILE, CameraType.SCANNER) or cam.mac in ["UNKNOWN", "V4L2", "FILE", "SCANNER"]:
                continue
            
            new_ip = NetworkUtils.get_ip_from_mac(cam.mac)
            if new_ip:
                if new_ip != cam.ip:
                    print(f"  {pad(cam.name[:25], 25)} | {pad(cam.ip, 15)} | {GRN}{pad(new_ip, 15)}{RST} | {BLU}{cam.mac[:17]}{RST}")
                    changes.append((cam, cam.ip, new_ip))
        
        if changes:
            print(f"\n{GRN}Found {len(changes)} camera(s) with changed IP!{RST}")
            print(f"\n{YLW}Update all? (y/n):{RST} ", end='')
            
            if get_key().lower() == 'y':
                for cam, old, new in changes:
                    cam.ip = new
                    logger.info(f"Updated {cam.name}: {old} -> {new}")
                
                self.config_mgr.save()
                print(f"\n{GRN}Updated {len(changes)} IP(s){RST}")
                time.sleep(2)
        else:
            print(f"  {GRN}✓ All cameras at correct IP addresses{RST}")
            time.sleep(2)
    
    def _detect_all_types(self):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        print(f"{CYN}Detecting camera types...{RST}\n")
        
        print(f"  {WHT}CAMERA{pad('', 20)} | IP/DEVICE{pad('', 7)} | TYPE{RST}")
        print(f"  " + "-" * 57)
        
        for cam in self.config.cameras:
            if cam.type == CameraType.V4L2:
                dev = cam.device.split('/')[-1] if cam.device else "?"
                print(f"  {pad(cam.name[:25], 25)} | {pad(dev, 15)} | {BLU}V4L2 (local){RST}")
                continue
            
            old_type = cam.type
            new_type, _ = CameraDetector.detect(cam)
            cam.type = new_type
            
            color = {
                CameraType.ONVIF: GRN,
                CameraType.DVRIP: MAG,
                CameraType.RTSP_ONLY: YLW,
                CameraType.UNKNOWN: RED
            }.get(new_type, WHT)
            
            note = f" (was: {old_type.value})" if old_type != new_type else ""
            print(f"  {pad(cam.name[:25], 25)} | {pad(cam.ip, 15)} | {color}{new_type.value}{RST}{note}")
        
        print(f"\n{CYN}Detection completed!{RST}")
        print(f"\n{YLW}Press any key...{RST}")
        self._wait_click_or_key()

    def _get_device_info(self, cam: Camera, client: ONVIFClient) -> dict:
        result = {
            'Manufacturer': 'N/A',
            'Model': 'N/A',
            'FirmwareVersion': 'N/A',
            'SerialNumber': 'N/A',
            'HardwareId': 'N/A'
        }

        url = f"http://{cam.ip}:{cam.ports.onvif}/onvif/device_service"
        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tds="http://www.onvif.org/ver10/device/wsdl">
    <s:Header>{client._get_auth_header()}</s:Header>
    <s:Body><tds:GetDeviceInformation/></s:Body>
    </s:Envelope>'''

        try:
            r = client._get_session().post(url, data=body, timeout=3)
            if r.status_code == 200:
                xml = r.text
                for key in result.keys():
                    match = re.search(f'<tds:{key}>(.*?)</tds:{key}>', xml)
                    if match:
                        result[key] = match.group(1).strip()
        except Exception as e:
            logger.debug(f"GetDeviceInformation error: {e}")

        return result

    def _get_system_info(self, cam: Camera, client: ONVIFClient) -> dict:
        result = {
            'system_date': 'N/A',
            'device_time': 'N/A',
            'ntp': False
        }

        url = f"http://{cam.ip}:{cam.ports.onvif}/onvif/device_service"
        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tds="http://www.onvif.org/ver10/device/wsdl">
    <s:Header>{client._get_auth_header()}</s:Header>
    <s:Body><tds:GetSystemDateAndTime/></s:Body>
    </s:Envelope>'''

        try:
            r = client._get_session().post(url, data=body, timeout=3)
            if r.status_code == 200:
                xml = r.text

                if '<tds:DaylightSavings>' in xml:
                    result['ntp'] = 'UTCDateTime' in xml

                date_match = re.search(r'<tds:Date>(\d+)-(\d+)-(\d+)</tds:Date>', xml)
                time_match = re.search(r'<tds:Time>(\d+):(\d+):(\d+)</tds:Time>', xml)

                if date_match and time_match:
                    result['device_time'] = f"{date_match.group(1)}-{date_match.group(2)}-{date_match.group(3)} {time_match.group(1)}:{time_match.group(2)}"

                date_match = re.search(r'<tt:Date>(\d+)-(\d+)-(\d+)</tt:Date>', xml)
                time_match = re.search(r'<tt:Time>(\d+):(\d+):(\d+)</tt:Time>', xml)

                if date_match and time_match:
                    result['system_date'] = f"{date_match.group(1)}-{date_match.group(2)}-{date_match.group(3)}"
        except Exception as e:
            logger.debug(f"GetSystemDateAndTime error: {e}")

        return result

    def _get_camera_network_info(self, cam: Camera, client: ONVIFClient) -> dict:
        result = {
            'gateway': 'N/A',
            'dns': 'N/A',
            'dhcp': 'N/A',
            'mac': cam.mac,
            'ip': cam.ip
        }

        url = f"http://{cam.ip}:{cam.ports.onvif}/onvif/device_service"

        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tds="http://www.onvif.org/ver10/device/wsdl">
    <s:Header>{client._get_auth_header()}</s:Header>
    <s:Body><tds:GetNetworkInterfaces/></s:Body>
    </s:Envelope>'''

        try:
            r = client._get_session().post(url, data=body, timeout=3)
            if r.status_code == 200:
                xml = r.text

                dhcp_match = re.search(r'<tt:DHCP>(true|false)</tt:DHCP>', xml)
                if dhcp_match:
                    result['dhcp'] = "YES" if dhcp_match.group(1) == 'true' else "NO"

                ip_match = re.search(r'<tt:IPAddress>([^<]+)</tt:IPAddress>', xml)
                if ip_match:
                    result['ip'] = ip_match.group(1)

                if result['mac'] == 'UNKNOWN':
                    mac_match = re.search(r'<tt:PhysicalAddress>([^<]+)</tt:PhysicalAddress>', xml)
                    if mac_match:
                        result['mac'] = mac_match.group(1).upper()
        except Exception as e:
            logger.debug(f"GetNetworkInterfaces error: {e}")

        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tds="http://www.onvif.org/ver10/device/wsdl">
    <s:Header>{client._get_auth_header()}</s:Header>
    <s:Body><tds:GetNetworkDefaultGateway/></s:Body>
    </s:Envelope>'''

        try:
            r = client._get_session().post(url, data=body, timeout=2)
            if r.status_code == 200:
                xml = r.text
                gateway_match = re.search(r'<tt:IPv4Address>([^<]+)</tt:IPv4Address>', xml)
                if gateway_match:
                    result['gateway'] = gateway_match.group(1)
        except Exception:
            pass

        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tds="http://www.onvif.org/ver10/device/wsdl">
    <s:Header>{client._get_auth_header()}</s:Header>
    <s:Body><tds:GetDNS/></s:Body>
    </s:Envelope>'''

        try:
            r = client._get_session().post(url, data=body, timeout=2)
            if r.status_code == 200:
                xml = r.text
                dns_match = re.search(r'<tt:IPAddress>([^<]+)</tt:IPAddress>', xml)
                if dns_match:
                    result['dns'] = dns_match.group(1)
        except Exception:
            pass

        return result

    def _discover_services(self, cam: Camera, client: ONVIFClient) -> dict:
        services = {
            'device': '/onvif/device_service',
            'media': 'Not found',
            'ptz': 'Not found',
            'imaging': 'Not found',
            'events': 'Not found',
            'devio': 'Not found',
        }

        url = f"http://{cam.ip}:{cam.ports.onvif}/onvif/device_service"
        body = f'''<s:Envelope xmlns:s="http://www.w3.org/2003/05/soap-envelope" xmlns:tds="http://www.onvif.org/ver10/device/wsdl">
    <s:Header>{client._get_auth_header()}</s:Header>
    <s:Body><tds:GetServices><tds:IncludeCapability>true</tds:IncludeCapability></tds:GetServices></s:Body>
    </s:Envelope>'''

        try:
            r = client._get_session().post(url, data=body, timeout=3)
            if r.status_code == 200:
                xml = r.text

                if 'http://www.onvif.org/ver10/media/wsdl' in xml or 'Media' in xml:
                    services['media'] = '/onvif/Media'

                if 'http://www.onvif.org/ver20/ptz/wsdl' in xml or 'PTZ' in xml:
                    services['ptz'] = '/onvif/PTZ'

                if 'http://www.onvif.org/ver20/imaging/wsdl' in xml or 'Imaging' in xml:
                    services['imaging'] = '/onvif/imaging'

                if 'http://www.onvif.org/ver10/events/wsdl' in xml or 'Events' in xml:
                    services['events'] = '/onvif/Events'

                if 'http://www.onvif.org/ver10/deviceio/wsdl' in xml or 'DeviceIO' in xml:
                    services['devio'] = '/onvif/DeviceIO'

                matches = re.findall(r'<tds:XAddr>([^<]+)</tds:XAddr>', xml)
                for match in matches:
                    path = match.replace(f"http://{cam.ip}:{cam.ports.onvif}", "")
                    if 'media' in path.lower():
                        services['media'] = path
                    elif 'ptz' in path.lower():
                        services['ptz'] = path
                    elif 'imaging' in path.lower():
                        services['imaging'] = path
                    elif 'event' in path.lower():
                        services['events'] = path
                    elif 'deviceio' in path.lower() or 'devio' in path.lower():
                        services['devio'] = path
        except Exception as e:
            logger.debug(f"GetServices error: {e}")

        return services

    def _pick_scan_results(self, found: list):
        while True:
            items = []
            for cam in found:
                color_tag = "ONVIF" if cam["type"] == CameraType.ONVIF else cam["type"].value
                port_s = str(cam["port"]) if cam["port"] else "N/A"
                exists = any(c.ip == cam["ip"] for c in self.config.cameras)
                tag = f"{GRN}E{RST}" if exists else f"{RED}N{RST}"
                items.append(f"{cam['ip']:<15}  {port_s:<5}  {color_tag:<5} {tag} {cam['mac']}")

            items.append(f"── Add ALL {len(found)} cameras ──")

            idx = select_menu(items, selected=0,
                              title=f"📡 Scan Results – {len(found)} found   ENTER=add  Q=cancel")

            if idx == -1 or idx >= len(items):
                return None
            elif idx == len(found):
                return found
            else:
                return [found[idx]]

    def _get_v4l2_controls(self, device: str) -> list:
        if not shutil.which('v4l2-ctl'):
            return []
        try:
            r = subprocess.run(
                ['v4l2-ctl', '-d', device, '-l'],
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                universal_newlines=True, timeout=3
            )
            controls = []
            for line in r.stdout.splitlines():
                line = line.strip()
                if not line or ':' not in line:
                    continue
                m = re.match(r'^(\S+)\s+0x\w+\s+\((\w+)\)\s*:(.+)$', line)
                if not m:
                    m2 = re.match(r'^(\S+)\s*:\s*(.+)$', line)
                    if not m2:
                        continue
                    name, typ, rest = m2.group(1), 'int', m2.group(2)
                else:
                    name, typ, rest = m.group(1), m.group(2), m.group(3)
                def _val(key, s=rest):
                    mv = re.search(rf'{key}=(-?\d+)', s)
                    return int(mv.group(1)) if mv else None
                controls.append({
                    'name':    name,
                    'type':    typ,
                    'min':     _val('min'),
                    'max':     _val('max'),
                    'step':    _val('step'),
                    'default': _val('default'),
                    'value':   _val('value'),
                })
            return controls
        except Exception as e:
            logger.debug(f"v4l2 controls error: {e}")
            return []

    def _get_v4l2_udev_info(self, device: str) -> dict:
        result = {'manufacturer': 'N/A', 'model': 'N/A', 'serial': 'N/A',
                  'vid': 'N/A', 'pid': 'N/A', 'driver': 'N/A', 'card': 'N/A',
                  'bus': 'N/A'}
        try:
            r = subprocess.run(
                ['udevadm', 'info', '--query=property', '--name', device],
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                universal_newlines=True, timeout=3
            )
            props = dict(line.split('=', 1) for line in r.stdout.splitlines() if '=' in line)
            result['manufacturer'] = props.get('ID_VENDOR_ENC', props.get('ID_VENDOR', 'N/A')).replace('\\x20', ' ')
            result['model']        = props.get('ID_MODEL_ENC',  props.get('ID_MODEL',  'N/A')).replace('\\x20', ' ')
            result['serial']       = props.get('ID_SERIAL_SHORT', props.get('ID_SERIAL', 'N/A'))
            result['vid']          = props.get('ID_VENDOR_ID',  'N/A')
            result['pid']          = props.get('ID_MODEL_ID',   'N/A')
            result['card']         = props.get('ID_V4L_PRODUCT', 'N/A').replace('\\x20', ' ')
            result['bus']          = props.get('ID_BUS', 'N/A')
        except Exception as e:
            logger.debug(f"udevadm error: {e}")
        try:
            r2 = subprocess.run(
                ['v4l2-ctl', '-d', device, '--info'],
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                universal_newlines=True, timeout=2
            )
            for line in r2.stdout.splitlines():
                if 'Driver name' in line:
                    result['driver'] = line.split(':', 1)[1].strip()
                elif 'Card type' in line:
                    result['card'] = line.split(':', 1)[1].strip()
                elif 'Bus info' in line:
                    result['bus'] = line.split(':', 1)[1].strip()
        except Exception:
            pass
        return result

    def _get_v4l2_lock_info(self, device: str) -> str:
        if not shutil.which('lsof'):
            return ''
        try:
            r = subprocess.run(
                ['lsof', device],
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                universal_newlines=True, timeout=2
            )
            lines = [l for l in r.stdout.splitlines() if device in l]
            if lines:
                parts = lines[0].split()
                return f"{parts[0]} PID={parts[1]}" if len(parts) >= 2 else lines[0]
        except Exception:
            pass
        return ''

    def _show_imaging_v4l2(self, cam):
        W = 57

        dev = cam.device or '/dev/video?'
        sys.stdout.write('[2J[H')
        sys.stdout.flush()
        print(f"{CYN}Fetching V4L2 device info...{RST}")

        udev      = self._get_v4l2_udev_info(dev)
        controls  = self._get_v4l2_controls(dev)
        lock_info = self._get_v4l2_lock_info(dev)

        sel = cam.active_profile
        if not 0 <= sel < len(cam.profiles):
            sel = 0

        def _title(text):
            spaces = (W - ansilen(text)) // 2
            return f"{YLW}║{RST}{BLU}{' '*spaces}{text}{' '*(W-ansilen(text)-spaces)}{RST}{YLW}║{RST}"

        def draw(selected):
            sys.stdout.write('[2J[H')
            sys.stdout.flush()

            print(f"{YLW}╔{'═'*W}╗{RST}")
            print(_title(" 🎥 V4L2 Device Specification "))
            print(f"{YLW}╠{'═'*W}╣{RST}")
            fields = [
                ("Card",         udev['card']),
                ("Manufacturer", udev['manufacturer']),
                ("Model",        udev['model']),
                ("Serial",       udev['serial']),
                ("VID:PID",      f"{udev['vid']}:{udev['pid']}"),
                ("Driver",       udev['driver']),
                ("Bus",          udev['bus']),
                ("Device",       dev),
            ]
            max_lbl = max(len(l) for l, _ in fields)
            for label, value in fields:
                print(f"{YLW}║{RST}{pad(f' {label:<{max_lbl}} : {value}', W)}{YLW}║{RST}")
            print(f"{YLW}╚{'═'*W}╝{RST}\n")

            print(f"{YLW}╔{'═'*W}╗{RST}")
            print(_title(" 📐 Formats & Profiles "))
            print(f"{YLW}╠{'═'*W}╣{RST}")

            if cam.profiles:
                for i, p in enumerate(cam.profiles):
                    active = (i == selected)
                    marker = f"\033[5m{GRN}▶{RST}" if active else " "
                    arrow  = ">" if active else " "
                    hi_s   = f"\033[48;5;234m" if active else ""
                    hi_e   = RST if active else ""
                    line   = f" {i+1:2}) {marker} {hi_s}{dev}  {p.res:<10} {p.name}{hi_e}"
                    print(f"{YLW}║{RST}{pad(line, W)}{YLW}║{RST}")
            else:
                print(f"{YLW}║{RST}{pad('  No profiles found', W)}{YLW}║{RST}")

            print(f"{YLW}╠{'═'*W}╣{RST}")
            if lock_info:
                print(f"{YLW}║{RST}{pad(f'  {RED}🔒 Locked by: {lock_info}', W)}{YLW}║{RST}")
            else:
                print(f"{YLW}║{RST}{pad(f'  {GRN}🔓 Device available', W)}{YLW}║{RST}")
            print(f"{YLW}╚{'═'*W}╝{RST}\n")

            print(f"{YLW}╔{'═'*W}╗{RST}")
            print(_title(" 📊 V4L2 Controls "))
            print(f"{YLW}╠{'═'*W}╣{RST}")
            if controls:
                max_cname = max(len(c['name']) for c in controls)
                for c in controls:
                    val, mn, mx, dflt = c['value'], c['min'], c['max'], c['default']
                    col = GRN if val == dflt else (RED if val in (mn, mx) else YLW)
                    rng = f"[{mn}..{mx}]" if mn is not None else ""
                    line = f"  {c['name'].ljust(max_cname)} : {col}{val}{RST}  {DIM}{rng} def={dflt}{RST}"
                    print(f"{YLW}║{RST}{pad(line, W)}{YLW}║{RST}")
            else:
                msg = (f"  {RED}v4l2-ctl not installed{RST}" if not shutil.which('v4l2-ctl')
                       else f"  {DIM}No user controls available{RST}")
                print(f"{YLW}║{RST}{pad(msg, W)}{YLW}║{RST}")
            print(f"{YLW}╚{'═'*W}╝{RST}")

            print(f"\n{DIM} ↑↓ navigate   ENTER apply   {RST}{YLW}(Q){RST}{DIM} quit{RST}")

        if not cam.profiles:
            draw(sel)
            input(f"{DIM}Press Enter to continue...{RST}")
            return

        import tty
        fd = sys.stdin.fileno()
        old_term = termios.tcgetattr(fd)
        try:
            tty.setcbreak(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()
            draw(sel)
            while True:
                key = get_key()
                if isinstance(key, MouseEvent):
                    if not key.release:
                        if key.btn == 64:
                            if sel > 0: sel -= 1; draw(sel)
                        elif key.btn == 65:
                            if sel < len(cam.profiles) - 1: sel += 1; draw(sel)
                        else:
                            prof_row = key.row - 3
                            if 1 <= prof_row <= len(cam.profiles):
                                clicked = prof_row - 1
                                if clicked == sel:
                                    cam.active_profile = sel; break
                                else:
                                    sel = clicked
                                    draw(sel)  # FIXED: added draw after mouse click
                            elif key.row >= 3 + len(cam.profiles) + 5:
                                sel = cam.active_profile; break
                    continue
                if key == Key.UP and sel > 0:
                    sel -= 1; draw(sel)
                elif key == Key.DOWN and sel < len(cam.profiles) - 1:
                    sel += 1; draw(sel)
                elif key in ('\r', '\n', Key.ENTER):
                    cam.active_profile = sel
                    break
                elif key in ('q', 'Q', '\x1b'):
                    sel = cam.active_profile
                    break
        finally:
            sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
            sys.stdout.flush()
            termios.tcsetattr(fd, termios.TCSADRAIN, old_term)

    def _show_imaging(self):
        cam = self.ui.current_camera
        if not cam:
            return
        if cam.type == CameraType.V4L2:
            self._show_imaging_v4l2(cam)
            return
        if cam.type != CameraType.ONVIF:
            notify("Full diagnostics only for ONVIF cameras", "warning")
            return

        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        W = 57

        client = ONVIFClient(cam)

        print(f"{CYN}Fetching device information...{RST}")

        device_info = self._get_device_info(cam, client)
        services = self._discover_services(cam, client)
        system_info = self._get_system_info(cam, client)
        camera_network = self._get_camera_network_info(cam, client)

        snapshot_uri = ""
        prof = self.ui.current_profile
        if prof and prof.token and prof.token != "None":
            snapshot_uri = client.get_snapshot_uri(prof.token)

        settings = client.get_imaging_settings()

        presets_count = len(cam.presets)
        presets_max = 128
        presets_color = GRN if presets_count > 0 else YLW

        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()

        print(f"{YLW}╔{'═' * W}╗{RST}")
        title = " 🔍 Device Specification "
        vis_len = ansilen(title)
        spaces = (W - vis_len) // 2
        print(f"{YLW}║{RST}{BLU}{' ' * spaces}{title}{' ' * (W - vis_len - spaces)}{RST}{YLW}║{RST}")
        print(f"{YLW}╠{'═' * W}╣{RST}")

        fields = [
            ("Manufacturer", device_info.get('Manufacturer', 'N/A')),
            ("Model", device_info.get('Model', 'N/A')),
            ("Firmware", device_info.get('FirmwareVersion', 'N/A')),
            ("Serial Number", device_info.get('SerialNumber', 'N/A')),
            ("Hardware ID", device_info.get('HardwareId', 'N/A')),
        ]

        max_label_len = max(len(label) for label, _ in fields)

        for label, value in fields:
            line = f" {label:<{max_label_len}} : {value}"
            print(f"{YLW}║{RST}{pad(line, W)}{YLW}║{RST}")

        ntp_status = f"{GRN}OK{RST}" if system_info.get('ntp', False) else f"{RED}NO{RST}"
        time_line = f" System Time   : {system_info.get('system_date', 'N/A')} (NTP: {ntp_status})"
        print(f"{YLW}║{RST}{pad(time_line, W)}{YLW}║{RST}")

        print(f"{YLW}╚{'═' * W}╝{RST}\n")

        print(f"{YLW}╔{'═' * W}╗{RST}")
        title = " 📕 SERVICE REPORT "
        vis_len = ansilen(title)
        spaces = (W - vis_len) // 2
        print(f"{YLW}║{RST}{BLU}{' ' * spaces}{title}{' ' * (W - vis_len - spaces)}{RST}{YLW}║{RST}")
        print(f"{YLW}╠{'═' * W}╣{RST}")

        mac_display = camera_network.get('mac', cam.mac)
        if mac_display == "UNKNOWN":
            mac_display = "Unknown"
        print(f"{YLW}║{RST}{pad(f' 🌐 http://{cam.ip}:{cam.ports.onvif} ? ({mac_display})', W)}{YLW}║{RST}")
        print(f"{YLW}║{RST}{pad('', W)}{YLW}║{RST}")

        service_items = [
            ('device',  '🔧', 'Device'),
            ('media',   '📽', 'Media'),
            ('ptz',     '🕹', 'PTZ'),
            ('imaging', '👁', 'Imaging'),
            ('events',  '🔔', 'Events'),
            ('devio',   '🔌', 'DevIO'),
        ]

        COL = 16
        END = W + 2

        def svc_row(emoji: str, text: str, value: str, color: str) -> None:
            print(f"{YLW}║{RST}  {emoji} {text}[{COL}G: {color}{value}{RST}[{END}G{YLW}║{RST}")

        for service, emoji, text in service_items:
            path = services.get(service, 'Not found')
            if path.startswith('http'):
                from urllib.parse import urlparse
                path = urlparse(path).path
            color = GRN if path != 'Not found' else RED
            svc_row(emoji, text, path, color)

        snap_text = "Available" if snapshot_uri else "Not available"
        snap_color = GRN if snapshot_uri else RED
        presets_text = f"{presets_color}{presets_count}/{presets_max}{RST}"

        print(f"{YLW}║{RST}  📸 Snapshot[{COL}G: {snap_color}{snap_text}{RST}   │   🎯 Presets : {presets_text}[{END}G{YLW}║{RST}")

        print(f"{YLW}╚{'═' * W}╝{RST}\n")

        print(f"{YLW}╔{'═' * W}╗{RST}")
        title = " 🌐 CAMERA NETWORK CONFIGURATION "
        vis_len = ansilen(title)
        spaces = (W - vis_len) // 2
        print(f"{YLW}║{RST}{BLU}{' ' * spaces}{title}{' ' * (W - vis_len - spaces)}{RST}{YLW}║{RST}")
        print(f"{YLW}╠{'═' * W}╣{RST}")

        dhcp_status = f"{GRN}YES{RST}" if camera_network.get('dhcp') == "YES" else f"{YLW}{camera_network.get('dhcp')}{RST}"
        ip_line = f" IP Address   : {camera_network['ip']} (DHCP: {dhcp_status})"
        print(f"{YLW}║{RST}{pad(ip_line, W)}{YLW}║{RST}")

        gateway_line = f" Gateway      : {camera_network['gateway']}"
        dns_line = f" DNS          : {camera_network['dns']}"
        print(f"{YLW}║{RST}{pad(gateway_line, W)}{YLW}║{RST}")
        print(f"{YLW}║{RST}{pad(dns_line, W)}{YLW}║{RST}")

        if camera_network.get('mac', 'UNKNOWN') != "UNKNOWN":
            mac_line = f" MAC          : {camera_network['mac']}"
            print(f"{YLW}║{RST}{pad(mac_line, W)}{YLW}║{RST}")

        print(f"{YLW}╚{'═' * W}╝{RST}\n")

        if cam.profiles:
            print(f"{YLW}╔{'═' * W}╗{RST}")
            title = " 🔗 Profile Information "
            vis_len = ansilen(title)
            spaces = (W - vis_len) // 2
            print(f"{YLW}║{RST}{BLU}{' ' * spaces}{title}{' ' * (W - vis_len - spaces)}{RST}{YLW}║{RST}")
            print(f"{YLW}╠{'═' * W}╣{RST}")

            profile_labels = [
                ("Token", "Token"),
                ("Name", "Name"),
                ("Resolution", "Resolution"),
                ("Codec", "Codec"),
            ]

            max_profile_label = max(len(label) for _, label in profile_labels)

            for idx, prof in enumerate(cam.profiles, 1):
                if idx > 1:
                    print(f"{YLW}╠{'═' * W}╣{RST}")

                print(f"{YLW}║{RST}{pad(f' Profile {idx}:', W)}{YLW}║{RST}")

                values = [
                    (prof.token or "N/A"),
                    (prof.name or "N/A"),
                    (prof.res or "N/A"),
                    (prof.codec or "N/A"),
                ]

                for (field_key, field_label), value in zip(profile_labels, values):
                    line = f"  {field_label:<{max_profile_label}} : {value}"
                    print(f"{YLW}║{RST}{pad(line, W)}{YLW}║{RST}")

                uri_label = "Stream URI"
                print(f"{YLW}║{RST}{pad(f'  {uri_label:<{max_profile_label}} :', W)}{YLW}║{RST}")

                if prof.uri:
                    uri = prof.uri
                    indent = "  "
                    max_line_len = W - len(indent) - 2
                    remaining = uri

                    while remaining:
                        if len(remaining) <= max_line_len:
                            print(f"{YLW}║{RST}{pad(f'{indent}{remaining}', W)}{YLW}║{RST}")
                            break
                        else:
                            split_pos = max_line_len
                            for separator in ['/', '?', '&', '=']:
                                pos = remaining.rfind(separator, 0, max_line_len)
                                if pos > max_line_len * 0.3:
                                    split_pos = pos + 1
                                    break

                            line = remaining[:split_pos]
                            print(f"{YLW}║{RST}{pad(f'{indent}{line}', W)}{YLW}║{RST}")
                            remaining = remaining[split_pos:]
                else:
                    print(f"{YLW}║{RST}{pad('  none', W)}{YLW}║{RST}")

            print(f"{YLW}╚{'═' * W}╝{RST}\n")

        print(f"{YLW}╔{'═' * W}╗{RST}")
        title = f" 🎨 IMAGING SETTINGS – {cam.name[:20]} "
        vis_len = ansilen(title)
        spaces = (W - vis_len) // 2
        print(f"{YLW}║{RST}{BLU}{' ' * spaces}{title}{' ' * (W - vis_len - spaces)}{RST}{YLW}║{RST}")
        print(f"{YLW}╠{'═' * W}╣{RST}")

        if settings:
            imaging_items = [
                ("🌞", "Brightness", settings.get("brightness", "N/A")),
                ("🌓", "Contrast",   settings.get("contrast",   "N/A")),
                ("🌈", "Saturation", settings.get("saturation", "N/A")),
                ("🔪", "Sharpness",  settings.get("sharpness",  "N/A")),
            ]

            IMG_COL = 18
            IMG_END = W + 2

            for emoji, text, val in imaging_items:
                val_str = str(val)
                if val_str not in ["N/A", "0"] and (isinstance(val, (int, float)) and abs(float(val_str)) > 1000):
                    color = RED
                else:
                    color = WHT
                print(f"{YLW}║{RST}  {emoji} {text}[{IMG_COL}G: {color}{val_str}{RST}[{IMG_END}G{YLW}║{RST}")
        else:
            print(f"{YLW}║{RST}{pad(f'  {RED}No imaging data or not supported{RST}', W)}{YLW}║{RST}")

        if settings and 'vs_token' in settings:
            print(f"{YLW}╠{'═' * W}╣{RST}")
            vs_info = settings.get('vs_token', '?')
            ep_info = settings.get('endpoint', '?').replace(f"http://{cam.ip}:{cam.ports.onvif}", "")
            ns_info = settings.get('ns', '?')
            line = f"  {DIM}VideoSource: {vs_info} | {ep_info} ({ns_info}){RST}"
            print(f"{YLW}║{RST}{pad(line, W)}{YLW}║{RST}")

        print(f"{YLW}╚{'═' * W}╝{RST}")

        print()
        if snapshot_uri:
            print(f"{GRN}📸 Snapshot available{RST}")
            print(f"{CYN}   {snapshot_uri}{RST}")
            print(f"\n{DIM}Press {RST}{YLW}(s){RST}{DIM} to open snapshot in browser, any key or {RST}{YLW}(Q){RST}{DIM} to quit{RST}")

            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()
            key = get_key()
            sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
            sys.stdout.flush()

            open_snap = False
            if isinstance(key, MouseEvent):
                if not key.release and 7 <= key.col <= 9:
                    open_snap = True
            elif isinstance(key, str) and key.lower() == 's':
                open_snap = True

            if open_snap:
                print(f"{CYN}Opening snapshot...{RST}")
                subprocess.Popen(
                    ['xdg-open', snapshot_uri],
                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
                )
                time.sleep(1)
        else:
            print(f"{YLW}📸 Snapshot not available{RST}")
            print(f"{CYN}Press any key to continue...{RST}")
            self._wait_click_or_key()

    def _show_help(self):
        sys.stdout.write('\033[2J\033[H'); sys.stdout.flush()
        W = 57

        help_text = [
            ("NAVIGATION", ""),
            ("Arrow Keys", "Move camera (Pan/Tilt)"),
            ("+ / -", "Zoom in/out"),
            ("Space", "Stop current movement"),
            (", / .", "Previous/Next camera"),
            ("", ""),
            ("CAMERA CONTROL", ""),
            ("e", "Edit all camera parameters"),
            ("i", "Edit IP address & port"),
            ("I", "Imaging settings (brightness/contrast/saturation)"),
            ("u", "Edit username"),
            ("h", "Edit password"),
            ("?", "Change camera TYPE"),
            ("a", "Add new camera"),
            ("d", "Delete current camera"),
            ("g", "Sync profiles & detect TYPE"),
            ("t", "Cycle through profiles"),
            ("", ""),
            ("STREAM CONTROL", ""),
            ("p", "Play stream (RTSP/V4L2/FILE)"),
            ("x", "MPV live control (image/speed/seek/pause)"),
            ("k", "Kill current stream player"),
            ("o", "Edit player command"),
            ("", ""),
            ("PRESETS", ""),
            ("F4", "Recall preset position"),
            ("F5", "Save current position as preset"),
            ("", ""),
            ("SETTINGS", ""),
            ("s / f", "Decrease/Increase speed"),
            ("m / l", "Decrease/Increase duration"),
            ("z", "Reset speed & duration"),
            ("w", "Save configuration"),
            ("c", "Change config file"),
            ("", ""),
            ("BATCH & DISCOVERY", ""),
            ("F2", "Discover cameras (ping/nmap/V4L2/SANE)"),
            ("F3", "Batch operations"),
            ("F6 / \\", "Global mute toggle (all playing cameras)"),
            ("", ""),
            ("HELP & SYSTEM", ""),
            ("F1", "Show this help"),
            ("1-9", "Jump to camera N"),
            ("q", "Quit application (double q for quick exit)"),
        ]

        print(f"{YLW}┌" + "─" * W + f"┐{RST}")
        print(f"{YLW}│{pad(' PTZ MASTER v' + VERSION + ' - KEYBOARD SHORTCUTS ', W)}│{RST}")
        print(f"{YLW}├" + "─" * W + f"┤{RST}")

        for action, keys in help_text:
            if action == "":
                print(f"{YLW}│{pad('', W)}│{RST}")
            elif action.isupper() and not keys:
                line = f" {action}"
                print(f"{YLW}│ {MAG}{line}{YLW}{' ' * (W - len(line) - 1)}│{RST}")
            else:
                left = f"  {GRN}{action}{RST}"
                right = f"{keys} "
                print(f"{YLW}│{pad(left, W - ansilen(right))}{right}{YLW}│{RST}")

        print(f"{YLW}├" + "─" * W + f"┤{RST}")
        print(f"{YLW}│{pad(f' Log file: {LOG_FILE}', W)}│{RST}")
        print(f"{YLW}└" + "─" * W + f"┘{RST}")
        print(f"\n{GRN}Press any key to continue...{RST}")
        self._wait_click_or_key()

# =============================================================================
# MAIN CAMERA CONTROL SCREEN (PTZMasterApp) End
# =============================================================================

# =============================================================================
# PLAYER MODE MPV CONTROL SCREEN PLAYER Start
# =============================================================================

class PlayerModeApp:
    def __init__(self, files: list, config_mgr: 'ConfigManager', start_idx: int = 0, loop_mode: bool = False):
        self.files      = files
        self.config_mgr = config_mgr
        self.config     = config_mgr.config
        self.idx        = start_idx
        self._cam       = None
        self._prof      = None
        self.loop_mode  = loop_mode  # DODANE
        atexit.register(self.cleanup)
        Terminal.capture_window_id()

    def _make_cam_prof(self, path: str):
        name = os.path.basename(path)
        # Szukaj istniejącej kamery FILE z tym samym plikiem — zachowaj image_params
        existing = next(
            (c for c in self.config.cameras
             if c.type == CameraType.FILE and c.file_path == path),
            None
        )
        if existing:
            cam = existing
        else:
            cam = Camera(
                name=name, ip="", mac="",
                cam_type=CameraType.FILE, file_path=path,
                profiles=[],
            )
            # Zastosuj DEFAULT_IMAGE_PARAMS dla nowych plików
            cam.image_params = Camera.DEFAULT_IMAGE_PARAMS.copy()
        # file_loop=True (--loop-file=inf) tylko gdy 1 plik w trybie loop.
        # Dla playlisty (>1 pliku) loop obsługuje _run_control_loop w Pythonie,
        # a mpv odtwarza każdy plik jeden raz i wychodzi (eof_stops).
        single_file = (len(self.files) == 1)
        cam.file_loop = self.loop_mode and single_file
        prof = CameraProfile(name="FILE", uri=path)
        cam.profiles = [prof]
        return cam, prof

    def _load(self, idx: int):
        if self._prof and self._prof.pid:
            try:
                import signal as _s
                os.kill(self._prof.pid, _s.SIGTERM)
            except Exception:
                pass
            PlayerWatchdog.stop_for_pid(self._prof.pid)
        self.idx   = idx
        path       = self.files[idx]
        if not os.path.isfile(path):
            notify(f"File not found: {os.path.basename(path)}", "error")
            logger.error(f"PlayerModeApp._load: file not found: {path}")
            return
        self._cam, self._prof = self._make_cam_prof(path)
        layout = self.config.layout.get("mpv_default") or WindowLayout(0, 0, 640, 360)
        Player._play_file(self._cam, layout,
                          global_mute=self.config.global_mute)

    def _save_as_camera(self, name: str):
        path = self.files[self.idx]
        for cam in self.config.cameras:
            if cam.type == CameraType.FILE and cam.file_path == path:
                notify(f"Camera '{cam.name}' already exists in list", "warning")
                return
        prof = CameraProfile(name="FILE", uri=path)
        cam = Camera(
            name=name, ip="", mac="",
            cam_type=CameraType.FILE, file_path=path,
            profiles=[prof],
        )
        cam.image_params = Camera.DEFAULT_IMAGE_PARAMS.copy()
        self.config.cameras.append(cam)
        self.config_mgr.save()
        notify(f"✅ Saved '{name}' to camera list", "info")

    def cleanup(self):
        if self._prof and self._prof.pid:
            try:
                os.kill(self._prof.pid, 15)
                logger.info(f"Killed mpv process {self._prof.pid}")
            except:
                pass

    def run(self):
        if not self.files:
            print("-p mode: no files to play.")
            return

        missing = [f for f in self.files if not os.path.isfile(f)]
        if missing:
            for m in missing:
                print(f"  ⚠ File not found: {m}")
            self.files = [f for f in self.files if os.path.isfile(f)]
            if not self.files:
                print("No available files.")
                return

        layout = self.config.layout.get("mpv_default") or WindowLayout(0, 0, 640, 360)
        self._load(self.idx)

        self._run_control_loop(layout, None)

    def _run_control_loop(self, layout, _on_eof=None):
        while self.idx < len(self.files):
            cam, prof = self._cam, self._prof

            result, loop_mode_new = _mpv_control_screen_player(
                cam, prof, self.files, self.idx,
                save_as_camera_fn=self._save_as_camera,
                config_mgr=self.config_mgr,
                loop_mode=self.loop_mode,
            )

            # persist loop state changed inside player
            self.loop_mode = loop_mode_new

            if isinstance(result, tuple) and result[0] == "goto":
                self._load(result[1])
            elif result == "next":
                if self.idx + 1 < len(self.files):
                    self._load(self.idx + 1)
                elif self.loop_mode:
                    self._load(0)
                else:
                    break
            elif result == "prev":
                if self.idx > 0:
                    self._load(self.idx - 1)
                elif self.loop_mode:
                    self._load(len(self.files) - 1)
                else:
                    break
            elif result == "eof_next":
                if self.idx + 1 < len(self.files):
                    self._load(self.idx + 1)
                elif self.loop_mode:
                    self._load(0)
                else:
                    break
            else:
                break

def _mpv_control_screen_player(cam, prof, files, current_idx,
                                save_as_camera_fn=None, config_mgr=None,
                                loop_mode=False, cam_mode=False,
                                all_cameras=None):
    """
    Uniwersalny ekran sterowania mpv.
    - cam_mode=True  → tryb kamer: SELECT / PAN / PTZ
    - cam_mode=False → tryb plików: SELECT / PAN
    """
    def _edit_pan_x(): pass
    def _edit_pan_y(): pass
    def _zoom_toggle(): pass
    def _edit_zoom(): pass
    import select as _sel
    import signal as _sig
    import shutil as _sh2
    import time as _time
    import os as _os
    import threading as _thr

    fd   = sys.stdin.fileno()
    STATUS_ROW = 18
    W    = 78
    MIN_H = 20
    MIN_W = 80

    # --------------------------------------------------------------------------
    # Tryb interfejsu – dla kamer: SELECT/PTZ/PAN, dla plików: SELECT/PAN
    # --------------------------------------------------------------------------
    if cam_mode:
        ui_mode = "SELECT"   # SELECT, PTZ, PAN
    else:
        ui_mode_file = "SELECT"   # SELECT, PAN

    def _term_size():
        try:
            sz = _sh2.get_terminal_size()
            return sz.columns, sz.lines
        except Exception:
            return 80, 24

    _sigwinch_flag = [False]
    def _sigwinch(sig, frame):
        _sigwinch_flag[0] = True
    try:
        _old_sigwinch = _sig.signal(_sig.SIGWINCH, _sigwinch)
    except Exception:
        _old_sigwinch = None

    GRN = Colors.GREEN; RED = Colors.RED; YLW = Colors.YELLOW
    CYN = Colors.CYAN;  DIM = Colors.DIM; RST = Colors.RESET
    BLU = Colors.BLUE;  WHT = Colors.WHITE; MAG = Colors.MAGENTA

    _mouse_off = mouse_off
    _mouse_on  = mouse_on

    def out(s): sys.stdout.write(s); sys.stdout.flush()

    # --------------------------------------------------------------------------
    # Inicjalizacja połączenia IPC
    # --------------------------------------------------------------------------
    _ctrl_socket = prof.ipc_path if (prof and prof.ipc_path) else None
    ctrl = MpvController(_ctrl_socket) if _ctrl_socket else None

    # --------------------------------------------------------------------------
    # Zmienne stanu odtwarzacza i interfejsu
    # --------------------------------------------------------------------------
    paused        = True
    pos_f         = 0.0
    dur_f         = 0.0
    fps           = 0.0
    stream_info   = "📊 —"
    last_msg      = "Player mode"
    _last_msg_t   = 0.0
    _MSG_HOLD     = 3.0
    loop_mode_local = loop_mode
    auto_fps      = 2.0
    auto_dir      = True
    auto_run      = False
    auto_accum    = 0.0
    _first_draw   = True
    _in_overlay   = False
    zoom_mode     = False
    zoom_val      = 0.0
    pan_x         = 0.0
    pan_y         = 0.0
    ZOOM_STEP     = 0.1
    ZOOM_MIN      = -3.0
    ZOOM_MAX      = 3.0
    PAN_STEP      = 0.1
    ab_a          = -1.0
    ab_b          = -1.0
    ab_active     = False
    _clipping     = False
    _rec_active   = False   # stream-record aktywny (cam_mode)
    _rec_path     = ""      # ścieżka aktualnego nagrania
    ptz_active = False          # czy trwa ruch PTZ
    ptz_progress = 0.0          # postęp ruchu (0..1)
    ptz_direction = ""          # opcjonalnie kierunek do wyświetlenia
    is_file_cam   = (cam is not None and cam.type == CameraType.FILE)
    last_step_dir = None
    _ip    = cam.image_params if hasattr(cam, 'image_params') else {}
    speed  = _ip.get("speed",  1.0)
    # global_mute ma priorytet — jeśli włączony globalnie, startuj wyciszony
    _global_mute = config_mgr.config.global_mute if config_mgr else False
    muted  = _global_mute or _ip.get("mute", False)

    PARAMS   = ["BRIGHTNESS", "CONTRAST", "SATURATION", "GAMMA", "HUE", "VOL"]
    PROP_MAP = {
        "BRIGHTNESS": "brightness", "CONTRAST": "contrast",
        "SATURATION": "saturation", "GAMMA": "gamma", "HUE": "hue",
        "VOL": "volume",
    }
    PARAM_RANGE = {
        "BRIGHTNESS": (-100, 100), "CONTRAST": (-100, 100),
        "SATURATION": (-100, 100), "GAMMA":    (-100, 100),
        "HUE":        (-100, 100), "VOL":      (0, 150),
    }
    ICONS = {
        "BRIGHTNESS": "💡", "CONTRAST": "🎭", "SATURATION": "🌈",
        "GAMMA": "✨", "HUE": "🎨", "VOL": "🔊",
    }
    JUMP_KEY = {"b": 0, "c": 1, "s": 2, "g": 3, "h": 4, "v": 5}
    values = {
        "BRIGHTNESS": _ip.get("brightness", 0),
        "CONTRAST":   _ip.get("contrast",   0),
        "SATURATION": _ip.get("saturation", 0),
        "GAMMA":      _ip.get("gamma",      0),
        "HUE":        _ip.get("hue",        0),
        "VOL":        _ip.get("volume",    100),
    }
    sel      = 0
    step     = 5

    AUTO_FPS_STEPS = [0.5, 1.0, 2.0, 3.0, 5.0, 8.0, 10.0, 15.0, 24.0]

    # --------------------------------------------------------------------------
    # Funkcje pomocnicze (seek, fetch, step, pause, itd.)
    # --------------------------------------------------------------------------
    def _seek(secs):
        nonlocal last_msg
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        ok = ctrl._send(["seek", secs, "relative"])
        last_msg = f"{'OK' if ok else 'ERR'} seek {secs:+}s"

    def _fetch_state():
        nonlocal pos_f, dur_f, fps, stream_info, paused, speed, last_msg, values
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        p  = ctrl.get_property("time-pos")
        d  = ctrl.get_property("duration")
        fp = ctrl.get_property("container-fps")
        sp = ctrl.get_property("speed")
        vo = ctrl.get_property("volume")
        pa = ctrl.get_property("pause")
        if p  is not None: pos_f  = float(p)
        if d  is not None: dur_f  = float(d)
        if fp and float(fp) > 0: fps = float(fp)
        if sp is not None: speed  = float(sp)
        if vo is not None: values["VOL"] = int(vo)
        if pa is not None and not auto_run: paused = bool(pa)
        # Drag & drop: śledź aktualny plik bezpośrednio z mpv
        _cur_path = ctrl.get_property("path")
        if _cur_path and _cur_path != getattr(_fetch_state, "_last_path", None):
            _fetch_state._last_path  = _cur_path
            _fetch_state._last_title = ctrl.get_property("media-title") or os.path.basename(_cur_path)
            _fetch_state._ffprobe_br = None  # wymuś ponowny odczyt bitrate
            logger.debug(f"mpv path changed: {_cur_path}")
        for pp in PARAMS:
            if pp == "VOL": continue
            v = ctrl.get_property(PROP_MAP[pp])
            if v is not None: values[pp] = int(v)
        # Video info (bez zmian)
        vc = ctrl.get_property("video-codec") or "—"
        w  = ctrl.get_property("width")
        h  = ctrl.get_property("height")
        if w and h:
            _fetch_state._vid_w = int(w)
            _fetch_state._vid_h = int(h)

        # Audio info — track-list jest najbardziej wiarygodne
        ac = None
        ar = None   # samplerate jako int lub None
        ach = None  # channel count jako int lub None
        abr = None  # bitrate z demux
        track_list = ctrl._send(["get_property", "track-list"])
        if track_list and track_list.get("error") == "success":
            for track in track_list.get("data", []):
                if track.get("type") == "audio" and track.get("selected"):
                    ac  = track.get("codec")
                    # demux-samplerate jest int — nie używaj "or" (0 jest falsy)
                    _sr = track.get("demux-samplerate")
                    ar  = _sr if _sr is not None else track.get("samplerate")
                    _ch = track.get("demux-channel-count")
                    ach = _ch if _ch is not None else track.get("audio-channels")
                    abr = track.get("demux-bitrate")
                    break
        # Fallback — stare właściwości (gdy track-list puste: RTSP przed buforem)
        if not ac:
            ac = ctrl.get_property("audio-codec-name") or ctrl.get_property("audio-codec")
        if ar is None:
            _ar = ctrl.get_property("audio-params/samplerate")
            ar  = _ar if (_ar is not None and _ar != 0) else None
        if ach is None:
            # audio-channels zwraca "auto-safe" — bezużyteczne
            # audio-params/channel-count zwraca int — poprawne
            _ach = ctrl.get_property("audio-params/channel-count")
            ach  = _ach if (_ach is not None and _ach != 0) else None

        vs = _codec_name(vc)
        as_ = _codec_name(ac) if ac else "—"
        ws = str(int(w)) if w else "—"
        hs = str(int(h)) if h else "—"
        fps_s = f" {fps:.1f}fps" if fps else ""
        ar_s  = f" {int(ar)//1000}kHz" if ar else ""
        # Formatowanie kanałów z int (nie string "auto-safe")
        if ach:
            _ACH_MAP = {
                1: "mono", 2: "stereo", 3: "3.0", 4: "4.0",
                6: "5.1",  7: "6.1",   8: "7.1",
            }
            try:
                _n = int(ach)
                ach_s = f" {_ACH_MAP.get(_n, str(_n)+'ch')}"
            except: ach_s = ""
        else:
            ach_s = ""
        buf_s = ctrl.get_property("demuxer-cache-duration")
        _fetch_state._buf_s_last = buf_s

        if is_file_cam:
            if not hasattr(_fetch_state, "_ffprobe_br"):
                try:
                    fp_path = files[current_idx] if files else (cam.file_path or "")
                    if fp_path:
                        import subprocess as _sp
                        def _try_br(args):
                            r = _sp.run(args, stdout=_sp.PIPE, stderr=_sp.PIPE, timeout=3)
                            out = (r.stdout or b"").decode("utf-8", errors="replace").strip()
                            for line in out.splitlines():
                                line = line.strip()
                                try:
                                    v = int(float(line))
                                    if v > 0: return v / 1_000_000
                                except: pass
                            return None
                        br = _try_br(["ffprobe", "-v", "quiet",
                                      "-show_entries", "format=bit_rate",
                                      "-of", "default=noprint_wrappers=1:nokey=1", fp_path])
                        if not br:
                            br = _try_br(["ffprobe", "-v", "quiet",
                                          "-select_streams", "v:0",
                                          "-show_entries", "stream=bit_rate",
                                          "-of", "default=noprint_wrappers=1:nokey=1", fp_path])
                        _fetch_state._ffprobe_br = br
                except Exception:
                    _fetch_state._ffprobe_br = None
            br_mbps = _fetch_state._ffprobe_br
            br_str = f"  \U0001f3ac {br_mbps:.1f}Mb" if br_mbps else ""
        else:
            br_raw = ctrl.get_property("video-bitrate")
            if br_raw and float(br_raw) > 0:
                br_mbps = float(br_raw) / 1_000_000
                _br_hist = getattr(_fetch_state, "_br_hist", [])
                _br_hist.append(br_mbps)
                if len(_br_hist) > 16: _br_hist.pop(0)
                _fetch_state._br_hist = _br_hist
            else:
                _br_hist = getattr(_fetch_state, "_br_hist", [])
            buf_ms_str = f" Buf:{int(float(buf_s)*1000)}ms" if buf_s is not None else ""
            if _br_hist:
                _sp_hi = max(_br_hist) or 1.0
                _sp_lo = min(_br_hist)
                _sp_rng = _sp_hi - _sp_lo
                if _sp_rng < _sp_hi * 0.05:  # stabilny → płaska linia
                    spark = "▄" * len(_br_hist)
                else:
                    spark = "".join(" ▁▂▃▄▅▆▇█"[min(8, int((_v - _sp_lo) / _sp_rng * 8))]
                                   for _v in _br_hist)
                br_str = "" if cam_mode else f"  🚀 {_br_hist[-1]:.1f}Mb{buf_ms_str} {spark}"
            else:
                br_str = ""
        stream_info = f"📊 {vs} {ws}x{hs}{fps_s}  🔊 {as_}{ar_s}{ach_s}{br_str}"
        last_msg = "OK"

    def _frame_step(forward=True):
        nonlocal last_msg, paused, last_step_dir, auto_run
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return None
        if not paused: ctrl.set_property("pause", True); paused = True
        EPSILON = 0.1
        if forward and dur_f > 0 and pos_f >= dur_f - EPSILON:
            last_msg = "⏭ end of file"; auto_run = False; return "eof"
        if not forward and pos_f <= EPSILON:
            last_msg = "⏮ start of file"; auto_run = False; return None
        cmd = ["frame-step"] if forward else ["frame-back-step"]
        ctrl._send(cmd); last_step_dir = forward
        last_msg = f"{'>>|' if forward else '|<<'}"
        return None

    def _toggle_pause():
        nonlocal paused, auto_run, last_msg
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        paused = not paused
        ctrl.set_property("pause", paused)
        if not paused: auto_run = False
        last_msg = "⏸ PAUSED" if paused else "▶ PLAYING"

    def _auto_toggle_dir():
        nonlocal auto_dir; auto_dir = not auto_dir
        last_msg = f"dir → {'►' if auto_dir else '◄'}"

    def _auto_toggle_run():
        nonlocal auto_run, auto_accum
        if not paused: last_msg = "Pause first"; return
        auto_run = not auto_run; auto_accum = 0.0
        last_msg = "▶ RUN" if auto_run else "■ STP"

    def _set_val(param, delta):
        nonlocal last_msg
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        mn, mx = PARAM_RANGE.get(param, (-100, 100))
        values[param] = max(mn, min(mx, values[param] + delta))
        if param == "VOL":
            ok = ctrl.set_property("volume", values[param])
        else:
            ok = ctrl.set_property(PROP_MAP[param], values[param])
        last_msg = f"{'OK' if ok else 'ERR'} {param}={values[param]:+d}" if param != "VOL" else f"{'OK' if ok else 'ERR'} VOL={values[param]:3d}%"

    def _reset_image_settings():
        nonlocal speed, muted, last_msg, values
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        for p in PARAMS:
            if p == "VOL": values[p] = 100; ctrl.set_property("volume", 100)
            else:          values[p] = 0;   ctrl.set_property(PROP_MAP[p], 0)
        # speed = 1.0; ctrl.set_property("speed", 1.0)
        # muted = False; ctrl.set_property("mute", False)
        last_msg = "Reset image settings OK"

    def _reset_all_settings():
        nonlocal speed, muted, last_msg, values
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        for p in PARAMS:
            if p == "VOL": values[p] = 100; ctrl.set_property("volume", 100)
            else:          values[p] = 0;   ctrl.set_property(PROP_MAP[p], 0)
        speed = 1.0; ctrl.set_property("speed", 1.0)
        muted = False; ctrl.set_property("mute", False)
        last_msg = "Reset all settings (image + speed)"

    def _set_speed(delta):
        nonlocal speed, last_msg
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        speed = 1.0 if delta == 0.0 else round(max(0.1, min(10.0, speed + delta)), 2)
        ctrl.set_property("speed", speed)
        last_msg = f"speed={speed:.2f}x"

    def _toggle_mute():
        nonlocal muted, last_msg
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        muted = not muted
        ctrl.set_property("mute", muted)
        # Synchronizuj global_mute — następna kamera/plik dziedziczy
        if config_mgr:
            config_mgr.config.global_mute = muted
        last_msg = f"🔇 Global mute {'ON' if muted else 'OFF'}"

    def _zoom_apply():
        if not ctrl: return
        _pid = prof.pid if prof else None
        if not (_pid and ProcessManager.is_running(_pid)): return
        ctrl.set_property("video-zoom",  zoom_val)
        ctrl.set_property("video-pan-x", pan_x)
        ctrl.set_property("video-pan-y", pan_y)

    def _zoom_in():
        nonlocal zoom_val, zoom_mode, last_msg
        zoom_val = min(zoom_val + ZOOM_STEP, ZOOM_MAX)
        zoom_mode = True
        _zoom_apply()
        last_msg = f"🔍 Zoom: {2.0**zoom_val:.2f}x"

    def _zoom_out():
        nonlocal zoom_val, zoom_mode, last_msg
        zoom_val = max(zoom_val - ZOOM_STEP, ZOOM_MIN)
        zoom_mode = True
        _zoom_apply()
        last_msg = f"🔍 Zoom: {2.0**zoom_val:.2f}x"

    def _zoom_zero():
        nonlocal zoom_val, zoom_mode, last_msg
        zoom_val = 0.0
        zoom_mode = False   # lub True? Dla 0 nie ma zoomu, ale pan może być niezależne
        _zoom_apply()
        last_msg = "🔍 Zoom → 1.0x"

    def _zoom_reset():
        nonlocal zoom_val, pan_x, pan_y, zoom_mode, last_msg
        zoom_val = 0.0
        pan_x = 0.0
        pan_y = 0.0
        zoom_mode = False
        _zoom_apply()
        last_msg = "🔍 Zoom+Pan reset"

    def _pan(dx, dy):
        nonlocal pan_x, pan_y, zoom_mode, zoom_val, last_msg
        if not zoom_mode:
            if zoom_val == 0.0: zoom_val = ZOOM_STEP
            zoom_mode = True
        pan_x = max(-0.5, min(0.5, pan_x + dx))
        pan_y = max(-0.5, min(0.5, pan_y + dy))
        _zoom_apply()
        last_msg = f"🔍 Pan x:{pan_x:+.2f} y:{pan_y:+.2f}"

    def _pan_center():
        nonlocal pan_x, pan_y, last_msg
        pan_x = 0.0; pan_y = 0.0
        _zoom_apply()
        last_msg = "🔍 Pan → center"

    def _screenshot():
        nonlocal last_msg
        if not ctrl or not ctrl.is_alive(): last_msg = "mpv disconnected"; return
        ok = ctrl._send(["screenshot", "video"])
        last_msg = "📸 screenshot OK" if ok else "screenshot ERR"

    def _save_image_params():
        nonlocal last_msg
        if not cam: last_msg = "No camera"; return
        ip = {
            "brightness": values["BRIGHTNESS"], "contrast":   values["CONTRAST"],
            "saturation": values["SATURATION"], "gamma":      values["GAMMA"],
            "hue":        values["HUE"],        "volume":     values["VOL"],
            "mute":       muted,                "speed":      speed,
        }
        cam.image_params = ip
        if config_mgr: config_mgr.save()
        last_msg = f"💾 Saved settings for {cam.name}"

    def _restore_image_settings():
        """Load saved image parameters, speed, and mute from cam.image_params."""
        nonlocal values, speed, muted, last_msg
        if not cam:
            last_msg = "No camera"
            return
        saved = cam.image_params.copy()
        for p in PARAMS:
            key = p.lower() if p != "VOL" else "volume"
            val = saved.get(key, 0 if p != "VOL" else 100)
            values[p] = val
            if ctrl and ctrl.is_alive():
                if p == "VOL":
                    ctrl.set_property("volume", val)
                else:
                    ctrl.set_property(PROP_MAP[p], val)
        speed = saved.get("speed", 1.0)
        if ctrl and ctrl.is_alive():
            ctrl.set_property("speed", speed)
        muted = saved.get("mute", False)
        if ctrl and ctrl.is_alive():
            ctrl.set_property("mute", muted)
        last_msg = f"Loaded saved settings for {cam.name}"

    def _fmt_time(s):
        s = int(s); h, m, sec = s//3600, (s%3600)//60, s%60
        return f"{h}:{m:02d}:{sec:02d}" if h else f"{m}:{sec:02d}"

    def _prog_bar(pos, dur, width=22):
        if dur <= 0: return f"{DIM}{'─' * width}{RST}"
        cur = max(0, min(width-1, int(pos / dur * width)))
        a_pos = max(0, min(width-1, int(ab_a / dur * width))) if (ab_a >= 0 and dur > 0) else -1
        b_pos = max(0, min(width-1, int(ab_b / dur * width))) if (ab_b >= 0 and dur > 0) else -1
        bar_chars = []
        for j in range(width):
            if   j == a_pos and j == b_pos: bar_chars.append(f"{YLW}⌂{RST}")
            elif j == a_pos:                bar_chars.append(f"{GRN if ab_active else YLW}A{RST}")
            elif j == b_pos:                bar_chars.append(f"{GRN if ab_active else YLW}B{RST}")
            elif j < cur:
                if ab_active and a_pos >= 0 and b_pos > a_pos and a_pos < j < b_pos:
                    bar_chars.append(f"{GRN}▓{RST}")
                else:
                    bar_chars.append(f"{GRN}█{RST}")
            else:
                if ab_active and a_pos >= 0 and b_pos > a_pos and a_pos < j < b_pos:
                    bar_chars.append(f"{GRN}░{RST}")
                else:
                    bar_chars.append(f"{DIM}─{RST}")
        return "".join(bar_chars)

    def bar(param, width=20):
        val = values[param]
        if param == "VOL":
            filled = int(val / 150 * width)
            col = RED if val <= 0 else (YLW if val <= 30 else (GRN if val <= 100 else RED))
        else:
            filled = int((val + 100) / 200 * width)
            col = GRN if val == 0 else (BLU if val < 0 else (YLW if val < 50 else RED))
        return f"{col}{chr(9608) * filled}{RST}{DIM}{chr(9617) * (width - filled)}{RST}"

    # --------------------------------------------------------------------------
    # AB-Loop i funkcje pomocnicze dla klipów
    # --------------------------------------------------------------------------
    def _ab_set_a():
        nonlocal ab_a, ab_b, ab_active, last_msg
        ab_a = pos_f
        ab_active = False
        if ctrl and ctrl.is_alive():
            ctrl._send(["set_property", "ab-loop-a", "no"])
            ctrl._send(["set_property", "ab-loop-b", "no"])
        last_msg = f"[a] ▷ {_fmt_time(ab_a)} — naciśnij [a] ponownie dla stop"

    def _ab_set_b():
        nonlocal ab_b, ab_active, last_msg
        if ab_a < 0:
            last_msg = "Naciśnij [a] aby ustawić start"
            return
        ab_b = pos_f
        if ab_b <= ab_a:
            last_msg = "[a] stop musi być po starcie"
            return
        ab_active = True
        if ctrl and ctrl.is_alive():
            ctrl._send(["set_property", "ab-loop-a", ab_a])
            ctrl._send(["set_property", "ab-loop-b", ab_b])
            ctrl._send(["seek", ab_a, "absolute"])
            ctrl._send(["set_property", "pause", False])
        last_msg = f"[a] loop: {_fmt_time(ab_a)}↔{_fmt_time(ab_b)}  — [a] aby wyczyścić"

    def _ab_clear():
        nonlocal ab_a, ab_b, ab_active, last_msg
        ab_a = -1.0; ab_b = -1.0; ab_active = False
        if ctrl and ctrl.is_alive():
            ctrl._send(["set_property", "ab-loop-a", "no"])
            ctrl._send(["set_property", "ab-loop-b", "no"])
        last_msg = "[a] loop wyłączony"

    def _rec_toggle():
        """cam_mode: start/stop nagrywania strumienia przez mpv stream-record."""
        nonlocal _rec_active, _rec_path, last_msg
        if not ctrl or not ctrl.is_alive():
            last_msg = "mpv disconnected"; return
        if not _rec_active:
            import datetime as _dt
            _ts = _dt.datetime.now().strftime("%y-%m-%d-%H.%M.%S")
            _cn = (cam.name if cam else "cam").replace("/", "_").replace(" ", "_")
            _rec_path = os.path.join(REC_DIR, f"{_cn}-{_ts}.ts")
            if ctrl.set_property("stream-record", _rec_path):
                _rec_active = True
                last_msg = f"⏺ REC → {os.path.basename(_rec_path)}"
                logger.info(f"stream-record START: {_rec_path}")
            else:
                last_msg = "⏺ REC start failed"
        else:
            ctrl.set_property("stream-record", "")
            _rec_active = False
            _saved = _rec_path
            _rec_path = ""
            # Pełna ścieżka — oznacz gdy fallback do /tmp
            _in_tmp = _saved.startswith("/tmp")
            _lbl = "[/tmp] " if _in_tmp else ""
            last_msg = f"⏹ REC {_lbl}{_saved}"
            logger.info(f"stream-record STOP: {_saved}")

    def _parse_time(s: str) -> float:
        s = s.strip()
        try:
            if ':' in s:
                parts = s.split(':')
                return int(parts[0]) * 60 + float(parts[1])
            else:
                return float(s)
        except (ValueError, IndexError):
            return -1.0

    def _status_prompt(prompt: str) -> None:
        right = f"{CYN}v{VERSION}{RST}"
        content = f" {prompt}\033[5m█\033[0m"
        padding = " " * max(0, W - ansilen(content) - ansilen(right) - 2)
        sys.stdout.write(
            f"\033[{STATUS_ROW}H\r{BLU}║{RST}{content}{padding}{right}{BLU}║{RST}"
        )
        prompt_vis = len(re.sub(r'\x1b\[[0-9;]*[a-zA-Z]', '', f" {prompt}"))
        sys.stdout.write(f"\033[{STATUS_ROW};{2 + prompt_vis}H")
        sys.stdout.flush()

    def _ask_time_input(prompt: str) -> float:
        nonlocal last_msg
        _draw()
        _status_prompt(prompt)
        try:
            with _cooked_input(fd):
                entered = input()
            return _parse_time(entered)
        except (EOFError, KeyboardInterrupt):
            return -1.0
        finally:
            last_msg = "OK"

    def _ab_edit_a():
        nonlocal ab_a, ab_b, ab_active, last_msg
        val = _ask_time_input(f"Set A (current {_fmt_time(int(ab_a)) if ab_a>=0 else '--'}): ")
        if val < 0:
            last_msg = "AB: invalid time"
            return
        ab_a = val
        ab_b = -1.0
        ab_active = False
        if ctrl and ctrl.is_alive():
            ctrl._send(["set_property", "ab-loop-a", "no"])
            ctrl._send(["set_property", "ab-loop-b", "no"])
            ctrl._send(["seek", ab_a, "absolute"])
        last_msg = f"[A] set {_fmt_time(int(ab_a))}"

    def _ab_edit_b():
        nonlocal ab_b, ab_active, last_msg
        if ab_a < 0:
            last_msg = "Set [A] first"
            return
        val = _ask_time_input(f"Set B (A={_fmt_time(int(ab_a))}): ")
        if val < 0 or val <= ab_a:
            last_msg = "AB: B must be > A"
            return
        ab_b = val
        ab_active = True
        if ctrl and ctrl.is_alive():
            ctrl._send(["set_property", "ab-loop-a", ab_a])
            ctrl._send(["set_property", "ab-loop-b", ab_b])
            ctrl._send(["seek", ab_a, "absolute"])
            ctrl._send(["set_property", "pause", False])
        last_msg = f"[A]{_fmt_time(int(ab_a))}↔[B]{_fmt_time(int(ab_b))} loop ON"

    def _ask_clip_options():
        nonlocal last_msg
        opts = {"codec": "copy", "crf": 23, "use_pan_zoom": False}
        def _ask_inline(prompt, history=""):
            nonlocal last_msg
            _status_prompt(f"{history}{prompt}")
            try:
                with _cooked_input(fd):
                    return input()
            except (EOFError, KeyboardInterrupt):
                return None
        try:
            ans = _ask_inline("Codec [1=copy 2=x264 3=x265 q=cancel]: ")
            if ans is None or ans.strip().lower() == 'q':
                last_msg = "🎬 Cancelled"
                return None
            if ans.strip() == "2": opts["codec"] = "x264"
            elif ans.strip() == "3": opts["codec"] = "x265"
            hist = f"Codec={opts['codec']}  "
            if opts["codec"] != "copy":
                ans = _ask_inline("CRF [0-51, ENTER=23]: ", hist)
                if ans is None: return None
                try: opts["crf"] = max(0, min(51, int(ans.strip())))
                except ValueError: pass
                hist += f"CRF={opts['crf']}  "
            if zoom_mode and (zoom_val != 0.0 or pan_x != 0.0 or pan_y != 0.0):
                ans = _ask_inline("Pan/zoom mpv? [y/N]: ", hist)
                if ans is None: return None
                opts["use_pan_zoom"] = (ans.strip().lower() == 'y')
            last_msg = f"🎬 {hist.strip()}"
        except Exception:
            last_msg = "🎬 Cancelled"
            return None
        return opts

    def _extract_clip_current():
        nonlocal last_msg, _clipping
        # REC działa tylko dla plików — w cam_mode files[] to obiekty Camera
        if not is_file_cam:
            last_msg = "🎬 REC tylko dla plików (nie dla strumieni)"
            return
        if not ab_active or ab_a < 0 or ab_b <= ab_a:
            last_msg = "🎬 Set AB loop first ([A] twice)"
            return
        fp = files[current_idx] if (files and current_idx < len(files)) else ""
        # Upewnij się że fp to ścieżka do pliku, nie obiekt Camera
        if not isinstance(fp, str):
            fp = getattr(fp, "file_path", "") or ""
        if not fp or not os.path.isfile(fp):
            last_msg = "🎬 No file path"
            return
        # Pliki audio nie mają video — AB-loop clip extraction nie ma sensu
        _AUDIO_EXTS = {'.mp3', '.flac', '.ogg', '.opus', '.m4a',
                       '.aac', '.wav', '.wma', '.ape', '.mka'}
        if os.path.splitext(fp)[1].lower() in _AUDIO_EXTS:
            last_msg = "🎬 Clip extraction niedostępny dla plików audio"
            return
        _has_filters = any(values.get(p, 0) != 0 for p in ["BRIGHTNESS","CONTRAST","SATURATION","GAMMA","HUE"])
        _has_zoom    = zoom_mode and (zoom_val != 0.0 or pan_x != 0.0 or pan_y != 0.0)
        if _has_filters or _has_zoom:
            _draw()
            opts = _ask_clip_options()
            if opts is None:
                last_msg = "🎬 Cancelled"
                return
        else:
            opts = {"codec": "copy", "crf": 23, "use_pan_zoom": False}
        extra_vf = None
        if opts["use_pan_zoom"] and _has_zoom:
            _vid_w = getattr(_fetch_state, "_vid_w", None)
            _vid_h = getattr(_fetch_state, "_vid_h", None)
            if not _vid_w or not _vid_h:
                try:
                    import subprocess as _sp2
                    _r = _sp2.run(
                        ["ffprobe", "-v", "quiet", "-select_streams", "v:0",
                         "-show_entries", "stream=width,height",
                         "-of", "csv=p=0", fp],
                        stdout=_sp2.PIPE, stderr=_sp2.DEVNULL, timeout=3
                    )
                    _wh = _r.stdout.decode().strip().split(",")
                    _vid_w, _vid_h = int(_wh[0]), int(_wh[1])
                except Exception:
                    _vid_w, _vid_h = 320, 240
            scale = 2.0 ** zoom_val
            w_src = max(2, int(_vid_w / scale))
            h_src = max(2, int(_vid_h / scale))
            x_off = int((_vid_w - w_src) / 2 + pan_x * _vid_w)
            y_off = int((_vid_h - h_src) / 2 + pan_y * _vid_h)
            x_off = max(0, min(_vid_w - w_src, x_off))
            y_off = max(0, min(_vid_h - h_src, y_off))
            extra_vf = f"crop={w_src}:{h_src}:{x_off}:{y_off},scale={_vid_w}:{_vid_h}"
        codec_map = {"copy": None, "x264": "libx264", "x265": "libx265"}
        vcodec = codec_map.get(opts["codec"])
        ok = _extract_clip(
            fp, ab_a, ab_b,
            brightness=values.get("BRIGHTNESS", 0),
            contrast=values.get("CONTRAST", 0),
            saturation=values.get("SATURATION", 0),
            gamma=values.get("GAMMA", 0),
            hue=values.get("HUE", 0),
            vcodec_override=vcodec,
            crf=opts["crf"],
            extra_vf=extra_vf,
        )
        if ok:
            _clipping = True
            codec_tag = f" [{opts['codec']}]" if opts["codec"] != "copy" else ""
            last_msg = f"🎬{codec_tag} {_fmt_time(ab_a)}–{_fmt_time(ab_b)} → clip_{int(ab_a)}_{int(ab_b)}.mp4"
            def _monitor_clip():
                nonlocal _clipping, last_msg
                clip_log = f"{fp}_clip_{int(ab_a)}_{int(ab_b)}.mp4.ffmpeg.log"
                prev_size = -1
                for _ in range(120):
                    _time.sleep(0.5)
                    try:
                        cur_size = os.path.getsize(clip_log)
                        if cur_size == prev_size and cur_size > 0:
                            break
                        prev_size = cur_size
                    except OSError:
                        break
                _clipping = False
                last_msg = f"🎬 Gotowe: clip_{int(ab_a)}_{int(ab_b)}.mp4"
                # Usuń plik logu ffmpeg po zakończeniu
                try:
                    if os.path.exists(clip_log):
                        os.unlink(clip_log)
                        logger.debug(f"Removed ffmpeg log: {clip_log}")
                except OSError as _e:
                    logger.debug(f"Could not remove ffmpeg log: {_e}")
            _thr.Thread(target=_monitor_clip, daemon=True).start()
        else:
            last_msg = "🎬 Clip extraction failed"

    def _auto_fps_change(delta):
        nonlocal auto_fps, last_msg
        try:    aidx = AUTO_FPS_STEPS.index(auto_fps)
        except: aidx = 2
        aidx = max(0, min(len(AUTO_FPS_STEPS)-1, aidx + delta))
        auto_fps = AUTO_FPS_STEPS[aidx]
        last_msg = f"auto fps → {auto_fps:.1f}"

    def _ask_save_name():
        name_default = os.path.splitext(os.path.basename(files[current_idx]))[0]
        old = termios.tcgetattr(fd)
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
        try:
            out(f"\033[2J\033[H {YLW}Camera name [{name_default}]: {RST}")
            sys.stdout.flush()
            entered = input()
            name = entered.strip() if entered.strip() else name_default
            return name
        finally:
            sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
            sys.stdout.flush()
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
            tty.setraw(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()

    def _ask_duration_input():
        """Prompt user to enter new duration (0.1 .. 5.0)."""
        nonlocal last_msg
        old = termios.tcgetattr(fd)
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        # Wyłącz śledzenie myszy przed wejściem w cooked
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        # Opróżnij bufor wejściowy – usuń zalegające zdarzenia myszy/klawiszy
        try:
            termios.tcflush(fd, termios.TCIFLUSH)
        except Exception:
            pass
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
        try:
            sys.stdout.write(f"\033[2J\033[H {YLW}New duration (0.1-5.0s) [{cam.duration:.1f}]: {RST}")
            sys.stdout.flush()
            entered = input()
            if entered.strip():
                val = float(entered.strip())
                return max(0.1, min(5.0, val))
        except (ValueError, EOFError):
            pass
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
            tty.setraw(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()
        return None

    def _ask_speed_input():
        """Prompt user to enter new PTZ speed (0.1 .. 1.0)."""
        nonlocal last_msg
        old = termios.tcgetattr(fd)
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        try:
            termios.tcflush(fd, termios.TCIFLUSH)
        except Exception:
            pass
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
        try:
            sys.stdout.write(f"\033[2J\033[H {YLW}New PTZ speed (0.1-1.0) [{cam.speed:.1f}]: {RST}")
            sys.stdout.flush()
            entered = input()
            if entered.strip():
                val = float(entered.strip())
                return max(0.1, min(1.0, val))
        except (ValueError, EOFError):
            pass
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
            tty.setraw(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()
        return None

    def _edit_pan_x():
        nonlocal pan_x, last_msg
        old = termios.tcgetattr(fd)
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        try:
            termios.tcflush(fd, termios.TCIFLUSH)
        except Exception:
            pass
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
        try:
            sys.stdout.write(f"\033[2J\033[H {YLW}New pan X (-0.5..0.5) [{pan_x:+.2f}]: {RST}")
            sys.stdout.flush()
            entered = input()
            if entered.strip():
                val = float(entered.strip())
                pan_x = max(-0.5, min(0.5, val))
                _zoom_apply()
                last_msg = f"Pan X set to {pan_x:+.2f}"
        except (ValueError, EOFError):
            pass
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
            tty.setraw(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()

    def _edit_pan_y():
        nonlocal pan_y, last_msg
        old = termios.tcgetattr(fd)
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        try:
            termios.tcflush(fd, termios.TCIFLUSH)
        except Exception:
            pass
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
        try:
            sys.stdout.write(f"\033[2J\033[H {YLW}New pan Y (-0.5..0.5) [{pan_y:+.2f}]: {RST}")
            sys.stdout.flush()
            entered = input()
            if entered.strip():
                val = float(entered.strip())
                pan_y = max(-0.5, min(0.5, val))
                _zoom_apply()
                last_msg = f"Pan Y set to {pan_y:+.2f}"
        except (ValueError, EOFError):
            pass
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
            tty.setraw(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()

    def _edit_zoom():
        nonlocal zoom_val, last_msg
        old = termios.tcgetattr(fd)
        cooked = termios.tcgetattr(fd)
        cooked[3] |= termios.ECHO | termios.ICANON
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        try:
            termios.tcflush(fd, termios.TCIFLUSH)
        except Exception:
            pass
        termios.tcsetattr(fd, termios.TCSADRAIN, cooked)
        try:
            sys.stdout.write(f"\033[2J\033[H {YLW}New zoom level (0.0..4.0) [{zoom_val:.1f}]: {RST}")
            sys.stdout.flush()
            entered = input()
            if entered.strip():
                val = float(entered.strip())
                zoom_val = max(0.0, min(4.0, val))
                _zoom_apply()
                last_msg = f"Zoom set to {2.0**zoom_val:.2f}x"
        except (ValueError, EOFError):
            pass
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old)
            tty.setraw(fd)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()
    # --------------------------------------------------------------------------
    # Główna funkcja rysująca
    # --------------------------------------------------------------------------
    def _draw():
        if _in_overlay: return
        _buf = []
        def _w(s): _buf.append(s)

        nonlocal _first_draw, last_msg, _last_msg_t

        _tw, _th = _term_size()
        if _th < MIN_H or _tw < MIN_W:
            _w("\033[2J\033[H\033[?25l")
            _w(f"\r{YLW}⚠ Terminal za mały: {_tw}x{_th}  (min {MIN_W}x{MIN_H}){RST}\033[K\r\n")
            _w(f"\r{DIM}Powiększ okno terminala{RST}\033[K\r\n")
            sys.stdout.write("".join(_buf)); sys.stdout.flush()
            return

        _w("\033[?25l")
        if _first_draw: _w("\033[2J\033[H"); _first_draw = False
        else: _w("\033[H")
        _w(f"\r{BLU}╔{'═'*W}╗{RST}\033[K\r\n")

        def row(content):
            _w(f"\r{BLU}║{RST}{pad(content, W)}{BLU}║{RST}\033[K\r\n")
        def sep():
            _w(f"\r{BLU}╠{'═'*W}╣{RST}\033[K\r\n")

        # --- Nagłówek ---------------------------------------------------------
        if cam_mode:
            cur_cam = (all_cameras or files)[current_idx]
            cam_name = getattr(cur_cam, 'name', str(files[current_idx]))
            cam_ip = getattr(cur_cam, 'ip', '')
            fname = f"{cam_name} [{cam_ip}]"
            loop_char = "🔁" if loop_mode_local else "⏹ "
            nav_prev = f"{YLW}[◄,]{RST}"
            nav_next = f"{YLW}[.►]{RST}"
            idx_str  = f"{current_idx+1}/{len(files)}"
            lewa_czesc = f" 🎥 {nav_prev} {idx_str}".ljust(15)
            if len(fname) > 36: fname = fname[:33] + "..."
            row(f"{lewa_czesc} {fname:<38} {nav_next} {YLW}[P]{RST}T{YLW}[Z]{RST} {YLW}[L]{RST}{loop_char} {YLW}[K>]{RST}🎥")
        else:
            # Drag & drop: użyj tytułu z IPC jeśli mpv gra inny plik
            _ipc_title = getattr(_fetch_state, "_last_title", None)
            _ipc_path  = getattr(_fetch_state, "_last_path", None)
            _static    = files[current_idx] if current_idx < len(files) else ""
            if _ipc_path and os.path.abspath(_ipc_path) != os.path.abspath(_static):
                fname = (_ipc_title or os.path.basename(_ipc_path))
                fname = fname + " ↕"  # wskaźnik że to plik wrzucony do mpv
            else:
                fname = os.path.basename(_static)
            loop_char = "🔁" if loop_mode_local else "⏹ "
            nav_prev = f"{YLW}[◄,]{RST}"
            nav_next = f"{YLW}[.►]{RST}"
            idx_str  = f"{current_idx+1}/{len(files)}"
            lewa_czesc = f" 🎬 {nav_prev} {idx_str}".ljust(15)
            if len(fname) > 36: fname = fname[:33] + "..."
            row(f"{lewa_czesc} {fname:<38} {nav_next} {YLW}[P]{RST}list {YLW}[L]{RST}{loop_char} {YLW}[K>]{RST}🎥")

        row(f" {stream_info}")
        sep()

        # --- Pasek postępu / AB-loop ------------------------------------------
        ts = f"{_fmt_time(pos_f)} / {_fmt_time(dur_f)}"
        _fps_vis = f"  {fps:.0f}fps" if fps > 0 else ""  # widoczna długość bez ANSI
        fps_tag  = f"  {DIM}{fps:.0f}fps{RST}" if fps > 0 else ""
        _L, _R = 48, 29
        # ⏱(2)+spacje(2)=4, spacja(1) między pb a ts — reszta na pasek
        _pb_w = max(8, _L - 4 - 1 - len(ts) - len(_fps_vis))
        pb = _prog_bar(pos_f, dur_f, width=_pb_w)
        _blink = int(_time.time() * 2) % 2
        _A_fix   = f"{YLW}[A]{RST}"
        _A_blink = f"{YLW}[A]{RST}" if _blink else f"{DIM}[A]{RST}"
        if ab_active:
            ab_right = f" Loop {_A_fix}{RED}{_fmt_time(ab_a)}{RST}↔{GRN}[B]{RST}{RED}{_fmt_time(ab_b)}{RST}"
        elif ab_a >= 0 and ab_b < 0:
            ab_right = f" Set {DIM}[A]{RST}{YLW}{_fmt_time(ab_a)}{RST}─{_A_blink}{DIM}···{RST} end"
        else:
            ab_right = f" Set {_A_fix}{DIM}···{RST} loop start"
        l1_left = f" ⏱ {pb} {ts}{fps_tag}"
        row(f"{pad(l1_left, _L)}{BLU}║{RST}{pad(ab_right, _R)}")

        # --- Bitrate / REC ----------------------------------------------------
        _SPARK16 = " ▁▂▃▄▅▆▇█"
        _br_hist_draw = getattr(_fetch_state, "_br_hist", []) if not is_file_cam else []
        _br_file = getattr(_fetch_state, "_ffprobe_br", None) if is_file_cam else None
        if is_file_cam and _br_file:
            br_val, spark16 = _br_file, "─" * 16
        elif _br_hist_draw:
            br_val = _br_hist_draw[-1]
            _sp_hi  = max(_br_hist_draw) or 1.0
            _sp_lo  = min(_br_hist_draw)
            _sp_rng = _sp_hi - _sp_lo
            _data16 = _br_hist_draw[-16:]
            if _sp_rng < _sp_hi * 0.05:  # stabilny bitrate → płaska linia ▄
                spark16 = ("▄" * len(_data16)).ljust(16)
            else:                         # min-max: pełen zakres paska
                spark16 = "".join(
                    _SPARK16[min(8, int((_v - _sp_lo) / _sp_rng * 8))]
                    for _v in _data16
                ).ljust(16)
        else:
            br_val, spark16 = 0.0, " " * 16
        buf_ms = int(float(getattr(_fetch_state, "_buf_s_last", 0) or 0) * 1000)
        buf_str = f" Buf:{buf_ms}ms" if buf_ms > 0 else ""
        if _rec_active:
            # cam_mode: aktywne nagrywanie stream-record — miga czerwony
            _R_col = RED if _blink else WHT
            rec_dot = f"{_R_col}●{RST}"; _RR = f"{_R_col}[A]{RST}"
            _rec_short = os.path.basename(_rec_path)[:20] if _rec_path else ""
            rec_right = f" {rec_dot} {_RR} {DIM}{_rec_short}{RST}"
        elif _clipping:
            _R_col = RED if _blink else YLW
            rec_dot = f"{_R_col}●{RST}"; _RR = f"{_R_col}[R]{RST}"
            rec_right = f" {rec_dot} {_RR}EC"
        elif ab_active:
            rec_dot = f"{GRN}●{RST}"; _RR = f"{GRN}[R]{RST}"
            rec_right = f" {rec_dot} {_RR}EC / {YLW}Clear[A]{RST} Loop"
        else:
            _A_lbl = f"{YLW}[A]{RST}" if cam_mode else f"{DIM}[R]{RST}"
            rec_dot = f"{DIM}○{RST}"
            _hint   = f" REC" if cam_mode else f"EC"
            rec_right = f" {rec_dot} {_A_lbl}{_hint}"
            if not cam_mode and ab_active:
                rec_right = f" {GRN}●{RST} {GRN}[R]{RST}EC / {YLW}Clear[A]{RST} Loop"
        l2_left = f" 🚀 {br_val:.1f}Mb [{DIM}{spark16}{RST}]{buf_str}"
        row(f"{pad(l2_left, _L)}{BLU}║{RST}{pad(rec_right, _R)}")

        # --- Kontrolki play/pause ---------------------------------------------
        if paused:
            dir_indicator = f"◄|{GRN}►{RST}" if auto_dir else f"{RED}◄{RST}|►"
            if auto_run:
                run_indicator = f"{RED}■ STP{RST}"; pause_icon = f"{RED}⏸{RST}"
                _r_btn = f"{RED if _blink else YLW}[r]{RST}"
            else:
                run_indicator = f"{GRN}▶ RUN{RST}"; pause_icon = f"{GRN}⏯{RST}"
                _r_btn = f"{DIM}[r]{RST}"
            row(f" {pause_icon} {YLW}[SPACE]{RST} {YLW}[ ←[]→ ]{RST} ║ FRAME MODE: {YLW}[D]{RST} {dir_indicator} ║ {_r_btn} {run_indicator} ║ Pg {YLW}[↑]{RST}{YLW}[↓]{RST} {auto_fps:.1f}fps")
        else:
            sp_col = GRN if speed == 1.0 else YLW
            row(f" ⏸ {YLW}[SPACE]{RST} ▶ PLAYING  {YLW}[-]{RST} -30s  {YLW}[+]{RST} +30s  🚀 Sp{YLW}[E]{RST}ed  {YLW}[D]{RST}🐢  {YLW}[F]{RST}🐇  : {sp_col}{speed:.2f}x{RST}")

        sep()

        # --- Linia Select / Reset Progress ------------------------------------
        if ptz_active:
            # animowany pasek postępu PTZ
            bar_len = 10
            filled = int(ptz_progress * bar_len)
            ptz_bar = f"{GRN}{'█' * filled}{DIM}{'─' * (bar_len - filled)}{RST}"
            row(f" 🔧 Select: {YLW}[B]{RST} {YLW}[C]{RST} {YLW}[S]{RST} {YLW}[G]{RST} {YLW}[H]{RST} {YLW}[V]{RST}    {YLW}[0]{RST} PTZ active: [{ptz_bar}]")
        else:
            row(f" 🔧 Select: {YLW}[B]{RST} {YLW}[C]{RST} {YLW}[S]{RST} {YLW}[G]{RST} {YLW}[H]{RST} {YLW}[V]{RST}    {YLW}[0]{RST} Reset Progress: [----------]")

        # ----------------------------------------------------------------------
        # Panel prawy – zgodny z projektem (SELECT / PAN / PTZ)– prosty, linia po linii (zgodny z projektem)
        # ----------------------------------------------------------------------

        if cam_mode:
            active_mode = ui_mode
        else:
            active_mode = ui_mode_file

        # Budowa nagłówka z ikonami trybów
        header_parts = []
        for mode_name, icon in [("SELECT", "📊"), ("PAN", "📺"), ("PTZ", "🎥")]:
            if mode_name == "PTZ" and not cam_mode:
                continue
            if mode_name == active_mode:
                header_parts.append(f"{RED}[Z{icon}]{RST}")
            else:
                header_parts.append(f"{DIM}[Z{icon}]{RST}")
        header_str = "".join(header_parts)

        # Definicje linii panelu dla każdego trybu
        if active_mode == "SELECT":
            border_color = DIM
            # Wybór prawej części: 11 kresek dla trybu plików, 7 dla trybu kamer
            right_dashes = "────────────" if not cam_mode else "───────"
            line1 = f"{border_color}┌───────────{RST}{header_str}{border_color}{right_dashes}┐{RST}"
            line2 = f"{border_color}│{RST}   {DIM}▲{RST}   {border_color}│{RST} {YLW}Z📊{RST}{DIM}[0🔍]{RST}   {YLW}[↑]{RST}{YLW}[↓]{RST}       {border_color}│{RST}"
            line3 = f"{border_color}│{RST} {DIM}◄{RST} {DIM}■{RST} {DIM}►{RST} {border_color}│{RST} Adjust     {YLW}[←]{RST}{YLW}[→]{RST}       {border_color}│{RST}"
            line4 = f"{border_color}│{RST}   {DIM}▼{RST}   {border_color}│{RST} Step       {YLW}[<]{RST}{YLW}[>]{RST} {step:<2}    {border_color}│{RST}"
            line5 = f"{border_color}└─[1-9]───[ F4 Recall F5 Save ]───┘{RST}"
        elif active_mode == "PAN":
            border_color = YLW
            if zoom_val == 0.0:
               zoom_str = f"{DIM}{2.0**zoom_val:.1f}x{RST}"
            else:
                zoom_str = f"{RED}{2.0**zoom_val:.1f}x{RST}"
            pan_x_col = RED if pan_x != 0 else DIM
            pan_y_col = RED if pan_y != 0 else DIM
            pan_str = f"{pan_x_col}x:{pan_x:+.2f}{RST} {pan_y_col}y:{pan_y:+.2f}{RST}"
            right_dashes = "────────────" if not cam_mode else "───────"
            line1 = f"{border_color}┌───────────{RST}{header_str}{border_color}{right_dashes}┐{RST}"
            line2 = f"{border_color}│{RST}   {YLW}▲{RST}   {border_color}│{RST} {YLW}Z📺{RST}{DIM}[0🔍]{RST} {YLW}[+]{RST}{YLW}[-]{RST}    {zoom_str} {border_color}│{RST}"
            line3 = f"{border_color}│{RST} {YLW}◄{RST} {YLW}■{RST} {YLW}►{RST} {border_color}│{RST} Pan: {pan_str}    {border_color}│{RST}"
            line4 = f"{border_color}│{RST}   {YLW}▼{RST}   {border_color}│{RST}                         {border_color}│{RST}"
            line5 = f"{border_color}└─[1-9]───[ F4 Recall F5 Save ]───┘{RST}"
        elif active_mode == "PTZ":
            border_color = GRN
            zoom_str = f"{GRN}{2.0**zoom_val:.1f}x{RST}"
            dur_str = f"{GRN}{cam.duration:.1f}s{RST}" if cam else f"{GRN}0.4s{RST}"
            speed_str = f"{GRN}{cam.speed:.1f}{RST}" if cam else f"{GRN}0.5{RST}"
            line1 = f"{border_color}┌───────────{RST}{header_str}{border_color}───────┐{RST}"
            line2 = f"{border_color}│{RST}   {GRN}▲{RST}   {border_color}│{RST} {YLW}Z🎥{RST}{DIM}[0🔍]{RST} {YLW}[+]{RST}{YLW}[-]{RST}   {zoom_str}  {border_color}│{RST}"
            line3 = f"{border_color}│{RST} {GRN}◄{RST} {GRN}■{RST} {GRN}►{RST} {border_color}│{RST} {YLW}(m/l){RST} Dur:        {dur_str}  {border_color}│{RST}"
            line4 = f"{border_color}│{RST}   {GRN}▼{RST}   {border_color}│{RST} {YLW}(s/f){RST} Speed:      {speed_str}   {border_color}│{RST}"
            line5 = f"{border_color}└─[1-9]───[ F4 Recall F5 Save ]───┘{RST}"
        else:
            line1 = line2 = line3 = line4 = line5 = ""

        panel_parts = [line1, line2, line3, line4, line5]

        # Rysowanie parametrów z doklejonym panelem
        for i, p in enumerate(PARAMS):
            cursor = f"{YLW}►{RST}" if i == sel else " "
            b = bar(p)
            if p == "VOL":
                vstr = f"{GRN if values[p]==100 else YLW} {values[p]:3d}%{RST}"
                _gm = config_mgr.config.global_mute if config_mgr else muted
                mute_color = RED if muted else YLW
                _mute_lbl = f"🔇 Global mute ON" if _gm else f"Mute ({'ON' if muted else 'OFF'})"
                mute_status = f"  {YLW}[{mute_color}M{RST}{YLW}]{RST} {mute_color}{_mute_lbl}{RST}"
                row(f" {cursor}{ICONS[p]}{MAG}{p:<11}{RST} {b} {vstr}{mute_status}")
            else:
                vstr = f"{GRN if values[p]==0 else YLW}{values[p]:+4d}%{RST}"
                prefix = f" {cursor}{ICONS[p]}{MAG}{p:<11}{RST} {b} {vstr} "
                panel_part = panel_parts[i] if i < len(panel_parts) else ""
                full_line = prefix + panel_part
                padding = (W - 2) - ansilen(full_line)
                row(full_line + " " * max(0, padding))

        sep()
        row(f" {YLW}[,]{RST} Prev  {YLW}[.]{RST} Next  {YLW}[T]{RST} Screenshot  {YLW}[x/X]{RST}💾 Restore/Store Set")

        # --- Linia statusu ----------------------------------------------------
        if last_msg not in ("OK", "Player mode", "mpv stopped", "mpv disconnected"):
            if _last_msg_t == 0.0: _last_msg_t = _time.time()
            elif _time.time() - _last_msg_t > _MSG_HOLD: last_msg = "OK"; _last_msg_t = 0.0
        else:
            _last_msg_t = 0.0

        msg_col = GRN if "OK" in last_msg else (RED if ("ERR" in last_msg or "stop" in last_msg or "fail" in last_msg.lower()) else DIM)
        cpu = get_cpu_usage()
        free_pct = get_free_space_percent()
        _BW = 8
        def _bar8(pct, col=GRN):
            f = int(pct / 100 * _BW)
            return f"{col}{'█'*f}{DIM}{'░'*(_BW-f)}{RST}"
        try:
            with open('/proc/meminfo') as _mf:
                _ml = {l.split(':')[0]: int(l.split()[1]) for l in _mf if ':' in l}
            ram_pct = int(100 * (1 - _ml.get('MemAvailable', 0) / max(_ml.get('MemTotal', 1), 1)))
        except:
            ram_pct = 0
        cpu_n = int(cpu.replace('%','').strip() or 0)
        cpu_col = RED if cpu_n > 80 else (YLW if cpu_n > 50 else GRN)
        ram_col = RED if ram_pct > 80 else (YLW if ram_pct > 60 else GRN)
        hdd_use = 100 - free_pct
        hdd_col = RED if hdd_use > 90 else (YLW if hdd_use > 75 else GRN)
        cpu_str = f"{cpu_n:3d}%"; ram_str = f"{ram_pct:3d}%"; hdd_str = f"{hdd_use:3d}%"
        right = f"{CYN}v{VERSION}{RST} {YLW}(ESC){RST} Quit"
        _status_fixed = f" ⚙{cpu_str} 🧠[{'█'*_BW}]{ram_str} 💽[{'█'*_BW}]{hdd_str}  🔔 "
        _msg_max = W - ansilen(_status_fixed) - ansilen(right) - 2
        _msg_disp = last_msg if ansilen(last_msg) <= _msg_max else last_msg[:_msg_max-1] + "…"
        left = f" ⚙{cpu_col}{cpu_str}{RST} 🧠[{_bar8(ram_pct,ram_col)}]{ram_col}{ram_str}{RST} 💽[{_bar8(hdd_use,hdd_col)}]{hdd_col}{hdd_str}{RST}  🔔 {msg_col}{_msg_disp}{RST}"
        padding = W - ansilen(left) - ansilen(right) - 2
        row(f"{left}{' ' * max(0, padding)}{right}")
        _w(f"\r{BLU}╚{'═'*W}╝{RST}\033[K\r\n")
        sys.stdout.write("".join(_buf))
        sys.stdout.write("\033[J\033[?25h")
        sys.stdout.flush()

    # --------------------------------------------------------------------------
    # Pomocnicze: ruch PTZ i lista kamer
    # --------------------------------------------------------------------------
    def _ptz_move(dx, dy, dz=0.0, label=""):
        if not cam or not prof: return
        if cam.type == CameraType.ONVIF:
            client = ONVIFClient(cam)
            pan = dx * cam.speed
            tilt = dy * cam.speed
            zoom = dz * cam.speed
            client.move_continuous(prof.token, pan, tilt, zoom)
            _time.sleep(cam.duration)
            client.stop(prof.token)
        elif cam.type == CameraType.DVRIP:
            client = DVRIPClient(cam)
            direction = ""
            if dy > 0: direction = "U"
            elif dy < 0: direction = "D"
            elif dx < 0: direction = "L"
            elif dx > 0: direction = "R"
            elif dz > 0: direction = "Z+"
            elif dz < 0: direction = "Z-"
            if direction:
                ptz_speed = int(cam.speed * 8)
                client.move(direction, ptz_speed, cam.duration)

    def _ptz_move_async(dx, dy, dz=0.0, direction_label=""):
        """Uruchamia ruch PTZ w tle i animuje pasek postępu."""
        nonlocal ptz_active, ptz_progress, ptz_direction, last_msg
        if not cam or not prof:
            return
        if ptz_active:
            # już trwa ruch – ignorujemy kolejne kliknięcia
            return
        ptz_active = True
        ptz_progress = 0.0
        ptz_direction = direction_label

        def _move_worker():
            nonlocal ptz_active, ptz_progress, last_msg
            duration = cam.duration
            steps = 10
            step_time = duration / steps
            try:
                if cam.type == CameraType.ONVIF:
                    client = ONVIFClient(cam)
                    pan = dx * cam.speed
                    tilt = dy * cam.speed
                    zoom = dz * cam.speed
                    client.move_continuous(prof.token, pan, tilt, zoom)
                    for i in range(steps + 1):
                        ptz_progress = i / steps
                        _time.sleep(step_time)
                    client.stop(prof.token)
                elif cam.type == CameraType.DVRIP:
                    client = DVRIPClient(cam)
                    direction = ""
                    if dy > 0: direction = "U"
                    elif dy < 0: direction = "D"
                    elif dx < 0: direction = "L"
                    elif dx > 0: direction = "R"
                    elif dz > 0: direction = "Z+"
                    elif dz < 0: direction = "Z-"
                    try:
                        if direction:
                            ptz_speed = int(cam.speed * 8)
                            client.move(direction, ptz_speed, duration)
                            for i in range(steps + 1):
                                ptz_progress = i / steps
                                _time.sleep(step_time)
                    finally:
                        client.close()
                last_msg = f"PTZ {direction_label} done"
            except Exception as e:
                last_msg = f"PTZ error: {e}"
            finally:
                ptz_active = False
                ptz_progress = 0.0
        _thr.Thread(target=_move_worker, daemon=True).start()

    def _show_camera_playlist(cameras, cur_idx):
        nonlocal old_settings
        items = []
        for i, c in enumerate(cameras):
            name = getattr(c, 'name', f'Camera {i+1}')
            ip = getattr(c, 'ip', '')
            if ip:
                name = f"{name} ({ip})"
            prefix = "🎥 " if i == cur_idx else "   "
            items.append(f"{prefix}{i+1:2}. {name}")
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        raw_attrs = termios.tcgetattr(fd)
        try:
            termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)
            sys.stdout.write('\033[2J\033[H')
            sys.stdout.flush()
            result = select_menu(
                items,
                selected=cur_idx,
                title=f"📋 Kamery ({len(cameras)}) - ENTER wybierz, Q/ESC anuluj",
                W=70,
                page_size=15
            )
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, raw_attrs)
            sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
            sys.stdout.flush()
        return result

    # --------------------------------------------------------------------------
    # Inicjalizacja IPC i pierwszego stanu
    # --------------------------------------------------------------------------
    if _ctrl_socket:
        for _ in range(50):
            if _os.path.exists(_ctrl_socket): break
            _time.sleep(0.1)
        _time.sleep(0.15)

    for _ in range(20):
        _fetch_state()
        if dur_f > 0: break
        _time.sleep(0.1)

    if ctrl and ctrl.is_alive():
        for p in PARAMS:
            if p == "VOL": ctrl.set_property("volume", values[p])
            else:          ctrl.set_property(PROP_MAP[p], values[p])
        ctrl.set_property("speed", speed)
        ctrl.set_property("mute", muted)
        # loop-file: tylko dla 1 pliku — dla playlisty wrapper Pythona obsługuje loop
        _loop_file_val = "inf" if (loop_mode_local and len(files) == 1) else "no"
        ctrl.set_property("loop-file", _loop_file_val)
        _fetch_state()

    last_tick = _time.monotonic()
    old_settings = termios.tcgetattr(fd)

    try:
        tty.setraw(fd)
        sys.stdout.write('\033[?1049h')
        sys.stdout.write('\033[?1000h\033[?1002h\033[?1006h')
        sys.stdout.flush()
        running = True
        result  = "quit"

# --- Mouse handling start (restored & adjusted) -------------------------
        def _handle_mouse_p(r, c):
            nonlocal sel, running, result, auto_dir, paused, step, auto_run, auto_fps, current_idx, loop_mode_local, last_msg
            nonlocal ui_mode, ui_mode_file

            # Row 2: Header with navigation, mode, loop, playlist
            if r == 2:
                if 6 <= c <= 8:                                         # [◄,] prev
                    _mouse_off()
                    result = "prev"; running = False
                    _mouse_on()
                elif 54 <= c <= 56:                                     # [.►] next
                    _mouse_off()
                    result = "next"; running = False
                    _mouse_on()
                elif 59 <= c <= 61:                                     # [P]list / [P]T[Z]
                    if cam_mode:
                        _mouse_off()
                        _in_overlay = True
                        ui_mode = "PTZ"
                        _in_overlay = False
                        _first_draw = True
                        _mouse_on()
                    else:
                        _mouse_off()
                        _in_overlay = True
                        new_idx = _show_playlist(files, current_idx)
                        _in_overlay = False
                        _first_draw = True
                        if isinstance(new_idx, tuple) and new_idx[0] == "add":
                            new_path = new_idx[1]
                            if new_path not in files:
                                files.append(new_path)
                            result = ("goto", files.index(new_path))
                            running = False
                        elif new_idx >= 0:
                            result = ("goto", new_idx)
                            running = False
                        _mouse_on()
                elif 63 <= c <= 65:                                     # [Z] mode toggle
                    if cam_mode:
                        ui_mode = {"SELECT": "PAN", "PAN": "PTZ", "PTZ": "SELECT"}[ui_mode]
                    else:
                        ui_mode_file = "PAN" if ui_mode_file == "SELECT" else "SELECT"
                    last_msg = f"Mode: {ui_mode if cam_mode else ui_mode_file}"
                elif 67 <= c <= 71:                                     # [L] loop
                    loop_mode_local = not loop_mode_local
                    if len(files) == 1 and ctrl and ctrl.is_alive():
                        ctrl._send(["set_property", "loop-file",
                                    "inf" if loop_mode_local else "no"])
                    last_msg = f"Loop {'🔁 ON (file)' if (loop_mode_local and len(files)==1) else ('🔁 ON (playlist)' if loop_mode_local else '⏹ OFF')}"
                elif 73 <= c <= 78:                                     # [K>] save as camera
                    if save_as_camera_fn:
                        _mouse_off()
                        name = _ask_save_name()
                        if name: save_as_camera_fn(name); last_msg = f"📷 saved as '{name}'"
                        _mouse_on()
                elif 79 <= c <= 80:                                     # 🎥 (same as [K>])
                    if save_as_camera_fn:
                        _mouse_off()
                        name = _ask_save_name()
                        if name: save_as_camera_fn(name); last_msg = f"📷 saved as '{name}'"
                        _mouse_on()

            # Row 5: Progress bar and AB‑loop markers
            elif r == 5 and dur_f > 0:
                BAR_START, BAR_LEN = 5, 22
                if BAR_START <= c <= BAR_START + BAR_LEN:
                    frac = (c - BAR_START) / BAR_LEN
                    target = frac * dur_f
                    if ctrl and ctrl.is_alive():
                        ctrl._send(["seek", target, "absolute"])
                    last_msg = f"seek {target:.1f}s"
                elif c >= 50:                                           # AB‑loop area
                    if ab_active:
                        if 57 <= c <= 59:  _ab_clear()
                        elif 60 <= c <= 63:  _ab_edit_a()
                        elif 65 <= c <= 67:  _ab_clear()
                        elif 68 <= c <= 71:  _ab_edit_b()
                    elif ab_a >= 0 and ab_b < 0:
                        if 56 <= c <= 58:  _ab_edit_a()
                        elif 59 <= c <= 63:  _ab_edit_a()
                        elif 64 <= c <= 66:  _ab_set_b()
                        elif 67 <= c <= 69:  _ab_set_b()
                    else:
                        if 56 <= c <= 58:  _ab_set_a()
                        elif 59 <= c <= 61:  _ab_set_a()

            # Row 6: REC and Clear[A]
            elif r == 6:
                if c >= 50:
                    if 53 <= c <= 55:                                   # ● [A]REC / [R]EC
                        if cam_mode: _rec_toggle()
                        elif is_file_cam: _extract_clip_current()
                        else: last_msg = "🎬 REC tylko dla plików"
                    elif 65 <= c <= 71 and ab_active:                   # Clear[A]
                        _ab_clear()

            # Row 7: Play controls (paused / playing)
            elif r == 7:
                if 3 <= c <= 11:                                        # [SPACE]
                    _toggle_pause()
                elif paused:
                    if 13 <= c <= 16:    _frame_step(False)            # [ ←[
                    elif 17 <= c <= 20:  _frame_step(True)             # ]→ ]
                    elif 36 <= c <= 38:  auto_dir = not auto_dir       # [D] dir
                    elif 46 <= c <= 48:                                # [R] run/stop
                        auto_run = not auto_run
                        auto_accum = 0.0
                    elif 61 <= c <= 63:  auto_fps = max(0.5, auto_fps - 0.5)  # [↑]
                    elif 64 <= c <= 66:  auto_fps = min(24.0, auto_fps + 0.5) # [↓]
                else:  # playing
                    if 24 <= c <= 26 and ctrl and ctrl.is_alive():      # [-]
                        ctrl._send(["seek", -30, "relative"])
                    elif 34 <= c <= 36 and ctrl and ctrl.is_alive():    # [+]
                        ctrl._send(["seek", +30, "relative"])
                    elif 47 <= c <= 53:  _set_speed(0.0)               # Sp[E]ed
                    elif 56 <= c <= 60:  _set_speed(-0.25)             # [D] slow
                    elif 63 <= c <= 67:  _set_speed(+0.25)             # [F] fast

            # Row 9: Parameter selection row
            elif r == 9:
                # Direct letter buttons (B,C,S,G,H,V)
                if 14 <= c <= 16:       # [B]
                    sel = 0
                elif 18 <= c <= 20:     # [C]
                    sel = 1
                elif 22 <= c <= 24:     # [S]
                    sel = 2
                elif 26 <= c <= 28:     # [G]
                    sel = 3
                elif 30 <= c <= 32:     # [H]
                    sel = 4
                elif 34 <= c <= 36:     # [V]
                    sel = 5
                # [0] Reset (right side)
                elif 41 <= c <= 43:
                    _reset_image_settings()
                # Reset (right side)
                elif 45 <= c <= 49:
                    _reset_all_settings()
                # Progress (right side)
                elif 51 <= c <= 59:
                    pass  # TODO_progress()
                # Progress bar (right side)
                elif 61 <= c <= 72:
                    pass  # TODO_bar_progress()

            # ------------------------------------------------------------------
            # Row 10: Header with mode icons (different for CAMERA vs PLAYER)
            # ------------------------------------------------------------------
            if r == 10 and c >= 46:
                # [Z📊] SELECT – kolumny ok. 55-59 (dla obu trybów)
                if 55 <= c <= 59:
                    if cam_mode:
                        ui_mode = "SELECT"
                    else:
                        ui_mode_file = "SELECT"
                    last_msg = "Mode: SELECT"
                # [Z📺] PAN – kolumny ok. 60-64 (dla obu trybów)
                elif 60 <= c <= 64:
                    if cam_mode:
                        ui_mode = "PAN"
                    else:
                        ui_mode_file = "PAN"
                    last_msg = "Mode: PAN"
                # [Z🎥] PTZ – tylko w trybie CAMERA, kolumny ok. 65-69
                elif 65 <= c <= 69 and cam_mode:
                    ui_mode = "PTZ"
                    last_msg = "Mode: PTZ"

            # ------------------------------------------------------------------
            # Rows 11–13: Zoom/Pan panel – identyczne dla obu trybów
            # (różnica tylko w dostępności trybu PTZ)
            # ------------------------------------------------------------------
            elif r == 11 and 46 <= c <= 79:                             # ▲ and zoom controls (PAN/PTZ)
                if c == 49:                                             # ▲
                    if cam_mode:
                        if ui_mode == "SELECT":
                            sel = (sel - 1) % len(PARAMS)
                        elif ui_mode == "PAN":
                            _pan(0, +PAN_STEP)
                        elif ui_mode == "PTZ":
                            _ptz_move_async(0.0, 1.0, 0.0, "U")
                    else:
                        if ui_mode_file == "SELECT":
                            sel = (sel - 1) % len(PARAMS)
                        elif ui_mode_file == "PAN":
                            _pan(0, +PAN_STEP)
                # Przyciski dostępne tylko w trybie SELECT
                elif (cam_mode and ui_mode == "SELECT") or (not cam_mode and ui_mode_file == "SELECT"):
                    if 58 <= c <= 62:       # [0🔍] – reset obrazu
                        _reset_image_settings()
                    elif 66 <= c <= 68:     # [↑]
                        sel = (sel - 1) % len(PARAMS)
                    elif 69 <= c <= 71:     # [↓]
                        sel = (sel + 1) % len(PARAMS)
                # Przyciski specyficzne dla trybu PAN (zoom i reset)
                elif (cam_mode and ui_mode == "PAN") or (not cam_mode and ui_mode_file == "PAN"):
                    if 58 <= c <= 62:       # [0🔍] – reset zoom/pan
                        _zoom_reset()
                    elif 64 <= c <= 66:     # [+]
                        _zoom_in()
                    elif 67 <= c <= 69:     # [-]
                        _zoom_out()
                    elif 73 <= c <= 77:     # "1.0x" – edycja zoomu
                        _edit_zoom()
                # Przyciski specyficzne dla trybu PTZ (tylko CAMERA)
                elif cam_mode and ui_mode == "PTZ":
                    if 58 <= c <= 62:       # [0🔍] – reset zoomu
                        _zoom_zero()
                    elif 66 <= c <= 68:     # [+]
                        _zoom_in()
                    elif 69 <= c <= 71:     # [-]
                        _zoom_out()
                    elif 73 <= c <= 76:     # "1.0x" – edycja zoomu
                        _edit_zoom()

            elif r == 12 and 46 <= c <= 79:                             # ◄ ■ ► and pan info (PAN) / zoom controls
                if c == 47:             # ◄
                    if cam_mode:
                        if ui_mode == "SELECT":
                            _set_val(PARAMS[sel], -step)
                        elif ui_mode == "PAN":
                            _pan(+PAN_STEP, 0)
                        elif ui_mode == "PTZ":
                            _ptz_move_async(-1.0, 0.0, 0.0, "L")
                    else:
                        if ui_mode_file == "SELECT":
                            _set_val(PARAMS[sel], -step)
                        elif ui_mode_file == "PAN":
                            _pan(+PAN_STEP, 0)
                elif c == 49:           # ■
                    if cam_mode:
                        if ui_mode == "SELECT":
                            _reset_image_settings()
                        elif ui_mode == "PAN":
                            _pan_center()
                        elif ui_mode == "PTZ":
                            if cam and prof:
                                if cam.type == CameraType.ONVIF:
                                    ONVIFClient(cam).stop(prof.token)
                                elif cam.type == CameraType.DVRIP:
                                    DVRIPClient(cam).move("C", 0, 0)
                    else:
                        if ui_mode_file == "SELECT":
                            _reset_image_settings()
                        elif ui_mode_file == "PAN":
                            _pan_center()
                elif c == 51:           # ►
                    if cam_mode:
                        if ui_mode == "SELECT":
                            _set_val(PARAMS[sel], +step)
                        elif ui_mode == "PAN":
                            _pan(-PAN_STEP, 0)
                        elif ui_mode == "PTZ":
                            _ptz_move_async(1.0, 0.0, 0.0, "R")
                    else:
                        if ui_mode_file == "SELECT":
                            _set_val(PARAMS[sel], +step)
                        elif ui_mode_file == "PAN":
                            _pan(-PAN_STEP, 0)
                # Przyciski dostępne tylko w trybie SELECT
                elif (cam_mode and ui_mode == "SELECT") or (not cam_mode and ui_mode_file == "SELECT"):
                    if 66 <= c <= 68:       # [←]
                        _set_val(PARAMS[sel], -step)
                    elif 69 <= c <= 71:     # [→]
                        _set_val(PARAMS[sel], +step)
                # --- Tryb PAN: edycja wartości x/y z tekstu "Pan: x:+0.00 y:+0.00" ---
                elif (cam_mode and ui_mode == "PAN") or (not cam_mode and ui_mode_file == "PAN"):
                    # Kliknięcie na wartość x (po "x:")
                    if 60 <= c <= 65:
                        _edit_pan_x()
                    # Kliknięcie na wartość y (po "y:")
                    elif 66 <= c <= 71:
                        _edit_pan_y()
                # --- Tryb PTZ: obsługa (m/l) Dur (tylko CAMERA) ---
                elif cam_mode and ui_mode == "PTZ":
                    # litera 'm' (zmniejsz duration)
                    if 56 <= c <= 57:
                        cam.duration = max(0.1, cam.duration - 0.1)
                        last_msg = f"Duration: {cam.duration:.1f}s"
                    # litera 'l' (zwiększ duration)
                    elif 58 <= c <= 59:
                        cam.duration = min(5.0, cam.duration + 0.1)
                        last_msg = f"Duration: {cam.duration:.1f}s"
                    # wartość liczbowa (np. "0.4s") – otwórz prompt
                    elif 66 <= c <= 71:
                        new_dur = _ask_duration_input()
                        if new_dur is not None:
                            cam.duration = new_dur
                            last_msg = f"Duration set to {cam.duration:.1f}s"
                # Istniejące kontrolki zoomu (wspólne dla PAN/PTZ) – ale tylko jeśli nie były obsłużone
                elif 55 <= c <= 59:     _zoom_toggle()
                elif 60 <= c <= 64:     _zoom_zero()
                elif 66 <= c <= 68:     _zoom_in()
                elif 69 <= c <= 71:     _zoom_out()
                elif 73 <= c <= 76:     _edit_zoom()

            elif r == 13 and 46 <= c <= 79:                             # ▼ and speed/duration (PTZ) / step (SELECT)
                if c == 49:                                             # ▼
                    if cam_mode:
                        if ui_mode == "SELECT":
                            sel = (sel + 1) % len(PARAMS)
                        elif ui_mode == "PAN":
                            _pan(0, -PAN_STEP)
                        elif ui_mode == "PTZ":
                            _ptz_move_async(0.0, -1.0, 0.0, "D")
                    else:
                        if ui_mode_file == "SELECT":
                            sel = (sel + 1) % len(PARAMS)
                        elif ui_mode_file == "PAN":
                            _pan(0, -PAN_STEP)
                # Przyciski dostępne tylko w trybie SELECT
                elif (cam_mode and ui_mode == "SELECT") or (not cam_mode and ui_mode_file == "SELECT"):
                    if 66 <= c <= 68:       # [<]
                        step = max(1, step - 1)
                    elif 69 <= c <= 71:     # [>]
                        step = min(50, step + 1)
                # --- Tryb PTZ: obsługa (s/f) Speed (tylko CAMERA) ---
                elif cam_mode and ui_mode == "PTZ":
                    # litera 's' (zmniejsz speed)
                    if 56 <= c <= 57:
                        cam.speed = max(0.1, cam.speed - 0.1)
                        last_msg = f"Speed: {cam.speed:.1f}"
                    # litera 'f' (zwiększ speed)
                    elif 58 <= c <= 59:
                        cam.speed = min(1.0, cam.speed + 0.1)
                        last_msg = f"Speed: {cam.speed:.1f}"
                    # wartość liczbowa (np. "0.4") – otwórz prompt
                    elif 66 <= c <= 71:
                        new_speed = _ask_speed_input()
                        if new_speed is not None:
                            cam.speed = new_speed
                            last_msg = f"Speed set to {cam.speed:.1f}"
            # Rows 11–13: Zoom/Pan panel (right side end)

            # Rows 10–15: Parameter sliders (click to set value) – ale tylko dla r od 10 do 15,
            # ale r=10 już obsłużyliśmy powyżej, więc żeby nie dubować, zaczynamy od r=11?
            # W oryginalnym kodzie był blok dla 10 <= r <= 15, ale ponieważ r=10 mamy wyżej,
            # to tutaj możemy zacząć od r=11. Dla bezpieczeństwa zostawiam oryginalną logikę,
            # ale z wykluczeniem r==10, które już obslużyliśmy.
            elif 11 <= r <= 15:
                new_sel = r - 10
                # Mute button on VOL row (r==15)
                if r == 15 and 45 <= c <= 47:
                    _toggle_mute()
                elif c <= 37:                                           # slider area
                    if sel == new_sel:
                        if 18 <= c <= 37:                               # bar region
                            param = PARAMS[sel]
                            if param == "VOL":
                                frac = (c - 18) / (37 - 18)
                                new_val = max(0, min(150, int(frac * 150)))
                                if ctrl and ctrl.is_alive():
                                    ctrl.set_property("volume", new_val)
                                values[param] = new_val
                            else:
                                frac = (c - 18) / (37 - 18)
                                new_val = max(-100, min(100, int((frac - 0.5) * 200)))
                                if ctrl and ctrl.is_alive():
                                    ctrl.set_property(PROP_MAP[param], new_val)
                                values[param] = new_val
                    else:
                        sel = new_sel

            # Row 17: Bottom navigation
            elif r == 17:
                if 3 <= c <= 5:         result = "prev"; running = False
                elif 13 <= c <= 15:     result = "next"; running = False
                elif 23 <= c <= 25:     _screenshot()                   # [T]
                elif 39 <= c <= 40:     _restore_image_settings()       # [x] Restore
                elif 42 <= c <= 43:     _save_image_params()            # [X] Store

            elif r == 18:
                if 68 <= c <= 73:     running = False                 # [Q]
# --- Mouse handling end -------------------------------------------------

# --- Główna pętla -----------------------------------------------------
        while running:
            _mpv_pid = prof.pid if prof else None
            _mpv_alive = _mpv_pid and ProcessManager.is_running(_mpv_pid)
            if not _mpv_alive:
                # Plik zakończył się (EOF) lub mpv crashnął.
                # Dla pliku bez loop → eof_next, żeby wrapper przeszedł do następnego.
                # Dla kamer RTSP/V4L2 lub błędu → quit.
                if is_file_cam and not loop_mode_local:
                    last_msg = "EOF"; _draw(); _time.sleep(0.3)
                    result = "eof_next"; break
                else:
                    last_msg = "mpv stopped"; _draw(); _time.sleep(1)
                    result = "quit"; break

            _draw()

            if auto_run and paused: timeout = min(0.05, 1.0 / auto_fps)
            elif paused:            timeout = 0.3
            else:                   timeout = 1.0

            rlist, _, _ = _sel.select([sys.stdin], [], [], timeout)

            now = _time.monotonic()
            dt  = now - last_tick; last_tick = now

            if ctrl and ctrl.is_alive():
                p2 = ctrl.get_property("time-pos")
                d2 = ctrl.get_property("duration")
                if p2 is not None: pos_f = float(p2)
                if d2 is not None: dur_f = float(d2)
                if stream_info == "📊 —" or (not auto_run and int(now) % 2 == 0):
                    _fetch_state()
                if not auto_run:
                    for pp in PARAMS:
                        if pp == "VOL":
                            vo = ctrl.get_property("volume")
                            if vo is not None: values["VOL"] = int(vo)
                        else:
                            v = ctrl.get_property(PROP_MAP[pp])
                            if v is not None: values[pp] = int(v)
                    sp = ctrl.get_property("speed")
                    if sp is not None: speed = float(sp)

            if auto_run and paused:
                auto_accum += dt
                step_interval = 1.0 / auto_fps
                while auto_accum >= step_interval:
                    auto_accum -= step_interval
                    r = _frame_step(forward=auto_dir)
                    if r == "eof": auto_run = False; result = "eof_next"; running = False; break

            if not rlist:
                if _sigwinch_flag[0]: _sigwinch_flag[0] = False; _first_draw = True
                continue

            _tw, _th = _term_size()
            _term_ok = (_th >= MIN_H and _tw >= MIN_W)
###
            ch = sys.stdin.read(1)
            if ch == '\x1b':
                ch2 = sys.stdin.read(1)
                if ch2 == '[':
                    ch3 = sys.stdin.read(1)
                    if ch3 == '<':
                        buf = ''
                        while True:
                            c2 = sys.stdin.read(1)
                            if c2 in ('M', 'm', ''): release = (c2 == 'm'); break
                            buf += c2
                        try:
                            parts = buf.split(';')
                            btn_n, m_col, m_row = int(parts[0]), int(parts[1]), int(parts[2])
                            if not release:
                                if btn_n == 64: _seek(+5)
                                elif btn_n == 65: _seek(-5)
                                elif btn_n == 0 and _term_ok: _handle_mouse_p(m_row, m_col)
                        except: pass
                    elif ch3 in ('C', 'D'):
                        forward = (ch3 == 'C')
                        if cam_mode and ui_mode == "PAN": _pan(-PAN_STEP if forward else +PAN_STEP, 0)
                        elif cam_mode and ui_mode == "PTZ": _ptz_move(1.0 if forward else -1.0, 0.0)
                        elif not cam_mode and ui_mode_file == "PAN": _pan(-PAN_STEP if forward else +PAN_STEP, 0)
                        else: _set_val(PARAMS[sel], +step if forward else -step)
                    elif ch3 == 'A':
                        if cam_mode and ui_mode == "PAN": _pan(0, +PAN_STEP)
                        elif cam_mode and ui_mode == "PTZ": _ptz_move(0.0, 1.0)
                        elif not cam_mode and ui_mode_file == "PAN": _pan(0, +PAN_STEP)
                        else: sel = (sel - 1) % len(PARAMS)
                    elif ch3 == 'B':
                        if cam_mode and ui_mode == "PAN": _pan(0, -PAN_STEP)
                        elif cam_mode and ui_mode == "PTZ": _ptz_move(0.0, -1.0)
                        elif not cam_mode and ui_mode_file == "PAN": _pan(0, -PAN_STEP)
                        else: sel = (sel + 1) % len(PARAMS)
                else: running = False
            elif ch in ('q', 'Q'): running = False
            elif ch == ' ': _toggle_pause()
            elif ch in ('z', 'Z'):
                if cam_mode:
                    ui_mode = {"SELECT": "PAN", "PAN": "PTZ", "PTZ": "SELECT"}[ui_mode]
                else:
                    ui_mode_file = "PAN" if ui_mode_file == "SELECT" else "SELECT"
                last_msg = f"Mode: {ui_mode if cam_mode else ui_mode_file}"
            elif ch == '0':
                _reset_image_settings()
            elif ch == '*':
                _zoom_zero()
            elif ch in ('d', 'D'):
                if paused: auto_dir = not auto_dir
                else: _set_speed(-0.25)
            elif ch in ('e', 'E'): _set_speed(0.0)

            # --- f / F (speed odtwarzania vs PTZ speed) ---
            elif ch == 'f':
                if cam_mode and ui_mode == "PTZ":
                    if cam:
                        cam.speed = min(1.0, cam.speed + 0.1)
                        last_msg = f"Speed: {cam.speed:.1f}"
                else:
                    _set_speed(+0.25)
            elif ch == 'F':
                _set_speed(+0.25)

            # --- m / M (mute vs PTZ duration) ---
            elif ch == 'm':
                if cam_mode and ui_mode == "PTZ":
                    if cam:
                        cam.duration = max(0.1, cam.duration - 0.1)
                        last_msg = f"Duration: {cam.duration:.1f}s"
                else:
                    _toggle_mute()
            elif ch == 'M':
                _toggle_mute()

            # --- l / L (loop vs PTZ duration) ---
            elif ch == 'l':
                if cam_mode and ui_mode == "PTZ":
                    if cam:
                        cam.duration = min(5.0, cam.duration + 0.1)
                        last_msg = f"Duration: {cam.duration:.1f}s"
                else:
                    loop_mode_local = not loop_mode_local
                    # 1 plik: loop-file steruje mpv bezpośrednio
                    # >1 plik: loop-file zawsze "no" — wrapper obsługuje listę
                    if len(files) == 1 and ctrl and ctrl.is_alive():
                        ctrl._send(["set_property", "loop-file", "inf" if loop_mode_local else "no"])
                    last_msg = f"Loop {'🔁 ON (file)' if (loop_mode_local and len(files)==1) else ('🔁 ON (playlist)' if loop_mode_local else '⏹ OFF')}"
            elif ch == 'L':
                loop_mode_local = not loop_mode_local
                if len(files) == 1 and ctrl and ctrl.is_alive():
                    ctrl._send(["set_property", "loop-file", "inf" if loop_mode_local else "no"])
                last_msg = f"Loop {'🔁 ON (file)' if (loop_mode_local and len(files)==1) else ('🔁 ON (playlist)' if loop_mode_local else '⏹ OFF')}"

            # --- s / S (saturation vs PTZ speed) ---
            elif ch == 's':
                if cam_mode and ui_mode == "PTZ":
                    if cam:
                        cam.speed = max(0.1, cam.speed - 0.1)
                        last_msg = f"Speed: {cam.speed:.1f}"
                else:
                    sel = 2   # Saturation
            elif ch == 'S':
                sel = 2

            elif ch in ('r', 'R'):
                if paused: _auto_toggle_run()
                elif is_file_cam: _extract_clip_current()
                else: last_msg = "🎬 REC tylko dla plików"
            elif ch == 'x': _restore_image_settings()
            elif ch == 'X': _save_image_params()
            elif ch in ('i', 'I'): _zoom_in()
            elif ch in ('o', 'O'): _zoom_out()
            elif ch in ('t', 'T'): _screenshot()
            elif ch in ('k', 'K'):
                name = _ask_save_name()
                if save_as_camera_fn: save_as_camera_fn(name); last_msg = f"📷 saved as '{name}'"
            elif ch in ('a', 'A'):
                if cam_mode:
                    _rec_toggle()  # cam_mode: start/stop stream-record
                elif ab_a < 0: _ab_set_a()
                elif ab_b < 0: _ab_set_b()
                else: _ab_clear()
            elif ch.lower() in JUMP_KEY: sel = JUMP_KEY[ch.lower()]
            elif ch == '[':
                if paused: _frame_step(False)    # krok wstecz
                else: _seek(-1.0)               # przewijanie 1s gdy gra
            elif ch == ']':
                if paused: _frame_step(True)     # krok wprzód
                else: _seek(+1.0)               # przewijanie 1s gdy gra
            elif ch == '+':
                if cam_mode and ui_mode == "PTZ": _ptz_move(0, 0, 1.0)
                elif (cam_mode and ui_mode == "PAN") or (not cam_mode and ui_mode_file == "PAN"): _zoom_in()
                elif paused: _auto_fps_change(+1)
                else: _seek(30)
            elif ch == '-':
                if cam_mode and ui_mode == "PTZ": _ptz_move(0, 0, -1.0)
                elif (cam_mode and ui_mode == "PAN") or (not cam_mode and ui_mode_file == "PAN"): _zoom_out()
                elif paused: _auto_fps_change(-1)
                else: _seek(-30)
            elif ch == ',': result = "prev"; running = False
            elif ch == '.': result = "next"; running = False
            elif ch in ('p', 'P'):
                if cam_mode:
                    _mouse_off(); _in_overlay = True
                    new_idx = _show_camera_playlist(files, current_idx)
                    _in_overlay = False
                    if new_idx >= 0 and new_idx != current_idx:
                        result = ("goto", new_idx); running = False
                    else: _first_draw = True; _draw()
                    _mouse_on()
                else:
                    new_idx = _show_playlist(files, current_idx)
                    if isinstance(new_idx, tuple) and new_idx[0] == 'add':
                        new_path = new_idx[1]
                        if new_path not in files: files.append(new_path)
                        result = ('goto', files.index(new_path)); running = False
                    elif new_idx >= 0 and new_idx != current_idx:
                        result = ('goto', new_idx); running = False
                    else: out('\033[2J\033[H'); _draw()
            elif ch == '<': step = max(1, step - 1)
            elif ch == '>': step = min(50, step + 1)

    finally:
        sys.stdout.write('\033[?1000l\033[?1002l\033[?1006l')
        sys.stdout.flush()
        termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)

    return result, loop_mode_local
# =============================================================================
# PLAYER MODE MPV CONTROL SCREEN PLAYER End
# =============================================================================

def _show_playlist(files, current_idx):
    """Picker plików — lista + nawigacja po katalogu.
    Zwraca nowy index (int) lub -1 (anuluj).
    """
    import os, stat as _stat, time as _time
    fd  = sys.stdin.fileno()
    W   = 78
    GRN = Colors.GREEN;  RED = Colors.RED;   YLW = Colors.YELLOW
    CYN = Colors.CYAN;   DIM = Colors.DIM;   RST = Colors.RESET
    BLU = Colors.BLUE;   WHT = Colors.WHITE; MAG = Colors.MAGENTA

    def out(s): sys.stdout.write(s); sys.stdout.flush()

    # ── Stan pickera ──────────────────────────────────────────────
    # Tryb: "playlist" = tylko files[], "dir" = przeglądanie katalogu
    mode         = "playlist"
    cwd          = os.path.dirname(os.path.abspath(files[0])) if files else os.getcwd()
    dir_entries  = []          # wypełniane w trybie dir
    selected     = current_idx
    dir_sel      = 0
    columns      = 1           # 1..4
    col_w        = W - 4       # szerokość kolumny
    orientation  = "V"         # V/H
    show_hidden  = False
    filter_str   = ""          # wpisany filtr
    page_size    = 10

    VIDEO_EXT = {".mp4",".mkv",".avi",".mov",".wmv",".flv",".ts",".mpg",
                 ".mpeg",".m4v",".webm",".ogv",".3gp",".vob",".mts",".m2ts"}

    def _scan_dir(path, show_hid, flt):
        entries = []
        # Wpis ".." zawsze na początku (chyba że filtrujemy)
        parent = os.path.dirname(path)
        if parent != path and not flt:
            entries.append({"name": "..", "path": parent,
                            "is_dir": True, "size": 0, "mtime": ""})
        try:
            for name in sorted(os.listdir(path)):
                if not show_hid and name.startswith("."):
                    continue
                if flt and flt.lower() not in name.lower():
                    continue
                fp = os.path.join(path, name)
                try:
                    st = os.stat(fp)
                    is_dir = _stat.S_ISDIR(st.st_mode)
                    size   = st.st_size
                    mtime  = _time.strftime("%y-%m-%d", _time.localtime(st.st_mtime))
                except OSError:
                    is_dir, size, mtime = False, 0, "?"
                entries.append({"name": name, "path": fp,
                                 "is_dir": is_dir, "size": size, "mtime": mtime})
        except PermissionError:
            pass
        # katalogi pierwsze (.. już jest na początku)
        non_dotdot = [e for e in entries if e["name"] != ".."]
        non_dotdot.sort(key=lambda e: (not e["is_dir"], e["name"].lower()))
        dotdot = [e for e in entries if e["name"] == ".."]
        return dotdot + non_dotdot

    def _fmt_size(n):
        for unit in ("B","K","M","G","T"):
            if n < 1024: return f"{n:.0f}{unit}"
            n /= 1024
        return f"{n:.0f}P"

    def _page_offset(sel, offset, total):
        if sel < offset:
            return sel
        if sel >= offset + page_size:
            return sel - page_size + 1
        return offset

    _btn_pos = lambda text: btn_pos(text, offset=1)  # +1 za ║

    def _draw_playlist(sel, off):
        out("\033[2J\033[H\033[?25l")
        out(f"\r{BLU}╔{'═'*W}╗{RST}\r\n")
        title = f" 📋 Playlista ({len(files)}) — {YLW}[↑↓]{RST} nawigacja  {YLW}[D]{RST} katalog  {YLW}[F]{RST} filtr  {YLW}[ESC]{RST} wróć"
        out(f"\r{BLU}║{RST}{pad(title, W)}{BLU}║{RST}\r\n")
        if filter_str:
            out(f"\r{BLU}║{RST}{pad(f'  {YLW}Filtr:{RST} {filter_str}', W)}{BLU}║{RST}\r\n")
        out(f"\r{BLU}╠{'═'*W}╣{RST}\r\n")
        visible = files[off:off + page_size]
        for i, fp in enumerate(visible):
            idx  = off + i
            name = os.path.basename(fp)
            ext  = os.path.splitext(name)[1].lower()
            if len(name) > W - 8: name = "…" + name[-(W-9):]
            icon = "🎬" if ext in VIDEO_EXT else "📄"
            if idx == sel:
                line = f" {GRN}▶ {icon} {WHT}{name}{RST}"
            elif idx == current_idx:
                line = f"   {icon} {CYN}{name}{RST} {DIM}◀ current{RST}"
            else:
                line = f"   {DIM}{icon} {name}{RST}"
            out(f"\r{BLU}║{RST}{pad(line, W)}{BLU}║{RST}\r\n")
        # dopełnij do page_size
        for _ in range(page_size - len(visible)):
            out(f"\r{BLU}║{RST}{' '*W}{BLU}║{RST}\r\n")
        out(f"\r{BLU}╠{'═'*W}╣{RST}\r\n")
        pg = f"{sel+1}/{len(files)}"
        nav = f" {YLW}[↑↓PgUp/Dn]{RST} {YLW}[ENTER]{RST} wybierz  {YLW}[D]{RST} katalog  {YLW}[Q/ESC]{RST} anuluj  {DIM}{pg}{RST}"
        out(f"\r{BLU}║{RST}{pad(nav, W)}{BLU}║{RST}\r\n")
        out(f"\r{BLU}╚{'═'*W}╝{RST}\r\n")
        out("\033[?25h")

    def _draw_dir(entries, sel, cwd_path):
        nonlocal col_w
        cols = min(columns, max(1, (W - 2) // 20))
        col_w = (W - 2) // cols
        n = len(entries)
        rows = max(1, (n + cols - 1) // cols) if n else 1
        vis_rows = min(rows, 10)

        out("\033[2J\033[H\033[?25l")
        out(f"\r{BLU}╔{'═'*W}╗{RST}\r\n")
        cwd_short = cwd_path if len(cwd_path) <= W-4 else "…"+cwd_path[-(W-5):]
        out(f"\r{BLU}║{RST}{pad(f' 📁 {CYN}{cwd_short}{RST}', W)}{BLU}║{RST}\r\n")
        flt_str = f"  {YLW}Filtr: {filter_str}{RST}" if filter_str else f"  {DIM}{n} elementów{RST}"
        out(f"\r{BLU}║{RST}{pad(flt_str, W)}{BLU}║{RST}\r\n")
        out(f"\r{BLU}╠{'═'*W}╣{RST}\r\n")

        # oblicz offset dla widoku
        if n == 0:
            out(f"\r{BLU}║{RST}{pad(f'  {DIM}(pusty katalog){RST}', W)}{BLU}║{RST}\r\n")
            for _ in range(vis_rows - 1):
                out(f"\r{BLU}║{RST}{' '*W}{BLU}║{RST}\r\n")
        else:
            sel_row = sel // cols if orientation == "H" else sel % rows
            row_off = max(0, min(sel_row - vis_rows//2, rows - vis_rows))

            for r in range(row_off, row_off + vis_rows):
                line_parts = []
                for c in range(cols):
                    idx = r * cols + c if orientation == "H" else c * rows + r
                    if idx >= n:
                        line_parts.append(" " * col_w)
                        continue
                    e = entries[idx]
                    nm = e["name"]
                    max_nm = col_w - 5
                    if len(nm) > max_nm: nm = nm[:max_nm-1]+"…"
                    icon = "📁" if e["is_dir"] else ("🎬" if os.path.splitext(e["name"])[1].lower() in VIDEO_EXT else "📄")
                    cell = f" {icon} {nm}"
                    cell_vis = ansilen(cell)
                    if idx == sel:
                        cell = f" {GRN}▶{RST}{icon} {WHT}{nm}{RST}"
                    elif not e["is_dir"] and os.path.splitext(e["name"])[1].lower() not in VIDEO_EXT:
                        cell = f" {DIM}{icon} {nm}{RST}"
                    else:
                        cell = f" {icon} {nm}"
                    pad_n = max(0, col_w - ansilen(cell))
                    line_parts.append(cell + " "*pad_n)
                row_str = "".join(line_parts)
                out(f"\r{BLU}║{RST}{pad(row_str, W)}{BLU}║{RST}\r\n")

        out(f"\r{BLU}╠{'═'*W}╣{RST}\r\n")
        # info o zaznaczonym
        if 0 <= sel < n:
            e = entries[sel]
            info = f" {e['mtime']}  {_fmt_size(e['size']) if not e['is_dir'] else 'DIR'}"
            _ename = e["name"]
            out(f"\r{BLU}║{RST}{pad(f'  {YLW}{_ename}{DIM}{info}{RST}', W)}{BLU}║{RST}\r\n")
        else:
            out(f"\r{BLU}║{RST}{' '*W}{BLU}║{RST}\r\n")
        hint = f" {YLW}[ENTER]{RST} otwórz  {YLW}[F2]{RST} kolumny  {YLW}[F3]{RST} V/H  {YLW}[F4]{RST} ukryte  {YLW}[F]{RST} filtr  {YLW}[ESC]{RST} lista"
        out(f"\r{BLU}║{RST}{pad(hint, W)}{BLU}║{RST}\r\n")
        out(f"\r{BLU}╚{'═'*W}╝{RST}\r\n")
        out("\033[?25h")

    # ── Główna pętla ──────────────────────────────────────────────
    old_settings = termios.tcgetattr(fd)
    off = _page_offset(selected, 0, len(files))
    try:
        tty.setraw(fd)
        sys.stdout.write("\033[?1000h\033[?1002h\033[?1006h")
        sys.stdout.flush()

        while True:
            if mode == "playlist":
                _draw_playlist(selected, off)
            else:
                _draw_dir(dir_entries, dir_sel, cwd)

            key = get_key()

            # ── PLAYLIST mode ─────────────────────────────────────
            if mode == "playlist":
                if key == Key.UP:
                    selected = max(0, selected - 1)
                    off = _page_offset(selected, off, len(files))
                elif key == Key.DOWN:
                    selected = min(len(files)-1, selected + 1)
                    off = _page_offset(selected, off, len(files))
                elif key == Key.PAGE_UP:
                    selected = max(0, selected - page_size)
                    off = _page_offset(selected, off, len(files))
                elif key == Key.PAGE_DOWN:
                    selected = min(len(files)-1, selected + page_size)
                    off = _page_offset(selected, off, len(files))
                elif key == Key.HOME:
                    selected = 0; off = 0
                elif key == Key.END:
                    selected = len(files)-1
                    off = _page_offset(selected, off, len(files))
                elif key in ("\r", "\n", Key.ENTER):
                    return selected
                elif key in ("q", "Q", "\x1b", Key.ESC):
                    return -1
                elif key in ("d", "D"):
                    # przejdź do trybu katalogu
                    mode = "dir"
                    dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                    dir_sel = 0
                elif key in ("f", "F"):
                    # filtr — wpisz w linii
                    filter_str = ""
                    _draw_playlist(selected, off)
                    out(f"\033[{16};3H")
                    tty.setcbreak(fd)
                    ch = ""
                    while True:
                        c = sys.stdin.read(1)
                        if c in ("\r","\n","\x1b"): break
                        elif c == "\x7f": filter_str = filter_str[:-1]
                        else: filter_str += c
                        # odśwież hint
                        out(f"\033[18;3H{YLW}Filtr:{RST} {filter_str}{DIM}█{RST}   ")
                    tty.setraw(fd)
                    # Filtruj files
                    flt_lower = filter_str.lower()
                    visible_files = [f for f in files if flt_lower in os.path.basename(f).lower()] if filter_str else files
                    selected = 0 if visible_files else -1
                    off = 0
                elif isinstance(key, MouseEvent) and not key.release:
                    r, c = key.row, key.col
                    # Oblicz pozycje przycisków dynamicznie z tekstu nagłówka
                    # ' 📋 Playlista (N) — [↑↓] nawigacja  [D] katalog  [F] filtr  [ESC] wróć'
                    # Liczymy od col 2 (po ║)
                    if r == 2:
                        # [D] katalog — znajdź "[D]" w nagłówku
                        hdr = f" 📋 Playlista ({len(files)}) — [↑↓] nawigacja  [D] katalog  [F] filtr  [ESC] wróć"
                        _col = 2
                        _btn = {}
                        for _i, _ch in enumerate(hdr):
                            for _k, _t in [('D','[D]'),('F','[F]'),('ESC','[ESC]')]:
                                if hdr[_i:_i+len(_t)] == _t and _k not in _btn:
                                    _btn[_k] = (_col, _col+len(_t)-1)
                            _col += 2 if ord(_ch) >= 0x1F000 else 1
                        if   'D'   in _btn and _btn['D'][0]   <= c <= _btn['D'][1]:
                            mode = "dir"; dir_entries = _scan_dir(cwd, show_hidden, filter_str); dir_sel = 0
                        elif 'F'   in _btn and _btn['F'][0]   <= c <= _btn['F'][1]:
                            # Uruchom filtr klawiszowy
                            filter_str = ""
                            _draw_playlist(selected, off)
                            tty.setcbreak(fd)
                            out(f"\033[3;10H{YLW}Filtr:{RST} ")
                            while True:
                                _fc = sys.stdin.read(1)
                                if _fc in ("\r","\n","\x1b"): break
                                elif _fc == "\x7f": filter_str = filter_str[:-1]
                                else: filter_str += _fc
                                out(f"\033[3;18H{filter_str}{DIM}█{RST}   ")
                            tty.setraw(fd)
                        elif 'ESC' in _btn and _btn['ESC'][0] <= c <= _btn['ESC'][1]:
                            return -1
                    # r3+: lista plików
                    else:
                        header_rows = 4 if filter_str else 3
                        list_start = header_rows + 1
                        nav_row = list_start + page_size + 1  # r19
                        if list_start <= r <= list_start + page_size - 1:
                            clicked = off + (r - list_start)
                            if 0 <= clicked < len(files):
                                if clicked == selected:
                                    return selected
                                selected = clicked
                                off = _page_offset(selected, off, len(files))
                        elif r == nav_row:
                            _pg   = f"{selected+1}/{len(files)}"
                            _nav  = f" [↑↓PgUp/Dn] [ENTER] wybierz  [D] katalog  [Q/ESC] anuluj  {_pg}"
                            _bp   = _btn_pos(_nav)
                            if   'ENTER' in _bp and _bp['ENTER'][0] <= c <= _bp['ENTER'][1]: return selected
                            elif 'D'     in _bp and _bp['D'][0]     <= c <= _bp['D'][1]:
                                mode = "dir"; dir_entries = _scan_dir(cwd, show_hidden, filter_str); dir_sel = 0
                            elif 'Q/ESC' in _bp and _bp['Q/ESC'][0] <= c <= _bp['Q/ESC'][1]: return -1

            # ── DIR mode ──────────────────────────────────────────
            else:
                n = len(dir_entries)
                cols = min(columns, max(1, (W-2)//20))
                rows = max(1, (n + cols - 1) // cols) if n else 1

                if key == Key.UP:
                    if orientation == "V":
                        dir_sel = max(0, dir_sel - 1)
                    else:
                        dir_sel = max(0, dir_sel - cols)
                elif key == Key.DOWN:
                    if orientation == "V":
                        dir_sel = min(n-1, dir_sel + 1)
                    else:
                        dir_sel = min(n-1, dir_sel + cols)
                elif key == Key.LEFT:
                    if orientation == "V":
                        dir_sel = max(0, dir_sel - rows)
                    else:
                        dir_sel = max(0, dir_sel - 1)
                elif key == Key.RIGHT:
                    if orientation == "V":
                        dir_sel = min(n-1, dir_sel + rows)
                    else:
                        dir_sel = min(n-1, dir_sel + 1)
                elif key == Key.PAGE_UP:
                    dir_sel = max(0, dir_sel - 12*cols)
                elif key == Key.PAGE_DOWN:
                    dir_sel = min(n-1, dir_sel + 12*cols)
                elif key == Key.HOME:
                    dir_sel = 0
                elif key == Key.END:
                    dir_sel = n - 1
                elif key in ("\r", "\n", Key.ENTER):
                    if 0 <= dir_sel < n:
                        e = dir_entries[dir_sel]
                        if e["is_dir"]:
                            cwd = e["path"]
                            dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                            dir_sel = 0
                        else:
                            # Dodaj plik do zwróconego wyniku — kodujemy jako tuple
                            return ("add", e["path"])
                elif key in (Key.BACKSPACE, "\x7f"):
                    parent = os.path.dirname(cwd)
                    if parent != cwd:
                        cwd = parent
                        dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                        dir_sel = 0
                elif key == Key.F2:
                    columns = (columns % 4) + 1
                    dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                elif key == Key.F3:
                    orientation = "H" if orientation == "V" else "V"
                elif key == Key.F4:
                    show_hidden = not show_hidden
                    dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                    dir_sel = 0
                elif key in ("f", "F"):
                    filter_str = ""
                    tty.setcbreak(fd)
                    out(f"\033[18;10H{YLW}Filtr:{RST} ")
                    ch = ""
                    while True:
                        c = sys.stdin.read(1)
                        if c in ("\r","\n","\x1b"): break
                        elif c == "\x7f": filter_str = filter_str[:-1]
                        else: filter_str += c
                        out(f"\033[18;16H{filter_str}{DIM}█{RST}   ")
                    tty.setraw(fd)
                    dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                    dir_sel = 0
                elif key in ("\x1b", Key.ESC):
                    mode = "playlist"
                    filter_str = ""
                elif isinstance(key, MouseEvent) and not key.release:
                    _r, _c = key.row, key.col
                    # r4..r15: lista plików (vis_rows=12, zaczyna od r5)
                    _list_r0 = 5
                    _vis = 12
                    if _list_r0 <= _r <= _list_r0 + _vis - 1:
                        _row_in = _r - _list_r0
                        _col_in = max(0, (_c - 1) // max(1, col_w))
                        if orientation == "V":
                            _idx = _col_in * rows + _row_in
                        else:
                            _idx = _row_in * cols + _col_in
                        if 0 <= _idx < n:
                            if _idx == dir_sel:
                                # podwójny klik = enter
                                e = dir_entries[dir_sel]
                                if e["is_dir"]:
                                    cwd = e["path"]
                                    dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                                    dir_sel = 0
                                else:
                                    return ("add", e["path"])
                            else:
                                dir_sel = _idx
                    # r7 (hint): dynamiczne pozycje
                    elif _r == _list_r0 + _vis + 2:
                        _hint = f" [ENTER] otwórz  [F2] kolumny  [F3] V/H  [F4] ukryte  [F] filtr  [ESC] lista"
                        _bp = _btn_pos(_hint)
                        if   'ENTER' in _bp and _bp['ENTER'][0] <= _c <= _bp['ENTER'][1]:
                            if 0 <= dir_sel < n:
                                e = dir_entries[dir_sel]
                                if e["is_dir"]: cwd = e["path"]; dir_entries = _scan_dir(cwd, show_hidden, filter_str); dir_sel = 0
                                else: return ("add", e["path"])
                        elif 'F2'    in _bp and _bp['F2'][0]    <= _c <= _bp['F2'][1]:
                            columns = (columns % 4) + 1; dir_entries = _scan_dir(cwd, show_hidden, filter_str)
                        elif 'F3'    in _bp and _bp['F3'][0]    <= _c <= _bp['F3'][1]:
                            orientation = "H" if orientation == "V" else "V"
                        elif 'F4'    in _bp and _bp['F4'][0]    <= _c <= _bp['F4'][1]:
                            show_hidden = not show_hidden; dir_entries = _scan_dir(cwd, show_hidden, filter_str); dir_sel = 0
                        elif 'ESC'   in _bp and _bp['ESC'][0]   <= _c <= _bp['ESC'][1]:
                            mode = "playlist"; filter_str = ""

    finally:
        sys.stdout.write("\033[?1000l\033[?1002l\033[?1006l")
        termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)
        sys.stdout.write("\033[2J\033[H\033[?25h")
        sys.stdout.flush()


def main():
    if not _UNIX_TTY:
        print("PTZ Master TUI requires Unix/Linux system (termios/tty module missing).")
        sys.exit(1)
    logger.info(f"{'='*60}")
    logger.info(f"PTZ Master v{VERSION} starting – {time.strftime('%Y-%m-%d %H:%M:%S')}")
    logger.info(f"{'='*60}")

    # Sprawdź zależności przed uruchomieniem — w każdym trybie
    check_dependencies()

    if PLAYER_FILES:
        logger.info(f"Player mode: {len(PLAYER_FILES)} file(s)")
        config_mgr = ConfigManager(CONFIG_FILE)
        loop_mode = PLAYLIST_LOOP
        app = PlayerModeApp(PLAYER_FILES, config_mgr, start_idx=0, loop_mode=loop_mode)
        app.run()
    else:
        app = PTZMasterApp(CONFIG_FILE, RESTORE_MODE, START_CAMERA, START_MAC)
        app.run()

if __name__ == "__main__":
    main()
