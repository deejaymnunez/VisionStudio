import sys
import os
import json
import re
import random
import subprocess
import shutil
import tempfile
import math
import wave
import struct
import time
import threading
import queue
import traceback
import hashlib
import uuid
import urllib.request
import urllib.parse
import base64
from array import array
from collections import deque, Counter
from datetime import datetime, timedelta

from PyQt6.QtWidgets import (QApplication, QWidget, QVBoxLayout, QPushButton,
                             QLabel, QFileDialog, QTabWidget, QFormLayout, QComboBox,
                             QHBoxLayout, QLineEdit, QScrollArea, QMessageBox, QSlider,
                             QCheckBox, QListWidget, QListWidgetItem, QTableWidget,
                             QTableWidgetItem, QHeaderView, QKeySequenceEdit, QSpinBox,
                             QInputDialog, QGroupBox, QDialog, QDialogButtonBox,
                             QAbstractItemView, QWizard, QWizardPage, QTreeWidget, QTreeWidgetItem,
                             QMenuBar, QMenu, QSystemTrayIcon, QStackedWidget, QAbstractSpinBox, QPlainTextEdit)
from PyQt6.QtCore import QSettings, QUrl, QTimer, Qt, QThread, QObject, pyqtSignal, QPointF, QRectF, QEvent, QStandardPaths
from PyQt6.QtGui import QPixmap, QKeySequence, QShortcut, QPainter, QColor, QPen, QBrush, QIcon, QAction, QKeyEvent
from PyQt6.QtMultimedia import (QMediaDevices, QMediaPlayer, QAudioOutput, QAudioSource,
                                 QAudioSink, QAudioFormat, QAudio, QSoundEffect)

try:
    import mutagen
    from mutagen.id3 import ID3
    from mutagen.flac import FLAC
    from mutagen.mp4 import MP4
    MUTAGEN_AVAILABLE = True
except Exception:
    MUTAGEN_AVAILABLE = False

# numpy and QAudioBufferOutput (Qt 6.8 or newer) are both needed for the live
# program mix that feeds the encoders. If either is missing the app still runs
# and the encoders fall back to streaming the current track file.
try:
    import numpy as np
    NUMPY_AVAILABLE = True
except Exception:
    np = None
    NUMPY_AVAILABLE = False

try:
    from PyQt6.QtMultimedia import QAudioBufferOutput
    BUFFER_OUTPUT_AVAILABLE = True
except Exception:
    QAudioBufferOutput = None
    BUFFER_OUTPUT_AVAILABLE = False

# Accessibility alert events, so NVDA/JAWS announce important changes.
try:
    from PyQt6.QtGui import QAccessible, QAccessibleEvent
    ACCESSIBLE_EVENTS_AVAILABLE = True
except Exception:
    QAccessible = None
    QAccessibleEvent = None
    ACCESSIBLE_EVENTS_AVAILABLE = False


# On Windows a windowed (no console) program would flash a console window for
# every ffmpeg call unless this flag is passed.
SUBPROCESS_FLAGS = getattr(subprocess, "CREATE_NO_WINDOW", 0) if sys.platform == "win32" else 0


# ---------------------------------------------------------------------------
# Crash guard: in PyQt6 an unhandled Python exception inside a Qt callback can
# abort the whole program. This logs the error to a file and keeps running.
# ---------------------------------------------------------------------------
def _writable_dir(folder):
    try:
        os.makedirs(folder, exist_ok=True)
        probe = os.path.join(folder, ".write_test")
        with open(probe, "w") as handle:
            handle.write("x")
        os.remove(probe)
        return True
    except OSError:
        return False


def get_reports_folder():
    """Reports (the daily folder report) sit next to Logs, Playlists and VoiceTracks."""
    if getattr(sys, "frozen", False):
        candidate = os.path.join(os.path.dirname(sys.executable), "Reports")
        if _writable_dir(candidate):
            return candidate
    fallback = os.path.join(os.path.expanduser("~"), "VisionStudio", "Reports")
    if _writable_dir(fallback):
        return fallback
    return tempfile.gettempdir()


def get_logs_folder():
    """Installed copy: a Logs folder inside the program folder, for example
    C:\\Program Files (x86)\\Vision Studio\\Logs. Otherwise a folder under the user profile."""
    if getattr(sys, "frozen", False):
        candidate = os.path.join(os.path.dirname(sys.executable), "Logs")
        if _writable_dir(candidate):
            return candidate
    fallback = os.path.join(os.path.expanduser("~"), "VisionStudio", "Logs")
    if _writable_dir(fallback):
        return fallback
    return tempfile.gettempdir()


def get_voice_folder():
    """Voice tracks are saved here, next to Logs and Playlists."""
    if getattr(sys, "frozen", False):
        candidate = os.path.join(os.path.dirname(sys.executable), "VoiceTracks")
        if _writable_dir(candidate):
            return candidate
    fallback = os.path.join(os.path.expanduser("~"), "VisionStudio", "VoiceTracks")
    if _writable_dir(fallback):
        return fallback
    return tempfile.gettempdir()


def get_recordings_folder():
    """Live-show recordings are saved here by default, next to Logs and Playlists."""
    if getattr(sys, "frozen", False):
        candidate = os.path.join(os.path.dirname(sys.executable), "Recordings")
        if _writable_dir(candidate):
            return candidate
    fallback = os.path.join(os.path.expanduser("~"), "VisionStudio", "Recordings")
    if _writable_dir(fallback):
        return fallback
    return tempfile.gettempdir()


# --- Start with Windows (current user, no administrator rights needed) ---
AUTOSTART_VALUE_NAME = "VisionStudio"
AUTOSTART_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"


def autostart_command():
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}" --startup'
    return f'"{sys.executable}" "{os.path.abspath(sys.argv[0])}" --startup'


def autostart_enabled():
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, AUTOSTART_KEY) as key:
            winreg.QueryValueEx(key, AUTOSTART_VALUE_NAME)
            return True
    except Exception:
        return False


def set_autostart(enabled):
    """Adds or removes the Windows start-up entry. Returns (ok, message)."""
    try:
        import winreg
    except ImportError:
        return False, "Starting with Windows only works on Windows."
    try:
        with winreg.CreateKey(winreg.HKEY_CURRENT_USER, AUTOSTART_KEY) as key:
            if enabled:
                winreg.SetValueEx(key, AUTOSTART_VALUE_NAME, 0, winreg.REG_SZ, autostart_command())
            else:
                try:
                    winreg.DeleteValue(key, AUTOSTART_VALUE_NAME)
                except FileNotFoundError:
                    pass
        return True, "Vision Studio will start with Windows, in the system tray." if enabled else \
            "Vision Studio will no longer start with Windows."
    except Exception as e:
        return False, f"Could not change the Windows start-up setting: {e}"


def refresh_autostart_path():
    """If start-up is on, keep its command pointing at this copy of the program (after a reinstall or move)."""
    if autostart_enabled():
        set_autostart(True)


def keep_system_awake():
    """Asks Windows not to sleep while Vision Studio is open. The display may still turn off."""
    try:
        import ctypes
        ctypes.windll.kernel32.SetThreadExecutionState(0x80000001)   # ES_CONTINUOUS | ES_SYSTEM_REQUIRED
    except Exception:
        pass


def get_layouts_folder():
    """Keyboard layout files (one .json per automation system) live here, next to Logs and Playlists."""
    if getattr(sys, "frozen", False):
        candidate = os.path.join(os.path.dirname(sys.executable), "Layouts")
        if _writable_dir(candidate):
            return candidate
    fallback = os.path.join(os.path.expanduser("~"), "VisionStudio", "Layouts")
    if _writable_dir(fallback):
        return fallback
    return tempfile.gettempdir()


APP_VERSION = "26.0"             # the release number; changes only when Luis names a new one (26.1, 26.2 ... 27.0)
BUILD_NUMBER = 0                  # goes up by one with every update; starts again at 1 with a new version
BUILD_DATE = "2026-10-20"         # the day this build was made
BUILD_ID = f"{BUILD_DATE}.{BUILD_NUMBER}"      # kept for the log


class RunLog:
    """A plain text as-run log, one file per day: what played, which break items ran, alerts and errors."""

    KEEP_DAYS = 60

    def __init__(self):
        self.folder = get_logs_folder()
        self.lock = threading.Lock()
        self.prune()

    def path_for_today(self):
        return os.path.join(self.folder, time.strftime("%Y-%m-%d") + ".log")

    def write(self, kind, text):
        try:
            with self.lock:
                os.makedirs(self.folder, exist_ok=True)
                with open(self.path_for_today(), "a", encoding="utf-8") as handle:
                    handle.write(f"{time.strftime('%H:%M:%S')}  {kind:<7} {text}\n")
        except Exception:
            pass

    def prune(self):
        cutoff = time.time() - self.KEEP_DAYS * 86400
        try:
            for name in os.listdir(self.folder):
                full = os.path.join(self.folder, name)
                if name.lower().endswith(".log") and os.path.isfile(full) and os.path.getmtime(full) < cutoff:
                    os.remove(full)
        except OSError:
            pass


RUN_LOG = RunLog()
ERROR_LOG_PATH = os.path.join(RUN_LOG.folder, "errors.log")
_CRASH_NOTIFIER = {"callback": None}


def _log_exception(exc_type, exc_value, exc_tb):
    try:
        with open(ERROR_LOG_PATH, "a", encoding="utf-8") as log_file:
            log_file.write(time.strftime("%Y-%m-%d %H:%M:%S") + "\n")
            log_file.write("".join(traceback.format_exception(exc_type, exc_value, exc_tb)))
            log_file.write("\n")
    except Exception:
        pass
    callback = _CRASH_NOTIFIER.get("callback")
    if callback:
        try:
            callback(f"Internal error: {exc_value}. Details saved to {ERROR_LOG_PATH}")
        except Exception:
            pass


def disable_power_throttling():
    """Windows may slow a program that is hidden in the tray; ask it not to, so the stream keeps flowing."""
    if sys.platform != "win32":
        return
    try:
        import ctypes
        from ctypes import wintypes

        class PROCESS_POWER_THROTTLING_STATE(ctypes.Structure):
            _fields_ = [("Version", wintypes.ULONG), ("ControlMask", wintypes.ULONG), ("StateMask", wintypes.ULONG)]

        state = PROCESS_POWER_THROTTLING_STATE(1, 1, 0)   # execution-speed throttling: controlled, and switched off
        ctypes.windll.kernel32.SetProcessInformation(
            ctypes.windll.kernel32.GetCurrentProcess(), 4, ctypes.byref(state), ctypes.sizeof(state))
    except Exception:
        pass


def install_crash_guard():
    sys.excepthook = _log_exception

    def thread_hook(args):
        _log_exception(args.exc_type, args.exc_value, args.exc_traceback)

    threading.excepthook = thread_hook


# ---------------------------------------------------------------------------
# FFmpeg bundling: looks for ffmpeg bundled inside the PyInstaller executable
# first, and falls back to a system-installed ffmpeg if not found.
# ---------------------------------------------------------------------------
def get_ffmpeg_path():
    if getattr(sys, "frozen", False):
        base_path = getattr(sys, "_MEIPASS", os.path.dirname(sys.executable))
        bundled = os.path.join(base_path, "ffmpeg", "ffmpeg.exe")
        if os.path.isfile(bundled):
            return bundled
        bundled_nox = os.path.join(base_path, "ffmpeg", "ffmpeg")
        if os.path.isfile(bundled_nox):
            return bundled_nox
    return "ffmpeg"


SUPPORTED_AUDIO = (".mp3", ".wav", ".ogg", ".flac", ".m4a", ".aac", ".opus")

SLOT_CONFIG = {
    ":00": {"folder_key": ":00", "sequence": "sandwich"},
    ":15": {"folder_key": ":15", "sequence": "sandwich"},
    ":30": {"folder_key": ":30", "sequence": "simple"},
    ":45": {"folder_key": ":45", "sequence": "sandwich"},
}

CROSSFADE_LEAD_SECONDS = 10
BREAK_WINDOW_DEFAULT = 120  # a song that ends this many seconds (or fewer) before a mark hands over to the break
FADE_STEPS = 20
FADE_INTERVAL_MS = (CROSSFADE_LEAD_SECONDS * 1000) // FADE_STEPS

# How far music ducks under the microphone while it's live.
MIC_DUCKING_LEVEL = 0.25
DUCK_FADE_STEPS = 10
DUCK_FADE_INTERVAL_MS = 30

MAX_ENCODER_SLOTS = 24
PROTOCOL_OPTIONS = ["Icecast", "Shoutcast", "Live365"]
FORMAT_OPTIONS = ["MP3", "AAC"]

# Format of the program mix that is fed to the encoders.
STREAM_SAMPLE_RATE = 44100
STREAM_CHANNELS = 2
MIX_INTERVAL_MS = 20
MAX_SOURCE_BUFFER_SECONDS = 4

# An encoder counts as connected once its ffmpeg process has stayed alive this long.
CONNECT_CONFIRM_SECONDS = 3

# ---------------------------------------------------------------------------
# Broadcast console color palette (dark charcoal console, green = on air,
# red = live mic / problem, amber = warning, blue = selected / active).
# ---------------------------------------------------------------------------

COLOR_BACKGROUND = "#1A1A1A"
COLOR_PANEL_DARK = "#232323"
COLOR_BORDER = "#3A3A3A"
COLOR_TEXT_BRIGHT = "#F0F0F0"
COLOR_TEXT_DIM = "#A0A0A0"
COLOR_ON_AIR_GREEN = "#3DDC84"
COLOR_LIVE_RED = "#E53935"
COLOR_WARNING_AMBER = "#FFB300"
COLOR_ACTIVE_BLUE = "#3B82F6"

BUTTON_STYLE_CONSOLE = f"""
    QPushButton {{
        background-color: {COLOR_PANEL_DARK};
        color: {COLOR_TEXT_BRIGHT};
        border: 1px solid {COLOR_BORDER};
        border-radius: 4px;
        padding: 4px 8px;
    }}
    QPushButton:hover {{
        border: 1px solid {COLOR_ACTIVE_BLUE};
    }}
    QPushButton:pressed {{
        background-color: {COLOR_ACTIVE_BLUE};
    }}
"""

SLIDER_STYLE_DECK_FADER = f"""
    QSlider::groove:vertical {{
        background: {COLOR_PANEL_DARK};
        width: 6px;
        border-radius: 3px;
    }}
    QSlider::handle:vertical {{
        background: {COLOR_ON_AIR_GREEN};
        height: 14px;
        margin: 0 -6px;
        border-radius: 7px;
    }}
"""

SLIDER_STYLE_CROSSFADER = f"""
    QSlider::groove:horizontal {{
        background: {COLOR_PANEL_DARK};
        height: 6px;
        border-radius: 3px;
    }}
    QSlider::handle:horizontal {{
        background: {COLOR_ACTIVE_BLUE};
        width: 14px;
        margin: -6px 0;
        border-radius: 7px;
    }}
"""

MAIN_WINDOW_STYLE = f"""
    QWidget {{
        background-color: {COLOR_BACKGROUND};
        color: {COLOR_TEXT_BRIGHT};
    }}
    QTabWidget::pane {{
        border: 1px solid {COLOR_BORDER};
    }}
    QTabBar::tab {{
        background: {COLOR_PANEL_DARK};
        color: {COLOR_TEXT_DIM};
        padding: 6px 12px;
    }}
    QTabBar::tab:selected {{
        background: {COLOR_ACTIVE_BLUE};
        color: {COLOR_TEXT_BRIGHT};
    }}
    QLineEdit, QComboBox {{
        background-color: {COLOR_PANEL_DARK};
        color: {COLOR_TEXT_BRIGHT};
        border: 1px solid {COLOR_BORDER};
        border-radius: 3px;
        padding: 2px;
    }}
    QPushButton {{
        background-color: {COLOR_PANEL_DARK};
        color: {COLOR_TEXT_BRIGHT};
        border: 1px solid {COLOR_BORDER};
        border-radius: 4px;
        padding: 4px 10px;
    }}
    QPushButton:hover {{
        border: 1px solid {COLOR_ACTIVE_BLUE};
    }}
    QPushButton:pressed {{
        background-color: {COLOR_ACTIVE_BLUE};
    }}
"""


# Target loudness for normalization, in LUFS (common broadcast/streaming target).
LOUDNESS_TARGET_LUFS = -16.0
NORMALIZED_CACHE_DIR = os.path.join(tempfile.gettempdir(), "visionstudio_normalized")
NORMALIZATION_STATE = {"last_error": "", "ffmpeg_missing": False}


def scan_audio_files(folder, recursive=True):
    """Finds audio files in a folder, including every subfolder unless recursive=False."""
    if not folder or not os.path.isdir(folder):
        return []
    found = []
    try:
        if recursive:
            for root, dirs, files in os.walk(folder):
                dirs[:] = [d for d in dirs if not d.startswith(".")]
                for name in files:
                    if name.lower().endswith(SUPPORTED_AUDIO):
                        found.append(os.path.join(root, name))
        else:
            for name in os.listdir(folder):
                full = os.path.join(folder, name)
                if os.path.isfile(full) and name.lower().endswith(SUPPORTED_AUDIO):
                    found.append(full)
    except OSError:
        pass
    found.sort(key=lambda p: p.lower())
    return found


# --- loudness normalization -------------------------------------------------
_FILE_LOCKS = {}
_FILE_LOCKS_GUARD = threading.Lock()


def _lock_for(path):
    with _FILE_LOCKS_GUARD:
        if path not in _FILE_LOCKS:
            _FILE_LOCKS[path] = threading.Lock()
        return _FILE_LOCKS[path]


def get_normalized_path_for(original_path):
    os.makedirs(NORMALIZED_CACHE_DIR, exist_ok=True)
    try:
        mtime = int(os.path.getmtime(original_path))
        size = os.path.getsize(original_path)
    except OSError:
        mtime = 0
        size = 0
    digest = hashlib.md5(os.path.abspath(original_path).encode("utf-8", "replace")).hexdigest()[:12]
    base = os.path.splitext(os.path.basename(original_path))[0]
    safe_base = "".join(c for c in base if c.isalnum() or c in ("_", "-"))[:40]
    return os.path.join(NORMALIZED_CACHE_DIR, f"{safe_base}.{digest}.{mtime}.{size}.norm2.wav")


def is_normalized_cached(original_path):
    return os.path.isfile(get_normalized_path_for(original_path))


def run_ffmpeg(cmd, timeout=900, cancel_event=None):
    """Runs ffmpeg without blocking forever. Returns (return_code, stderr_text).
    Return code -1 = cancelled, -2 = timed out, -3 = ffmpeg not found."""
    try:
        err_file = tempfile.TemporaryFile()
        proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=err_file,
                                creationflags=SUBPROCESS_FLAGS)
    except FileNotFoundError:
        return -3, "ffmpeg not found"
    except Exception as e:
        return -3, str(e)

    started = time.time()
    try:
        while True:
            try:
                proc.wait(timeout=0.25)
                break
            except subprocess.TimeoutExpired:
                pass
            if cancel_event is not None and cancel_event.is_set():
                proc.kill()
                proc.wait()
                return -1, "cancelled"
            if time.time() - started > timeout:
                proc.kill()
                proc.wait()
                return -2, "timed out"
        err_file.seek(0)
        text = err_file.read().decode("utf-8", "replace")
        return proc.returncode, text
    finally:
        try:
            err_file.close()
        except Exception:
            pass


def measure_loudness(path, cancel_event=None):
    """First pass: measures the file's loudness. Returns the measured values or None."""
    cmd = [get_ffmpeg_path(), "-hide_banner", "-nostats", "-i", path, "-vn", "-af",
           f"loudnorm=I={LOUDNESS_TARGET_LUFS}:TP=-1.5:LRA=11:print_format=json",
           "-f", "null", "-"]
    code, text = run_ffmpeg(cmd, cancel_event=cancel_event)
    if code == -3:
        NORMALIZATION_STATE["ffmpeg_missing"] = True
        NORMALIZATION_STATE["last_error"] = "ffmpeg was not found"
        return None
    if code != 0:
        return None
    match = re.search(r'\{[^{}]*"input_i"[^{}]*\}', text, re.DOTALL)
    if not match:
        return None
    try:
        return json.loads(match.group(0))
    except Exception:
        return None


def normalize_file_loudness(original_path, on_status=None, cancel_event=None):
    """
    Two-pass loudness normalization to LOUDNESS_TARGET_LUFS. Pass one measures
    the file, pass two applies an exact linear gain, which is far more accurate
    for short jingles and ads than a single dynamic pass. The result is cached,
    so each file is only processed once. Returns the path to play: the
    normalized copy on success, or the original file if anything fails.
    """
    if not original_path or not os.path.isfile(original_path):
        return original_path

    out_path = get_normalized_path_for(original_path)
    if os.path.isfile(out_path):
        return out_path

    with _lock_for(original_path):
        if os.path.isfile(out_path):
            return out_path

        data = measure_loudness(original_path, cancel_event)
        if NORMALIZATION_STATE["ffmpeg_missing"]:
            return original_path

        measured_ok = False
        filter_text = f"loudnorm=I={LOUDNESS_TARGET_LUFS}:TP=-1.5:LRA=11"
        if data:
            try:
                measured_i = float(data["input_i"])
                if measured_i > -70.0:
                    filter_text = (
                        f"loudnorm=I={LOUDNESS_TARGET_LUFS}:TP=-1.5:LRA=11"
                        f":measured_I={data['input_i']}:measured_LRA={data['input_lra']}"
                        f":measured_TP={data['input_tp']}:measured_thresh={data['input_thresh']}"
                        f":offset={data['target_offset']}:linear=true"
                    )
                    measured_ok = True
            except Exception:
                measured_ok = False

        tmp_path = out_path + f".{os.getpid()}.{threading.get_ident()}.part"
        cmd = [get_ffmpeg_path(), "-y", "-hide_banner", "-nostats", "-i", original_path,
               "-vn", "-af", filter_text, "-ar", "44100", "-ac", "2",
               "-c:a", "pcm_s16le", "-f", "wav", tmp_path]
        code, text = run_ffmpeg(cmd, cancel_event=cancel_event)
        if code == 0 and os.path.isfile(tmp_path) and os.path.getsize(tmp_path) > 1000:
            try:
                os.replace(tmp_path, out_path)
            except OSError:
                pass
            if os.path.isfile(out_path):
                if on_status:
                    note = "" if measured_ok else " (approximate)"
                    on_status(f"Loudness matched{note}: {os.path.basename(original_path)}")
                return out_path

        try:
            if os.path.isfile(tmp_path):
                os.remove(tmp_path)
        except OSError:
            pass
        NORMALIZATION_STATE["last_error"] = text[-200:] if text else f"ffmpeg exit code {code}"
        if code == -3:
            NORMALIZATION_STATE["ffmpeg_missing"] = True
        if on_status and code not in (-1,):
            on_status(f"Loudness matching skipped for {os.path.basename(original_path)}.")
        return original_path


class NormalizeJob(QThread):
    """Background loudness analysis of a list of files, so importing never freezes the app."""
    progress = pyqtSignal(int, int, str)
    job_done = pyqtSignal(int, int)

    def __init__(self, paths, parent=None):
        super().__init__(parent)
        self.paths = list(paths)
        self.cancel_event = threading.Event()

    def run(self):
        ok = 0
        failed = 0
        index = 0
        while index < len(self.paths):
            if self.cancel_event.is_set():
                break
            path = self.paths[index]
            index += 1
            result = normalize_file_loudness(path, cancel_event=self.cancel_event)
            if result != path:
                ok += 1
            else:
                failed += 1
            self.progress.emit(index, len(self.paths), os.path.basename(path))
        self.job_done.emit(ok, failed)

    def cancel(self):
        self.cancel_event.set()


class NormalizeManager(QObject):
    """
    Starts loudness analysis the moment files are imported. Bulk imports run
    one after another in a single background thread; priority requests (the
    next few tracks in the queue) get their own thread so they never wait.
    """
    progress = pyqtSignal(int, int, str)
    batch_done = pyqtSignal(int, int)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.bulk_job = None
        self.priority_jobs = []

    def start(self, paths, priority=False):
        pending = [p for p in paths if p and os.path.isfile(p) and not is_normalized_cached(p)]
        if not pending or NORMALIZATION_STATE["ffmpeg_missing"]:
            return
        if priority:
            job = NormalizeJob(pending, self)
            job.job_done.connect(lambda ok, failed, j=job: self._priority_finished(j))
            self.priority_jobs.append(job)
            job.start()
            return
        if self.bulk_job is not None and self.bulk_job.isRunning():
            known = set(self.bulk_job.paths)
            for p in pending:
                if p not in known:
                    self.bulk_job.paths.append(p)
            return
        job = NormalizeJob(pending, self)
        job.progress.connect(self.progress)
        job.job_done.connect(self._bulk_finished)
        self.bulk_job = job
        job.start()

    def _priority_finished(self, job):
        if job in self.priority_jobs:
            self.priority_jobs.remove(job)

    def _bulk_finished(self, ok, failed):
        self.batch_done.emit(ok, failed)

    def shutdown(self):
        jobs = list(self.priority_jobs)
        if self.bulk_job is not None:
            jobs.append(self.bulk_job)
        for job in jobs:
            job.cancel()
        for job in jobs:
            job.wait(5000)


# --- track metadata ----------------------------------------------------------
def get_track_metadata(file_path):
    """Returns artist, title and album for a file, with the file name as a fallback title."""
    meta = {"artist": "", "title": "", "album": ""}
    if MUTAGEN_AVAILABLE and file_path and os.path.isfile(file_path):
        try:
            audio = mutagen.File(file_path, easy=True)
            if audio and audio.tags:
                for key in meta:
                    values = audio.tags.get(key)
                    if values:
                        meta[key] = str(values[0]).strip()
        except Exception:
            pass
    if not meta["title"]:
        meta["title"] = os.path.splitext(os.path.basename(file_path or ""))[0]
    return meta


# --- audio devices -----------------------------------------------------------
def get_selected_output_device(settings):
    wanted = settings.value("output_device", "")
    devices = QMediaDevices.audioOutputs()
    for device in devices:
        if device.description() == wanted:
            return device
    return QMediaDevices.defaultAudioOutput() if devices else None


def get_selected_input_device(settings):
    wanted = settings.value("input_device", "")
    devices = QMediaDevices.audioInputs()
    for device in devices:
        if device.description() == wanted:
            return device
    return QMediaDevices.defaultAudioInput() if devices else None


# --- screen reader announcements ---------------------------------------------
def announce_accessible(label, text):
    """Shows text in a label and raises accessibility events so NVDA/JAWS speak it."""
    label.setText(text)
    label.setAccessibleName(text)
    if ACCESSIBLE_EVENTS_AVAILABLE:
        try:
            QAccessible.updateAccessibleEvent(QAccessibleEvent(label, QAccessible.Event.NameChanged))
            QAccessible.updateAccessibleEvent(QAccessibleEvent(label, QAccessible.Event.Alert))
        except Exception:
            pass


# --- beeps -------------------------------------------------------------------
def write_tone_sequence_wav(path, tones, amplitude=15000, rate=44100):
    """tones is a list of (frequency_hz, duration_s, gap_s_after)."""
    frames = bytearray()
    ramp = int(rate * 0.005)
    for freq, duration, gap in tones:
        count = int(rate * duration)
        for i in range(count):
            envelope = 1.0
            if ramp:
                envelope = min(1.0, i / ramp, (count - i) / ramp)
            sample = int(amplitude * envelope * math.sin(2 * math.pi * freq * i / rate))
            frames += struct.pack("<h", sample)
        frames += b"\x00\x00" * int(rate * gap)
    with wave.open(path, "w") as wav_file:
        wav_file.setnchannels(1)
        wav_file.setsampwidth(2)
        wav_file.setframerate(rate)
        wav_file.writeframes(bytes(frames))


def get_or_create_beep(name, tones):
    os.makedirs(NORMALIZED_CACHE_DIR, exist_ok=True)
    path = os.path.join(NORMALIZED_CACHE_DIR, name)
    if not os.path.isfile(path):
        write_tone_sequence_wav(path, tones)
    return path


def get_or_create_warning_beep_path():
    return get_or_create_beep("warning_beep_v2.wav", [(880.0, 0.25, 0.0)])


def get_or_create_connect_beep_path():
    # Rising three-note chirp: an encoder just connected.
    return get_or_create_beep("connect_beep.wav",
                              [(660.0, 0.10, 0.03), (880.0, 0.10, 0.03), (1175.0, 0.16, 0.0)])


def get_or_create_disconnect_beep_path():
    # Falling three-note chirp: an encoder just disconnected.
    return get_or_create_beep("disconnect_beep.wav",
                              [(1175.0, 0.10, 0.03), (880.0, 0.10, 0.03), (523.0, 0.24, 0.0)])


class HostBeep:
    """
    A cue sound played only on this computer's own output (the host side). It is
    never sent to the encoders. It waits for the sound to finish loading before
    playing, and plays through whichever output device is selected in Settings.
    """

    def __init__(self, path, device=None, volume=0.7):
        self.pending = False
        self.effect = QSoundEffect()
        if device is not None:
            self.effect.setAudioDevice(device)
        self.effect.setVolume(volume)
        self.effect.statusChanged.connect(self._on_status_changed)
        self.effect.setSource(QUrl.fromLocalFile(path))

    def set_device(self, device):
        if device is not None:
            self.effect.setAudioDevice(device)

    def play(self):
        status = self.effect.status()
        if status == QSoundEffect.Status.Ready:
            self.effect.play()
        else:
            self.pending = True

    def _on_status_changed(self):
        if self.effect.status() == QSoundEffect.Status.Ready and self.pending:
            self.pending = False
            self.effect.play()


# ---------------------------------------------------------------------------
# Album artwork extraction (current + upcoming track preview)
# ---------------------------------------------------------------------------

ARTWORK_PLACEHOLDER_SIZE = 100

# How many seconds before a track ends the warning beep should fire, giving
# the DJ a Station-Playlist-style heads-up that the track is wrapping up.
BEEP_WARNING_SECONDS = 5

# Default artist/title separation window, in seconds. Station-Playlist-style:
# the same song or the same artist shouldn't repeat until this much time has
# passed since it last played. Applies globally, regardless of category.
DEFAULT_SEPARATION_SECONDS = 2 * 60 * 60


def get_embedded_artwork(file_path):
    """
    Pulls embedded cover art out of an audio file's tags, if any is present.
    Returns raw image bytes (JPEG/PNG) or None if there's no art, the file
    has no tags, or mutagen isn't available.
    """
    if not MUTAGEN_AVAILABLE or not file_path or not os.path.isfile(file_path):
        return None
    try:
        lower = file_path.lower()
        if lower.endswith(".mp3"):
            tags = ID3(file_path)
            for key in tags.keys():
                if key.startswith("APIC"):
                    return tags[key].data
        elif lower.endswith(".flac"):
            audio = FLAC(file_path)
            if audio.pictures:
                return audio.pictures[0].data
        elif lower.endswith(".m4a"):
            audio = MP4(file_path)
            covers = audio.tags.get("covr") if audio.tags else None
            if covers:
                return bytes(covers[0])
        else:
            audio = mutagen.File(file_path)
            if audio and getattr(audio, "pictures", None):
                return audio.pictures[0].data
    except Exception:
        return None
    return None


def build_artwork_pixmap(file_path, size=ARTWORK_PLACEHOLDER_SIZE):
    data = get_embedded_artwork(file_path)
    if not data:
        return None
    pixmap = QPixmap()
    if pixmap.loadFromData(data):
        return pixmap.scaled(size, size, Qt.AspectRatioMode.KeepAspectRatio,
                              Qt.TransformationMode.SmoothTransformation)
    return None


def get_track_artist(file_path):
    """Reads the lowercased artist tag off a file, used for separation-rule comparisons."""
    if not MUTAGEN_AVAILABLE or not file_path or not os.path.isfile(file_path):
        return ""
    try:
        audio = mutagen.File(file_path, easy=True)
        if audio and audio.tags:
            artist_values = audio.tags.get("artist")
            if artist_values:
                return artist_values[0].strip().lower()
    except Exception:
        pass
    return ""


# ---------------------------------------------------------------------------
# Fade controller (volume ramps for crossfades, ducking, mute)
# ---------------------------------------------------------------------------

class FadeController:
    """
    Gradually ramps a QAudioOutput's volume up or down over time. Accepts
    an optional on_progress(start_vol, end_vol, progress_0_to_1) callback so
    a UI element, like a visual crossfader, can move in step with the real
    fade instead of guessing at timing separately.
    """

    def __init__(self, audio_output, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS, on_progress=None):
        self.audio_output = audio_output
        self.steps = steps
        self.interval_ms = interval_ms
        self.on_progress = on_progress
        self.timer = QTimer()
        self.timer.timeout.connect(self._step)
        self.current_step = 0
        self.start_vol = 1.0
        self.end_vol = 1.0
        self.on_complete = None
        self.mute_check = None  # optional callable; True means output stays silent

    def fade_to(self, target_volume, on_complete=None, steps=None, interval_ms=None):
        self.timer.stop()
        if steps is not None:
            self.steps = steps
        if interval_ms is not None:
            self.interval_ms = interval_ms
        self.start_vol = self.audio_output.volume()
        self.end_vol = target_volume
        self.current_step = 0
        self.on_complete = on_complete
        self.timer.start(self.interval_ms)

    def _step(self):
        self.current_step += 1
        progress = self.current_step / self.steps
        new_vol = self.start_vol + (self.end_vol - self.start_vol) * progress
        if self.mute_check is not None and self.mute_check():
            new_vol = 0.0
        self.audio_output.setVolume(max(0.0, min(1.0, new_vol)))
        if self.on_progress:
            self.on_progress(self.start_vol, self.end_vol, progress)
        if self.current_step >= self.steps:
            self.timer.stop()
            if self.mute_check is not None and self.mute_check():
                self.audio_output.setVolume(0.0)
            else:
                self.audio_output.setVolume(self.end_vol)
            if self.on_complete:
                self.on_complete()


# ---------------------------------------------------------------------------
# Play history (feeds the separation rules, Station-Playlist style)
# ---------------------------------------------------------------------------

class PlayHistory:
    """
    Remembers when each track and each artist last played, so the rotation
    can enforce a minimum separation window between repeats -- persists
    across reshuffles rather than forgetting what already played.
    """

    def __init__(self):
        self.last_played_track = {}
        self.last_played_artist = {}

    def record_play(self, file_path):
        now = time.time()
        self.last_played_track[file_path] = now
        artist = get_track_artist(file_path)
        if artist:
            self.last_played_artist[artist] = now

    def seconds_since_track_played(self, file_path):
        last = self.last_played_track.get(file_path)
        if last is None:
            return None
        return time.time() - last

    def seconds_since_artist_played(self, file_path):
        artist = get_track_artist(file_path)
        if not artist:
            return None
        last = self.last_played_artist.get(artist)
        if last is None:
            return None
        return time.time() - last

    def violates_separation(self, file_path, separation_seconds):
        track_gap = self.seconds_since_track_played(file_path)
        if track_gap is not None and track_gap < separation_seconds:
            return True
        artist_gap = self.seconds_since_artist_played(file_path)
        if artist_gap is not None and artist_gap < separation_seconds:
            return True
        return False




# ---------------------------------------------------------------------------
# Track durations, time formatting
# ---------------------------------------------------------------------------

HOUR_MARKER_TOKEN = "#HOURMARKER#"
AVERAGE_TRACK_SECONDS = 210.0
_DURATION_CACHE = {}


def is_hour_marker(entry):
    return isinstance(entry, str) and entry.startswith(HOUR_MARKER_TOKEN)


def marker_for(day, hour):
    """An hour marker that remembers which hour it opens, e.g. #HOURMARKER#2026101821."""
    return f"{HOUR_MARKER_TOKEN}{day.strftime('%Y%m%d')}{hour:02d}"


def marker_tag(entry):
    return entry[len(HOUR_MARKER_TOKEN):] if is_hour_marker(entry) else ""


def get_track_duration(path):
    """Length of an audio file in seconds (tags), or an average guess if unknown."""
    if path in _DURATION_CACHE:
        return _DURATION_CACHE[path]
    seconds = 0.0
    if MUTAGEN_AVAILABLE and path and os.path.isfile(path):
        try:
            audio = mutagen.File(path)
            if audio is not None and getattr(audio, "info", None) is not None:
                seconds = float(audio.info.length)
        except Exception:
            seconds = 0.0
    if seconds <= 0:
        seconds = AVERAGE_TRACK_SECONDS
    _DURATION_CACHE[path] = seconds
    return seconds


def speak_duration(seconds):
    """'3 minutes 12 seconds' style text, good for screen readers."""
    seconds = max(0, int(round(seconds)))
    hours, rest = divmod(seconds, 3600)
    minutes, secs = divmod(rest, 60)
    parts = []
    if hours:
        parts.append(f"{hours} hour{'s' if hours != 1 else ''}")
    if minutes:
        parts.append(f"{minutes} minute{'s' if minutes != 1 else ''}")
    if secs or not parts:
        parts.append(f"{secs} second{'s' if secs != 1 else ''}")
    return " ".join(parts)


def hour_label(hour):
    return f"{hour % 24:02d}00"


def voice_underlay_ms(path):
    """A voice track's file name carries how many seconds of the next song's intro play under its end
    (voicetrack_..._u6.wav). Returns milliseconds, or None when the file is not a voice track."""
    if not path:
        return None
    name = os.path.splitext(os.path.basename(path))[0].lower()
    if not name.startswith("voicetrack_"):
        return None
    match = re.search(r"_u(\d+)$", name)
    return int(match.group(1)) * 1000 if match else 0


def format_track_display(path):
    if is_hour_marker(path):
        tag = marker_tag(path)
        if tag == "VOICE":
            return "---- Voice track slot (empty) ----"
        if len(tag) >= 2 and tag[-2:].isdigit():
            return f"---- Hour marker: {hour_label(int(tag[-2:]) % 24)} ----"
        return "---- Hour marker ----"
    name = os.path.basename(path)
    if name.lower().startswith("voicetrack_"):
        stamp = re.sub(r"_u\d+$", "", os.path.splitext(name)[0][len("voicetrack_"):]).replace("_", " ")
        return f"Voice track {stamp}"
    meta = get_track_metadata(path)
    if meta["artist"]:
        return f"{meta['artist']} - {meta['title']}"
    return meta["title"]


def describe_folder(path):
    """Shows the folder path, how many audio files it holds, and the first one, so you can see it is being read."""
    if not path:
        return "not set"
    if not os.path.isdir(path):
        return f"{path} (folder not found)"
    files = sorted(scan_audio_files(path), key=lambda p: p.lower())
    if not files:
        return f"{path} (no audio files found)"
    return f"{path} ({len(files)} audio files, first: {os.path.basename(files[0])})"


# ---------------------------------------------------------------------------
# Rotations: unlimited named rotations, each backed by a folder
# ---------------------------------------------------------------------------

def pretty_folder_name(folder_name):
    name = re.sub(r"[_\-]+", " ", folder_name).strip()
    name = re.sub(r"\s+", " ", name)
    if name and name == name.lower():
        name = name.title()
    return name or folder_name


class MusicRotation:
    def __init__(self, name, folder, recursive=True, auto=False, rotation_id=None, regular=True, mix=False):
        self.id = rotation_id or uuid.uuid4().hex[:8]
        self.mix = mix              # the one rotation over the whole music folder: every folder feeds every hour
        self.regular = regular      # part of the everyday schedule; holiday music is not until you schedule it
        self.name = name
        self.folder = folder
        self.recursive = recursive
        self.auto = auto  # created automatically from a subfolder of the music library

    def to_dict(self):
        return {"id": self.id, "name": self.name, "folder": self.folder,
                "recursive": self.recursive, "auto": self.auto, "regular": self.regular, "mix": self.mix}

    @staticmethod
    def from_dict(data):
        return MusicRotation(data.get("name", "Rotation"), data.get("folder", ""),
                             bool(data.get("recursive", True)), bool(data.get("auto", False)),
                             data.get("id"), bool(data.get("regular", True)), bool(data.get("mix", False)))

    def track_paths(self):
        return scan_audio_files(self.folder, self.recursive)


class RotationLibrary:
    """
    Holds every rotation. Pointing the music library at a folder builds one
    rotation per subfolder (a "category") automatically. Anything that changes
    the list calls on_changed(kind) so the schedule can follow right away.
    """

    def __init__(self, settings, on_changed=None):
        self.settings = settings
        self.on_changed = on_changed
        self.rotations = []
        self.known_files = {}
        self.load()

    def load(self):
        try:
            data = json.loads(self.settings.value("rotations_json", "[]"))
            self.rotations = [MusicRotation.from_dict(d) for d in data]
        except Exception:
            self.rotations = []

    def save(self):
        try:
            self.settings.setValue("rotations_json", json.dumps([r.to_dict() for r in self.rotations]))
        except Exception:
            pass

    def _changed(self, kind):
        self.save()
        if self.on_changed:
            self.on_changed(kind)

    def find(self, rotation_id):
        for rotation in self.rotations:
            if rotation.id == rotation_id:
                return rotation
        return None

    def unique_name(self, name, ignore_id=None):
        taken = {r.name.lower() for r in self.rotations if r.id != ignore_id}
        candidate = name.strip() or "Rotation"
        base = candidate
        number = 2
        while candidate.lower() in taken:
            candidate = f"{base} {number}"
            number += 1
        return candidate

    def add_rotation(self, name, folder, recursive=True, auto=False, notify=True, regular=None):
        if regular is None:
            regular = not self.rotations          # the very first rotations make the everyday schedule; later ones wait to be scheduled
        rotation = MusicRotation(self.unique_name(name), folder, recursive, auto, regular=regular)
        self.rotations.append(rotation)
        if notify:
            self._changed("added")
        return rotation

    def remove_rotation(self, rotation_id):
        rotation = self.find(rotation_id)
        if rotation is None:
            return False
        self.rotations.remove(rotation)
        self.known_files.pop(rotation_id, None)
        self._changed("removed")
        return True

    def rename_rotation(self, rotation_id, new_name):
        rotation = self.find(rotation_id)
        if rotation is None or not new_name.strip():
            return False
        rotation.name = self.unique_name(new_name, ignore_id=rotation_id)
        rotation.auto = False  # an edited rotation is no longer managed automatically
        self._changed("renamed")
        return True

    def set_rotation_folder(self, rotation_id, folder):
        rotation = self.find(rotation_id)
        if rotation is None or not folder:
            return False
        rotation.folder = folder
        rotation.recursive = True
        rotation.auto = False
        self.known_files.pop(rotation_id, None)
        self._changed("folder")
        return True

    def relink_folder(self, rotation_id, folder):
        """A category's folder changed: the rotation follows it without rebuilding the schedule."""
        rotation = self.find(rotation_id)
        if rotation is None or not folder:
            return False
        rotation.folder = folder
        rotation.recursive = True
        rotation.auto = False
        self.known_files.pop(rotation_id, None)
        self._changed("linked")
        return True

    def sync_from_root(self, root):
        """
        Builds rotations from the music library folder: every subfolder that holds
        audio becomes a rotation; loose files in the folder itself become one more.
        Safe to call repeatedly: it adds new subfolders and removes vanished ones
        without touching rotations you made or edited yourself.
        Returns (added_names, removed_names).
        """
        if not root or not os.path.isdir(root):
            return [], []
        wanted = []
        try:
            subdirs = sorted((d for d in os.listdir(root)
                              if not d.startswith(".") and os.path.isdir(os.path.join(root, d))),
                             key=str.lower)
        except OSError:
            subdirs = []
        for d in subdirs:
            path = os.path.join(root, d)
            if scan_audio_files(path):
                wanted.append((pretty_folder_name(d), path, True))
        if scan_audio_files(root, recursive=False):
            wanted.append(("Library" if not wanted else "Loose tracks", root, False))

        first_build = not self.rotations
        existing = {r.folder: r for r in self.rotations if r.auto}
        wanted_folders = {folder for _, folder, _ in wanted}
        added = []
        removed = []
        for name, folder, recursive in wanted:
            if folder in existing:
                existing[folder].recursive = recursive
            else:
                rotation = self.add_rotation(name, folder, recursive, auto=True, notify=False,
                                             regular=(not self.rotations) or first_build)
                added.append(rotation.name)
        for rotation in list(self.rotations):
            if rotation.auto and rotation.folder not in wanted_folders:
                self.rotations.remove(rotation)
                self.known_files.pop(rotation.id, None)
                removed.append(rotation.name)
        if added or removed:
            self._changed("added" if added else "removed")
        return added, removed

    def ensure_mix(self, root):
        """The "All Volumes (mixed)" rotation: the whole music folder in one rotation, so the folder rotor can
        give each of the (74) folders its turn in every hour. Made once, and kept pointing at the music folder."""
        mix = next((r for r in self.rotations if getattr(r, "mix", False)), None)
        if not root or not os.path.isdir(root):
            return mix
        if mix is None:
            mix = MusicRotation(self.unique_name("All Volumes (mixed)"), root, True, auto=False, regular=False, mix=True)
            self.rotations.append(mix)
            self.save()
        elif os.path.normcase(os.path.normpath(mix.folder)) != os.path.normcase(os.path.normpath(root)):
            mix.folder = root
            self.save()
        return mix

    def detect_new_files(self):
        """Compares every rotation's folder with the last look. Returns {rotation_id: [new files]}."""
        result = {}
        for rotation in self.rotations:
            if getattr(rotation, "mix", False):
                continue                      # its songs already show up under their own volumes
            current = set(rotation.track_paths())
            previous = self.known_files.get(rotation.id)
            self.known_files[rotation.id] = current
            if previous is None:
                continue
            new_files = sorted(current - previous, key=str.lower)
            if new_files:
                result[rotation.id] = new_files
        return result


class _Hours(list):
    """The 24 hourly rotations. Setting one by hand pins that hour, so the automatic spread leaves it alone."""

    def __init__(self, items, owner):
        super().__init__(items)
        self.owner = owner

    def __setitem__(self, index, value):
        super().__setitem__(index, value)
        if getattr(self.owner, "tracking", False) and isinstance(index, int):
            self.owner.pinned.add(index % 24)
            self.owner.save_pins()
            self.owner.save()


VOLUME_ROTOR_KEY = "volume_rotor_json"
PINNED_HOURS_KEY = "schedule_pinned_json"


class RotationSchedule:
    """
    A 24-hour schedule saying which rotation is live in each hour. Unless an hour has been set by hand, every
    rotation (volume) takes a turn before any volume plays twice: the ones that have waited longest, or have
    never played, come first, so no folder is left out for good. It regenerates whenever rotations change.
    """

    def __init__(self, settings, library):
        self.settings = settings
        self.library = library
        self.tracking = False
        self.pinned = set()
        self.hours = _Hours([None] * 24, self)
        self.events = None          # the dated schedules (EventLibrary), set by the app
        self._rotor = None
        self.load()
        self.ensure_valid()
        self.tracking = True

    # --- every volume gets a turn ---
    def hour_mode(self):
        """'mix' (default): every hour mixes all folders. 'volume': one volume per hour, every volume in turn.
        'fixed': the schedule exactly as set."""
        try:
            mode = str(self.settings.value("hour_mode", ""))
            if mode in ("mix", "volume", "fixed"):
                return mode
            if str(self.settings.value("rotate_all_volumes", "true")).lower() == "false":
                return "fixed"
        except Exception:
            pass
        return "mix"

    def rotate_enabled(self):
        return self.hour_mode() != "fixed"

    def mix_id(self):
        mix = next((r for r in self.library.rotations if getattr(r, "mix", False)), None)
        return mix.id if mix is not None else None

    def save_pins(self):
        try:
            self.settings.setValue(PINNED_HOURS_KEY, json.dumps(sorted(self.pinned)))
        except Exception:
            pass

    def state(self):
        if self._rotor is None:
            try:
                data = json.loads(str(self.settings.value(VOLUME_ROTOR_KEY, "{}")))
                self._rotor = data if isinstance(data, dict) else {}
            except Exception:
                self._rotor = {}
            for key, default in (("remaining", []), ("plan", {}), ("last", {}), ("count", {}), ("known", [])):
                self._rotor.setdefault(key, default)
            self._rotor.setdefault("rounds", 0)
        return self._rotor

    def save_state(self):
        try:
            self.settings.setValue(VOLUME_ROTOR_KEY, json.dumps(self.state()))
        except Exception:
            pass

    def regular_ids(self):
        ids = [r.id for r in self.library.rotations if getattr(r, "regular", True)]
        return ids or [r.id for r in self.library.rotations]

    def note_used(self, rotation_id, borrowed=False):
        """A volume went on air for an hour (or had a song borrowed from it): it goes to the back of the line."""
        st = self.state()
        st["last"][rotation_id] = time.time()
        if not borrowed:
            st["count"][rotation_id] = int(st["count"].get(rotation_id, 0)) + 1
        self.save_state()

    def volume_last_used(self, rotation_id):
        return float(self.state()["last"].get(rotation_id, 0))

    def planned_id(self, day, hour):
        """The volume for that hour: planned once, in order, and remembered."""
        fallback = self.hours[hour % 24]
        ids = self.regular_ids()
        if not ids:
            return fallback
        now = datetime.now()
        if day < now.date() or (day == now.date() and hour < now.hour):
            return fallback            # an hour that has already gone by is not planned
        st = self.state()
        valid = set(r.id for r in self.library.rotations)
        key = day.strftime("%Y%m%d") + f"{hour:02d}"
        if st["plan"].get(key) in valid:
            return st["plan"][key]
        known = [i for i in st["known"] if i in valid]
        remaining = [i for i in st["remaining"] if i in valid and i in ids]
        for i in ids:
            if i not in known:
                known.append(i)
                remaining.insert(0, i)          # a volume the program has not seen before goes first
        if not remaining:
            st["rounds"] = int(st["rounds"]) + 1
            remaining = sorted(ids, key=lambda i: (int(st["count"].get(i, 0)), float(st["last"].get(i, 0)), random.random()))
        previous = st["plan"].get((datetime.combine(day, datetime.min.time()) + timedelta(hours=hour - 1)).strftime("%Y%m%d%H"))
        pick = next((i for i in remaining if i != previous), remaining[0])
        remaining.remove(pick)
        st["plan"][key] = pick
        st["remaining"] = remaining
        st["known"] = known
        cutoff = (now - timedelta(days=3)).strftime("%Y%m%d00")
        st["plan"] = {k: v for k, v in st["plan"].items() if k >= cutoff}
        self.save_state()
        return pick

    def usage_lines(self):
        if self.hour_mode() == "mix" and self.mix_id():
            return ["Every hour mixes all the folders, the ones that have waited longest first."]
        ids = self.regular_ids()
        st = self.state()
        names = {r.id: r.name for r in self.library.rotations}
        waiting = [names[i] for i in st["remaining"] if i in names]
        never = [names[i] for i in ids if int(st["count"].get(i, 0)) == 0]
        lines = [f"Volumes (rotations): {len(ids)}. Round {int(st['rounds'])}: {len(ids) - len(waiting)} have had their turn, "
                 f"{len(waiting)} are still waiting.",
                 f"Never on air yet: {len(never)}" + (f" ({', '.join(never[:12])}{', ...' if len(never) > 12 else ''})" if never else "") + "."]
        return lines

    def load(self):
        try:
            data = json.loads(self.settings.value("schedule_json", "[]"))
            if isinstance(data, list) and len(data) == 24:
                self.hours = _Hours(data, self)
        except Exception:
            pass
        try:
            self.pinned = set(int(h) % 24 for h in json.loads(str(self.settings.value(PINNED_HOURS_KEY, "[]"))))
        except Exception:
            self.pinned = set()

    def save(self):
        try:
            self.settings.setValue("schedule_json", json.dumps(self.hours))
        except Exception:
            pass

    def regenerate_even(self):
        ids = [r.id for r in self.library.rotations if getattr(r, "regular", True)]
        ids = ids or [r.id for r in self.library.rotations]
        self.hours = _Hours([ids[h % len(ids)] if ids else None for h in range(24)], self)
        self.pinned = set()
        self.save_pins()
        self.save()

    def ensure_valid(self):
        valid = {r.id for r in self.library.rotations}
        if any(h not in valid for h in self.hours) and valid:
            self.regenerate_even()
        elif not valid:
            self.hours = _Hours([None] * 24, self)

    def rotation_id_for(self, day, hour):
        """The rotation for that hour on that day: a running dated schedule wins over the everyday one."""
        if self.events is not None:
            try:
                event = self.events.event_for_hour(day, hour)
            except Exception:
                event = None
            if event is not None and event.get("rotation_id") and self.library.find(event["rotation_id"]):
                return event["rotation_id"]
        if self.rotate_enabled() and (hour % 24) not in self.pinned:
            if self.hour_mode() == "mix" and self.mix_id():
                return self.mix_id()
            return self.planned_id(day, hour)
        return self.hours[hour % 24]

    def rotation_id_for_hour(self, hour):
        return self.rotation_id_for(datetime.now().date(), hour)

    def set_hour(self, hour, rotation_id):
        self.hours[hour % 24] = rotation_id
        self.save()

    def describe_day(self, current_hour):
        rows = []
        for hour in range(24):
            rotation = self.library.find(self.rotation_id_for(datetime.now().date(), hour))
            rows.append((hour_label(hour), rotation.name if rotation else "(none)", hour == current_hour))
        return rows


# ---------------------------------------------------------------------------
# Categories and spot groups (jingles, sweepers, ads) feeding the sandwich
# ---------------------------------------------------------------------------

CATEGORY_TYPES = ("jingle", "sweeper", "ad", "music")
AD_WORDS = {"ad", "ads", "advert", "adverts", "advertisement", "advertisements", "commercial",
            "commercials", "spot", "spots", "sponsor", "sponsors", "underwriting"}
SWEEPER_WORDS = {"sweeper", "sweepers", "liner", "liners", "imaging", "promo", "promos",
                 "stinger", "stingers", "teaser", "teasers"}
JINGLE_WORDS = {"jingle", "jingles", "id", "ids", "ident", "idents", "legal", "toh",
                "station", "bumper", "bumpers"}


def folder_words(folder_name):
    spaced = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", folder_name)
    return {w.lower() for w in re.split(r"[^A-Za-z0-9]+", spaced) if w}


def guess_category_type(folder_name):
    """Picks ad, sweeper or jingle from the folder's name. Defaults to jingle."""
    words = folder_words(folder_name)
    if words & AD_WORDS:
        return "ad"
    if words & SWEEPER_WORDS:
        return "sweeper"
    return "jingle"


class CategoryLibrary:
    """Named, typed folders of short audio. Name and type are guessed from the folder name."""

    def __init__(self, settings, on_changed=None):
        self.settings = settings
        self.on_changed = on_changed
        self.categories = []
        self.load()

    def load(self):
        try:
            self.categories = json.loads(self.settings.value("categories_json", "[]"))
        except Exception:
            self.categories = []

    def save(self):
        try:
            self.settings.setValue("categories_json", json.dumps(self.categories))
        except Exception:
            pass

    def _changed(self):
        self.save()
        if self.on_changed:
            self.on_changed()

    def find(self, category_id):
        for category in self.categories:
            if category["id"] == category_id:
                return category
        return None

    def add_category(self, folder, name=None, category_type=None, active=False, rotation_id=None):
        """New categories are listed but do not play anywhere until you switch them on or schedule them."""
        base = os.path.basename(os.path.normpath(folder))
        category = {"id": uuid.uuid4().hex[:8],
                    "name": name or pretty_folder_name(base),
                    "type": category_type or guess_category_type(base),
                    "folder": folder, "active": bool(active), "rotation_id": rotation_id}
        self.categories.append(category)
        return category

    def audio_folders(self, folder):
        """The folders a category import covers: the folder itself if it holds audio, otherwise each subfolder that does."""
        if not folder or not os.path.isdir(folder):
            return []
        if scan_audio_files(folder, recursive=False):
            return [folder]
        found = []
        for d in sorted(os.listdir(folder), key=str.lower):
            path = os.path.join(folder, d)
            if not d.startswith(".") and os.path.isdir(path) and scan_audio_files(path):
                found.append(path)
        return found

    def import_folder(self, folder, forced_type=None):
        """
        One folder that holds audio becomes one category. A folder that holds only
        subfolders becomes one category per subfolder. Returns the categories added.
        Imported categories are off until you switch them on.
        """
        added = [self.add_category(path, category_type=forced_type) for path in self.audio_folders(folder)]
        if added:
            self._changed()
        return added

    def rename(self, category_id, new_name):
        category = self.find(category_id)
        if category and new_name.strip():
            category["name"] = new_name.strip()
            self._changed()

    def set_type(self, category_id, category_type):
        category = self.find(category_id)
        if category and category_type in CATEGORY_TYPES:
            category["type"] = category_type
            self._changed()

    def remove(self, category_id):
        category = self.find(category_id)
        if category:
            self.categories.remove(category)
            self._changed()

    def is_active(self, category):
        return bool(category.get("active", True))      # categories saved before this option existed stay on

    def set_active(self, category_id, active):
        category = self.find(category_id)
        if category:
            category["active"] = bool(active)
            self._changed()

    def files_for_types(self, types, only_active=True):
        files = []
        for category in self.categories:
            if category["type"] in types and (not only_active or self.is_active(category)):
                files += scan_audio_files(category["folder"])
        return files

    def files_for_category(self, category_id):
        category = self.find(category_id)
        return scan_audio_files(category["folder"]) if category else []

    def sync_music(self, rotation_library):
        """Every rotation has a music category beside it, so the Categories tab shows everything that can
        play. Returns True when something was added or updated."""
        changed = False
        linked = {c.get("rotation_id"): c for c in self.categories if c.get("rotation_id")}
        for rotation in rotation_library.rotations:
            category = linked.get(rotation.id)
            if category is None:
                self.add_category(rotation.folder, rotation.name, "music",
                                  active=getattr(rotation, "regular", True), rotation_id=rotation.id)
                changed = True
            else:
                if category["folder"] != rotation.folder or category["name"] != rotation.name:
                    category["folder"], category["name"] = rotation.folder, rotation.name
                    changed = True
        valid = {r.id for r in rotation_library.rotations}
        for category in list(self.categories):
            if category.get("type") == "music" and category.get("rotation_id") and category["rotation_id"] not in valid:
                self.categories.remove(category)
                changed = True
        if changed:
            self._changed()
        return changed

    def describe(self, category):
        state = "in the regular schedule" if self.is_active(category) else "not in the regular schedule"
        return f"{category['name']} ({category['type']}, {state}) - {category['folder']}"


# ---------------------------------------------------------------------------
# M3U playlists and the Station-Playlist-style hour playlist generator
# ---------------------------------------------------------------------------

def write_m3u(path, entries):
    """Writes an extended M3U (UTF-8). Hour markers become a comment line other software ignores."""
    lines = ["#EXTM3U"]
    for entry in entries:
        if is_hour_marker(entry):
            tag = marker_tag(entry)
            lines.append("#VISIONSTUDIO-HOURMARKER" + (f":{tag}" if tag else ""))
            continue
        meta = get_track_metadata(entry)
        label = f"{meta['artist']} - {meta['title']}" if meta["artist"] else meta["title"]
        lines.append(f"#EXTINF:{int(get_track_duration(entry))},{label}")
        lines.append(entry)
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    temp_path = path + ".tmp"          # written whole, then swapped in, so a playlist is never half-written
    with open(temp_path, "w", encoding="utf-8", newline="\n") as handle:
        handle.write("\n".join(lines) + "\n")
    os.replace(temp_path, path)


def read_m3u(path):
    """Reads an M3U/M3U8. Returns (entries, missing_count). Relative paths resolve next to the playlist."""
    entries = []
    missing = 0
    base_dir = os.path.dirname(os.path.abspath(path))
    raw = None
    for encoding in ("utf-8-sig", "cp1252", "latin-1"):
        try:
            with open(path, "r", encoding=encoding) as handle:
                raw = handle.read()
            break
        except UnicodeDecodeError:
            continue
    if raw is None:
        return [], 0
    for line in raw.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("#VISIONSTUDIO-HOURMARKER"):
            tag = line.split(":", 1)[1].strip() if ":" in line else ""
            entries.append(HOUR_MARKER_TOKEN + tag)
            continue
        if line.startswith("#"):
            continue
        full = line if os.path.isabs(line) else os.path.normpath(os.path.join(base_dir, line))
        if os.path.isfile(full):
            entries.append(full)
        else:
            missing += 1
    return entries, missing


def _folder_is_writable(folder):
    try:
        os.makedirs(folder, exist_ok=True)
        probe = os.path.join(folder, ".write_test")
        with open(probe, "w") as handle:
            handle.write("x")
        os.remove(probe)
        return True
    except OSError:
        return False


def default_playlist_folder():
    """
    Installed copy: a Playlists folder inside the program folder, for example
    C:\\Program Files (x86)\\Vision Studio\\Playlists (the installer opens it up for writing).
    Otherwise Documents\\VisionStudio\\Playlists.
    """
    if getattr(sys, "frozen", False):
        candidate = os.path.join(os.path.dirname(sys.executable), "Playlists")
        if _folder_is_writable(candidate):
            return candidate
    documents = ""
    try:
        documents = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.DocumentsLocation)
    except Exception:
        documents = ""
    if not documents or not isinstance(documents, str):
        documents = os.path.join(os.path.expanduser("~"), "Documents")
    return os.path.join(documents, "VisionStudio", "Playlists")


class PlaylistGenerator:
    """
    Writes M3U playlists from the 24-hour schedule, Station Playlist style.
    Modes: 'midnight_full_day' (default: the whole day at once, exactly at
    midnight or a set number of seconds before), 'hour_lead' (each hour, a set
    number of seconds before it starts) and 'fixed_times' (at times you choose).
    Every hour's playlist starts with an hour marker and holds about an hour of
    music, honouring the same artist/title separation as live playback.
    """

    MODES = ("midnight_full_day", "hour_lead", "fixed_times")

    def __init__(self, settings, library, schedule):
        self.settings = settings
        self.library = library
        self.schedule = schedule
        self.last_fire_key = None
        self._artist_cache = {}
        self._pool_cache = {}
        self.carry_clock = [0.0]
        self.carry_track = {}
        self.carry_artist = {}
        self.events = None            # EventLibrary, set by the app
        self.marks = None             # BreakMarks, set by the app
        self.rotor = FolderRotor(settings)

    def rotate_folders_on(self):
        try:
            return str(self.settings.value("rotate_folders", "true")).lower() != "false"
        except Exception:
            return True

    def rotor_pick(self, rotation, pool, used, separation_ok):
        """The next song from the next folder in the round, or None when folder rotation does not apply."""
        if rotation is None or not self.rotate_folders_on():
            return None
        groups = group_by_folder(pool, rotation.folder)
        if len(groups) < 2:
            return None
        eligible = {}
        for folder, tracks in groups.items():
            ok = [t for t in tracks if t not in used and separation_ok(t)]
            if ok:
                eligible[folder] = ok
        folder = self.rotor.pick_folder(rotation.id, set(eligible), set(groups))
        return random.choice(eligible[folder]) if folder else None

    # --- settings ---
    def mode(self):
        mode = str(self.settings.value("playlist_mode", "midnight_full_day"))
        return mode if mode in self.MODES else "midnight_full_day"

    def lead_seconds(self):
        try:
            return max(0, int(self.settings.value("playlist_lead_seconds", 0)))
        except Exception:
            return 0

    def fixed_times(self):
        text = str(self.settings.value("playlist_fixed_times", "00:00"))
        times = []
        for part in re.split(r"[,\s;]+", text):
            match = re.fullmatch(r"(\d{1,2}):(\d{2})", part.strip())
            if match and int(match.group(1)) < 24 and int(match.group(2)) < 60:
                times.append((int(match.group(1)), int(match.group(2))))
        return times

    def output_folder(self):
        folder = str(self.settings.value("playlist_output_folder", "") or "")
        return folder or default_playlist_folder()

    # --- building ---
    def _artist(self, path):
        if path not in self._artist_cache:
            self._artist_cache[path] = get_track_artist(path)
        return self._artist_cache[path]

    def hour_options(self, day, hour):
        """(voice tracked, last hour of the show, seconds of the hour taken by breaks) for that hour."""
        voice = signoff = False
        event = None
        if self.events is not None:
            try:
                event = self.events.event_for_hour(day, hour)
            except Exception:
                event = None
        if event is not None and event.get("voice"):
            voice = True
            signoff = self.events.is_last_hour_of_show(event, day, hour)
        try:
            estimate = int(float(self.settings.value("break_estimate_seconds", DEFAULT_BREAK_ESTIMATE_SECONDS)))
        except Exception:
            estimate = DEFAULT_BREAK_ESTIMATE_SECONDS
        slots = BreakMarks.SLOTS
        count = sum(1 for sl in slots if (self.marks.enabled(day, hour, sl) if self.marks is not None else True))
        return voice, signoff, count * estimate

    def voice_slot_seconds(self):
        try:
            return int(float(self.settings.value("voice_slot_seconds", DEFAULT_VOICE_SLOT_SECONDS)))
        except Exception:
            return DEFAULT_VOICE_SLOT_SECONDS

    def build_hour_entries(self, rotation, virtual_clock, last_track, last_artist, separation=None,
                           marker=HOUR_MARKER_TOKEN, voice=False, signoff=False, break_seconds=0):
        """About an hour of tracks, starting with an hour marker. virtual_clock is advanced in place.
        The songs are chosen so the last one finishes at the end of the hour (less the breaks)."""
        rules = ProgramRules(self.settings)
        if separation is None:
            song_sep = rules.values["song_minutes"] * 60 if rules.enabled else 0
            artist_sep = rules.values["artist_minutes"] * 60 if rules.enabled else 0
        else:
            song_sep = artist_sep = separation
        if rotation is None:
            pool = []
        elif rotation.id in self._pool_cache:
            pool = list(self._pool_cache[rotation.id])
        else:
            pool = rotation.track_paths()
        entries = [marker]
        if not pool:
            return entries
        random.shuffle(pool)
        queue_items = list(pool)
        filled = 0.0
        guard = 0
        target = 3600.0 - float(break_seconds)
        if voice:
            target -= (target / AVERAGE_TRACK_SECONDS / VOICE_MARKER_EVERY) * self.voice_slot_seconds()
        target = max(600.0, target)
        used = set()

        def separation_ok(candidate):
            last = last_track.get(candidate)
            artist = self._artist(candidate)
            a_last = last_artist.get(artist) if artist else None
            return ((last is None or virtual_clock[0] - last >= song_sep) and
                    (a_last is None or virtual_clock[0] - a_last >= artist_sep))

        while filled < target and guard < 5000:
            guard += 1
            remaining = target - filled
            if FIT_MIN_SECONDS <= remaining <= 480:
                candidates = [c for c in pool if c not in used and separation_ok(c)]
                rotating = rotation is not None and self.rotate_folders_on()
                if rotating:
                    waiting = self.rotor.waiting_folders(rotation.id)
                    preferred = [c for c in candidates if folder_group(c, rotation.folder) in waiting]
                    if len(preferred) >= 4:
                        candidates = preferred          # keep the round going: favor folders that have not had a turn
                chosen, _score = choose_fill(remaining + overlap_seconds(), candidates,
                                             get_track_duration, self._artist, max_songs=2)
                if chosen:
                    for track in chosen:
                        if rotating:
                            self.rotor.note_used(rotation.id, folder_group(track, rotation.folder))
                        entries.append(track)
                        used.add(track)
                        last_track[track] = virtual_clock[0]
                        artist = self._artist(track)
                        if artist:
                            last_artist[artist] = virtual_clock[0]
                        virtual_clock[0] += get_track_duration(track)
                    break
            if not queue_items:
                queue_items = list(pool)
                random.shuffle(queue_items)
            track = self.rotor_pick(rotation, pool, used, separation_ok)
            if track is not None and track in queue_items:
                queue_items.remove(track)
            elif track is None:
                chosen_index = None
                for i, candidate in enumerate(queue_items):
                    last = last_track.get(candidate)
                    artist = self._artist(candidate)
                    a_last = last_artist.get(artist) if artist else None
                    if (last is None or virtual_clock[0] - last >= song_sep) and \
                       (a_last is None or virtual_clock[0] - a_last >= artist_sep):
                        chosen_index = i
                        break
                if chosen_index is None:
                    chosen_index = 0  # relax the rule when the rotation is too small
                track = queue_items.pop(chosen_index)
            used.add(track)
            entries.append(track)
            duration = get_track_duration(track)
            last_track[track] = virtual_clock[0]
            artist = self._artist(track)
            if artist:
                last_artist[artist] = virtual_clock[0]
            virtual_clock[0] += duration
            filled += duration
        if voice:
            entries = insert_voice_markers(entries, VOICE_MARKER_EVERY, signoff)
        return entries

    def playlist_path(self, day, hour, rotation_name):
        safe = "".join(c for c in rotation_name if c.isalnum() or c in (" ", "_", "-")).strip().replace(" ", "_")
        return os.path.join(self.output_folder(), f"{day.strftime('%Y-%m-%d')}_{hour:02d}00_{safe or 'rotation'}.m3u8")

    def locked_settings(self):
        return self.settings

    def hour_is_locked(self, day, hour):
        return is_hour_locked(self.settings, day, hour)

    def generate_hour(self, day, hour, virtual_clock=None, last_track=None, last_artist=None):
        rotation = self.library.find(self.schedule.rotation_id_for(day, hour))
        if rotation is None:
            return None
        if self.hour_is_locked(day, hour):
            existing = self.current_hour_playlist(day, hour)
            if existing:
                return existing          # recorded voice tracks are never rebuilt away
        voice, signoff, break_seconds = self.hour_options(day, hour)
        # One continuous virtual clock and play history, so separation carries from hour to hour.
        entries = self.build_hour_entries(
            rotation, virtual_clock if virtual_clock is not None else self.carry_clock,
            last_track if last_track is not None else self.carry_track,
            last_artist if last_artist is not None else self.carry_artist,
            marker=marker_for(day, hour), voice=voice, signoff=signoff, break_seconds=break_seconds)
        old = self.current_hour_playlist(day, hour)
        path = self.playlist_path(day, hour, rotation.name)
        write_m3u(path, entries)
        if old and os.path.normcase(old) != os.path.normcase(path):
            try:
                os.remove(old)
            except OSError:
                pass
        return path

    def generate_full_day(self, day=None):
        """Writes all 24 hourly playlists plus one combined file. Returns the list of files written."""
        day = day or datetime.now().date()
        clock = [0.0]
        last_track = {}
        last_artist = {}
        written = []
        combined = []
        locked_hours = {h for h in range(24) if self.hour_is_locked(day, h)}
        self.remove_day_playlists(day, keep_hours=locked_hours)    # replaced, except hours you voice tracked
        self._pool_cache = {}
        for rotation in self.library.rotations:
            self._pool_cache[rotation.id] = rotation.track_paths()
        for hour in range(24):            # 00:00 up to and including 23:00
            if hour in locked_hours:
                existing = self.current_hour_playlist(day, hour)
                if existing:
                    kept, _missing = read_m3u(existing)
                    combined += kept
                    written.append(existing)
                    continue
            rotation = self.library.find(self.schedule.rotation_id_for(day, hour))
            if rotation is None:
                continue
            voice, signoff, break_seconds = self.hour_options(day, hour)
            entries = self.build_hour_entries(rotation, clock, last_track, last_artist,
                                              marker=marker_for(day, hour), voice=voice, signoff=signoff,
                                              break_seconds=break_seconds)
            path = self.playlist_path(day, hour, rotation.name)
            write_m3u(path, entries)
            written.append(path)
            combined += entries
        if combined:
            full_path = os.path.join(self.output_folder(), f"{day.strftime('%Y-%m-%d')}_fullday.m3u8")
            write_m3u(full_path, combined)
            written.append(full_path)
        self._pool_cache = {}
        return written

    def remove_day_playlists(self, day, keep_hours=()):
        """Deletes every playlist already saved for that day, so corrected ones replace mistaken ones.
        Hours in keep_hours (voice tracked) are left alone."""
        prefix = f"{day.strftime('%Y-%m-%d')}_"
        removed = 0
        keep_prefixes = tuple(f"{prefix}{h:02d}00_" for h in keep_hours)
        try:
            for name in os.listdir(self.output_folder()):
                if name.startswith(prefix) and name.lower().endswith((".m3u", ".m3u8")):
                    if keep_prefixes and name.startswith(keep_prefixes):
                        continue
                    try:
                        os.remove(os.path.join(self.output_folder(), name))
                        removed += 1
                    except OSError:
                        pass
        except OSError:
            pass
        return removed

    def current_hour_playlist(self, day=None, hour=None):
        now = datetime.now()
        day = day or now.date()
        hour = now.hour if hour is None else hour
        folder = self.output_folder()
        prefix = f"{day.strftime('%Y-%m-%d')}_{hour:02d}00_"
        try:
            for name in sorted(os.listdir(folder)):
                if name.startswith(prefix) and name.lower().endswith((".m3u", ".m3u8")):
                    return os.path.join(folder, name)
        except OSError:
            pass
        return None

    # --- timing: returns what should be generated right now, or None ---
    def due_job(self, now=None):
        """Returns ('day', date) or ('hour', date, hour) when generation is due; fires once per target."""
        now = now or datetime.now()
        if now.second >= 10:
            return None
        seconds_of_day = now.hour * 3600 + now.minute * 60 + now.second
        mode = self.mode()
        lead = self.lead_seconds()
        job = None
        key = None
        if mode == "midnight_full_day":
            if lead == 0 and seconds_of_day < 10:
                job = ("day", now.date())
            elif lead > 0 and 86400 - lead <= seconds_of_day < 86400 - lead + 10:
                job = ("day", now.date() + timedelta(days=1))
        elif mode == "hour_lead":
            seconds_into_hour = now.minute * 60 + now.second
            if 3600 - lead <= seconds_into_hour < 3600 - lead + 10 or (lead == 0 and seconds_into_hour < 10):
                target = now if lead == 0 else now + timedelta(seconds=lead + 5)
                job = ("hour", target.date(), target.hour)
        elif mode == "fixed_times":
            if (now.hour, now.minute) in self.fixed_times():
                job = ("day", now.date())
        if job is not None:
            key = (mode, job, now.hour, now.minute)
            if key == self.last_fire_key:
                return None
            self.last_fire_key = key
        return job


# ---------------------------------------------------------------------------
# Keyboard shortcuts: Station Playlist layout by default, fully remappable
# ---------------------------------------------------------------------------

# (command id, label, default key, can be rebound)
DEFAULT_SHORTCUTS = [
    ("insert_tracks", "Insert tracks into the queue", "Ins", True),
    ("insert_tracks_alt", "Insert tracks (alternate key)", "Ctrl+I", True),
    ("automation_toggle", "Automation on / off (the first song goes onto the deck, like Station Playlist)", "A", True),
    ("stop_fade", "Stop with fade (the record stays on the deck)", "S", True),
    ("start_rotation", "Automation on", "Ctrl+Return", True),
    ("stop_rotation", "Stop everything at once", "Ctrl+Shift+S", True),
    ("mute_all", "Mute or unmute all audio", "Ctrl+Shift+U", True),
    ("open_options", "Open or close Settings", "Ctrl+O", True),
    ("toggle_recording", "Start or stop recording", "R", True),
    ("new_item", "New rotation, category or hour marker (depends on the tab)", "Ctrl+N", True),
    ("generate_now", "Generate playlists now", "Ctrl+Shift+G", True),
    ("say_elapsed", "Announce elapsed time of the current track", "Ctrl+Alt+Shift+T", True),
    ("say_remaining", "Announce time remaining on the current track", "Ctrl+Alt+T", True),
    ("say_current", "Announce the current track", "Ctrl+Alt+C", True),
    ("say_status", "Announce play status", "Ctrl+Alt+P", True),
    ("say_hour_remaining", "Announce time remaining in this hour", "Ctrl+Alt+H", True),
    ("say_mute", "Announce mute status", "Ctrl+Alt+M", True),
    ("say_encoders", "Announce encoder status", "Ctrl+Alt+E", True),
    ("voice_track_before", "Voice track: record before the selected queue item", "V", True),
    ("voice_track_after", "Voice track: record after the selected queue item", "Shift+V", True),
    ("queue_move_up", "Queue list: move the selected track up", "Ctrl+Up", False),
    ("queue_move_down", "Queue list: move the selected track down", "Ctrl+Down", False),
    ("queue_remove", "Queue list: remove the selected track", "Del", False),
    ("queue_browse", "Queue list: browse tracks", "Up / Down", False),
]


DEFAULT_LAYOUT_NAME = "Station Playlist (default)"


def list_shortcut_layouts():
    names = [DEFAULT_LAYOUT_NAME]
    try:
        for name in sorted(os.listdir(get_layouts_folder()), key=str.lower):
            if name.lower().endswith(".json"):
                names.append(os.path.splitext(name)[0])
    except OSError:
        pass
    return names


def read_layout_keys(name):
    """The command-to-key map of a layout file, or {} for the built-in Station Playlist layout."""
    if not name or name == DEFAULT_LAYOUT_NAME:
        return {}
    try:
        with open(os.path.join(get_layouts_folder(), name + ".json"), "r", encoding="utf-8") as handle:
            data = json.load(handle)
        keys = data.get("keys", data) if isinstance(data, dict) else {}
        return {str(k): str(v) for k, v in keys.items() if isinstance(v, str)}
    except Exception:
        return {}


def export_shortcut_layout(settings, path, name):
    bindings = load_shortcut_bindings(settings)
    data = {
        "name": name,
        "note": "Edit the keys below, save, then use Import Layout in Vision Studio. "
                "Key names look like Ctrl+Shift+T. Leave a key empty to turn a command off.",
        "keys": {sid: bindings.get(sid, "") for sid, _l, _k, rebind in DEFAULT_SHORTCUTS if rebind},
        "commands": {sid: label for sid, label, _k, rebind in DEFAULT_SHORTCUTS if rebind},
    }
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(data, handle, indent=2)


def import_shortcut_layout(src_path):
    """Copies a layout file into the Layouts folder. Returns the layout name, or None if it is not valid."""
    with open(src_path, "r", encoding="utf-8") as handle:
        data = json.load(handle)
    keys = data.get("keys", data) if isinstance(data, dict) else None
    if not isinstance(keys, dict) or not keys:
        return None
    name = re.sub(r"[^\w .()-]", "_", os.path.splitext(os.path.basename(src_path))[0]).strip() or "Imported layout"
    with open(os.path.join(get_layouts_folder(), name + ".json"), "w", encoding="utf-8") as handle:
        json.dump({"name": name, "keys": {str(k): str(v) for k, v in keys.items()}}, handle, indent=2)
    return name


def set_shortcut_layout(settings, name):
    settings.setValue("shortcut_layout", name)
    settings.setValue("shortcut_overrides", "{}")


def load_shortcut_bindings(settings):
    """Default layout, then the chosen layout file, then any keys the user changed on top."""
    bindings = {sid: key for sid, _label, key, _rebind in DEFAULT_SHORTCUTS}
    for sid, key in read_layout_keys(str(settings.value("shortcut_layout", DEFAULT_LAYOUT_NAME))).items():
        if sid in bindings:
            bindings[sid] = key
    try:
        overrides = json.loads(settings.value("shortcut_overrides", "{}"))
        for sid, key in overrides.items():
            if sid in bindings:
                bindings[sid] = key
    except Exception:
        pass
    return bindings


def save_shortcut_override(settings, shortcut_id, key):
    try:
        overrides = json.loads(settings.value("shortcut_overrides", "{}"))
    except Exception:
        overrides = {}
    overrides[shortcut_id] = key
    settings.setValue("shortcut_overrides", json.dumps(overrides))


def reset_shortcut_overrides(settings):
    settings.setValue("shortcut_overrides", "{}")


# ---------------------------------------------------------------------------
# Dated schedules (holidays, one-day shows), break marks, voice track markers, locked hours,
# the played list, and fitting the end of an hour so the last song finishes on the mark.
# ---------------------------------------------------------------------------

# A voice track slot is an hour-marker-shaped entry, so every part of the queue that skips hour markers
# also skips an empty slot. It is saved in playlists as a comment line, which other software ignores.
VOICE_MARKER_TOKEN = HOUR_MARKER_TOKEN + "VOICE"
VOICE_MARKER_EVERY = 3
DEFAULT_VOICE_SLOT_SECONDS = 15
DEFAULT_SIGNOFF_SECONDS = 180
DEFAULT_BREAK_ESTIMATE_SECONDS = 90
CROSSFADE_OVERLAP_SECONDS = 4.0
_OVERLAP = [CROSSFADE_OVERLAP_SECONDS]      # 0 when crossfading is off: songs play to their end


def overlap_seconds():
    return _OVERLAP[0]


def set_crossfade_overlap(enabled):
    _OVERLAP[0] = CROSSFADE_OVERLAP_SECONDS if enabled else 0.0
FIT_WINDOW_SECONDS = 720          # start fitting this long before the mark
FIT_MIN_SECONDS = 75              # too close to the mark to fit anything
FIT_GOOD_ENOUGH_EARLY = 5         # ending up to this many seconds early counts as on time (setting: fit_early_seconds)
FIT_GOOD_ENOUGH_LATE = 2
FIT_MIN_SONG_SECONDS = 180        # songs shorter than this are only used to fit when nothing longer will do
_FIT_EARLY = [FIT_GOOD_ENOUGH_EARLY]
_FIT_MIN_SONG = [FIT_MIN_SONG_SECONDS]


def fit_early_limit():
    return _FIT_EARLY[0]


def fit_min_song():
    return _FIT_MIN_SONG[0]


def set_fit_options(early_seconds=None, min_song_seconds=None):
    if early_seconds is not None:
        _FIT_EARLY[0] = max(0.0, float(early_seconds))
    if min_song_seconds is not None:
        _FIT_MIN_SONG[0] = max(0.0, float(min_song_seconds))


def is_voice_marker(entry):
    return isinstance(entry, str) and entry.startswith(VOICE_MARKER_TOKEN)


def is_song_entry(entry):
    """A real music file: not a marker and not a recorded voice track."""
    return (isinstance(entry, str) and not is_hour_marker(entry)
            and not os.path.basename(entry).lower().startswith("voicetrack_"))


def insert_voice_markers(entries, every=VOICE_MARKER_EVERY, signoff=False):
    """A voice track slot after every `every` songs. With signoff=True the last song is always
    preceded by a slot (the sign-off before the final song of a show)."""
    out = []
    count = 0
    for entry in entries:
        out.append(entry)
        if not is_song_entry(entry):
            continue
        count += 1
        if count % every == 0:
            out.append(VOICE_MARKER_TOKEN)
    while out and is_voice_marker(out[-1]):
        out.pop()                       # nothing to introduce after the last song
    if signoff:
        last_song = max((i for i, e in enumerate(out) if is_song_entry(e)), default=None)
        if last_song is not None and not (last_song > 0 and is_voice_marker(out[last_song - 1])):
            out.insert(last_song, VOICE_MARKER_TOKEN)
    return out


# --- locked hours: an hour with recorded voice tracks is never rebuilt by accident ---

def hour_key(day, hour):
    return f"{day.strftime('%Y%m%d')}{int(hour):02d}"


def load_locked_hours(settings):
    try:
        data = json.loads(str(settings.value("locked_hours_json", "[]")))
        return set(str(x) for x in data) if isinstance(data, list) else set()
    except Exception:
        return set()


def save_locked_hours(settings, locked):
    cutoff = (datetime.now() - timedelta(days=3)).strftime("%Y%m%d00")
    settings.setValue("locked_hours_json", json.dumps(sorted(k for k in locked if k >= cutoff)))


def is_hour_locked(settings, day, hour):
    return hour_key(day, hour) in load_locked_hours(settings)


def set_hour_locked(settings, day, hour, locked=True):
    keys = load_locked_hours(settings)
    (keys.add if locked else keys.discard)(hour_key(day, hour))
    save_locked_hours(settings, keys)


# --- dated schedules ---

def shift_years(moment, years):
    try:
        return moment.replace(year=moment.year + years)
    except ValueError:                  # February 29
        return moment.replace(year=moment.year + years, day=28)


def parse_moment(text):
    try:
        return datetime.strptime(str(text), "%Y-%m-%dT%H:%M")
    except Exception:
        return None


def format_moment(moment):
    return moment.strftime("%Y-%m-%dT%H:%M")


class EventLibrary:
    """Named schedules that run between two dates and times and replace the regular schedule while
    they do. A draft (no saved dates) is never active."""

    def __init__(self, settings, on_changed=None):
        self.settings = settings
        self.on_changed = on_changed
        self.events = []
        self.load()

    def load(self):
        try:
            data = json.loads(str(self.settings.value("event_schedules_json", "[]")))
            self.events = [e for e in data if isinstance(e, dict) and e.get("id")]
        except Exception:
            self.events = []

    def save(self):
        try:
            self.settings.setValue("event_schedules_json", json.dumps(self.events))
        except Exception:
            pass

    def _changed(self):
        self.save()
        if self.on_changed:
            self.on_changed()

    def find(self, event_id):
        for event in self.events:
            if event["id"] == event_id:
                return event
        return None

    def add_draft(self, name, rotation_id=None, jingle_category_id=None):
        event = {"id": uuid.uuid4().hex[:8], "name": name, "rotation_id": rotation_id,
                 "jingle_category_id": jingle_category_id, "ad_category_id": None,
                 "start": "", "end": "", "repeat": False, "voice": False, "marks": [1, 1, 1, 1],
                 "active": False, "created": time.time()}
        self.events.append(event)
        self._changed()
        return event

    def validate(self, event):
        start, end = parse_moment(event.get("start")), parse_moment(event.get("end"))
        if start is None or end is None:
            return "Choose a start and an end."
        if end <= start:
            return "The end must be after the start."
        return ""

    def save_event(self, event):
        """Saves dates and activates the schedule. Returns an error text, or '' when saved."""
        problem = self.validate(event)
        if problem:
            return problem
        event["active"] = True
        if self.find(event["id"]) is None:
            event["created"] = event.get("created", time.time())
            self.events.append(event)
        self._changed()
        return ""

    def update(self, event, **fields):
        event.update(fields)
        self._changed()

    def remove(self, event_id):
        event = self.find(event_id)
        if event:
            self.events.remove(event)
            self._changed()

    def occurrences(self, event, around):
        start, end = parse_moment(event.get("start")), parse_moment(event.get("end"))
        if start is None or end is None or end <= start:
            return []
        if not event.get("repeat"):
            return [(start, end)]
        base = around.year - start.year
        return [(shift_years(start, k), shift_years(end, k)) for k in range(base - 1, base + 3)]

    def is_running(self, event, now):
        if not event.get("active"):
            return False
        return any(s <= now < e for s, e in self.occurrences(event, now))

    def next_start(self, event, now):
        if not event.get("active"):
            return None
        future = [s for s, _e in self.occurrences(event, now) if s > now]
        return min(future) if future else None

    def event_at(self, moment):
        """The running schedule that wins at this moment: the one created last."""
        winner = None
        for event in self.events:
            if self.is_running(event, moment):
                if winner is None or event.get("created", 0) >= winner.get("created", 0):
                    winner = event
        return winner

    def event_for_hour(self, day, hour):
        return self.event_at(datetime(day.year, day.month, day.day, int(hour) % 24, 0))

    def is_last_hour_of_show(self, event, day, hour):
        hour_start = datetime(day.year, day.month, day.day, int(hour) % 24, 0)
        hour_end = hour_start + timedelta(hours=1)
        for s, e in self.occurrences(event, hour_start):
            if s <= hour_start < e:
                return e <= hour_end
        return False

    def overlaps(self, event):
        """Other saved schedules that overlap this one (checked over the next two years)."""
        mine = self.occurrences(event, datetime.now())
        found = []
        for other in self.events:
            if other["id"] == event["id"] or not other.get("active"):
                continue
            for s1, e1 in mine:
                if any(s1 < e2 and s2 < e1 for s2, e2 in self.occurrences(other, datetime.now())):
                    found.append(other["name"])
                    break
        return found

    def describe(self, event, now=None):
        now = now or datetime.now()
        if not event.get("active"):
            return f"{event['name']}: draft, not scheduled yet"
        start, end = parse_moment(event["start"]), parse_moment(event["end"])
        text = f"{event['name']}: {start.strftime('%a %b %d %Y %I:%M %p')} to {end.strftime('%a %b %d %Y %I:%M %p')}"
        if event.get("repeat"):
            text += ", repeats every year"
        if event.get("voice"):
            text += ", voice tracked"
        if self.is_running(event, now):
            text += " (on air now)"
        else:
            nxt = self.next_start(event, now)
            text += f" (next starts {nxt.strftime('%b %d %Y')})" if nxt else " (finished)"
        return text


class BreakMarks:
    """Which of :00, :15, :30 and :45 run a break, hour by hour. A running dated schedule has its own set."""

    SLOTS = (":00", ":15", ":30", ":45")

    def __init__(self, settings, events=None):
        self.settings = settings
        self.events = events
        self.grid = [[1, 1, 1, 1] for _ in range(24)]
        self.load()

    def load(self):
        try:
            data = json.loads(str(self.settings.value("break_marks_json", "[]")))
            if isinstance(data, list) and len(data) == 24:
                self.grid = [[1 if int(v) else 0 for v in (row + [1, 1, 1, 1])[:4]] for row in data]
        except Exception:
            pass

    def save(self):
        try:
            self.settings.setValue("break_marks_json", json.dumps(self.grid))
        except Exception:
            pass

    def set_mark(self, hour, slot, enabled):
        self.grid[hour % 24][self.SLOTS.index(slot)] = 1 if enabled else 0
        self.save()

    def set_hour(self, hour, flags):
        self.grid[hour % 24] = [1 if f else 0 for f in flags]
        self.save()

    def set_all(self, flags):
        self.grid = [[1 if f else 0 for f in flags] for _ in range(24)]
        self.save()

    def enabled(self, day, hour, slot):
        index = self.SLOTS.index(slot)
        if self.events is not None:
            event = self.events.event_for_hour(day, hour)
            if event is not None:
                marks = (list(event.get("marks", [1, 1, 1, 1])) + [1, 1, 1, 1])[:4]
                return bool(marks[index])
        return bool(self.grid[hour % 24][index])


# --- fitting the end of the hour ---

def choose_fill(gap, candidates, duration, artist=None, max_songs=3, overlap=None,
                sample=70, use_min_song=True):
    """Picks 1 to max_songs songs whose combined length (less the crossfade overlaps) comes closest to
    `gap` seconds, preferring to end a little early rather than late. Returns (songs, score) where the
    score is how far off it lands (lower is better), or (None, None)."""
    if gap < FIT_MIN_SECONDS or not candidates:
        return None, None
    if overlap is None:
        overlap = overlap_seconds()
    pool = list(candidates)
    if len(pool) > 400:
        pool = random.sample(pool, 400)
    lengths = {p: duration(p) for p in pool}
    minimum = fit_min_song() if use_min_song else 0
    narrowed = False
    if minimum > 0:
        long_enough = [p for p in pool if lengths[p] >= minimum]
        if len(long_enough) >= 30:          # keep the pool wide enough to find an exact fit
            pool = long_enough
            narrowed = True

    def score(total):
        diff = gap - total
        return diff if diff >= 0 else -diff * 3.0

    def distinct(songs):
        if artist is None:
            return True
        names = [artist(s) for s in songs]
        names = [n for n in names if n]
        return len(names) == len(set(names))

    best = (None, None)
    ordered = sorted(pool, key=lambda p: lengths[p])
    # one song
    for p in ordered:
        s = score(lengths[p])
        if best[1] is None or s < best[1]:
            best = ([p], s)
    # two songs: two-pointer over the sorted lengths
    if max_songs >= 2:
        lo, hi = 0, len(ordered) - 1
        target = gap + overlap
        while lo < hi:
            total = lengths[ordered[lo]] + lengths[ordered[hi]]
            pair = [ordered[hi], ordered[lo]]
            s = score(total - overlap)
            if (best[1] is None or s < best[1]) and distinct(pair):
                best = (pair, s)
            if total < target:
                lo += 1
            else:
                hi -= 1
    # three songs: first song from a random sample, best pair for the rest
    if max_songs >= 3 and (best[1] is None or best[1] > min(2.0, fit_early_limit())):
        firsts = random.sample(ordered, min(sample, len(ordered)))
        for first in firsts:
            rest_target = gap - lengths[first] + 2 * overlap
            lo, hi = 0, len(ordered) - 1
            while lo < hi:
                a, b = ordered[lo], ordered[hi]
                if first in (a, b):
                    if a == first:
                        lo += 1
                    else:
                        hi -= 1
                    continue
                total = lengths[first] + lengths[a] + lengths[b] - 2 * overlap
                s = score(total)
                trio = [first, b, a]
                if (best[1] is None or s < best[1]) and distinct(trio):
                    best = (trio, s)
                if lengths[a] + lengths[b] < rest_target:
                    lo += 1
                else:
                    hi -= 1
    if narrowed and (best[1] is None or best[1] > fit_early_limit()):
        # The longer songs alone could not land it; let the shorter ones help.
        wide = choose_fill(gap, candidates, duration, artist, max_songs, overlap, sample, use_min_song=False)
        if wide[1] is not None and (best[1] is None or wide[1] < best[1]):
            best = wide
    return best


def timeline_length(songs, duration, overlap=None):
    if overlap is None:
        overlap = overlap_seconds()
    if not songs:
        return 0.0
    return sum(duration(s) for s in songs) - overlap * (len(songs) - 1)


def natural_fit(queue_songs, gap, duration):
    """How the songs already queued would land. Returns (songs_used, score)."""
    used = []
    total = 0.0
    for song in queue_songs:
        used.append(song)
        total = timeline_length(used, duration)
        if total >= gap:
            break
    diff = gap - total
    return used, (diff if diff >= 0 else -diff * 3.0)


def plan_hour_end(queue_songs, gap, candidates, duration, artist=None):
    """Decides whether to replace the queued songs so the hour ends on the mark.
    Returns the replacement songs, or None to leave the queue alone."""
    if gap < FIT_MIN_SECONDS or gap > FIT_WINDOW_SECONDS:
        return None
    used, natural = natural_fit(queue_songs, gap, duration)
    overshoot = timeline_length(used, duration) - gap
    if natural <= fit_early_limit() and overshoot <= FIT_GOOD_ENOUGH_LATE:
        return None
    songs, score = choose_fill(gap, candidates, duration, artist)
    if songs is None or score >= natural:
        return None
    return songs


# --- the played list ---

class PersistentPlayHistory(PlayHistory):
    """Remembers what played, saved to disk, so a restart does not forget the last two hours."""

    KEY = "play_history_json"

    def __init__(self, settings=None, keep_seconds=DEFAULT_SEPARATION_SECONDS):
        super().__init__()
        self.settings = settings
        self.keep_seconds = keep_seconds
        self.load()

    def load(self):
        if self.settings is None:
            return
        try:
            data = json.loads(str(self.settings.value(self.KEY, "{}")))
        except Exception:
            data = {}
        now = time.time()
        for path, stamp in (data.items() if isinstance(data, dict) else []):
            try:
                stamp = float(stamp)
            except Exception:
                continue
            if now - stamp < self.keep_seconds:
                self.last_played_track[path] = stamp
                artist = get_track_artist(path) if os.path.isfile(path) else ""
                if artist and stamp > self.last_played_artist.get(artist, 0):
                    self.last_played_artist[artist] = stamp

    def save(self):
        if self.settings is None:
            return
        now = time.time()
        recent = {p: t for p, t in self.last_played_track.items() if now - t < self.keep_seconds}
        try:
            self.settings.setValue(self.KEY, json.dumps(recent))
        except Exception:
            pass

    def record_play(self, file_path):
        super().record_play(file_path)
        self.save()

    def recent(self, separation_seconds):
        """(path, played_at, available_at) for everything still held back, newest first."""
        now = time.time()
        rows = [(p, t, t + separation_seconds) for p, t in self.last_played_track.items()
                if now - t < separation_seconds and is_song_entry(p)]
        return sorted(rows, key=lambda r: -r[1])


# ---------------------------------------------------------------------------
# Folder rotation: every folder of a rotation takes a turn before any folder repeats.
# ---------------------------------------------------------------------------

ROOT_GROUP = "(top folder)"
FOLDER_ROTOR_KEY = "folder_rotor_json"
OTHER_AUDIO = (".wma", ".aiff", ".aif", ".ape", ".wv", ".mp2", ".mka", ".m4b", ".ac3", ".dsf", ".mpc")


def folder_group(path, root):
    """The folder directly under the rotation's folder that a song belongs to (songs in deeper folders
    belong to that top folder)."""
    try:
        rel = os.path.relpath(path, root)
    except ValueError:
        return ROOT_GROUP
    parts = rel.replace("\\", "/").split("/")
    return parts[0] if len(parts) > 1 else ROOT_GROUP


def group_by_folder(paths, root):
    groups = {}
    for path in paths:
        groups.setdefault(folder_group(path, root), []).append(path)
    return groups


class FolderRotor:
    """Remembers, for each rotation, which folders still wait for their turn in the current round. A round
    uses every folder once, in a shuffled order, then starts again. The state is kept between hours, days
    and restarts."""

    def __init__(self, settings=None):
        self.settings = settings
        self.state = {}
        try:
            if settings is not None:
                self.state = json.loads(str(settings.value(FOLDER_ROTOR_KEY, "{}")))
        except Exception:
            self.state = {}

    def save(self):
        if self.settings is None:
            return
        try:
            self.settings.setValue(FOLDER_ROTOR_KEY, json.dumps(self.state))
        except Exception:
            pass

    def entry(self, rotation_id):
        e = self.state.setdefault(rotation_id, {})
        e.setdefault("remaining", [])
        e.setdefault("last", {})
        e.setdefault("count", {})
        e.setdefault("rounds", 0)
        return e

    def pick_folder(self, rotation_id, eligible, all_folders, stamp=None):
        """The next folder in the round that has a song that can play now (`eligible`), or None. Folders
        without a playable song are passed over for this round."""
        if not eligible:
            return None
        e = self.entry(rotation_id)
        for _attempt in range(2):
            remaining = [f for f in e["remaining"] if f in all_folders]
            while remaining:
                folder = remaining.pop(0)
                if folder in eligible:
                    e["remaining"] = remaining
                    e["last"][folder] = stamp if stamp is not None else time.time()
                    e["count"][folder] = int(e["count"].get(folder, 0)) + 1
                    self.save()
                    return folder
            order = list(all_folders)
            random.shuffle(order)
            e["remaining"] = order
            e["rounds"] = int(e["rounds"]) + 1
        return None

    def waiting_folders(self, rotation_id):
        return set(self.entry(rotation_id)["remaining"])

    def note_used(self, rotation_id, folder, stamp=None):
        """A song was chosen some other way (to fit the end of an hour): that folder has had its turn."""
        e = self.entry(rotation_id)
        if folder in e["remaining"]:
            e["remaining"].remove(folder)
        e["last"][folder] = stamp if stamp is not None else time.time()
        e["count"][folder] = int(e["count"].get(folder, 0)) + 1
        self.save()

    def last_scheduled(self, rotation_id, folder):
        return self.entry(rotation_id)["last"].get(folder, 0)


def folder_report(rotation, rotor=None, now=None):
    """A plain-text report of every folder in a rotation: how many songs were found, when the folder was
    last scheduled, and anything that was not read and why."""
    now = now or time.time()
    lines = []
    root = rotation.folder
    if not root or not os.path.isdir(root):
        return f"The folder for {rotation.name} was not found: {root}"
    songs = rotation.track_paths()
    groups = group_by_folder(songs, root)
    other = {}
    skipped_dirs = []
    try:
        for name in sorted(os.listdir(root), key=str.lower):
            full = os.path.join(root, name)
            if os.path.isdir(full) and (name.startswith(".") or os.path.islink(full)):
                skipped_dirs.append(name + (" (starts with a period)" if name.startswith(".") else " (a shortcut or link)"))
        for current, dirs, files in os.walk(root):
            dirs[:] = [d for d in dirs if not d.startswith(".")]
            for name in files:
                if name.lower().endswith(OTHER_AUDIO):
                    other.setdefault(folder_group(os.path.join(current, name), root), []).append(name)
    except OSError:
        pass
    real_dirs = []
    try:
        real_dirs = [n for n in os.listdir(root) if os.path.isdir(os.path.join(root, n)) and not n.startswith(".")
                     and not os.path.islink(os.path.join(root, n))]
    except OSError:
        pass
    names = sorted(set(groups) | set(real_dirs), key=str.lower)
    empty = [n for n in names if not groups.get(n)]
    entry = rotor.entry(rotation.id) if rotor is not None else {"last": {}, "count": {}, "rounds": 0}
    never = [n for n in names if groups.get(n) and not entry["last"].get(n)]
    lines.append(f"Rotation {rotation.name}: {len(songs)} songs in {len([n for n in names if groups.get(n)])} folders.")
    if not rotation.recursive:
        lines.append("Include subfolders is OFF for this rotation, so only the top folder is read.")
    lines.append(f"Folders with no readable songs: {len(empty)}." + (" " + ", ".join(empty) if empty else ""))
    lines.append(f"Folders not yet scheduled in a playlist: {len(never)}." + (" " + ", ".join(never[:40]) if never else ""))
    lines.append(f"Rounds completed through all folders: {entry.get('rounds', 0)}.")
    if skipped_dirs:
        lines.append("Folders skipped: " + "; ".join(skipped_dirs) + ".")
    lines.append("")
    for name in names:
        count = len(groups.get(name, []))
        last = entry["last"].get(name, 0)
        when = time.strftime("%b %d %I:%M %p", time.localtime(last)) if last else "not yet"
        line = f"{name}: {count} songs, last scheduled {when}, scheduled {int(entry['count'].get(name, 0))} times."
        if other.get(name):
            line += f" Not read ({len(other[name])} files of a type the program does not play, such as {other[name][0]})."
        lines.append(line)
    return "\n".join(lines)


def day_folder_report(rotation_library, rotor, day, playlist_files, schedule=None):
    """The report saved with each day's playlists: every rotation's folders, plus how many songs of each
    folder went into that day's playlists."""
    used = {}
    for path in playlist_files:
        if path.lower().endswith("fullday.m3u8"):
            continue
        try:
            entries, _missing = read_m3u(path)
        except Exception:
            continue
        for entry in entries:
            if is_hour_marker(entry):
                continue
            for rotation in rotation_library.rotations:
                root = rotation.folder
                if root and os.path.normcase(os.path.normpath(entry)).startswith(
                        os.path.normcase(os.path.normpath(root)) + os.sep):
                    used.setdefault(rotation.id, Counter())[folder_group(entry, root)] += 1
                    break
    lines = [f"Folder report for the playlists of {day.strftime('%A %B %d, %Y')}",
             f"Made {time.strftime('%Y-%m-%d %I:%M %p')}", ""]
    if schedule is not None:
        try:
            lines += schedule.usage_lines() + [""]
        except Exception:
            pass
    for rotation in rotation_library.rotations:
        lines.append(folder_report(rotation, rotor))
        counts = used.get(rotation.id)
        if counts:
            lines.append("")
            lines.append(f"Songs from each folder in this day's playlists ({sum(counts.values())} songs):")
            for name, number in sorted(counts.items(), key=lambda kv: kv[0].lower()):
                lines.append(f"{name}: {number}")
        else:
            lines.append("No songs from this rotation were scheduled on this day.")
        lines.append("")
        lines.append("-" * 40)
        lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Programming rules: the US webcasting limits Live365 publishes, kept strict.
# ---------------------------------------------------------------------------

_TAG_CACHE = {}


def track_tags(path):
    """(artist, album, title), lowercased, read once per file. Blank when a tag is missing."""
    if path in _TAG_CACHE:
        return _TAG_CACHE[path]
    artist = album = title = ""
    if MUTAGEN_AVAILABLE and path and os.path.isfile(path):
        try:
            audio = mutagen.File(path, easy=True)
            if audio and audio.tags:
                def first(key):
                    values = audio.tags.get(key)
                    return values[0].strip().lower() if values else ""
                artist, album, title = first("artist"), first("album"), first("title")
        except Exception:
            pass
    _TAG_CACHE[path] = (artist, album, title)
    return _TAG_CACHE[path]


def primary_artist(artist):
    """'ariana grande feat. mac miller' counts as Ariana Grande for the same-artist limits."""
    return re.split(r"\s+(?:feat\.?|ft\.?|featuring|with)\s+|\s*[,;/]\s*|\s+&\s+|\s+and\s+", artist or "", maxsplit=1)[0].strip()


RULE_PRESETS = {
    # The US webcasting limits Live365 publishes. A played song waits 45 minutes (the shortest hold Live365's
    # AutoDJ offers); the artist and album limits do the rest, so there is no fixed two hour hold.
    "live365": {"window_hours": 3, "artist_max": 4, "artist_run": 3, "album_max": 3, "album_run": 2,
                "song_minutes": 45, "artist_minutes": 0},
}
RULE_KEYS = ("window_hours", "artist_max", "artist_run", "album_max", "album_run", "song_minutes", "artist_minutes")


class ProgramRules:
    """
    Checks a song against what already played (and what is queued ahead of it):
      - the same song, or the same artist, is held back for `separation_seconds` (the Hours setting);
      - within the window (3 hours), no more than `artist_max` different songs by one artist and `album_max`
        from one album, and no more than `artist_run` / `album_run` of them in a row (the US webcasting
        performance complement that Live365 publishes).
    A song that fails is never played and never relaxed; the engine borrows another that passes.
    """

    def __init__(self, settings):
        self.settings = settings
        self.load()

    def load(self):
        s = self.settings
        self.preset = str(s.value("rules_preset", "live365"))
        if self.preset not in ("live365", "custom", "off"):
            self.preset = "live365"
        base = RULE_PRESETS["live365"]
        self.values = dict(base)
        if self.preset == "custom":
            for key in RULE_KEYS:
                try:
                    low = 0 if key in ("song_minutes", "artist_minutes") else 1
                    self.values[key] = max(low, int(float(s.value("rules_" + key, base[key]))))
                except Exception:
                    self.values[key] = base[key]

    @property
    def enabled(self):
        return self.preset != "off"

    def keep_seconds(self, separation_seconds=0):
        longest = max(self.values["song_minutes"], self.values["artist_minutes"]) * 60
        return max(separation_seconds, longest, self.values["window_hours"] * 3600, 4 * 3600) + 600

    def check(self, path, history, planned=(), now=None):
        """Returns '' when the song may play, or the reason it may not."""
        if not self.enabled or not is_song_entry(path):
            return ""
        now = time.time() if now is None else now
        artist, album, title = track_tags(path)
        artist = primary_artist(artist)
        window = self.values["window_hours"] * 3600
        song_hold = self.values["song_minutes"] * 60
        artist_hold = self.values["artist_minutes"] * 60
        horizon = max(window, song_hold, artist_hold)
        seq = [(t, p) for p, t in history.last_played_track.items()
               if now - t < horizon and is_song_entry(p) and p != path]
        seq.sort(key=lambda item: item[0])
        for offset, p in enumerate(planned):
            if is_song_entry(p) and p != path:
                seq.append((now, p))
        own_key = (artist, title)
        if song_hold and path in history.last_played_track and now - history.last_played_track[path] < song_hold:
            return "the same song played too recently"
        if any(p == path for p in planned):
            return "the same song is already queued ahead"
        same_artist_songs = set()
        same_album_songs = set()
        for t, p in seq:
            pa, pal, pt = track_tags(p)
            pa = primary_artist(pa)
            if song_hold and title and pt == title and pa == artist and now - t < song_hold:
                return "the same song played too recently"
            if artist and pa == artist:
                if artist_hold and now - t < artist_hold:
                    return "the same artist played too recently"
                if now - t < window:
                    same_artist_songs.add(pt or p)
            if album and pal == album and now - t < window:
                same_album_songs.add(pt or p)
        if artist and len(same_artist_songs | {title or path}) > self.values["artist_max"]:
            return f"more than {self.values['artist_max']} different songs by the same artist in {self.values['window_hours']} hours"
        if album and len(same_album_songs | {title or path}) > self.values["album_max"]:
            return f"more than {self.values['album_max']} different songs from the same album in {self.values['window_hours']} hours"
        run_artist = run_album = 0
        # runs: count back from the newest song while the artist (or album) keeps matching
        for t, p in reversed(seq):
            pa, _pal, _pt = track_tags(p)
            if artist and primary_artist(pa) == artist:
                run_artist += 1
            else:
                break
        for t, p in reversed(seq):
            _pa, pal, _pt = track_tags(p)
            if album and pal == album:
                run_album += 1
            else:
                break
        if run_artist + 1 > self.values["artist_run"]:
            return f"more than {self.values['artist_run']} songs by the same artist in a row"
        if run_album + 1 > self.values["album_run"]:
            return f"more than {self.values['album_run']} songs from the same album in a row"
        return ""


def build_library_report(rotations, rules):
    """A plain text report: files with missing artist, title or album tags, and any album that has more songs in
    one volume than the album limit allows in the window. `rotations` is a list of (name, [paths])."""
    lines = [f"Library report, {time.strftime('%A %B %d %Y %H:%M')}", "",
             f"Rules in force: {'off' if not rules.enabled else rules.preset}. "
             f"At most {rules.values['artist_max']} different songs by one artist and {rules.values['album_max']} from one album "
             f"in {rules.values['window_hours']} hours; no more than {rules.values['artist_run']} by one artist and "
             f"{rules.values['album_run']} from one album in a row.", ""]
    totals = {"files": 0, "no_artist": 0, "no_album": 0, "no_title": 0, "crowded": 0}
    for name, paths in rotations:
        albums = Counter()
        missing = []
        for p in paths:
            artist, album, title = track_tags(p)
            totals["files"] += 1
            gaps = []
            if not artist:
                totals["no_artist"] += 1
                gaps.append("artist")
            if not album:
                totals["no_album"] += 1
                gaps.append("album")
            if not title:
                totals["no_title"] += 1
                gaps.append("title")
            if gaps:
                missing.append(f"    {os.path.basename(p)}: no {', '.join(gaps)}")
            if album:
                albums[album] += 1
        crowded = [(a, n) for a, n in albums.items() if n > rules.values["album_max"]]
        lines.append(f"{name}: {len(paths)} songs")
        for a, n in sorted(crowded, key=lambda x: -x[1]):
            totals["crowded"] += 1
            lines.append(f"    Album \"{a}\" has {n} songs in this volume; only {rules.values['album_max']} may play in "
                         f"{rules.values['window_hours']} hours, so the rest are borrowed or skipped.")
        lines.extend(missing)
    lines += ["", f"{totals['files']} songs checked: {totals['no_artist']} without an artist tag, "
                  f"{totals['no_title']} without a title, {totals['no_album']} without an album tag, "
                  f"{totals['crowded']} albums over the album limit inside one volume."]
    return lines, totals



# ---------------------------------------------------------------------------
# OctiMax-style stream processor: two-band AGC -> five-band compressor ->
# look-ahead peak limiter. Frequency-domain (numpy only), stereo-linked.
# This is an original implementation of the same signal flow; it is not
# Linear Acoustic's code and will not sound identical to a real OctiMax.
# It processes the audio sent to the stream (and can be switched on per
# source: Deck A, Deck B, jingles/ads), not the local speaker output.
# ---------------------------------------------------------------------------

PROCESSOR_PRESETS = {
    "Broadcast": {
        "thresholds": [-26.0, -24.0, -24.0, -26.0, -28.0],
        "ratios": [3.0, 3.5, 3.5, 4.0, 4.0],
        "attack_ms": [40.0, 25.0, 15.0, 8.0, 4.0],
        "release_ms": [400.0, 250.0, 180.0, 120.0, 90.0],
        "makeup_db": [3.0, 2.0, 2.0, 3.0, 4.0],
        "agc_target_db": -20.0,
    },
    "Gentle": {
        "thresholds": [-22.0, -22.0, -22.0, -22.0, -24.0],
        "ratios": [2.0, 2.0, 2.0, 2.5, 2.5],
        "attack_ms": [50.0, 30.0, 20.0, 10.0, 6.0],
        "release_ms": [500.0, 350.0, 250.0, 180.0, 120.0],
        "makeup_db": [1.0, 1.0, 1.0, 1.5, 2.0],
        "agc_target_db": -22.0,
    },
    "Loud": {
        "thresholds": [-30.0, -29.0, -29.0, -30.0, -32.0],
        "ratios": [4.0, 5.0, 5.0, 6.0, 6.0],
        "attack_ms": [30.0, 15.0, 10.0, 5.0, 3.0],
        "release_ms": [300.0, 180.0, 130.0, 90.0, 70.0],
        "makeup_db": [5.0, 4.0, 4.0, 5.0, 6.0],
        "agc_target_db": -18.0,
    },
    "Off (flat)": {
        "thresholds": [0.0] * 5, "ratios": [1.0] * 5, "attack_ms": [10.0] * 5,
        "release_ms": [100.0] * 5, "makeup_db": [0.0] * 5, "agc_target_db": None,
    },
}


def _smoothstep(x):
    x = np.clip(x, 0.0, 1.0)
    return x * x * (3.0 - 2.0 * x)


class StreamProcessor:
    FRAME = 2048
    HOP = 1024
    BAND_EDGES = (150.0, 600.0, 2500.0, 7000.0)
    AGC_EDGE = 250.0
    LOOKAHEAD = 220  # samples, about 5 ms at 44.1 kHz

    def __init__(self, sample_rate=44100, preset="Broadcast", ceiling_db=-1.0):
        self.sr = float(sample_rate)
        n = self.FRAME
        self.window = np.sqrt(0.5 - 0.5 * np.cos(2.0 * np.pi * np.arange(n) / n)).astype(np.float32)
        freqs = np.fft.rfftfreq(n, 1.0 / self.sr)
        freqs[0] = 1.0  # avoid log of zero; DC belongs to the lowest band
        log_f = np.log2(freqs)

        def transition(edge):
            centre = np.log2(edge)
            return _smoothstep((log_f - (centre - 0.25)) / 0.5)

        t = [transition(e) for e in self.BAND_EDGES]
        self.band_weights = [1.0 - t[0], t[0] - t[1], t[1] - t[2], t[2] - t[3], t[3]]
        agc_t = transition(self.AGC_EDGE)
        self.agc_weights = [1.0 - agc_t, agc_t]
        self.bin_scale = np.full(len(freqs), 2.0)
        self.bin_scale[0] = 1.0
        self.bin_scale[-1] = 1.0
        self.frame_seconds = self.HOP / self.sr

        self.enabled = True
        self.input_gain_db = 0.0
        self.ceiling = 10.0 ** (ceiling_db / 20.0)
        self.set_preset(preset)
        self.reset()

    # --- settings ---
    def set_preset(self, name):
        preset = PROCESSOR_PRESETS.get(name, PROCESSOR_PRESETS["Broadcast"])
        self.preset_name = name if name in PROCESSOR_PRESETS else "Broadcast"
        self.thresholds = list(preset["thresholds"])
        self.ratios = list(preset["ratios"])
        self.attack_ms = list(preset["attack_ms"])
        self.release_ms = list(preset["release_ms"])
        self.makeup_db = list(preset["makeup_db"])
        self.agc_target_db = preset["agc_target_db"]

    def set_ceiling_db(self, ceiling_db):
        self.ceiling = 10.0 ** (max(-12.0, min(0.0, ceiling_db)) / 20.0)

    def reset(self):
        self.in_fifo = np.zeros((0, 2), dtype=np.float32)
        self.out_fifo = np.zeros((self.FRAME, 2), dtype=np.float32)
        self.ola = np.zeros((self.FRAME, 2), dtype=np.float32)
        self.agc_gain_db = [0.0, 0.0]
        self.band_reduction_db = [0.0] * 5
        self.limiter_hist = np.zeros((2 * self.LOOKAHEAD, 2), dtype=np.float32)
        self.limiter_prev_gain = 1.0

    # --- processing ---
    def _band_levels_db(self, power, weights):
        mean_square = [float(np.sum(w * power * self.bin_scale)) / (self.FRAME * self.FRAME) / 0.5
                       for w in weights]
        return [10.0 * math.log10(max(ms, 1e-12)) for ms in mean_square]

    def _process_spectrum(self, spec):
        power = np.mean(np.abs(spec) ** 2, axis=1)

        # Stage 1: slow two-band AGC (evens out overall level and tonal balance).
        if self.agc_target_db is not None:
            levels = self._band_levels_db(power, self.agc_weights)
            for i, level in enumerate(levels):
                if level > -55.0:
                    desired = max(-12.0, min(12.0, self.agc_target_db - level))
                    tau = 1.0 if desired < self.agc_gain_db[i] else 3.5
                    alpha = 1.0 - math.exp(-self.frame_seconds / tau)
                    self.agc_gain_db[i] += alpha * (desired - self.agc_gain_db[i])
            agc_gain = sum(w * (10.0 ** (g / 20.0)) for w, g in zip(self.agc_weights, self.agc_gain_db))
            spec = spec * agc_gain[:, None]
            power = power * agc_gain ** 2

        # Stage 2: five-band compressor.
        levels = self._band_levels_db(power, self.band_weights)
        comp_gain = np.zeros(len(power))
        for b, level in enumerate(levels):
            over = level - self.thresholds[b]
            target = max(0.0, over * (1.0 - 1.0 / max(1.0, self.ratios[b])))
            current = self.band_reduction_db[b]
            tau = (self.attack_ms[b] if target > current else self.release_ms[b]) / 1000.0
            alpha = 1.0 - math.exp(-self.frame_seconds / max(tau, 1e-3))
            current += alpha * (target - current)
            self.band_reduction_db[b] = current
            comp_gain += self.band_weights[b] * (10.0 ** ((self.makeup_db[b] - current) / 20.0))
        return spec * comp_gain[:, None]

    def _limit(self, signal):
        """Look-ahead peak limiter: ramps the gain down before a peak arrives."""
        look = self.LOOKAHEAD
        n = len(signal)
        combined = np.concatenate([self.limiter_hist, signal])  # 2*look + n
        self.limiter_hist = combined[-2 * look:]
        peak = np.max(np.abs(combined), axis=1)
        need = np.minimum(1.0, self.ceiling / np.maximum(peak, 1e-9))
        forward_min = np.lib.stride_tricks.sliding_window_view(need, look + 1).min(axis=1)  # look + n
        csum = np.concatenate([[0.0], np.cumsum(forward_min, dtype=np.float64)])
        positions = np.arange(look, look + n)
        gain = (csum[positions + 1] - csum[positions - look]) / (look + 1)
        # Release: gain may only recover slowly (about 100 ms from full reduction).
        step = 1.0 / (0.1 * self.sr)
        idx = np.arange(n + 1, dtype=np.float64)
        seeded = np.concatenate([[self.limiter_prev_gain], gain])
        recovered = step * idx + np.minimum.accumulate(seeded - step * idx)
        gain = np.minimum(1.0, recovered[1:])
        self.limiter_prev_gain = float(gain[-1])
        out = combined[look:look + n] * gain[:, None].astype(np.float32)
        return np.clip(out, -self.ceiling, self.ceiling)

    def process(self, block):
        """block: float32 array (n, 2). Returns processed float32 (n, 2), delayed by about 50 ms."""
        if not self.enabled or len(block) == 0:
            return block
        n = len(block)
        gain_in = 10.0 ** (self.input_gain_db / 20.0)
        self.in_fifo = np.concatenate([self.in_fifo, block * np.float32(gain_in)])
        while len(self.in_fifo) >= self.FRAME:
            frame = self.in_fifo[:self.FRAME] * self.window[:, None]
            self.in_fifo = self.in_fifo[self.HOP:]
            spec = np.fft.rfft(frame, axis=0)
            spec = self._process_spectrum(spec)
            out = np.fft.irfft(spec, n=self.FRAME, axis=0).astype(np.float32) * self.window[:, None]
            self.ola += out
            self.out_fifo = np.concatenate([self.out_fifo, self.ola[:self.HOP]])
            self.ola = np.concatenate([self.ola[self.HOP:], np.zeros((self.HOP, 2), dtype=np.float32)])
        if len(self.out_fifo) < n:
            self.out_fifo = np.concatenate(
                [self.out_fifo, np.zeros((n - len(self.out_fifo), 2), dtype=np.float32)])
        chunk = self.out_fifo[:n]
        self.out_fifo = self.out_fifo[n:]
        return self._limit(chunk)



# ---------------------------------------------------------------------------
# Rotation engine: two alternating decks, crossfading like a DJ automation
# ---------------------------------------------------------------------------

class SplitOutput:
    """A deck's audio output with two levels: `volume()` is the level the program means (it feeds the
    stream mix and follows fades and ducking), while the real output to the speakers is set to silence
    when the speakers are muted. Muting never reaches the stream."""

    def __init__(self, device=None):
        self.real = QAudioOutput()
        if device is not None:
            self.real.setDevice(device)
        self.logical = float(self.real.volume())
        self.muted = False

    def setDevice(self, device):
        self.real.setDevice(device)

    def setVolume(self, value):
        self.logical = float(value)
        self.real.setVolume(0.0 if self.muted else self.logical)

    def volume(self):
        return self.logical

    def set_muted(self, muted):
        self.muted = bool(muted)
        self.real.setVolume(0.0 if self.muted else self.logical)


class Deck:
    """
    One playback deck: its own QMediaPlayer, QAudioOutput, and FadeController.
    Two of these alternate being "live" so every rotation transition is a
    real crossfade between two independent decks.
    """

    def __init__(self, name, on_fade_progress=None, output_device=None):
        self.name = name  # "A" or "B"
        self.player = QMediaPlayer()
        self.audio_output = SplitOutput(output_device)
        self.audio_output.setVolume(0.0)
        self.player.setAudioOutput(self.audio_output.real)
        self.fader = FadeController(self.audio_output, on_progress=on_fade_progress)
        self.current_track_path = None
        self.manual_volume = 1.0  # the deck's own fader level, independent of ducking/mute

    def load_and_play(self, play_path, original_path=None):
        self.current_track_path = original_path or play_path
        self.player.setSource(QUrl.fromLocalFile(play_path))
        self.player.play()

    def load_paused(self, play_path, original_path=None):
        """Loads a track and holds it at the very start, ready to be played at the crossfade."""
        self.current_track_path = original_path or play_path
        self.player.setSource(QUrl.fromLocalFile(play_path))
        self.player.pause()

    def play(self):
        self.player.play()

    def pause(self):
        self.player.pause()

    def stop(self):
        self.player.stop()
        self.current_track_path = None

    def set_manual_volume(self, level):
        self.manual_volume = max(0.0, min(1.0, level))


class RotationEngine:
    """
    Drives continuous music rotation across two alternating decks (A and B).
    Whichever deck is "live" plays the current track; shortly before it ends,
    the next track is loaded (paused) into the other deck and the engine
    crossfades: the live deck fades down while the cued deck starts and fades
    up, then the roles swap.
    """

    def __init__(self, settings, on_status, on_now_playing, on_track_ending=None,
                 on_crossfader_move=None, on_deck_update=None, normalizer=None,
                 output_device=None):
        self.settings = settings
        self.on_status = on_status
        self.on_now_playing = on_now_playing
        self.on_track_ending = on_track_ending
        self.on_crossfader_move = on_crossfader_move
        self.on_deck_update = on_deck_update  # on_deck_update(deck_name, track_path_or_None)
        self.normalizer = normalizer

        self.deck_a = Deck("A", on_fade_progress=self._on_deck_a_fade_progress,
                           output_device=output_device)
        self.deck_b = Deck("B", on_fade_progress=self._on_deck_b_fade_progress,
                           output_device=output_device)
        self.live_deck_name = "A"

        for deck in (self.deck_a, self.deck_b):
            deck.player.mediaStatusChanged.connect(
                lambda status, d=deck: self.on_media_status_changed(status, d)
            )
            deck.player.positionChanged.connect(
                lambda pos, d=deck: self.on_position_changed(pos, d)
            )

        self.shuffled_queue = []
        self.is_paused_for_sequence = False
        self.break_fading = False      # a break has taken over; the song is fading and nothing else may start
        self.automation_on = False     # A turns it on; with it off, the song on air finishes and nothing follows
        self.is_running = False
        self.next_track_cued = False

        self.apply_crossfade_setting()
        self.apply_fit_options()
        self.separation_seconds = self.separation_from_settings()
        self.rules = ProgramRules(settings)
        self.play_history = PersistentPlayHistory(settings, self.rules.keep_seconds(self.separation_seconds))
        self.pick_problem = ""
        self._borrow_cache = (0.0, [])
        self.passed = []                  # songs of this hour already aired or skipped: [(path, "played" or "skipped")]
        self.passed_hour = None
        self.replaceable = set()          # queued songs the end-of-hour fit may swap (playlist songs, not hand-placed ones)
        self._fit_pool = (None, [])
        self.ending_beep_fired = False

        self.is_ducked = False
        self.is_muted = False

        # Rotations, schedule and editable queue (filled in by the app after construction)
        self.rotation_library = None
        self.rotation_schedule = None
        self.active_rotation_id = None
        self.on_queue_changed = None      # on_queue_changed()
        self.on_rotation_swapped = None   # on_rotation_swapped(old_name, new_name)
        self.pinned_tracks = set()        # hand-inserted tracks skip the separation rule
        self.recently_added = []
        self.playlist_driven = False      # True once the queue is fed by hourly playlists

        # Break protection (never cut a song for a scheduled break)
        self.break_target = None
        self.break_slot = None
        self.break_callback = None
        self.break_started = False
        self.tail_loops = 0
        self.last_tail_seek = 0.0
        self.last_taken_slot = None
        self.last_taken_time = None

    def separation_from_settings(self):
        try:
            hours = float(self.settings.value("separation_hours", 2))
        except Exception:
            hours = 2.0
        return int(max(0.25, min(12.0, hours)) * 3600)

    def crossfade_enabled(self):
        try:
            return str(self.settings.value("crossfade_enabled", "false")).lower() == "true"
        except Exception:
            return False

    def apply_crossfade_setting(self):
        try:
            if str(self.settings.value("crossfade_tab_v1", "")) != "done":      # first run with the Crossfade section
                self.settings.setValue("fit_quarter_marks", "true")
                self.settings.setValue("crossfade_tab_v1", "done")
        except Exception:
            pass
        set_crossfade_overlap(self.crossfade_enabled())

    def apply_separation_setting(self):
        self.separation_seconds = self.separation_from_settings()
        self.rules.load()
        self.play_history.keep_seconds = self.rules.keep_seconds(self.separation_seconds)

    # --- deck helpers ---
    def get_live_deck(self):
        return self.deck_a if self.live_deck_name == "A" else self.deck_b

    def get_cued_deck(self):
        return self.deck_b if self.live_deck_name == "A" else self.deck_a

    @property
    def current_track_path(self):
        return self.get_live_deck().current_track_path

    def apply_output_device(self, device):
        if device is None:
            return
        self.deck_a.audio_output.setDevice(device)
        self.deck_b.audio_output.setDevice(device)

    def _effective_level(self):
        # Muting the speakers is handled by each deck's SplitOutput; the stream is never muted.
        if self.is_ducked:
            return MIC_DUCKING_LEVEL
        return 1.0

    def _on_deck_a_fade_progress(self, start_vol, end_vol, progress):
        self._on_deck_fade_progress("A", start_vol, end_vol, progress)

    def _on_deck_b_fade_progress(self, start_vol, end_vol, progress):
        self._on_deck_fade_progress("B", start_vol, end_vol, progress)

    def _on_deck_fade_progress(self, deck_name, start_vol, end_vol, progress):
        """Moves the on-screen crossfader (0 = Deck A, 100 = Deck B) in step with real fades."""
        if not self.on_crossfader_move:
            return
        if deck_name == "A":
            if end_vol < start_vol:
                position = progress * 100
            else:
                position = (1 - progress) * 100 if self.live_deck_name == "A" else 100
        else:
            if end_vol < start_vol:
                position = (1 - progress) * 100
            else:
                position = progress * 100 if self.live_deck_name == "B" else 0
        self.on_crossfader_move(position)

    def get_library_folder(self):
        return self.settings.value("music_library_folder", "")

    def has_rotations(self):
        return bool(self.rotation_library is not None and self.rotation_schedule is not None
                    and self.rotation_library.rotations)

    def source_files(self):
        """Tracks for the rotation scheduled for the current hour (or the plain library folder)."""
        if self.has_rotations():
            rotation = self.rotation_library.find(
                self.rotation_schedule.rotation_id_for_hour(datetime.now().hour))
            candidates = ([rotation] if rotation else []) + list(self.rotation_library.rotations)
            for candidate in candidates:
                files = candidate.track_paths()
                if files:
                    self.active_rotation_id = candidate.id
                    return files
        self.active_rotation_id = None
        return scan_audio_files(self.get_library_folder())  # includes every subfolder

    def active_rotation_name(self):
        if self.rotation_library is None:
            return ""
        rotation = self.rotation_library.find(self.active_rotation_id)
        return rotation.name if rotation else ""

    def build_shuffled_queue(self):
        files = self.source_files()
        random.shuffle(files)
        keep = [p for p in self.shuffled_queue if p in self.pinned_tracks or is_hour_marker(p)]
        self.shuffled_queue = keep + [f for f in files if f not in keep]
        self.prefetch_upcoming()
        self._queue_changed()
        return len(files)

    # --- editable queue ---
    def _queue_changed(self):
        if self.on_queue_changed:
            try:
                self.on_queue_changed()
            except Exception:
                pass

    def queue_snapshot(self):
        """What plays next, in order. A track already loaded onto the other deck is shown first."""
        items = list(self.shuffled_queue)
        if self.next_track_cued:
            cued = self.get_cued_deck().current_track_path
            if cued:
                items.insert(0, cued)
        return items

    def uncue_to_front(self):
        """Puts a track already loaded for the next crossfade back at the front of the queue, so edits
        (an inserted jingle or ad, a move, a removal) decide what plays next."""
        if not self.next_track_cued:
            return
        cued_deck = self.get_cued_deck()
        path = cued_deck.current_track_path
        cued_deck.stop()
        self._notify_deck_update(cued_deck.name, None)
        self.next_track_cued = False
        if path:
            self.shuffled_queue.insert(0, path)
            self.pinned_tracks.add(path)

    def move_queue_item(self, index, delta):
        self.uncue_to_front()
        new_index = index + delta
        if not (0 <= index < len(self.shuffled_queue)) or not (0 <= new_index < len(self.shuffled_queue)):
            return index
        item = self.shuffled_queue.pop(index)
        self.shuffled_queue.insert(new_index, item)
        self.replaceable.discard(item)
        if item not in self.pinned_tracks and not is_hour_marker(item):
            self.pinned_tracks.add(item)  # a hand-moved track plays where you put it
        self._queue_changed()
        return new_index

    def remove_queue_item(self, index):
        self.uncue_to_front()
        if not (0 <= index < len(self.shuffled_queue)):
            return None
        item = self.shuffled_queue.pop(index)
        self.pinned_tracks.discard(item)
        self._queue_changed()
        return item

    def insert_queue_item(self, path, index=None):
        """Adds a track (or hour marker) to the queue. Never starts playback. Inserted at the top, it
        replaces whatever was about to play next."""
        self.uncue_to_front()
        if index is None or index > len(self.shuffled_queue):
            index = len(self.shuffled_queue)
        index = max(0, index)
        self.shuffled_queue.insert(index, path)
        self.replaceable.discard(path)
        if not is_hour_marker(path):
            self.pinned_tracks.add(path)
            if self.normalizer is not None and index < 3:
                self.normalizer.start([path], priority=True)
        self._queue_changed()
        return index

    def load_queue_entries(self, entries, replace=True, locked=False):
        """locked=True (an hour with recorded voice tracks) keeps every song exactly where it is."""
        entries = [e for e in entries if is_hour_marker(e) or os.path.isfile(e)]
        if replace:
            if self.next_track_cued and not self.is_paused_for_sequence:
                cued_deck = self.get_cued_deck()      # the new list decides what plays next
                cued_deck.stop()
                self._notify_deck_update(cued_deck.name, None)
                self.next_track_cued = False
            self.shuffled_queue = []
        for e in entries:
            self.shuffled_queue.append(e)
            if not is_hour_marker(e):
                self.pinned_tracks.add(e)
                if locked or not is_song_entry(e):
                    self.replaceable.discard(e)
                else:
                    self.replaceable.add(e)
        self.prefetch_upcoming()
        self._queue_changed()
        return len(entries)

    def queue_has_tag(self, tag):
        return any(is_hour_marker(e) and marker_tag(e) == tag for e in self.shuffled_queue)

    def drop_before_marker(self, tag):
        """The hour has turned: remove what is left of the old hour, and the new hour's marker itself."""
        for i, entry in enumerate(self.shuffled_queue):
            if is_hour_marker(entry) and marker_tag(entry) == tag:
                dropped = self.shuffled_queue[:i + 1]
                self.shuffled_queue = self.shuffled_queue[i + 1:]
                for item in dropped:
                    self.pinned_tracks.discard(item)
                self._queue_changed()
                return len([d for d in dropped if not is_hour_marker(d)])
        return 0

    def drop_stale_cue(self):
        """A track already cued from the old hour is thrown away so the new hour starts with its own music."""
        if self.next_track_cued and not self.is_paused_for_sequence:
            cued_deck = self.get_cued_deck()
            cued_deck.stop()
            self._notify_deck_update(cued_deck.name, None)
            self.next_track_cued = False

    def add_new_tracks(self, rotation_id, paths):
        """New songs found in a rotation folder: join the live queue without touching the schedule."""
        if rotation_id != self.active_rotation_id or not paths:
            return 0
        for path in paths:
            if path not in self.shuffled_queue:
                self.shuffled_queue.insert(random.randint(0, len(self.shuffled_queue)), path)
        if self.normalizer is not None:
            self.normalizer.start(paths)
        self._queue_changed()
        return len(paths)

    def check_rotation_for_hour(self):
        """Called every second: when the hour turns over, swap to that hour's rotation live."""
        if not self.has_rotations():
            return
        new_id = self.rotation_schedule.rotation_id_for_hour(datetime.now().hour)
        if new_id == self.active_rotation_id or self.rotation_library.find(new_id) is None:
            return
        self.swap_rotation(new_id)

    def swap_rotation(self, new_id):
        new = self.rotation_library.find(new_id)
        if new is None:
            return False
        files = new.track_paths()
        if not files:
            return False
        old = self.rotation_library.find(self.active_rotation_id)
        if old is None or old.id != new_id:
            try:
                self.rotation_schedule.note_used(new_id)
                for line in self.rotation_schedule.usage_lines():
                    RUN_LOG.write("ROTATE", f"{new.name} goes on air. {line}")
            except Exception as e:
                _log_exception(type(e), e, e.__traceback__)
        self.active_rotation_id = new_id
        if not self.playlist_driven:
            random.shuffle(files)
            keep = [p for p in self.shuffled_queue if p in self.pinned_tracks or is_hour_marker(p)]
            self.shuffled_queue = keep + [f for f in files if f not in keep]
            if self.is_running:
                self.prefetch_upcoming()
        self._queue_changed()
        if self.on_rotation_swapped:
            self.on_rotation_swapped(old.name if old else "", new.name)
        return True

    # --- fitting the end of the hour ---
    def fit_slots(self):
        """Which break marks the last song is fitted to: the top of the hour, and the others if you switch it on."""
        slots = []
        if str(self.settings.value("fit_end_of_hour", "true")).lower() != "false":
            slots.append(0)
        if str(self.settings.value("fit_quarter_marks", "true")).lower() != "false":
            slots += [15, 30, 45]
        return slots

    def next_fit_mark(self, now=None):
        now = now or datetime.now()
        slots = self.fit_slots()
        if not slots:
            return None
        best = None
        for minute in slots:
            candidate = now.replace(minute=minute, second=0, microsecond=0)
            if candidate <= now:
                candidate += timedelta(hours=1)
            if best is None or candidate < best:
                best = candidate
        return best

    def fit_candidates(self, prefix):
        rotation_id = self.active_rotation_id
        if self._fit_pool[0] != rotation_id or not self._fit_pool[1]:
            rotation = self.rotation_library.find(rotation_id) if self.rotation_library else None
            self._fit_pool = (rotation_id, rotation.track_paths() if rotation else [])
        busy = {self.deck_a.current_track_path, self.deck_b.current_track_path}
        queued = set(self.shuffled_queue) - set(prefix)
        pool = list(self._fit_pool[1])
        if len(pool) < 60:
            have = set(pool)
            pool += [p for p in self.ranked_borrow_pool() if p not in have][:250]      # a small volume: borrow from the others, longest-waiting volumes first
        found = [p for p in pool if p not in busy and p not in queued and not self.rule_problem(p)]
        rotor = getattr(self, "folder_rotor", None)
        rotation = self.rotation_library.find(rotation_id) if self.rotation_library else None
        if rotor is not None and rotation is not None and len(found) > 60:
            # Favor songs from the folders that have waited longest, so the swaps keep every folder in turn.
            waited = sorted(found, key=lambda p: rotor.last_scheduled(rotation.id, folder_group(p, rotation.folder)))
            found = waited[:max(40, int(len(found) * 0.7))]
        return found

    def warm_up(self):
        """Reads every song's tags once, in the background, so the rules can check any song at once."""
        try:
            for path in self.borrow_pool():
                track_tags(path)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def rule_problem(self, path, planned=()):
        try:
            return self.rules.check(path, self.play_history, planned)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
            return ""

    def borrow_pool(self):
        """Every song of every rotation (refreshed every ten minutes), for when the hour's own volume runs short."""
        now = time.time()
        if now - self._borrow_cache[0] < 600 and self._borrow_cache[1]:
            return self._borrow_cache[1]
        found = []
        seen = set()
        owner = {}
        if self.rotation_library is not None:
            for rotation in sorted(self.rotation_library.rotations, key=lambda r: bool(getattr(r, "mix", False))):
                try:
                    for p in rotation.track_paths():
                        if p not in seen:
                            seen.add(p)
                            found.append(p)
                            owner[p] = rotation.id
                except Exception:
                    pass
        if not found:
            try:
                found = list(scan_audio_files(self.get_library_folder()))
            except Exception:
                found = []
        self._borrow_owner = owner
        self._borrow_cache = (now, found)
        return found

    def ranked_borrow_pool(self):
        """The borrow pool with the volumes that have waited longest (or never played) first."""
        pool = list(self.borrow_pool())
        random.shuffle(pool)
        owner = getattr(self, "_borrow_owner", {})
        schedule = self.rotation_schedule
        last = self.play_history.last_played_track

        def wait_key(p):
            volume = owner.get(p)
            used = schedule.volume_last_used(volume) if (schedule is not None and volume) else 0.0
            return (used, last.get(p, 0))
        pool.sort(key=wait_key)
        return pool

    def borrow_track(self):
        """A song that passes every rule, preferring the active volume, then whatever has waited longest."""
        busy = {self.deck_a.current_track_path, self.deck_b.current_track_path}
        queued = set(self.shuffled_queue)
        pool = [p for p in self.ranked_borrow_pool() if p not in busy and p not in queued]
        own = set()
        if self.rotation_library is not None and self.active_rotation_id:
            rotation = self.rotation_library.find(self.active_rotation_id)
            if rotation is not None:
                own = set(self._fit_pool[1]) if self._fit_pool[0] == self.active_rotation_id else set(rotation.track_paths())
        pool.sort(key=lambda p: 0 if p in own else 1)       # this volume first; the order inside each part is longest-waiting first
        for candidate in pool[:900]:
            if not self.rule_problem(candidate):
                where = "this volume" if candidate in own else "another volume"
                volume = getattr(self, "_borrow_owner", {}).get(candidate)
                if volume and candidate not in own and self.rotation_schedule is not None:
                    self.rotation_schedule.note_used(volume, borrowed=True)
                RUN_LOG.write("RULES", f"Borrowed from {where} so no rule is broken: {os.path.basename(candidate)}")
                return candidate
        return None

    def is_replaceable(self, item):
        return is_song_entry(item) and (item in self.replaceable or item not in self.pinned_tracks)

    def next_break_mark(self, now=None):
        now = now or datetime.now()
        best = None
        for minute in (0, 15, 30, 45):
            candidate = now.replace(minute=minute, second=0, microsecond=0)
            if candidate <= now:
                candidate += timedelta(hours=1)
            if best is None or candidate < best:
                best = candidate
        return best

    def apply_fit_options(self):
        try:
            early = float(self.settings.value("fit_early_seconds", FIT_GOOD_ENOUGH_EARLY))
            shortest = float(self.settings.value("fit_min_song_seconds", FIT_MIN_SONG_SECONDS))
        except Exception:
            early, shortest = FIT_GOOD_ENOUGH_EARLY, FIT_MIN_SONG_SECONDS
        set_fit_options(early, shortest)

    def fit_before_mark(self, now=None, force_mark=False, remaining_override=None):
        """Called just before the next song is chosen. When the mark is near, the queued songs are swapped
        for ones that finish exactly on it, so the last song is never faded out. Voice tracked hours and
        hand-placed songs are never touched. Returns the replacement songs, or None."""
        mark = self.next_break_mark(now) if force_mark else self.next_fit_mark(now)
        if mark is None or self.rotation_library is None:
            return None
        now = now or datetime.now()
        live = self.get_live_deck()
        remaining = 0.0
        if remaining_override is not None:
            remaining = float(remaining_override)
        elif live.current_track_path:
            try:
                remaining = max(0.0, (live.player.duration() - live.player.position()) / 1000.0)
            except Exception:
                remaining = 0.0
        gap = (mark - now).total_seconds() - remaining + overlap_seconds()
        if gap < FIT_MIN_SECONDS or gap > FIT_WINDOW_SECONDS:
            return None
        prefix = []
        for item in self.shuffled_queue:
            if is_hour_marker(item) or not self.is_replaceable(item):
                break
            prefix.append(item)
        if not prefix:
            return None
        candidates = self.fit_candidates(prefix)
        replacement = None
        for _attempt in range(5):
            replacement = plan_hour_end(prefix, gap, candidates, get_track_duration, get_track_artist)
            if not replacement:
                return None
            planned = []
            bad = None
            for song in replacement:
                if self.rule_problem(song, planned):
                    bad = song
                    break
                planned.append(song)
            if bad is None:
                break
            candidates = [c for c in candidates if c != bad]      # that combination breaks a rule: try again without it
            replacement = None
        if not replacement:
            return None
        del self.shuffled_queue[:len(prefix)]
        for item in prefix:
            self.replaceable.discard(item)
        for index, song in enumerate(replacement):
            self.shuffled_queue.insert(index, song)
            self.replaceable.add(song)
        total = timeline_length(replacement, get_track_duration)
        for item in prefix:
            RUN_LOG.write("FIT", f"Removed from the queue to make the break land on time: {os.path.basename(item)}")
        message = (f"Swapped {len(prefix)} queued song(s) for {len(replacement)} so the hour ends on time "
                   f"(about {int(total)} seconds of music for {int(gap)} seconds left).")
        self.on_status(message)
        RUN_LOG.write("FIT", message)
        self._queue_changed()
        return replacement

    # --- played and skipped songs (unchecked), joining an hour partway, playing a song on Enter ---
    def passed_rows(self):
        if self.passed_hour is not None and self.passed_hour != datetime.now().hour:
            self.passed = []
            self.passed_hour = None
        return list(self.passed)

    def note_played(self, path):
        """A song went on air: it stays in the list for the rest of the hour, unchecked."""
        if not is_song_entry(path):
            return
        self.passed_rows()
        self.passed = [(p, st) for p, st in self.passed if p != path]
        self.passed.append((path, "played"))
        self.passed = self.passed[-60:]
        self.passed_hour = datetime.now().hour
        self._queue_changed()

    def uncheck_queue_item(self, index):
        """Unchecking an upcoming song takes it out of the order; it stays listed as skipped."""
        item = self.remove_queue_item(index)
        if item is None:
            return None
        if is_song_entry(item):
            self.passed_rows()
            self.passed = [(p, st) for p, st in self.passed if p != item]
            self.passed.append((item, "skipped"))
            self.passed_hour = datetime.now().hour
        else:
            self.insert_queue_item(item, index)
            return None
        self._queue_changed()
        return item

    def recheck_passed(self, passed_index):
        """Checking a played or skipped song again puts it next in line."""
        rows = self.passed_rows()
        if not (0 <= passed_index < len(rows)):
            return None
        path = rows[passed_index][0]
        self.passed = [(p, st) for p, st in self.passed if p != path]
        self.insert_queue_item(path, 0)
        return path

    def play_item_now(self, index):
        """Enter on a queued song: it goes on air now. With automation off the music then waits for the next
        Enter (live assist); with automation on the queue carries on after it."""
        item = self.remove_queue_item(index)
        if item is None:
            return False
        if not is_song_entry(item):
            self.insert_queue_item(item, index)
            return False
        self.shuffled_queue.insert(0, item)
        self.pinned_tracks.add(item)
        path = self.pick_next_valid_track()
        if path is None:
            return False
        cued_deck = self.get_cued_deck()
        playback_path = normalize_file_loudness(path, self.on_status)
        cued_deck.audio_output.setVolume(0.0)
        cued_deck.load_paused(playback_path, path)
        self.next_track_cued = True
        self._notify_deck_update(cued_deck.name, path)
        self.break_fading = False
        self.is_paused_for_sequence = False
        self.crossfade_to_cued_deck()
        return True

    def join_hour(self, entries, now=None, locked=False):
        """Loads an hour's playlist at the right place when the clock is already partway through it. Songs
        the clock has passed are unchecked (listed as skipped); the first song that can still start in time
        and everything after it stay checked, and the stretch up to the next break is fitted so it lands
        on the mark. Returns (entries loaded, songs passed)."""
        now = now or datetime.now()
        offset = now.minute * 60 + now.second
        passed = []
        keep = list(entries)
        if offset >= 120:
            try:
                estimate = float(self.settings.value("break_estimate_seconds", DEFAULT_BREAK_ESTIMATE_SECONDS))
            except Exception:
                estimate = float(DEFAULT_BREAK_ESTIMATE_SECONDS)
            clock = 0.0
            next_mark = 900.0
            keep = []
            starting = False
            for entry in entries:
                if is_hour_marker(entry):
                    if is_voice_marker(entry):
                        if starting:
                            keep.append(entry)
                    else:
                        keep.append(entry)
                    continue
                start = clock
                clock += get_track_duration(entry)
                while clock >= next_mark:
                    clock += estimate
                    next_mark += 900.0
                if not starting and start >= offset - 10:
                    starting = True
                if starting:
                    keep.append(entry)
                else:
                    passed.append(entry)
        count = self.load_queue_entries(keep, replace=True, locked=locked)
        self.passed = [(p, "skipped") for p in passed if is_song_entry(p)]
        self.passed_hour = now.hour if self.passed else None
        if not locked:
            try:
                if self.rotation_schedule is not None:
                    rid = self.rotation_schedule.rotation_id_for_hour(now.hour)
                    if rid:
                        self.active_rotation_id = rid
                self.fit_before_mark(now, force_mark=True)
            except Exception as e:
                _log_exception(type(e), e, e.__traceback__)
        self._queue_changed()
        return count, len(self.passed)

    # --- break protection ---
    def arm_break(self, target, slot, callback):
        """Schedules a break for the clock time `target`. The song on air is never cut."""
        self.break_target = target
        self.break_slot = slot
        self.break_callback = callback
        self.break_started = False
        self.tail_loops = 0

    def disarm_break(self):
        self.break_target = None
        self.break_slot = None
        self.break_callback = None
        self.break_started = False

    def break_is_armed(self, slot=None):
        return self.break_target is not None and (slot is None or slot == self.break_slot)

    def break_recently_taken(self, slot, within_seconds=150):
        return (self.last_taken_slot == slot and self.last_taken_time is not None
                and (datetime.now() - self.last_taken_time).total_seconds() < within_seconds)

    QUICK_BREAK_FADE_SECONDS = 3.0

    def break_style(self):
        """'fade_at_mark' (default): the music fades out just before the mark so the break starts exactly on it.
        'finish_song': the song on air finishes and the break follows it."""
        try:
            value = str(self.settings.value("break_style", "fade_at_mark"))
        except Exception:
            value = "fade_at_mark"
        return value if value in ("fade_at_mark", "finish_song") else "fade_at_mark"

    def _seconds_to_mark(self):
        if self.break_target is None:
            return None
        return (self.break_target - datetime.now()).total_seconds()

    def _take_break(self, quick=False):
        callback = self.break_callback
        self.last_taken_slot = self.break_slot
        self.last_taken_time = datetime.now()
        self.break_started = True
        self.disarm_break()
        self.begin_crossfade_out(callback, seconds=self.QUICK_BREAK_FADE_SECONDS if quick else None)

    def _break_gate(self, deck, position_ms, duration_ms, ended=False):
        """
        Called when the song on air is in its closing seconds. A song is never cut and never looped:
        if a break is armed (it is within the break window before the mark, or the mark has passed),
        the song fades out as it finishes and the break plays right then. A song still playing at the
        mark simply finishes first, so the break comes in late, straight after it.
        Returns True when the break took over (so the normal cue/crossfade must not run).
        """
        if self.break_target is None or self.break_started:
            return False
        seconds_to_mark = (self.break_target - datetime.now()).total_seconds()
        early_limit = max(self.QUICK_BREAK_FADE_SECONDS + 1, fit_early_limit())
        if self.break_style() == "fade_at_mark" and seconds_to_mark > early_limit:
            return False        # not time yet: the song ends, the next one starts, and the break comes in at the mark
        if seconds_to_mark >= 0:
            self.on_status(f"Song finishing {int(seconds_to_mark)} seconds before the mark: starting the break now.")
        else:
            self.on_status("Song finished after the mark: starting the break now.")
        self._take_break(quick=(self.break_style() == "fade_at_mark" and seconds_to_mark >= 0))
        return True

    def prefetch_upcoming(self):
        """Gets the next few tracks loudness-matched in the background before they're needed."""
        if self.normalizer is not None:
            self.normalizer.start([p for p in self.shuffled_queue[:4] if not is_hour_marker(p)][:3], priority=True)

    def _notify_deck_update(self, deck_name, track_path):
        if self.on_deck_update:
            self.on_deck_update(deck_name, track_path)

    def start(self):
        folder = self.get_library_folder()
        if not self.has_rotations() and (not folder or not os.path.isdir(folder)):
            self.on_status("No music library folder set. Rotation cannot start.")
            return
        real_queued = [p for p in self.shuffled_queue if not is_hour_marker(p)]
        if self.playlist_driven and real_queued:
            count = len(real_queued)     # the hourly playlist is the queue: do not pile the library behind it
            self.prefetch_upcoming()
        else:
            self.shuffled_queue = [p for p in self.shuffled_queue if p in self.pinned_tracks or is_hour_marker(p)]
            count = self.build_shuffled_queue()
        if count == 0:
            self.on_status("Music library folder has no audio files, including its subfolders. Rotation cannot start.")
            return
        live = self.get_live_deck()
        if live.current_track_path and live.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            # A song is still finishing from before: automation simply takes over again after it.
            self.automation_on = True
            self.is_running = True
            self.is_paused_for_sequence = False
            self.on_status("Automation is on. The song on air continues and the queue plays after it.")
            return
        self.automation_on = True
        self.is_running = True
        self.is_paused_for_sequence = False
        self.break_fading = False
        # The first song goes onto Deck A. If Deck A still holds a record that was stopped, it goes onto Deck B.
        occupied = {d.name for d in (self.deck_a, self.deck_b) if d.current_track_path}
        if "A" not in occupied:
            target_name = "A"
        elif "B" not in occupied:
            target_name = "B"
        else:
            target_name = "B" if self.live_deck_name == "A" else "A"
        target = self.deck_a if target_name == "A" else self.deck_b
        self.live_deck_name = target_name
        self.on_status(f"Automation is on, {count} track(s) in the queue. The first song goes onto Deck {target_name}.")
        first_track = self.pick_next_valid_track()
        if first_track is None:
            self.on_status(f"{self.pick_problem or 'Music library is empty'}. Automation stopped.")
            self.is_running = False
            self.automation_on = False
            return
        self.play_history.record_play(first_track)
        self.note_played(first_track)
        self.ending_beep_fired = False
        self.next_track_cued = False
        playback_path = normalize_file_loudness(first_track, self.on_status)
        target.fader.timer.stop()
        target.audio_output.setVolume(self._effective_level() * target.manual_volume)
        target.load_and_play(playback_path, first_track)
        self._notify_deck_update(target_name, first_track)
        self.on_now_playing(first_track)

    def automation_off(self):
        """A while automation is on: the song on air plays to its end, then nothing follows."""
        self.automation_on = False
        self.disarm_break()
        self.uncue_to_front()
        self.on_status("Automation is off. The song on air will finish and nothing will play after it. "
                       "Press A to turn automation back on.")

    def stop_with_fade(self):
        """S: fades what is playing and stops it. The record stays on its deck."""
        self.automation_on = False
        self.break_fading = False
        self.disarm_break()
        self.uncue_to_front()
        self.is_paused_for_sequence = False
        faded = []
        for deck in (self.deck_a, self.deck_b):
            if deck.current_track_path and deck.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                faded.append(deck)
        if not faded:
            self.is_running = False
            self.on_status("Nothing is playing. Automation is off.")
            return
        remaining = {"count": len(faded)}

        def finished(d):
            d.pause()
            remaining["count"] -= 1
            if remaining["count"] <= 0:
                self.is_running = False
                self.on_status(f"Stopped. The record stays on Deck {self.live_deck_name}. "
                               "Press A to start automation again.")
        self.on_status("Fading out and stopping.")
        for deck in faded:
            deck.fader.fade_to(0.0, steps=20, interval_ms=100, on_complete=lambda d=deck: finished(d))

    def stop(self):
        self.is_running = False
        self.automation_on = False
        self.break_fading = False
        self.next_track_cued = False
        self.disarm_break()
        self.deck_a.stop()
        self.deck_b.stop()
        self._notify_deck_update("A", None)
        self._notify_deck_update("B", None)
        self.on_status("Rotation stopped.")

    def pick_next_valid_track(self):
        """Next track from the queue. Hour markers are passed over; hand-placed tracks play where
        you put them; everything else must satisfy the artist/title separation rule."""
        while self.shuffled_queue and is_hour_marker(self.shuffled_queue[0]):
            skipped = self.shuffled_queue.pop(0)
            if is_voice_marker(skipped):
                self.on_status("A voice track slot had no recording, so the music carries on.")
                RUN_LOG.write("VOICE", "An empty voice track slot was skipped.")
            else:
                self.on_status("Hour marker passed.")
        if not self.shuffled_queue:
            if self.build_shuffled_queue() == 0:
                return None
        chosen = None
        self.pick_problem = ""
        for i, candidate in enumerate(self.shuffled_queue):
            if is_hour_marker(candidate):
                continue
            if candidate in self.pinned_tracks:
                chosen = self.shuffled_queue.pop(i)
                reason = self.rule_problem(chosen)
                if reason:
                    RUN_LOG.write("RULES", f"Played as placed by hand, although {reason}: {os.path.basename(chosen)}")
                break
            reason = self.rule_problem(candidate)
            if not reason:
                chosen = self.shuffled_queue.pop(i)
                break
            logged = self.__dict__.setdefault("_rule_logged", set())
            if candidate not in logged:
                logged.add(candidate)
                RUN_LOG.write("RULES", f"Skipped {os.path.basename(candidate)}: {reason}.")
        if chosen is None:
            # Nothing queued may play. The rules are never relaxed: borrow a song from another volume that passes.
            chosen = self.borrow_track()
            if chosen is None:
                self.pick_problem = "No song in the library can play without breaking the programming rules"
                RUN_LOG.write("RULES", self.pick_problem + ".")
                return None
        self.pinned_tracks.discard(chosen)
        self.replaceable.discard(chosen)
        self._queue_changed()
        return chosen

    def cue_next_track_if_needed(self):
        """Loads the next track, paused at its start, into the non-live deck."""
        if self.next_track_cued or not self.is_running or not self.automation_on or self.is_paused_for_sequence:
            return
        try:
            self.fit_before_mark()
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
        next_track = self.pick_next_valid_track()
        if next_track is None:
            self.on_status(f"{self.pick_problem or 'Music library is empty'}. Rotation halted.")
            self.is_running = False
            return
        cued_deck = self.get_cued_deck()
        playback_path = normalize_file_loudness(next_track, self.on_status)
        cued_deck.audio_output.setVolume(0.0)
        cued_deck.load_paused(playback_path, next_track)
        self.next_track_cued = True
        self._notify_deck_update(cued_deck.name, next_track)
        self.prefetch_upcoming()

    def _retire_deck(self, deck):
        """Called when a deck has faded out: stop it and tell the screen it's empty."""
        deck.stop()
        self._notify_deck_update(deck.name, None)

    VOICE_UNDERLAY_LEVEL = 0.30

    def crossfade_to_cued_deck(self, underlay_ms=None):
        """Starts the cued deck, crossfades the live deck out and the cued deck in, then swaps roles.
        After a voice track (underlay_ms given) the song starts quietly under the end of the voice, and
        rises to full level the moment the voice finishes; the voice itself is never faded."""
        live_deck = self.get_live_deck()
        cued_deck = self.get_cued_deck()
        if cued_deck.current_track_path is None:
            return

        target_level = self._effective_level()
        cued_deck.play()
        if underlay_ms is None and not self.crossfade_enabled():
            # The song on air has finished: the next one starts at full level, nothing overlaps.
            cued_deck.fader.timer.stop()
            cued_deck.audio_output.setVolume(target_level * cued_deck.manual_volume)
            live_deck.fader.timer.stop()
            self._retire_deck(live_deck)
        elif underlay_ms is not None:
            full = target_level * cued_deck.manual_volume
            cued_deck.audio_output.setVolume(full * (self.VOICE_UNDERLAY_LEVEL if underlay_ms > 700 else 0.0))
            old_deck = live_deck

            def voice_finished():
                cued_deck.fader.fade_to(self._effective_level() * cued_deck.manual_volume,
                                        steps=15, interval_ms=100)
                QTimer.singleShot(1800, lambda d=old_deck: self._retire_deck(d))
            QTimer.singleShot(max(50, int(underlay_ms)), voice_finished)
        else:
            live_deck.fader.fade_to(0.0, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS,
                                     on_complete=lambda d=live_deck: self._retire_deck(d))
            cued_deck.fader.fade_to(target_level * cued_deck.manual_volume,
                                     steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS)

        self.live_deck_name = cued_deck.name
        self.next_track_cued = False
        self.ending_beep_fired = False
        self.play_history.record_play(cued_deck.current_track_path)
        self.note_played(cued_deck.current_track_path)
        self.on_now_playing(cued_deck.current_track_path)

    def get_upcoming_track_path(self):
        cued_deck = self.get_cued_deck()
        if cued_deck.current_track_path:
            return cued_deck.current_track_path
        real = [c for c in self.shuffled_queue if not is_hour_marker(c)]
        for candidate in real:
            if candidate in self.pinned_tracks or not self.rule_problem(candidate):
                return candidate
        return None

    def on_position_changed(self, position_ms, deck):
        if deck.name != self.live_deck_name:
            return
        duration_ms = deck.player.duration()
        if duration_ms <= 0:
            return
        remaining_ms = duration_ms - position_ms

        if not self.ending_beep_fired and self.on_track_ending and 0 < remaining_ms <= BEEP_WARNING_SECONDS * 1000:
            self.ending_beep_fired = True
            self.on_track_ending()

        if self.break_fading:
            return          # the break owns the closing seconds: no cue, no crossfade
        if (self.is_running and self.automation_on and not self.is_paused_for_sequence and self.break_target is not None
                and not self.break_started and self.break_style() == "fade_at_mark"
                and self._seconds_to_mark() <= self.QUICK_BREAK_FADE_SECONDS):
            self.on_status("Fading the music out so the break starts right on the mark.")
            self._take_break(quick=True)
            return
        if self.is_running and self.automation_on and not self.is_paused_for_sequence:
            crossfade_lead_ms = max(FADE_STEPS * FADE_INTERVAL_MS, 4000)
            if remaining_ms <= crossfade_lead_ms + 2000 and self._break_gate(deck, position_ms, duration_ms):
                return
            underlay = voice_underlay_ms(deck.current_track_path)
            lead_ms = crossfade_lead_ms if underlay is None else max(underlay, 500)
            if not self.next_track_cued and 0 < remaining_ms <= max(crossfade_lead_ms, lead_ms) + 2000:
                self.cue_next_track_if_needed()
            if underlay is None and not self.crossfade_enabled():
                return          # no overlap: the next song starts when this one finishes (see on_media_status_changed)
            if self.next_track_cued and 0 < remaining_ms <= lead_ms:
                self.crossfade_to_cued_deck(underlay_ms=remaining_ms if underlay is not None else None)

    def begin_crossfade_out(self, on_complete, seconds=None):
        """Fades the live deck out ahead of a scheduled break."""
        if not self.is_running or not self.automation_on or self.is_paused_for_sequence:
            if on_complete:
                on_complete()
            return
        self.on_status("Fading music out for upcoming scheduled break.")
        self.break_fading = True

        # A track already loaded for the next crossfade goes back to the front of
        # the queue so it still plays after the break instead of being lost.
        if self.next_track_cued:
            cued_deck = self.get_cued_deck()
            if cued_deck.current_track_path:
                self.shuffled_queue.insert(0, cued_deck.current_track_path)
            cued_deck.stop()
            self._notify_deck_update(cued_deck.name, None)
            self.next_track_cued = False

        live_deck = self.get_live_deck()

        def after_fade():
            self.break_fading = False
            self.is_paused_for_sequence = True
            live_deck.pause()
            if on_complete:
                on_complete()

        if seconds:
            steps = 30
            live_deck.fader.fade_to(0.0, on_complete=after_fade, steps=steps, interval_ms=int(seconds * 1000 / steps))
        else:
            live_deck.fader.fade_to(0.0, on_complete=after_fade, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS)

    def resume_after_sequence(self):
        self.is_paused_for_sequence = False
        if self.is_running and not self.automation_on:
            self.is_running = False
            self.on_status("The break is over. Automation is off, so no music follows. Press A to start automation.")
            return
        if self.is_running:
            self.on_status("Rotation resuming, fading music back in.")
            live_deck = self.get_live_deck()
            try:
                # The break is over and its real length is known: fit the songs up to the next mark now.
                self.fit_before_mark(remaining_override=0.0)
            except Exception as e:
                _log_exception(type(e), e, e.__traceback__)
            next_track = self.pick_next_valid_track()
            if next_track is None:
                self.on_status(f"{self.pick_problem or 'Music library is empty'}. Rotation halted.")
                self.is_running = False
                return
            self.play_history.record_play(next_track)
            self.note_played(next_track)
            self.ending_beep_fired = False
            self.next_track_cued = False
            playback_path = normalize_file_loudness(next_track, self.on_status)
            live_deck.audio_output.setVolume(0.0)
            live_deck.load_and_play(playback_path, next_track)
            self._notify_deck_update(live_deck.name, next_track)
            self.on_now_playing(next_track)
            target = self._effective_level() * live_deck.manual_volume
            live_deck.fader.fade_to(target, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS)

    def duck_for_microphone(self):
        self.is_ducked = True
        self.on_status("Ducking music under live microphone.")
        live_deck = self.get_live_deck()
        live_deck.fader.fade_to(MIC_DUCKING_LEVEL * live_deck.manual_volume,
                                 steps=DUCK_FADE_STEPS, interval_ms=DUCK_FADE_INTERVAL_MS)

    def unduck_after_microphone(self):
        self.is_ducked = False
        self.on_status("Microphone off, bringing music back up.")
        live_deck = self.get_live_deck()
        live_deck.fader.fade_to(1.0 * live_deck.manual_volume,
                                 steps=DUCK_FADE_STEPS, interval_ms=DUCK_FADE_INTERVAL_MS)

    def set_muted(self, muted):
        """Silences (or restores) the speakers only. The stream mix keeps the full program."""
        self.is_muted = muted
        for deck in (self.deck_a, self.deck_b):
            deck.audio_output.set_muted(muted)

    def set_deck_volume(self, deck_name, level):
        deck = self.deck_a if deck_name == "A" else self.deck_b
        deck.set_manual_volume(level)
        if deck.name == self.live_deck_name:
            deck.audio_output.setVolume(self._effective_level() * deck.manual_volume)

    def play_pause_deck(self, deck_name):
        deck = self.deck_a if deck_name == "A" else self.deck_b
        if deck.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            deck.player.pause()
        else:
            deck.player.play()

    def cue_deck_to_start(self, deck_name):
        deck = self.deck_a if deck_name == "A" else self.deck_b
        deck.player.setPosition(0)

    def on_media_status_changed(self, status, deck):
        if status == QMediaPlayer.MediaStatus.EndOfMedia and deck.name == self.live_deck_name:
            if self.break_fading:
                return
            if not self.automation_on and not self.is_paused_for_sequence:
                self.is_running = False
                self.on_status("The song finished. Automation is off, so nothing plays next. Press A to start automation.")
                return
            if not self.is_paused_for_sequence and self.is_running:
                if (self.break_target is not None and not self.break_started
                        and (self.break_style() == "finish_song" or self._seconds_to_mark() <= self.QUICK_BREAK_FADE_SECONDS + 1)):
                    self._take_break()
                    return
                if not self.next_track_cued:
                    self.cue_next_track_if_needed()
                self.crossfade_to_cued_deck()
        elif status == QMediaPlayer.MediaStatus.InvalidMedia and deck.name == self.live_deck_name:
            # A file the player can't read: skip it instead of going silent.
            if self.is_running and self.automation_on and not self.is_paused_for_sequence:
                self.on_status("Skipped an unreadable audio file.")
                if not self.next_track_cued:
                    self.cue_next_track_if_needed()
                self.crossfade_to_cued_deck()



# ---------------------------------------------------------------------------
# PCM helpers and the live program mixer (what the encoders actually stream)
# ---------------------------------------------------------------------------

def audio_buffer_bytes(buf):
    """Raw bytes of a QAudioBuffer."""
    size = buf.byteCount()
    pointer = buf.constData()
    try:
        return pointer.asstring(size)
    except Exception:
        return bytes(pointer)[:size]


def pcm_to_stereo_float(raw, sample_rate, channels, sample_format):
    """Converts raw PCM of any common format to float32 stereo at STREAM_SAMPLE_RATE (needs numpy)."""
    if not NUMPY_AVAILABLE or not raw or channels < 1:
        return None
    sf = QAudioFormat.SampleFormat
    if sample_format == sf.Int16:
        data = np.frombuffer(raw[: len(raw) // 2 * 2], dtype="<i2").astype(np.float32) / 32768.0
    elif sample_format == sf.Float:
        data = np.frombuffer(raw[: len(raw) // 4 * 4], dtype="<f4").astype(np.float32)
    elif sample_format == sf.Int32:
        data = np.frombuffer(raw[: len(raw) // 4 * 4], dtype="<i4").astype(np.float32) / 2147483648.0
    elif sample_format == sf.UInt8:
        data = (np.frombuffer(raw, dtype=np.uint8).astype(np.float32) - 128.0) / 128.0
    else:
        return None
    usable = (len(data) // channels) * channels
    if usable == 0:
        return None
    data = data[:usable].reshape(-1, channels)
    if channels == 1:
        data = np.repeat(data, 2, axis=1)
    elif channels > 2:
        data = data[:, :2]
    if sample_rate and sample_rate != STREAM_SAMPLE_RATE and len(data) > 1:
        new_length = max(1, int(round(len(data) * STREAM_SAMPLE_RATE / float(sample_rate))))
        old_positions = np.arange(len(data))
        new_positions = np.linspace(0, len(data) - 1, new_length)
        data = np.stack(
            [np.interp(new_positions, old_positions, data[:, 0]),
             np.interp(new_positions, old_positions, data[:, 1])], axis=1
        ).astype(np.float32)
    return np.ascontiguousarray(data, dtype=np.float32)


class _MixSource:
    def __init__(self, name, gain_fn):
        self.name = name
        self.gain_fn = gain_fn
        self.chunks = deque()
        self.frames = 0
        self.lock = threading.Lock()
        self.last_gain = 0.0
        self.peak = 0.0
        self.peak_time = 0.0


class ProgramMixer:
    """
    Sums everything that goes on air (Deck A, Deck B, the jingle/ad player and
    the microphone) into one stereo stream, 44.1 kHz, and hands it to every
    running encoder. Each source's gain follows its real volume, so fades,
    ducking and mute all affect the stream exactly as they affect the speakers.
    The mixer only runs while at least one encoder is streaming.
    """

    def __init__(self, on_status):
        self.on_status = on_status
        self.available = NUMPY_AVAILABLE and BUFFER_OUTPUT_AVAILABLE
        self.sources = {}
        self.encoders = []
        self._outputs = []
        self.timer = QTimer()
        self.timer.setInterval(MIX_INTERVAL_MS)
        try:
            self.timer.setTimerType(Qt.TimerType.PreciseTimer)
        except Exception:
            pass
        self.timer.timeout.connect(self._tick)
        self.last_time = None
        self.frame_remainder = 0.0
        # OctiMax-style processing of the stream feed (not the local speakers)
        self.master_processor = None
        self.source_processors = {}
        self.source_processing = {}   # source name -> bool
        self.processor_preset = "Broadcast"
        self.processor_ceiling_db = -1.0
        if NUMPY_AVAILABLE:
            try:
                self.master_processor = StreamProcessor(STREAM_SAMPLE_RATE)
            except Exception:
                self.master_processor = None

    def configure_processing(self, master_on, preset, ceiling_db, per_source):
        """per_source: dict of source name -> bool. Safe to call at any time."""
        self.processor_preset = preset
        self.processor_ceiling_db = ceiling_db
        self.source_processing = dict(per_source)
        if self.master_processor is not None:
            self.master_processor.enabled = bool(master_on)
            self.master_processor.set_preset(preset)
            self.master_processor.set_ceiling_db(ceiling_db)
        for name, proc in self.source_processors.items():
            proc.set_preset(preset)
            proc.set_ceiling_db(ceiling_db)

    def _source_processor(self, name):
        if not self.source_processing.get(name) or not NUMPY_AVAILABLE:
            return None
        proc = self.source_processors.get(name)
        if proc is None:
            proc = StreamProcessor(STREAM_SAMPLE_RATE, self.processor_preset, self.processor_ceiling_db)
            self.source_processors[name] = proc
        return proc

    def unavailable_reason(self):
        if not NUMPY_AVAILABLE:
            return "numpy is not installed"
        if not BUFFER_OUTPUT_AVAILABLE:
            return "this PyQt6 version is older than 6.8"
        return "it was turned off or could not be set up"

    def add_source(self, name, gain_fn):
        if name not in self.sources:
            self.sources[name] = _MixSource(name, gain_fn)

    def attach_player(self, name, player, gain_fn):
        """Taps a QMediaPlayer's decoded audio so it can be mixed for the stream."""
        if not self.available:
            return False
        self.add_source(name, gain_fn)
        try:
            fmt = QAudioFormat()
            fmt.setSampleRate(STREAM_SAMPLE_RATE)
            fmt.setChannelCount(STREAM_CHANNELS)
            fmt.setSampleFormat(QAudioFormat.SampleFormat.Int16)
            try:
                output = QAudioBufferOutput(fmt)
            except TypeError:
                output = QAudioBufferOutput()
            output.audioBufferReceived.connect(lambda buf, n=name: self._on_buffer(n, buf))
            player.setAudioBufferOutput(output)
            self._outputs.append(output)
            return True
        except Exception as e:
            self.available = False
            self.on_status(f"Live stream mix could not be set up: {e}")
            return False

    def _on_buffer(self, name, buf):
        if not self.timer.isActive():
            return
        try:
            fmt = buf.format()
            raw = audio_buffer_bytes(buf)
            self.push_raw(name, raw, fmt.sampleRate(), fmt.channelCount(), fmt.sampleFormat())
        except Exception:
            pass

    def push_raw(self, name, raw, sample_rate, channels, sample_format):
        if not self.timer.isActive():
            return
        source = self.sources.get(name)
        if source is None:
            return
        data = pcm_to_stereo_float(raw, sample_rate, channels, sample_format)
        if data is None or len(data) == 0:
            return
        try:
            source.peak = float(np.max(np.abs(data)))
            source.peak_time = time.time()
        except Exception:
            pass
        with source.lock:
            source.chunks.append(data)
            source.frames += len(data)
            limit = STREAM_SAMPLE_RATE * MAX_SOURCE_BUFFER_SECONDS
            while source.frames > limit and source.chunks:
                dropped = source.chunks.popleft()
                source.frames -= len(dropped)

    def recent_peak(self, name):
        """Loudest sample from this source in the last fraction of a second, 0 to 1 (0 when idle)."""
        source = self.sources.get(name)
        if source is None or time.time() - source.peak_time > 0.25:
            return 0.0
        return min(1.0, source.peak)

    def register_encoder(self, encoder):
        if encoder not in self.encoders:
            self.encoders.append(encoder)
        if not self.timer.isActive():
            for source in self.sources.values():
                with source.lock:
                    source.chunks.clear()
                    source.frames = 0
            self.last_time = None
            self.frame_remainder = 0.0
            if self.master_processor is not None:
                self.master_processor.reset()
            for proc in self.source_processors.values():
                proc.reset()
            self.timer.start()

    def unregister_encoder(self, encoder):
        if encoder in self.encoders:
            self.encoders.remove(encoder)
        if not self.encoders:
            self.timer.stop()

    def _pull(self, source, count):
        with source.lock:
            if source.frames == 0:
                return None
            parts = []
            need = count
            while need > 0 and source.chunks:
                chunk = source.chunks[0]
                if len(chunk) <= need:
                    parts.append(chunk)
                    need -= len(chunk)
                    source.chunks.popleft()
                else:
                    parts.append(chunk[:need])
                    source.chunks[0] = chunk[need:]
                    need = 0
            source.frames -= (count - need)
        out = np.concatenate(parts) if len(parts) > 1 else parts[0]
        if len(out) < count:
            out = np.concatenate([out, np.zeros((count - len(out), 2), dtype=np.float32)])
        return out

    def _tick(self):
        try:
            now = time.monotonic()
            if self.last_time is None:
                self.last_time = now
                return
            elapsed = min(now - self.last_time, 0.25)
            self.last_time = now
            exact = elapsed * STREAM_SAMPLE_RATE + self.frame_remainder
            count = int(exact)
            self.frame_remainder = exact - count
            if count <= 0:
                return
            mix = np.zeros((count, 2), dtype=np.float32)
            for source in self.sources.values():
                chunk = self._pull(source, count)
                try:
                    gain = float(source.gain_fn())
                except Exception:
                    gain = 0.0
                if chunk is not None:
                    proc = self._source_processor(source.name)
                    if proc is not None:
                        chunk = proc.process(chunk)
                    ramp = np.linspace(source.last_gain, gain, count, dtype=np.float32)[:, None]
                    mix += chunk * ramp
                source.last_gain = gain
            if self.master_processor is not None and self.master_processor.enabled:
                mix = self.master_processor.process(mix)
            np.clip(mix, -1.0, 1.0, out=mix)
            data = (mix * 32767.0).astype("<i2").tobytes()
            for encoder in list(self.encoders):
                encoder.feed(data)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)


# ---------------------------------------------------------------------------
# Microphone engine: live monitoring on the host output + feed to the stream
# ---------------------------------------------------------------------------

class MicrophoneEngine:
    """
    Opens the selected microphone, plays it live through the selected output
    (so you can hear it) and passes the same audio to the stream mix. Failures
    are reported with a reason; if the microphone opens but no audio arrives
    (often Windows microphone privacy settings) it says so.
    """

    def __init__(self, settings, on_status, on_mic_started, on_mic_stopped,
                 on_mic_failed=None, on_audio_chunk=None, on_signal_changed=None):
        self.settings = settings
        self.on_status = on_status
        self.on_mic_started = on_mic_started
        self.on_mic_stopped = on_mic_stopped
        self.on_mic_failed = on_mic_failed
        self.on_audio_chunk = on_audio_chunk
        self.on_signal_changed = on_signal_changed

        self.source = None
        self.sink = None
        self.source_io = None
        self.sink_io = None
        self.format = None
        self.is_live = False
        self.is_muted = False
        self.monitor_enabled = True
        self.bytes_received = 0
        self.peak = 0
        self.ticks_live = 0
        self.has_signal = None

        self.watch_timer = QTimer()
        self.watch_timer.setInterval(1000)
        self.watch_timer.timeout.connect(self._watch)

    def _fail(self, reason):
        self._teardown()
        self.on_status(reason)
        if self.on_mic_failed:
            self.on_mic_failed(reason)

    def _make_format(self):
        fmt = QAudioFormat()
        fmt.setSampleRate(STREAM_SAMPLE_RATE)
        fmt.setChannelCount(STREAM_CHANNELS)
        fmt.setSampleFormat(QAudioFormat.SampleFormat.Int16)
        return fmt

    def start(self):
        if self.is_live:
            return
        in_device = get_selected_input_device(self.settings)
        if in_device is None or in_device.isNull():
            self._fail("No microphone was found. On Windows, open Settings, Privacy and security, "
                       "Microphone, and make sure desktop apps are allowed to use the microphone.")
            return

        fmt = self._make_format()
        if not in_device.isFormatSupported(fmt):
            fmt = in_device.preferredFormat()
        self.format = fmt

        try:
            self.source = QAudioSource(in_device, fmt)
            self.source_io = self.source.start()
        except Exception as e:
            self._fail(f"The microphone could not be opened: {e}")
            return
        if self.source_io is None or self.source.error() != QAudio.Error.NoError:
            self._fail(f"The microphone '{in_device.description()}' could not be opened. "
                       "Check that no other program is using it and that Windows allows desktop apps to use it.")
            return

        out_device = get_selected_output_device(self.settings)
        if out_device is not None and out_device.isFormatSupported(fmt):
            try:
                self.sink = QAudioSink(out_device, fmt)
                self.sink_io = self.sink.start()
            except Exception:
                self.sink = None
                self.sink_io = None
        else:
            self.on_status("Microphone monitoring is off: the output device does not support the microphone format.")

        self.bytes_received = 0
        self.peak = 0
        self.ticks_live = 0
        self.has_signal = None
        self.source_io.readyRead.connect(self._on_ready_read)
        self.is_live = True
        self.watch_timer.start()
        self.on_status(f"Microphone is live: {in_device.description()}")
        self.on_mic_started()

    def _on_ready_read(self):
        if self.source_io is None:
            return
        data = bytes(self.source_io.readAll())
        if not data:
            return
        self.bytes_received += len(data)
        if self.format is not None and self.format.sampleFormat() == QAudioFormat.SampleFormat.Int16:
            samples = array("h")
            samples.frombytes(data[: len(data) // 2 * 2])
            if len(samples):
                level = max(max(samples), -min(samples))
                if level > self.peak:
                    self.peak = level
        if not self.is_muted and self.monitor_enabled and self.sink_io is not None and self.sink is not None:
            if self.sink.bytesFree() >= len(data):          # muted: nothing on the speakers, the stream still gets it
                self.sink_io.write(data)
        if self.on_audio_chunk and self.format is not None:
            self.on_audio_chunk(data, self.format)

    def _watch(self):
        if not self.is_live:
            return
        self.ticks_live += 1
        if self.bytes_received == 0:
            if self.ticks_live == 3:
                self.on_status("The microphone is open but no audio is arriving. Check the Windows "
                               "microphone privacy setting and that the microphone is not muted.")
            signal = False
        else:
            signal = self.peak > 300  # about -40 dB
        self.peak = 0
        if signal != self.has_signal:
            self.has_signal = signal
            if self.on_signal_changed:
                self.on_signal_changed(signal)

    def set_muted(self, muted):
        self.is_muted = muted

    def _teardown(self):
        self.watch_timer.stop()
        try:
            if self.source is not None:
                self.source.stop()
        except Exception:
            pass
        try:
            if self.sink is not None:
                self.sink.stop()
        except Exception:
            pass
        self.source = None
        self.sink = None
        self.source_io = None
        self.sink_io = None
        self.is_live = False

    def stop(self):
        if not self.is_live:
            return
        self._teardown()
        self.on_status("Microphone stopped.")
        self.on_mic_stopped()


# ---------------------------------------------------------------------------
# Scheduler (quarter-hour marks, crossfade lead-in)
# ---------------------------------------------------------------------------

class SchedulerEngine:
    """
    Watches the clock and fires on_crossfade_start at the :00, :15, :30 and :45
    marks. Each mark fires exactly once: the last fired minute is remembered
    directly (no growing set that can be cleared at the wrong moment), a tick
    that lands a second late still fires, and starting the app in the middle of
    a marked minute does not fire a break.
    """

    def __init__(self, settings, on_crossfade_start, on_status):
        self.settings = settings
        self.on_crossfade_start = on_crossfade_start
        self.on_status = on_status
        now = datetime.now()
        self.last_fired_key = (now.year, now.month, now.day, now.hour, now.minute)
        self.on_break_upcoming = None   # on_break_upcoming(slot, target_datetime), about 2 minutes ahead
        self.armed_target = None

        self.timer = QTimer()
        self.timer.timeout.connect(self.check_schedule)
        self.timer.start(500)

    @staticmethod
    def next_mark(now):
        minute = ((now.minute // 15) + 1) * 15
        base = now.replace(second=0, microsecond=0)
        if minute >= 60:
            return base.replace(minute=0) + timedelta(hours=1)
        return base.replace(minute=minute)

    def check_schedule(self):
        now = datetime.now()
        if self.on_break_upcoming is not None:
            target = self.next_mark(now)
            if self.armed_target != target and (target - now).total_seconds() <= break_window_seconds(self.settings):
                self.armed_target = target
                slot = {0: ":00", 15: ":15", 30: ":30", 45: ":45"}[target.minute]
                try:
                    self.on_break_upcoming(slot, target)
                except Exception as e:
                    _log_exception(type(e), e, e.__traceback__)
        slot = {0: ":00", 15: ":15", 30: ":30", 45: ":45"}.get(now.minute)
        if slot is None or now.second >= 10:
            return
        key = (now.year, now.month, now.day, now.hour, now.minute)
        if key == self.last_fired_key:
            return
        self.last_fired_key = key
        self.on_status(f"Scheduled {slot} break triggered.")
        self.on_crossfade_start(slot)


# ---------------------------------------------------------------------------
# Sequence player (jingle / ad-break chains for scheduled breaks)
# ---------------------------------------------------------------------------

class SequencePlayer:
    def __init__(self, settings, on_status, on_sequence_done, output_device=None):
        self.settings = settings
        self.on_status = on_status
        self.on_sequence_done = on_sequence_done

        self.player = QMediaPlayer()
        self.audio_output = SplitOutput(output_device)
        self.player.setAudioOutput(self.audio_output.real)
        self.player.mediaStatusChanged.connect(self.on_media_status_changed)
        self.player.positionChanged.connect(self.on_position_changed)
        self.is_muted = False
        self.audio_output.setVolume(1.0)
        self.on_item_ending = None    # on_item_ending(): a warning beep shortly before a break item ends
        self.item_beep_fired = False

        self.queue = []
        self.category_library = None  # set by the app: imported categories feed the sandwich
        self.items = []               # the break in order, kept so the screen can show what is pulling
        self.item_index = -1
        self.active = False
        self.slot = ""
        self.on_changed = None        # on_changed(): the queue list and tree redraw
        self.event_provider = None    # callable returning the running dated schedule (or None)
        self.deck_names = ("C", "D")  # the break items alternate between these two decks on screen
        self.gap_timer = QTimer()
        self.gap_timer.setSingleShot(True)
        self.gap_timer.timeout.connect(self.play_next_in_queue)

    def gap_ms(self):
        try:
            return max(0, min(3000, int(float(self.settings.value("break_item_gap_ms", 250)))))
        except Exception:
            return 250

    def current_deck_name(self):
        """C or D: the deck the item now playing is on (items alternate)."""
        if not self.active or self.item_index < 0 or self.item_index >= len(self.items):
            return None
        return self.deck_names[self.item_index % 2]

    def stop_break(self):
        """The break decks' Stop button: ends the break and hands the music back."""
        if not self.active:
            return False
        self.gap_timer.stop()
        self.queue = []
        self.player.stop()
        self.active = False
        self.item_index = len(self.items)
        self._changed()
        self.on_status("Break stopped. The music comes back.")
        self.on_sequence_done()
        return True

    def toggle_pause(self):
        if not self.active:
            return False
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
        else:
            self.player.play()
        self._changed()
        return True

    def _changed(self):
        if self.on_changed:
            try:
                self.on_changed()
            except Exception:
                pass

    def apply_output_device(self, device):
        if device is not None:
            self.audio_output.setDevice(device)

    def set_muted(self, muted):
        self.is_muted = muted                # speakers only: the stream still carries jingles and ads
        self.audio_output.set_muted(muted)

    def build_queue(self, sequence, jingle_folder):
        """
        'sandwich' = jingle, ad, jingle. If no ad audio is set up, only one jingle
        plays (never two jingles back to back), and the second jingle is always a
        different file from the first when more than one exists.
        """
        self.queue = []
        jingles = scan_audio_files(jingle_folder)
        ads_from_categories = []
        if self.category_library is not None and self.category_library.categories:
            # Categories you switched on feed the break: jingles and sweepers around the ad.
            jingles = list(dict.fromkeys(
                jingles + self.category_library.files_for_types(("jingle", "sweeper"))))
            ads_from_categories = self.category_library.files_for_types(("ad",))
        event = None
        try:
            event = self.event_provider() if self.event_provider else None
        except Exception:
            event = None
        override_ads = None
        if event is not None and self.category_library is not None:
            # A running dated schedule (holiday programming) uses its own jingles, and its own ads if it has them.
            own_jingles = self.category_library.files_for_category(event.get("jingle_category_id"))
            if own_jingles:
                jingles = own_jingles
                self.on_status(f"Using the jingles of the {event.get('name', 'dated')} schedule.")
            if event.get("ad_category_id"):
                own_ads = self.category_library.files_for_category(event["ad_category_id"])
                if own_ads:
                    override_ads = own_ads
        if sequence == "simple":
            if jingles:
                self.queue.append(random.choice(jingles))
            return

        ads = list(dict.fromkeys(scan_audio_files(self.settings.value("ad_break_folder", ""))
                                 + ads_from_categories))
        if override_ads:
            ads = override_ads
        if ads and jingles:
            first = random.choice(jingles)
            others = [j for j in jingles if j != first]
            second = random.choice(others) if others else first
            self.queue = [first, random.choice(ads), second]
        elif ads:
            self.queue = [random.choice(ads)]
        elif jingles:
            self.queue = [random.choice(jingles)]
            self.on_status("No ad break audio found, so only one jingle will play.")

    def play_sequence(self, slot, sequence, jingle_folder):
        self.build_queue(sequence, jingle_folder)
        if not self.queue:
            self.on_status(f"No playable audio found for {slot} sequence.")
            self.active = False
            self.on_sequence_done()
            return
        self.items = list(self.queue)
        self.item_index = -1
        self.active = True
        self.slot = slot
        self.on_status(f"Starting {slot} sequence, {len(self.queue)} item(s) queued.")
        for i, item in enumerate(self.items, 1):
            self.on_status(f"{slot} break item {i} of {len(self.items)}: {item}")
        self._changed()
        self.play_next_in_queue()

    def play_next_in_queue(self):
        if not self.queue:
            self.on_status("Sequence finished.")
            self.active = False
            self.item_index = len(self.items)
            self._changed()
            self.on_sequence_done()
            return
        next_file = self.queue.pop(0)
        self.item_index += 1
        self.on_status(f"Playing {self.item_index + 1} of {len(self.items)}: {next_file}")
        RUN_LOG.write("BREAK", f"{self.slot} item {self.item_index + 1} of {len(self.items)}: {next_file}")
        self._changed()
        self.item_beep_fired = False
        playback_path = normalize_file_loudness(next_file, self.on_status)
        self.player.setSource(QUrl.fromLocalFile(playback_path))
        self.player.play()

    ITEM_BEEP_LEAD_MS = 2000
    ITEM_BEEP_MIN_MS = 3000

    def on_position_changed(self, position_ms):
        """One warning beep, 2 seconds before a jingle, ad or sweeper ends and another item follows it."""
        if self.item_beep_fired or not self.active or not self.queue or self.on_item_ending is None:
            return
        try:
            duration = self.player.duration()
        except Exception:
            return
        if duration >= self.ITEM_BEEP_MIN_MS and 0 < duration - position_ms <= self.ITEM_BEEP_LEAD_MS:
            self.item_beep_fired = True
            try:
                self.on_item_ending()
            except Exception:
                pass

    def on_media_status_changed(self, status):
        if status == QMediaPlayer.MediaStatus.EndOfMedia:
            self._next_after_gap()
        elif status == QMediaPlayer.MediaStatus.InvalidMedia:
            self.on_status("Skipped an unreadable jingle or ad file.")
            self.play_next_in_queue()

    def _next_after_gap(self):
        """A short silence between break items, so a jingle or an ad is never clipped by the next one."""
        gap = self.gap_ms()
        if gap > 0 and self.queue:
            self.gap_timer.start(gap)
        else:
            self.play_next_in_queue()


# ---------------------------------------------------------------------------
# Voice tracking: records the microphone to a WAV file (separate from the on-air microphone)
# ---------------------------------------------------------------------------

class VoiceRecorder:
    MAX_SECONDS = 300

    def __init__(self, settings, on_status):
        self.settings = settings
        self.on_status = on_status
        self.source = None
        self.io = None
        self.wav = None
        self.path = None
        self.format = None
        self.bytes_written = 0

    def start(self, path):
        in_device = get_selected_input_device(self.settings)
        if in_device is None or in_device.isNull():
            self.on_status("No microphone was found, so a voice track cannot be recorded.")
            return False
        fmt = QAudioFormat()
        fmt.setSampleRate(STREAM_SAMPLE_RATE)
        fmt.setChannelCount(STREAM_CHANNELS)
        fmt.setSampleFormat(QAudioFormat.SampleFormat.Int16)
        if not in_device.isFormatSupported(fmt):
            fmt = in_device.preferredFormat()
        if fmt.sampleFormat() not in (QAudioFormat.SampleFormat.Int16, QAudioFormat.SampleFormat.Float):
            self.on_status("This microphone uses a sound format Vision Studio cannot record yet.")
            return False
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            self.wav = wave.open(path, "wb")
            self.wav.setnchannels(fmt.channelCount())
            self.wav.setsampwidth(2)
            self.wav.setframerate(fmt.sampleRate())
            self.source = QAudioSource(in_device, fmt)
            self.io = self.source.start()
        except Exception as e:
            self._close_file()
            self.on_status(f"The voice track could not be started: {e}")
            return False
        if self.io is None:
            self._close_file()
            self.on_status("The microphone could not be opened for the voice track.")
            return False
        self.format = fmt
        self.path = path
        self.bytes_written = 0
        self.io.readyRead.connect(self._read)
        return True

    def _read(self):
        if self.io is None or self.wav is None:
            return
        data = bytes(self.io.readAll())
        if not data:
            return
        if self.format.sampleFormat() == QAudioFormat.SampleFormat.Float:
            samples = np.frombuffer(data[: len(data) // 4 * 4], dtype=np.float32)
            data = (np.clip(samples, -1.0, 1.0) * 32767.0).astype(np.int16).tobytes()
        self.wav.writeframes(data)
        self.bytes_written += len(data)

    def seconds(self):
        if self.format is None:
            return 0.0
        return self.bytes_written / float(max(1, self.format.sampleRate() * self.format.channelCount() * 2))

    def _close_file(self):
        try:
            if self.wav is not None:
                self.wav.close()
        except Exception:
            pass
        self.wav = None

    def stop(self):
        """Finishes the file and returns how many seconds were recorded."""
        try:
            self._read()
            if self.source is not None:
                self.source.stop()
        except Exception:
            pass
        self.source = None
        self.io = None
        seconds = self.seconds()
        self._close_file()
        return seconds

    def cancel(self):
        self.stop()
        try:
            if self.path and os.path.exists(self.path):
                os.remove(self.path)
        except OSError:
            pass



# ---------------------------------------------------------------------------
# Encoder bank (up to 24 simulcast destinations, FFmpeg-backed, bundled)
# ---------------------------------------------------------------------------

class EncoderSlot(QObject):
    """
    One simulcast destination. It streams the live program mix to an Icecast
    server through ffmpeg, reports connecting / live / offline, and pushes the
    artist, title and album of whatever is playing to the server.
    """
    state_changed = pyqtSignal(object, str, str)  # (slot, "offline"|"connecting"|"live", reason)
    message = pyqtSignal(str)

    def __init__(self, slot_number):
        super().__init__()
        self.slot_number = slot_number
        self.stream_name = f"Encoder {slot_number}"
        self.protocol = "Icecast"
        self.server_host = ""
        self.server_port = ""
        self.mount_point = ""
        self.username = "source"
        self.server_password = ""
        self.source_password = ""
        self.audio_format = "MP3"
        self.bitrate_kbps = "128"

        self.state = "offline"
        self.process = None
        self.feed_queue = None
        self.mixer = None
        self.stderr_tail = deque(maxlen=8)
        self.connect_started = 0.0
        self.current_metadata = None
        self.user_stopped = False
        self.keep_connected = "true"
        self.reconnect_seconds = "10"
        self.reconnect_on_start = "false"     # connect again when the program starts, if it was live when it closed
        self.was_live = "false"               # set by Start Streaming, cleared by Stop Streaming; a restart leaves it
        self.boot_retry_until = 0.0
        self.mixer_ref = None
        self.fallback_getter = None
        self.last_write = 0.0
        self.bytes_sent = 0
        self.minute_bytes = 0
        self.minute_mark = 0.0
        self.live_since = 0.0
        self.fail_count = 0
        self.retry_pending = False
        self.quiet_retry = False
        self.server_missing = 0
        self.server_check_busy = False
        self.last_server_check = 0.0
        self.retry_timer = QTimer()
        self.retry_timer.setSingleShot(True)
        self.retry_timer.timeout.connect(self._retry_now)

        self.poll_timer = QTimer()
        self.poll_timer.setInterval(1000)
        self.poll_timer.timeout.connect(self._poll)

    # --- persistence ---
    FIELDS = ("stream_name", "protocol", "server_host", "server_port", "mount_point",
              "username", "server_password", "source_password", "audio_format", "bitrate_kbps",
              "keep_connected", "reconnect_seconds", "reconnect_on_start", "was_live")

    def to_dict(self):
        return {name: getattr(self, name) for name in self.FIELDS}

    def load_dict(self, data):
        for name in self.FIELDS:
            if name in data:
                setattr(self, name, str(data[name]))

    def summary_text(self):
        host = self.server_host or "no server set"
        port = f":{self.server_port}" if self.server_port else ""
        return f"{self.stream_name}: {self.protocol} {host}{port}{self.mount_point}, {self.audio_format} {self.bitrate_kbps} kbps"

    # --- state ---
    def set_state(self, state, reason=""):
        if state == self.state and not reason:
            return
        self.state = state
        self.state_changed.emit(self, state, reason)

    def validate(self):
        if not self.server_host.strip():
            return "no server host is set"
        if not self.server_port.strip().isdigit():
            return "the server port is missing or not a number"
        if not self.source_password:
            return "no source password is set"
        return ""

    def build_ffmpeg_command(self, use_pipe, file_source):
        is_mp3 = self.audio_format == "MP3"
        codec = "libmp3lame" if is_mp3 else "aac"
        container = "mp3" if is_mp3 else "adts"
        content_type = "audio/mpeg" if is_mp3 else "audio/aac"
        mount = self.mount_point.strip()
        if not mount.startswith("/"):
            mount = "/" + mount
        password = urllib.parse.quote(self.source_password, safe="")
        user = urllib.parse.quote((self.username or "source").strip() or "source", safe="")
        url = f"icecast://{user}:{password}@{self.server_host.strip()}:{self.server_port.strip()}{mount}"

        cmd = [get_ffmpeg_path(), "-hide_banner", "-loglevel", "warning"]
        if use_pipe:
            cmd += ["-f", "s16le", "-ar", str(STREAM_SAMPLE_RATE), "-ac", str(STREAM_CHANNELS), "-i", "pipe:0"]
        else:
            cmd += ["-re", "-i", file_source]
        cmd += ["-vn", "-acodec", codec, "-b:a", f"{self.bitrate_kbps}k",
                "-ar", str(STREAM_SAMPLE_RATE), "-ac", str(STREAM_CHANNELS)]
        if self.current_metadata:
            cmd += ["-metadata", f"title={self.current_metadata.get('title', '')}",
                    "-metadata", f"artist={self.current_metadata.get('artist', '')}",
                    "-metadata", f"album={self.current_metadata.get('album', '')}"]
        cmd += ["-ice_name", self.stream_name, "-content_type", content_type, "-f", container, url]
        return cmd

    def keep_connected_on(self):
        return str(self.keep_connected).lower() == "true"

    def reconnect_delay(self):
        try:
            wanted = max(0, int(float(self.reconnect_seconds)))
        except Exception:
            wanted = 10
        if self.fail_count >= 10:
            wanted = max(wanted, 30)
        elif self.fail_count >= 2:
            wanted = max(wanted, 1)
        return wanted

    def start(self, mixer, fallback_source):
        """Returns True when ffmpeg was launched."""
        self.retry_timer.stop()
        if self.state != "offline":
            return False
        problem = self.validate()
        if problem:
            self.retry_pending = False
            self.message.emit(f"{self.stream_name} cannot start: {problem}.")
            return False
        use_pipe = mixer is not None and mixer.available
        if not use_pipe and not fallback_source:
            self.message.emit(f"{self.stream_name} cannot start: nothing is playing yet, and the live mix is "
                              f"unavailable ({mixer.unavailable_reason() if mixer else 'no mixer'}).")
            return False
        try:
            self.process = subprocess.Popen(
                self.build_ffmpeg_command(use_pipe, fallback_source),
                stdin=subprocess.PIPE if use_pipe else subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                creationflags=SUBPROCESS_FLAGS)
        except FileNotFoundError:
            self.message.emit(f"{self.stream_name} cannot start: ffmpeg was not found.")
            return False
        except Exception as e:
            self.message.emit(f"{self.stream_name} cannot start: {e}")
            return False

        self.mixer_ref = mixer
        now = time.monotonic()
        self.last_write = now
        self.minute_bytes = 0
        self.minute_mark = now
        self.live_since = 0.0
        self.server_missing = 0
        self.last_server_check = now
        self.user_stopped = False
        self.stderr_tail.clear()
        self.connect_started = time.monotonic()
        threading.Thread(target=self._drain_stderr, args=(self.process,), daemon=True).start()
        if use_pipe:
            self.feed_queue = queue.Queue(maxsize=100)
            threading.Thread(target=self._writer_loop, args=(self.process, self.feed_queue), daemon=True).start()
            self.mixer = mixer
            mixer.register_encoder(self)
        if not use_pipe:
            self.message.emit(f"{self.stream_name}: live mix unavailable, streaming only the current track file.")
        self.set_state("connecting")
        self.poll_timer.start()
        RUN_LOG.write("ENCODER", f"{self.stream_name}: connecting to {self.server_host}:{self.server_port}{self.mount_point}.")
        return True

    def _drain_stderr(self, proc):
        try:
            for line in iter(proc.stderr.readline, b""):
                text = line.decode("utf-8", "replace").strip()
                if text:
                    self.stderr_tail.append(text)
        except Exception:
            pass

    def _writer_loop(self, proc, feed_queue):
        try:
            while True:
                data = feed_queue.get()
                if data is None:
                    break
                proc.stdin.write(data)
                proc.stdin.flush()
                self.bytes_sent += len(data)
                self.minute_bytes += len(data)
                self.last_write = time.monotonic()
        except Exception:
            pass
        try:
            proc.stdin.close()
        except Exception:
            pass

    def feed(self, data):
        """Called by the mixer with 20 ms of program audio."""
        if self.feed_queue is None:
            return
        try:
            self.feed_queue.put_nowait(data)
        except queue.Full:
            pass

    AUTH_WORDS = ("401", "403", "unauthorized", "authentication", "forbidden", "not authorized")

    def _poll(self):
        if self.process is None:
            self.poll_timer.stop()
            return
        now = time.monotonic()
        code = self.process.poll()
        if code is not None:
            reason = " ".join(list(self.stderr_tail)[-2:]) or f"ffmpeg stopped (exit code {code})"
            self.handle_drop(reason)
            return
        if self.state == "connecting" and now - self.connect_started >= CONNECT_CONFIRM_SECONDS:
            self.live_since = now
            self.last_write = now
            self.fail_count = 0
            was_retry = self.quiet_retry
            self.quiet_retry = False
            self.retry_pending = False
            self.set_state("live")
            RUN_LOG.write("ENCODER", f"{self.stream_name}: LIVE" + (" (reconnected)." if was_retry else "."))
            if self.current_metadata:
                self.push_metadata(self.current_metadata)
            return
        if self.state != "live":
            return
        # Stall: ffmpeg is running but no audio has gone out for 10 seconds.
        if now - self.last_write > STALL_SECONDS:
            self.handle_drop(f"no audio was sent for {int(now - self.last_write)} seconds, the connection stalled")
            return
        # One line in the log each minute so a quiet failure can be traced afterwards.
        if now - self.minute_mark >= 60:
            tail = list(self.stderr_tail)[-1:] or ["none"]
            RUN_LOG.write("ENCODER", f"{self.stream_name}: live, {self.minute_bytes // 1024} KB sent in the last minute. "
                                    f"Last ffmpeg message: {tail[0]}")
            self.minute_bytes = 0
            self.minute_mark = now
        # Ask the server whether it still lists the mount (Icecast only).
        if (self.protocol == "Icecast" and not self.server_check_busy
                and now - self.last_server_check >= SERVER_CHECK_SECONDS and now - self.live_since >= 15):
            self.last_server_check = now
            self.server_check_busy = True
            threading.Thread(target=self._server_check, daemon=True).start()
        if self.server_missing >= 2:
            self.server_missing = 0
            self.handle_drop("the server no longer lists this mount point")

    def _server_check(self):
        """Reads the Icecast status page. A failed lookup is ignored; only a clear answer without our mount counts."""
        try:
            host = self.server_host.strip()
            port = self.server_port.strip()
            mount = self.mount_point.strip()
            if not mount.startswith("/"):
                mount = "/" + mount
            request = urllib.request.Request(f"http://{host}:{port}/status-json.xsl")
            request.add_header("User-Agent", "VisionStudio")
            data = json.loads(urllib.request.urlopen(request, timeout=6).read().decode("utf-8", "replace"))
            sources = data.get("icestats", {}).get("source", [])
            if isinstance(sources, dict):
                sources = [sources]
            found = any(str(src.get("listenurl", "")).rstrip("/").endswith(mount.rstrip("/")) for src in sources)
            self.server_missing = 0 if found else self.server_missing + 1
        except Exception:
            pass
        finally:
            self.server_check_busy = False

    def handle_drop(self, reason):
        """The stream ended without the user asking: tear down, announce it once, and reconnect if asked to."""
        was = self.state
        self._teardown()
        self.fail_count += 1
        RUN_LOG.write("ENCODER", f"{self.stream_name}: dropped ({reason}).")
        auth = any(word in reason.lower() for word in self.AUTH_WORDS)
        starting_up = time.monotonic() < self.boot_retry_until      # the network may still be coming up after a restart
        will_retry = (self.keep_connected_on() or starting_up) and not self.user_stopped and not auth
        self.retry_pending = will_retry
        self.set_state("offline", reason)
        if auth and (self.keep_connected_on() or starting_up):
            self.message.emit(f"{self.stream_name}: the server refused the login, so it will not retry. "
                              f"Check the username and password.")
            self.quiet_retry = False
        elif will_retry:
            self.quiet_retry = True
            delay = self.reconnect_delay()
            RUN_LOG.write("ENCODER", f"{self.stream_name}: reconnecting in {delay} seconds (attempt {self.fail_count}).")
            self.retry_timer.start(delay * 1000)
        else:
            self.quiet_retry = False

    def _retry_now(self):
        if self.state != "offline" or self.user_stopped:
            self.retry_pending = False
            return
        mixer = self.mixer_ref
        fallback = self.fallback_getter() if self.fallback_getter else None
        if not self.start(mixer, fallback):
            self.fail_count += 1
            if self.validate() or not (self.keep_connected_on() or time.monotonic() < self.boot_retry_until):
                self.retry_pending = False
                self.quiet_retry = False
                return
            self.retry_timer.start(self.reconnect_delay() * 1000)

    def reconnect(self):
        """Manual Reconnect button: drop whatever is there and connect again right now."""
        self.retry_timer.stop()
        self.retry_pending = False
        self.quiet_retry = False
        self.fail_count = 0
        RUN_LOG.write("ENCODER", f"{self.stream_name}: manual reconnect.")
        if self.process is not None:
            self._teardown()
        self.state = "offline"
        fallback = self.fallback_getter() if self.fallback_getter else None
        self.user_stopped = False
        self.start(self.mixer_ref, fallback)

    def _teardown(self):
        self.poll_timer.stop()
        if self.mixer is not None:
            self.mixer.unregister_encoder(self)
            self.mixer = None
        if self.feed_queue is not None:
            try:
                self.feed_queue.put_nowait(None)
            except queue.Full:
                pass
            self.feed_queue = None
        proc = self.process
        self.process = None
        if proc is not None:
            try:
                proc.terminate()
            except Exception:
                pass

    def stop(self):
        self.retry_timer.stop()
        was_waiting = self.retry_pending
        self.retry_pending = False
        self.quiet_retry = False
        self.fail_count = 0
        if self.state == "offline" and self.process is None:
            if was_waiting:
                self.set_state("offline", "stopped")
            return
        self.user_stopped = True
        self._teardown()
        self.set_state("offline", "stopped")

    # --- live metadata (artist / title / album) ---
    def push_metadata(self, meta):
        self.current_metadata = dict(meta)
        if self.state != "live":
            return
        threading.Thread(target=self._push_metadata_blocking, args=(dict(meta),), daemon=True).start()

    def _push_metadata_blocking(self, meta):
        try:
            song = f"{meta['artist']} - {meta['title']}" if meta.get("artist") else meta.get("title", "")
            host = self.server_host.strip()
            port = self.server_port.strip()
            if self.protocol == "Icecast":
                mount = self.mount_point.strip()
                if not mount.startswith("/"):
                    mount = "/" + mount
                params = urllib.parse.urlencode(
                    {"mode": "updinfo", "mount": mount, "song": song, "title": meta.get("title", ""),
                     "artist": meta.get("artist", ""), "album": meta.get("album", ""), "charset": "UTF-8"},
                    quote_via=urllib.parse.quote)
                url = f"http://{host}:{port}/admin/metadata?{params}"
                credentials = base64.b64encode(f"{(self.username or 'source').strip() or 'source'}:{self.source_password}".encode("utf-8")).decode("ascii")
                request = urllib.request.Request(url)
                request.add_header("Authorization", "Basic " + credentials)
            elif self.protocol == "Shoutcast":
                url = (f"http://{host}:{port}/admin.cgi?pass={urllib.parse.quote(self.server_password)}"
                       f"&mode=updinfo&song={urllib.parse.quote(song)}")
                request = urllib.request.Request(url)
            else:
                return
            request.add_header("User-Agent", "VisionStudio")
            urllib.request.urlopen(request, timeout=6).read()
        except Exception as e:
            self.message.emit(f"{self.stream_name}: could not update the now-playing text ({e}).")


STALL_SECONDS = 10
SERVER_CHECK_SECONDS = 30

STATE_TEXT = {"offline": "Offline", "connecting": "Connecting", "live": "LIVE"}
STATE_COLOR = {"offline": COLOR_TEXT_DIM, "connecting": COLOR_WARNING_AMBER, "live": COLOR_ON_AIR_GREEN}


class EncoderSlotWidget(QWidget):
    """One encoder: a full form while editing that folds down to one summary row after Save."""

    def __init__(self, slot, bank):
        super().__init__()
        self.slot = slot
        self.bank = bank
        self.collapsed = False
        self.setup_ui()
        slot.state_changed.connect(self.on_state_changed)

    def setup_ui(self):
        outer = QVBoxLayout()

        self.form_container = QWidget()
        layout = QFormLayout()

        self.name_edit = QLineEdit(self.slot.stream_name)
        self.name_edit.setAccessibleName(f"Encoder {self.slot.slot_number} stream name")
        layout.addRow(f"Encoder {self.slot.slot_number} Name:", self.name_edit)

        self.protocol_combo = QComboBox()
        self.protocol_combo.addItems(PROTOCOL_OPTIONS)
        self.protocol_combo.setCurrentText(self.slot.protocol)
        layout.addRow("Protocol:", self.protocol_combo)

        self.host_edit = QLineEdit(self.slot.server_host)
        layout.addRow("Host Address:", self.host_edit)

        self.port_edit = QLineEdit(self.slot.server_port)
        layout.addRow("Port:", self.port_edit)

        self.username_edit = QLineEdit(self.slot.username or "source")
        self.username_edit.setAccessibleName(f"Encoder {self.slot.slot_number} username")
        layout.addRow("Username:", self.username_edit)

        self.source_password_edit = QLineEdit(self.slot.source_password)
        self.source_password_edit.setEchoMode(QLineEdit.EchoMode.Password)
        self.source_password_edit.setAccessibleName(f"Encoder {self.slot.slot_number} password")
        layout.addRow("Password:", self.source_password_edit)

        self.mount_edit = QLineEdit(self.slot.mount_point)
        layout.addRow("Mount Point:", self.mount_edit)

        self.format_combo = QComboBox()
        self.format_combo.addItems(FORMAT_OPTIONS)
        self.format_combo.setCurrentText(self.slot.audio_format)
        layout.addRow("Format:", self.format_combo)

        self.bitrate_edit = QLineEdit(self.slot.bitrate_kbps)
        layout.addRow("Bitrate (kbps):", self.bitrate_edit)

        self.keep_check = QCheckBox("Keep connected (reconnect automatically if the stream drops)")
        self.keep_check.setChecked(self.slot.keep_connected_on())
        self.keep_check.setAccessibleName(f"Encoder {self.slot.slot_number} keep connected")
        layout.addRow(self.keep_check)

        self.reconnect_spin = QSpinBox()
        self.reconnect_spin.setRange(0, 3600)
        try:
            self.reconnect_spin.setValue(int(float(self.slot.reconnect_seconds)))
        except Exception:
            self.reconnect_spin.setValue(10)
        self.reconnect_spin.setAccessibleName(f"Encoder {self.slot.slot_number} reconnect after seconds, 0 reconnects right away")
        layout.addRow("Reconnect after (seconds, 0 = right away):", self.reconnect_spin)

        self.restart_check = QCheckBox("Reconnect when the program starts, if this stream was live when it closed")
        self.restart_check.setChecked(str(self.slot.reconnect_on_start).lower() == "true")
        self.restart_check.setAccessibleName(f"Encoder {self.slot.slot_number} reconnect when the program starts")
        layout.addRow(self.restart_check)

        self.server_password_edit = QLineEdit(self.slot.server_password)
        self.server_password_edit.setEchoMode(QLineEdit.EchoMode.Password)
        self.server_password_edit.setAccessibleName(f"Encoder {self.slot.slot_number} Shoutcast admin password")
        layout.addRow("Shoutcast Admin Password:", self.server_password_edit)
        self.encoder_form = layout
        self.protocol_combo.currentTextChanged.connect(self.update_protocol_rows)
        self.update_protocol_rows()

        save_btn = QPushButton("Save")
        save_btn.setAccessibleName(f"Save encoder {self.slot.slot_number}")
        save_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        save_btn.clicked.connect(self.save_settings)
        layout.addRow(save_btn)
        self.form_container.setLayout(layout)
        outer.addWidget(self.form_container)

        # One-line summary shown after Save: name, state, and the controls that matter.
        self.summary_widget = QWidget()
        summary_row = QHBoxLayout()
        self.summary_label = QLabel(self.slot.summary_text())
        self.summary_label.setWordWrap(True)
        summary_row.addWidget(self.summary_label, 1)

        self.state_label = QLabel("Offline")
        self.state_label.setStyleSheet(f"color: {COLOR_TEXT_DIM}; font-weight: bold;")
        summary_row.addWidget(self.state_label)

        self.edit_btn = QPushButton("Edit")
        self.edit_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.edit_btn.clicked.connect(self.expand_form)
        summary_row.addWidget(self.edit_btn)

        self.start_btn = QPushButton("Start Streaming")
        self.start_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.start_btn.clicked.connect(lambda: self.bank.start_slot(self.slot))
        summary_row.addWidget(self.start_btn)

        self.stop_btn = QPushButton("Stop Streaming")
        self.stop_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.stop_btn.clicked.connect(lambda: self.bank.stop_slot(self.slot))
        summary_row.addWidget(self.stop_btn)

        self.remove_btn = QPushButton("Remove")
        self.remove_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.remove_btn.clicked.connect(lambda: self.bank.remove_slot(self))
        summary_row.addWidget(self.remove_btn)

        self.summary_widget.setLayout(summary_row)
        outer.addWidget(self.summary_widget)
        self.setLayout(outer)
        self.refresh_accessible_names()
        self.on_state_changed(self.slot, self.slot.state, "")
        self.set_collapsed(False)

    def update_protocol_rows(self, *_args):
        """Icecast logs in with a username and password; the admin password row is only for Shoutcast."""
        icecast = self.protocol_combo.currentText() == "Icecast"
        for widget, shown in ((self.username_edit, icecast), (self.server_password_edit, not icecast)):
            try:
                self.encoder_form.setRowVisible(widget, shown)
            except Exception:
                widget.setVisible(shown)

    def refresh_accessible_names(self):
        name = self.slot.stream_name
        self.edit_btn.setAccessibleName(f"Edit {name}")
        self.start_btn.setAccessibleName(f"Start streaming {name}")
        self.stop_btn.setAccessibleName(f"Stop streaming {name}")
        self.remove_btn.setAccessibleName(f"Remove {name}")
        self.state_label.setAccessibleName(f"{name} status")

    def set_collapsed(self, collapsed):
        self.collapsed = collapsed
        self.form_container.setVisible(not collapsed)
        self.summary_widget.setVisible(True)
        self.edit_btn.setVisible(collapsed)
        self.summary_label.setVisible(collapsed)

    def expand_form(self):
        self.set_collapsed(False)
        self.name_edit.setFocus()

    def save_settings(self):
        self.slot.stream_name = self.name_edit.text().strip() or f"Encoder {self.slot.slot_number}"
        self.slot.protocol = self.protocol_combo.currentText()
        self.slot.server_host = self.host_edit.text().strip()
        self.slot.server_port = self.port_edit.text().strip()
        self.slot.mount_point = self.mount_edit.text().strip()
        self.slot.username = self.username_edit.text().strip() or "source"
        self.slot.audio_format = self.format_combo.currentText()
        self.slot.bitrate_kbps = self.bitrate_edit.text().strip() or "128"
        self.slot.server_password = self.server_password_edit.text()
        self.slot.source_password = self.source_password_edit.text()
        self.slot.keep_connected = "true" if self.keep_check.isChecked() else "false"
        self.slot.reconnect_seconds = str(self.reconnect_spin.value())
        self.slot.reconnect_on_start = "true" if self.restart_check.isChecked() else "false"
        self.summary_label.setText(self.slot.summary_text())
        self.refresh_accessible_names()
        self.bank.save_all()
        self.bank.on_status(f"{self.slot.stream_name}: saved.")
        self.set_collapsed(True)
        self.edit_btn.setFocus()

    def on_state_changed(self, slot, state, reason):
        shown = STATE_TEXT.get(state, state)
        if state == "offline" and getattr(slot, "retry_pending", False):
            shown = "Offline, reconnecting"
        self.state_label.setText(shown)
        self.state_label.setStyleSheet(
            f"color: {STATE_COLOR.get(state, COLOR_TEXT_DIM)}; font-weight: bold;")
        busy = state != "offline"
        self.start_btn.setEnabled(not busy)
        self.stop_btn.setEnabled(busy or bool(getattr(slot, "retry_pending", False)))
        self.remove_btn.setEnabled(not busy)


class EncoderBankWidget(QWidget):
    def __init__(self, settings, on_status, get_fallback_source, mixer, on_slot_state_changed):
        super().__init__()
        self.settings = settings
        self.on_status = on_status
        self.get_fallback_source = get_fallback_source
        self.mixer = mixer
        self.on_slot_state_changed = on_slot_state_changed
        self.slots = []
        self.slot_widgets = []
        self.setup_ui()
        self.restore_slots()

    def setup_ui(self):
        outer_layout = QVBoxLayout()
        add_btn = QPushButton("Add Encoder Slot")
        add_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        add_btn.clicked.connect(lambda: self.add_slot())
        outer_layout.addWidget(add_btn)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        container = QWidget()
        self.slots_layout = QVBoxLayout()
        self.slots_layout.addStretch(1)
        container.setLayout(self.slots_layout)
        scroll.setWidget(container)
        outer_layout.addWidget(scroll)
        self.setLayout(outer_layout)

    def restore_slots(self):
        try:
            saved = json.loads(self.settings.value("encoder_slots", "[]"))
        except Exception:
            saved = []
        for data in saved:
            self.add_slot(data, collapsed=True)

    def save_all(self):
        try:
            self.settings.setValue("encoder_slots", json.dumps([s.to_dict() for s in self.slots]))
        except Exception:
            pass

    def add_slot(self, data=None, collapsed=False):
        if len(self.slots) >= MAX_ENCODER_SLOTS:
            self.on_status(f"Maximum of {MAX_ENCODER_SLOTS} encoder slots reached.")
            return
        slot = EncoderSlot(len(self.slots) + 1)
        if data:
            slot.load_dict(data)
        slot.mixer_ref = self.mixer
        slot.fallback_getter = self.get_fallback_source
        slot.message.connect(self.on_status)
        slot.state_changed.connect(self.on_slot_state_changed)
        widget = EncoderSlotWidget(slot, self)
        self.slots.append(slot)
        self.slot_widgets.append(widget)
        self.slots_layout.insertWidget(self.slots_layout.count() - 1, widget)
        if collapsed:
            widget.set_collapsed(True)
        else:
            self.on_status(f"Encoder slot {slot.slot_number} added.")

    def remove_slot(self, widget):
        if widget not in self.slot_widgets:
            return
        slot = widget.slot
        slot.stop()
        self.slots.remove(slot)
        self.slot_widgets.remove(widget)
        widget.setParent(None)
        widget.deleteLater()
        self.save_all()
        self.on_status(f"{slot.stream_name} removed.")
        self.on_slot_state_changed(slot, "offline", "removed")

    def start_slot(self, slot):
        slot.mixer_ref = self.mixer
        slot.fallback_getter = self.get_fallback_source
        slot.fail_count = 0
        slot.was_live = "true"
        self.save_all()
        slot.start(self.mixer, self.get_fallback_source())

    def resume_saved(self):
        """After a restart: connect again every stream that is set to, and was live when the program closed."""
        for slot in self.slots:
            if str(slot.reconnect_on_start).lower() == "true" and str(slot.was_live).lower() == "true" and slot.state == "offline":
                RUN_LOG.write("ENCODER", f"{slot.stream_name}: was live when the program closed, connecting again.")
                slot.boot_retry_until = time.monotonic() + 300
                self.start_slot(slot)

    def stop_slot(self, slot):
        slot.was_live = "false"
        slot.boot_retry_until = 0.0
        self.save_all()
        slot.stop()

    def push_metadata(self, meta):
        for slot in self.slots:
            slot.push_metadata(meta)

    def shutdown(self):
        for slot in list(self.slots):
            slot.stop()



# ---------------------------------------------------------------------------
# Drop-two widgets: spinning record, editable queue, rotations, schedule,
# categories and keyboard shortcuts
# ---------------------------------------------------------------------------

class VinylWidget(QWidget):
    """A record that spins while its deck has a playing track. Turns at 45 rpm, with bright sheen
    wedges and a two-colour label so the turning is easy to see."""

    DEGREES_PER_SECOND = 270.0

    def __init__(self, deck_name, size=120):
        super().__init__()
        self.deck_name = deck_name
        self.angle = 0.0
        self.spinning = False
        self._last_tick = time.monotonic()
        self.setFixedSize(size, size)
        self.setAccessibleName(f"Deck {deck_name} record: stopped")

    def set_spinning(self, spinning):
        if spinning != self.spinning:
            self.spinning = spinning
            self._last_tick = time.monotonic()
            self.setAccessibleName(f"Deck {self.deck_name} record: {'spinning' if spinning else 'stopped'}")
            self.update()

    def tick(self):
        now = time.monotonic()
        elapsed = min(now - self._last_tick, 0.2)
        self._last_tick = now
        if self.spinning:
            self.angle = (self.angle + elapsed * self.DEGREES_PER_SECOND) % 360.0
            self.update()

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        w = self.width()
        radius = w / 2.0 - 3
        painter.translate(QPointF(w / 2.0, w / 2.0))
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QBrush(QColor("#0B0B0B")))
        painter.drawEllipse(QPointF(0, 0), radius, radius)
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.setPen(QPen(QColor("#2E2E2E"), 1))
        for frac in (0.92, 0.82, 0.72, 0.62, 0.52):
            painter.drawEllipse(QPointF(0, 0), radius * frac, radius * frac)
        painter.rotate(self.angle)
        # sheen wedges: bright, so the movement is obvious
        box = QRectF(-radius, -radius, radius * 2, radius * 2)
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QBrush(QColor(255, 255, 255, 70 if self.spinning else 30)))
        painter.drawPie(box, 20 * 16, 38 * 16)
        painter.drawPie(box, 200 * 16, 38 * 16)
        # label: two colours, so one half sweeping round is easy to follow
        label = radius * 0.42
        label_box = QRectF(-label, -label, label * 2, label * 2)
        painter.setBrush(QBrush(QColor(COLOR_ACTIVE_BLUE if self.spinning else "#555555")))
        painter.drawPie(label_box, 0, 180 * 16)
        painter.setBrush(QBrush(QColor(COLOR_WARNING_AMBER if self.spinning else "#777777")))
        painter.drawPie(label_box, 180 * 16, 180 * 16)
        painter.setBrush(QBrush(QColor("#F0F0F0")))
        painter.drawEllipse(QPointF(label * 0.62, 0), 4.0, 4.0)
        painter.setBrush(QBrush(QColor("#0B0B0B")))
        painter.drawEllipse(QPointF(0, 0), 3.5, 3.5)
        painter.end()


QUEUE_DISPLAY_LIMIT = 300
_QUEUE_TEXT_CACHE = {}


class MixerConsole(QWidget):
    """A broadcast-style mixer drawn on screen: a strip for each deck, the microphone, the jingle and ad
    player and the master, with level meters, on-air lamps and faders that light up when they move, a
    crossfader, and a lamp for every encoder (green when live)."""

    CHANNEL_ORDER = ("deck_a", "deck_b", "mic", "seq", "master")
    MOVE_FLASH_SECONDS = 1.5
    SEGMENTS = 16

    def __init__(self):
        super().__init__()
        self.setMinimumHeight(250)
        self.setMinimumWidth(480)
        self.setFocusPolicy(Qt.FocusPolicy.TabFocus)
        self.setAccessibleName("Mixer console")
        self.state = {"channels": {}, "crossfader": 0, "encoders": [], "summary": ""}
        self.vu_shown = {}
        self.fader_prev = {}
        self.moved_at = {}
        self._last_summary = ""

    def update_state(self, state):
        now = time.time()
        for key, channel in state.get("channels", {}).items():
            raw = float(channel.get("vu", 0.0))
            self.vu_shown[key] = max(raw, self.vu_shown.get(key, 0.0) * 0.82)
            fader = channel.get("fader")
            if fader is not None:
                previous = self.fader_prev.get(key)
                if previous is not None and abs(fader - previous) > 0.004:
                    self.moved_at[key] = now
                self.fader_prev[key] = fader
        cross = float(state.get("crossfader", 0))
        previous = self.fader_prev.get("xfade")
        if previous is not None and abs(cross - previous) > 0.5:
            self.moved_at["xfade"] = now
        self.fader_prev["xfade"] = cross
        self.state = state
        summary = state.get("summary", "")
        if summary != self._last_summary:
            self._last_summary = summary
            self.setAccessibleDescription(summary)
        self.update()

    def is_moving(self, key):
        return time.time() - self.moved_at.get(key, 0.0) < self.MOVE_FLASH_SECONDS

    def paintEvent(self, event):
        painter = QPainter(self)
        try:
            self.draw(painter)
        except Exception:
            pass
        finally:
            painter.end()

    def draw(self, p):
        w, h = self.width(), self.height()
        p.fillRect(0, 0, w, h, QColor(COLOR_PANEL_DARK))
        p.setPen(QPen(QColor(COLOR_BORDER), 1))
        p.drawRect(0, 0, w - 1, h - 1)
        bottom_rows = 76                       # crossfader and encoders
        strips = len(self.CHANNEL_ORDER)
        strip_w = (w - 16) / float(strips)
        top = 8
        strip_h = h - bottom_rows - top - 6
        channels = self.state.get("channels", {})
        for n, key in enumerate(self.CHANNEL_ORDER):
            channel = channels.get(key, {})
            x = 8 + n * strip_w
            self.draw_strip(p, key, channel, x, top, strip_w - 6, strip_h)
        self.draw_crossfader(p, 14, h - bottom_rows + 2, w - 28)
        self.draw_encoders(p, 14, h - 40, w - 28)

    def draw_strip(self, p, key, channel, x, y, w, h):
        p.setPen(QPen(QColor(COLOR_BORDER), 1))
        p.setBrush(QBrush(QColor(COLOR_BACKGROUND)))
        p.drawRoundedRect(QRectF(x, y, w, h), 6, 6)
        label = channel.get("label", key)
        p.setPen(QColor(COLOR_TEXT_BRIGHT))
        font = p.font()
        font.setBold(True)
        p.setFont(font)
        p.drawText(QRectF(x, y + 3, w, 16), Qt.AlignmentFlag.AlignCenter, label)
        font.setBold(False)
        p.setFont(font)
        # lamp and status
        color = QColor(channel.get("color", COLOR_TEXT_DIM))
        lit = bool(channel.get("on", False))
        p.setPen(QPen(color.darker(160), 1))
        p.setBrush(QBrush(color if lit else QColor(COLOR_BORDER)))
        p.drawEllipse(QPointF(x + 14, y + 32), 6, 6)
        p.setPen(color if lit else QColor(COLOR_TEXT_DIM))
        p.drawText(QRectF(x + 24, y + 22, w - 26, 20), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                   channel.get("status", ""))
        # meter
        meter_top, meter_bottom = y + 50, y + h - 22
        meter_x, meter_w = x + 12, 14
        seg_h = (meter_bottom - meter_top) / float(self.SEGMENTS)
        level = self.vu_shown.get(key, 0.0)
        lit_segments = int(round(min(1.0, level) * self.SEGMENTS))
        for s in range(self.SEGMENTS):
            from_bottom = s
            seg_y = meter_bottom - (from_bottom + 1) * seg_h
            if from_bottom < self.SEGMENTS * 0.62:
                seg_color = QColor(COLOR_ON_AIR_GREEN)
            elif from_bottom < self.SEGMENTS * 0.85:
                seg_color = QColor(COLOR_WARNING_AMBER)
            else:
                seg_color = QColor(COLOR_LIVE_RED)
            if from_bottom >= lit_segments:
                seg_color = seg_color.darker(400)
            p.fillRect(QRectF(meter_x, seg_y + 1, meter_w, max(1.0, seg_h - 2)), seg_color)
        # fader
        fader = channel.get("fader")
        track_x = x + w - 26
        p.setPen(QPen(QColor(COLOR_BORDER), 3))
        p.drawLine(QPointF(track_x, meter_top), QPointF(track_x, meter_bottom))
        if fader is None:
            p.setPen(QColor(COLOR_TEXT_DIM))
            p.drawText(QRectF(x + 32, meter_top, w - 34, meter_bottom - meter_top),
                       Qt.AlignmentFlag.AlignCenter, "no fader")
        else:
            moving = self.is_moving(key)
            knob_y = meter_bottom - max(0.0, min(1.0, fader)) * (meter_bottom - meter_top)
            knob_color = QColor(COLOR_ACTIVE_BLUE if moving else COLOR_TEXT_DIM)
            p.setPen(QPen(QColor(COLOR_TEXT_BRIGHT if moving else COLOR_BORDER), 2 if moving else 1))
            p.setBrush(QBrush(knob_color))
            p.drawRoundedRect(QRectF(track_x - 11, knob_y - 6, 22, 12), 3, 3)
            p.setPen(QColor(COLOR_ACTIVE_BLUE if moving else COLOR_TEXT_DIM))
            p.drawText(QRectF(x, y + h - 20, w, 18), Qt.AlignmentFlag.AlignCenter,
                       f"{int(round(fader * 100))}%" + ("  MOVING" if moving else ""))

    def draw_crossfader(self, p, x, y, w):
        p.setPen(QColor(COLOR_TEXT_BRIGHT))
        p.drawText(QRectF(x, y, w, 16), Qt.AlignmentFlag.AlignCenter, "CROSSFADER")
        track_y = y + 28
        p.setPen(QPen(QColor(COLOR_BORDER), 4))
        p.drawLine(QPointF(x + 22, track_y), QPointF(x + w - 22, track_y))
        p.setPen(QColor(COLOR_TEXT_DIM))
        p.drawText(QRectF(x, track_y - 10, 20, 20), Qt.AlignmentFlag.AlignCenter, "A")
        p.drawText(QRectF(x + w - 20, track_y - 10, 20, 20), Qt.AlignmentFlag.AlignCenter, "B")
        position = max(0.0, min(100.0, float(self.state.get("crossfader", 0)))) / 100.0
        knob_x = x + 22 + position * (w - 44)
        moving = self.is_moving("xfade")
        p.setPen(QPen(QColor(COLOR_TEXT_BRIGHT if moving else COLOR_BORDER), 2 if moving else 1))
        p.setBrush(QBrush(QColor(COLOR_ACTIVE_BLUE if moving else COLOR_TEXT_DIM)))
        p.drawRoundedRect(QRectF(knob_x - 6, track_y - 11, 12, 22), 3, 3)

    def draw_encoders(self, p, x, y, w):
        encoders = self.state.get("encoders", [])
        p.setPen(QColor(COLOR_TEXT_BRIGHT))
        p.drawText(QRectF(x, y, 80, 20), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, "ENCODERS")
        if not encoders:
            p.setPen(QColor(COLOR_TEXT_DIM))
            p.drawText(QRectF(x + 84, y, w - 84, 20), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                       "none set up")
            return
        colors = {"live": COLOR_ON_AIR_GREEN, "connecting": COLOR_WARNING_AMBER,
                  "problem": COLOR_LIVE_RED, "offline": COLOR_BORDER}
        cursor = x + 84
        shown = 0
        for name, state in encoders:
            text = name if len(name) <= 14 else name[:13] + "..."
            need = 26 + 7 * len(text)
            if cursor + need > x + w - 40 and shown < len(encoders):
                p.setPen(QColor(COLOR_TEXT_DIM))
                p.drawText(QRectF(cursor, y, 60, 20), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                           f"+{len(encoders) - shown}")
                break
            color = QColor(colors.get(state, COLOR_BORDER))
            p.setPen(QPen(color.darker(160), 1))
            p.setBrush(QBrush(color))
            p.drawEllipse(QPointF(cursor + 7, y + 10), 6, 6)
            p.setPen(QColor(COLOR_TEXT_BRIGHT if state == "live" else COLOR_TEXT_DIM))
            p.drawText(QRectF(cursor + 18, y, need - 18, 20), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, text)
            cursor += need
            shown += 1


class QueueList(QListWidget):
    """Browse with Up/Down. Ctrl+Up/Down moves a track, Delete removes it, Insert adds tracks."""

    move_requested = pyqtSignal(int, int)
    remove_requested = pyqtSignal(int)
    insert_requested = pyqtSignal()
    play_requested = pyqtSignal(int)
    check_changed = pyqtSignal(int, bool)

    def __init__(self):
        super().__init__()
        self.setAccessibleName("Queue: upcoming tracks. Up and Down browse, Control Up and Down move the "
                               "selected track, Delete removes it, Insert adds tracks.")
        self.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.header_count = 1   # rows above the queue itself: the song on air, break items, played and skipped songs
        self.passed_start = 1   # the first played or skipped row (they sit at the end of the header rows)
        self.itemChanged.connect(self._item_changed)

    def _item_changed(self, item):
        if item.flags() & Qt.ItemFlag.ItemIsUserCheckable:
            self.check_changed.emit(self.row(item), item.checkState() == Qt.CheckState.Checked)

    def keyPressEvent(self, event):
        key = event.key()
        ctrl = bool(event.modifiers() & Qt.KeyboardModifier.ControlModifier)
        row = self.currentRow()
        if ctrl and key in (Qt.Key.Key_Up, Qt.Key.Key_Down):
            if row >= self.header_count:
                self.move_requested.emit(row, -1 if key == Qt.Key.Key_Up else 1)
            event.accept()
            return
        if key == Qt.Key.Key_Delete:
            if row >= self.header_count:
                self.remove_requested.emit(row)
            event.accept()
            return
        if key == Qt.Key.Key_Insert:
            self.insert_requested.emit()
            event.accept()
            return
        if not ctrl and key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            if row >= self.header_count:
                self.play_requested.emit(row)
            event.accept()
            return
        if not ctrl and key == Qt.Key.Key_Space:
            item = self.currentItem()
            if item is not None and (item.flags() & Qt.ItemFlag.ItemIsUserCheckable):
                item.setCheckState(Qt.CheckState.Unchecked if item.checkState() == Qt.CheckState.Checked
                                   else Qt.CheckState.Checked)
            event.accept()
            return
        super().keyPressEvent(event)

    def event(self, e):
        # Stop application-wide shortcuts from swallowing the keys this list owns.
        if e.type() == QEvent.Type.ShortcutOverride:
            ctrl = bool(e.modifiers() & Qt.KeyboardModifier.ControlModifier)
            if e.key() in (Qt.Key.Key_Delete, Qt.Key.Key_Insert, Qt.Key.Key_Return, Qt.Key.Key_Enter,
                           Qt.Key.Key_Space) and not ctrl or e.key() in (Qt.Key.Key_Delete, Qt.Key.Key_Insert) or (
                    ctrl and e.key() in (Qt.Key.Key_Up, Qt.Key.Key_Down)):
                e.accept()
                return True
        return super().event(e)

    def show_queue(self, entries, headers=None, select_row=None, passed=None):
        """headers: rows shown above the queue (the song on air, then any break items). Insert with the
        song on air selected puts tracks at the very top of the queue, ahead of what was about to play."""
        headers = headers or []
        passed = passed or []
        self.passed_start = len(headers)
        self.header_count = len(headers) + len(passed)
        row = self.currentRow() if select_row is None else select_row
        self.blockSignals(True)
        self.clear()
        for header in headers:
            self.addItem(header)
        for text in passed:
            item = QListWidgetItem(text)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable)
            item.setCheckState(Qt.CheckState.Unchecked)
            self.addItem(item)
        shown = entries[:QUEUE_DISPLAY_LIMIT]
        fresh_reads = 0
        for i, entry in enumerate(shown):
            text = None
            if is_hour_marker(entry):
                text = format_track_display(entry)
            elif entry in _QUEUE_TEXT_CACHE:
                text = _QUEUE_TEXT_CACHE[entry]
            elif fresh_reads < 40:   # read a few tags per refresh so a huge queue never freezes the screen
                fresh_reads += 1
                try:
                    text = format_track_display(entry)
                    _QUEUE_TEXT_CACHE[entry] = text
                except Exception:
                    text = None
            if text is None:
                text = os.path.splitext(os.path.basename(str(entry)))[0]
            row_item = QListWidgetItem(f"{i + 1}. {text}")
            if not is_hour_marker(entry):
                row_item.setFlags(row_item.flags() | Qt.ItemFlag.ItemIsUserCheckable)
                row_item.setCheckState(Qt.CheckState.Checked)
            self.addItem(row_item)
        if len(entries) > len(shown):
            self.addItem(f"... and {len(entries) - len(shown)} more tracks")
        self.blockSignals(False)
        if self.count():
            self.setCurrentRow(max(0, min(row, self.count() - 1)))


class RotationsTab(QWidget):
    def __init__(self, app):
        super().__init__()
        self.app = app
        layout = QVBoxLayout()
        info = QLabel("Rotations: each one is a folder of music. Point the music library at a folder and one "
                      "rotation is made per subfolder automatically.")
        info.setWordWrap(True)
        layout.addWidget(info)
        self.list = QListWidget()
        self.list.setAccessibleName("Rotations list")
        layout.addWidget(self.list)
        for text, handler in (("Set Music Library Folder (builds rotations)", app.set_library_folder),
                              ("New Rotation (Ctrl+N)", self.new_rotation),
                              ("Rename Selected", self.rename_selected),
                              ("Change Folder of Selected", self.change_folder),
                              ("Remove Selected", self.remove_selected),
                              ("Import M3U Playlist Into Queue", app.import_m3u),
                              ("Export Queue as M3U Playlist", app.export_m3u)):
            btn = QPushButton(text)
            btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
            btn.clicked.connect(handler)
            layout.addWidget(btn)
        self.setLayout(layout)
        self.refresh()

    def refresh(self):
        row = self.list.currentRow()
        self.list.clear()
        for rotation in self.app.rotation_library.rotations:
            count = len(rotation.track_paths())
            kind = "automatic" if rotation.auto else "manual"
            self.list.addItem(f"{rotation.name}: {count} tracks, {kind}, {rotation.folder}")
        if self.list.count():
            self.list.setCurrentRow(max(0, min(row, self.list.count() - 1)))

    def selected(self):
        row = self.list.currentRow()
        rotations = self.app.rotation_library.rotations
        return rotations[row] if 0 <= row < len(rotations) else None

    def new_rotation(self):
        folder = QFileDialog.getExistingDirectory(self, "Choose the folder for the new rotation")
        if not folder:
            return
        default = pretty_folder_name(os.path.basename(os.path.normpath(folder)))
        name, ok = QInputDialog.getText(self, "New rotation", "Rotation name:", text=default)
        if ok and name.strip():
            rotation = self.app.rotation_library.add_rotation(name.strip(), folder, True, auto=False)
            self.app.normalizer.start(rotation.track_paths())
            self.app.update_status(f"Rotation {rotation.name} added. The schedule was rebuilt.")

    def rename_selected(self):
        rotation = self.selected()
        if rotation is None:
            return
        name, ok = QInputDialog.getText(self, "Rename rotation", "New name:", text=rotation.name)
        if ok and name.strip():
            self.app.rotation_library.rename_rotation(rotation.id, name.strip())

    def change_folder(self):
        rotation = self.selected()
        if rotation is None:
            return
        folder = QFileDialog.getExistingDirectory(self, "Choose the new folder", rotation.folder)
        if folder:
            self.app.rotation_library.set_rotation_folder(rotation.id, folder)
            self.app.normalizer.start(rotation.track_paths())

    def remove_selected(self):
        rotation = self.selected()
        if rotation is None:
            return
        answer = QMessageBox.question(self, "Remove rotation",
                                      f"Remove the rotation {rotation.name}? Your music files are not touched.")
        if answer == QMessageBox.StandardButton.Yes:
            self.app.rotation_library.remove_rotation(rotation.id)


class ScheduleTab(QWidget):
    def __init__(self, app):
        super().__init__()
        self.app = app
        layout = QVBoxLayout()
        self.live_label = QLabel("")
        self.live_label.setWordWrap(True)
        self.live_label.setStyleSheet(f"color: {COLOR_ON_AIR_GREEN}; font-weight: bold;")
        layout.addWidget(self.live_label)
        self.table = QTableWidget(24, 3)
        self.table.setHorizontalHeaderLabels(["Hour", "Rotation", "On air"])
        self.table.setAccessibleName("24 hour rotation schedule")
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        layout.addWidget(self.table)
        row = QHBoxLayout()
        self.rotation_combo = QComboBox()
        self.rotation_combo.setAccessibleName("Rotation to assign to the selected hour")
        row.addWidget(self.rotation_combo, 1)
        assign = QPushButton("Assign To Selected Hour")
        assign.setStyleSheet(BUTTON_STYLE_CONSOLE)
        assign.clicked.connect(self.assign_selected)
        row.addWidget(assign)
        layout.addLayout(row)
        regen = QPushButton("Regenerate Schedule Evenly")
        regen.setStyleSheet(BUTTON_STYLE_CONSOLE)
        regen.clicked.connect(self.regenerate)
        layout.addWidget(regen)
        self.setLayout(layout)
        self.refresh()

    def refresh(self):
        now_hour = datetime.now().hour
        schedule = self.app.rotation_schedule
        library = self.app.rotation_library
        selected = self.table.currentRow()
        self.rotation_combo.clear()
        for rotation in library.rotations:
            self.rotation_combo.addItem(rotation.name, rotation.id)
        for hour in range(24):
            rotation = library.find(schedule.rotation_id_for_hour(hour))
            live = hour == now_hour
            cells = [hour_label(hour), rotation.name if rotation else "(none)", "LIVE NOW" if live else ""]
            for col, text in enumerate(cells):
                item = QTableWidgetItem(text)
                if live:
                    font = item.font()
                    font.setBold(True)
                    item.setFont(font)
                    item.setForeground(QBrush(QColor(COLOR_ON_AIR_GREEN)))
                self.table.setItem(hour, col, item)
        self.table.setCurrentCell(selected if selected >= 0 else now_hour, 0)
        live_rotation = library.find(schedule.rotation_id_for_hour(now_hour))
        self.live_label.setText(f"On air now: {hour_label(now_hour)}, "
                                f"{live_rotation.name if live_rotation else 'no rotation'}")
        self.live_label.setAccessibleName(self.live_label.text())

    def assign_selected(self):
        hour = self.table.currentRow()
        rotation_id = self.rotation_combo.currentData()
        if hour >= 0 and rotation_id:
            self.app.rotation_schedule.set_hour(hour, rotation_id)
            self.refresh()
            self.app.rotation.check_rotation_for_hour()

    def regenerate(self):
        self.app.rotation_schedule.regenerate_even()
        self.refresh()
        self.app.rotation.check_rotation_for_hour()
        self.app.update_status("Schedule rebuilt evenly across the 24 hours.")


class CategoriesTab(QWidget):
    TYPE_CHOICES = (("Music (makes a rotation and a dated schedule)", "music"), ("Jingles", "jingle"),
                    ("Sweepers", "sweeper"), ("Ads", "ad"))

    def __init__(self, app):
        super().__init__()
        self.app = app
        layout = QVBoxLayout()
        info = QLabel("Categories: every folder of music, jingles, sweepers and ads. Music folders also make a "
                      "rotation. A newly imported category plays nowhere until you switch it on or put it in a "
                      "dated schedule, so holiday music and jingles stay off the air until you schedule them. "
                      "Change a category's folder and everything that uses it follows.")
        info.setWordWrap(True)
        layout.addWidget(info)
        self.list = QListWidget()
        self.list.setAccessibleName("Categories list")
        layout.addWidget(self.list)
        for text, handler in (("Import Category Folder (Ctrl+N)", self.import_folder),
                              ("Change Folder of Selected", self.change_folder),
                              ("Switch Selected On Or Off In The Regular Schedule", self.toggle_active),
                              ("Rename Selected", self.rename_selected),
                              ("Change Type of Selected", self.change_type),
                              ("Remove Selected", self.remove_selected)):
            btn = QPushButton(text)
            btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
            btn.clicked.connect(handler)
            layout.addWidget(btn)
        self.setLayout(layout)
        self.refresh()

    def refresh(self):
        row = self.list.currentRow()
        self.list.clear()
        for category in self.app.category_library.categories:
            self.list.addItem(f"{self.app.category_library.describe(category)}: {describe_folder(category['folder'])}")
        if self.list.count():
            self.list.setCurrentRow(max(0, min(row, self.list.count() - 1)))

    def selected(self):
        row = self.list.currentRow()
        cats = self.app.category_library.categories
        return cats[row] if 0 <= row < len(cats) else None

    def import_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Import a category folder")
        if not folder:
            return
        guess = guess_category_type(os.path.basename(os.path.normpath(folder)))
        labels = [label for label, _value in self.TYPE_CHOICES]
        default_index = next((i for i, (_l, v) in enumerate(self.TYPE_CHOICES) if v == guess), 1)
        choice, ok = QInputDialog.getItem(self, "What is in this folder?", "Type:", labels, default_index, False)
        if not ok:
            return
        kind = dict(self.TYPE_CHOICES)[choice]
        added = self.app.import_category_folder(folder, kind)
        if not added:
            self.app.update_status("No audio files found in that folder, so no category was made.")
            return
        names = ", ".join(f"{c['name']} ({c['type']})" for c in added)
        extra = " Each music folder also made a rotation and a draft dated schedule; nothing plays until you schedule it." \
            if kind == "music" else " It stays off the air until you switch it on or use it in a dated schedule."
        self.app.announce(f"Imported {names}.{extra}")

    def change_folder(self):
        category = self.selected()
        if category is None:
            return
        folder = QFileDialog.getExistingDirectory(self, "Choose the new folder", category["folder"])
        if folder:
            self.app.change_category_folder(category, folder)

    def toggle_active(self):
        category = self.selected()
        if category is None:
            return
        self.app.set_category_active(category, not self.app.category_library.is_active(category))

    def rename_selected(self):
        category = self.selected()
        if category is None:
            return
        name, ok = QInputDialog.getText(self, "Rename category", "New name:", text=category["name"])
        if ok:
            self.app.category_library.rename(category["id"], name)

    def change_type(self):
        category = self.selected()
        if category is None:
            return
        types = [t for t in CATEGORY_TYPES if t != "music"]
        if category["type"] == "music":
            self.app.announce("A music category stays music. Remove it and import it again to change that.")
            return
        choice, ok = QInputDialog.getItem(self, "Category type", "Type:", types,
                                          types.index(category["type"]) if category["type"] in types else 0, False)
        if ok:
            self.app.category_library.set_type(category["id"], choice)

    def remove_selected(self):
        category = self.selected()
        if category is not None:
            self.app.category_library.remove(category["id"])


class ShortcutsTab(QWidget):
    def __init__(self, app):
        super().__init__()
        self.app = app
        layout = QVBoxLayout()
        info = QLabel("Keyboard shortcuts. The default layout follows Station Playlist. Select a command and "
                      "choose Change Key to remap it.")
        info.setWordWrap(True)
        layout.addWidget(info)
        layout_row = QHBoxLayout()
        layout_row.addWidget(QLabel("Layout:"))
        self.layout_combo = QComboBox()
        self.layout_combo.setAccessibleName("Keyboard layout. Choose the automation system whose keys you know.")
        layout_row.addWidget(self.layout_combo, 1)
        import_btn = QPushButton("Import Layout File...")
        import_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        import_btn.clicked.connect(self.import_layout)
        layout_row.addWidget(import_btn)
        export_btn = QPushButton("Export Current Layout...")
        export_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        export_btn.clicked.connect(self.export_layout)
        layout_row.addWidget(export_btn)
        layout.addLayout(layout_row)
        self.fill_layouts()
        self.layout_combo.currentIndexChanged.connect(self.on_layout_chosen)
        self.table = QTableWidget(0, 2)
        self.table.setHorizontalHeaderLabels(["Command", "Key"])
        self.table.setAccessibleName("Keyboard shortcuts")
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        layout.addWidget(self.table)
        change = QPushButton("Change Key of Selected Command")
        change.setStyleSheet(BUTTON_STYLE_CONSOLE)
        change.clicked.connect(self.change_key)
        layout.addWidget(change)
        reset = QPushButton("Reset All Keys to the Selected Layout")
        reset.setStyleSheet(BUTTON_STYLE_CONSOLE)
        reset.clicked.connect(self.reset_all)
        layout.addWidget(reset)
        self.setLayout(layout)
        self.refresh()

    def fill_layouts(self):
        self.layout_combo.blockSignals(True)
        self.layout_combo.clear()
        current = str(self.app.settings.value("shortcut_layout", DEFAULT_LAYOUT_NAME))
        for name in list_shortcut_layouts():
            self.layout_combo.addItem(name)
        index = self.layout_combo.findText(current)
        self.layout_combo.setCurrentIndex(max(0, index))
        self.layout_combo.blockSignals(False)

    def on_layout_chosen(self, _index):
        name = self.layout_combo.currentText()
        set_shortcut_layout(self.app.settings, name)
        self.app.rebuild_shortcuts()
        self.refresh()
        self.app.announce(f"Keyboard layout: {name}. Your own key changes were cleared.")

    def import_layout(self):
        path, _ = QFileDialog.getOpenFileName(self, "Import a keyboard layout file", "", "Layout files (*.json)")
        if not path:
            return
        try:
            name = import_shortcut_layout(path)
        except Exception as e:
            self.app.announce(f"That layout file could not be read: {e}")
            return
        if not name:
            self.app.announce("That file has no keys in it, so it was not imported.")
            return
        self.fill_layouts()
        self.layout_combo.setCurrentIndex(max(0, self.layout_combo.findText(name)))   # applies it
        if self.app.settings.value("shortcut_layout", "") != name:
            self.on_layout_chosen(0)

    def export_layout(self):
        name = self.layout_combo.currentText()
        path, _ = QFileDialog.getSaveFileName(self, "Export the current keyboard layout",
                                              name.replace(" (default)", "") + ".json", "Layout files (*.json)")
        if not path:
            return
        try:
            export_shortcut_layout(self.app.settings, path, name)
            self.app.announce(f"Layout saved to {path}. Edit it and import it to make your own layout.")
        except Exception as e:
            self.app.announce(f"The layout could not be saved: {e}")

    def refresh(self):
        bindings = load_shortcut_bindings(self.app.settings)
        self.table.setRowCount(len(DEFAULT_SHORTCUTS))
        for row, (sid, label, _default, rebindable) in enumerate(DEFAULT_SHORTCUTS):
            self.table.setItem(row, 0, QTableWidgetItem(label))
            key = bindings.get(sid, "")
            self.table.setItem(row, 1, QTableWidgetItem(key if rebindable else f"{key} (fixed)"))

    def change_key(self):
        row = self.table.currentRow()
        if not (0 <= row < len(DEFAULT_SHORTCUTS)):
            return
        sid, label, _default, rebindable = DEFAULT_SHORTCUTS[row]
        if not rebindable:
            self.app.update_status(f"{label} is a fixed key and cannot be changed.")
            return
        dialog = QDialog(self)
        dialog.setWindowTitle(f"Change key: {label}")
        box = QVBoxLayout(dialog)
        box.addWidget(QLabel("Press the new key combination, then choose OK."))
        edit = QKeySequenceEdit()
        edit.setAccessibleName("New key combination")
        box.addWidget(edit)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        box.addWidget(buttons)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            key = edit.keySequence().toString()
            if key:
                save_shortcut_override(self.app.settings, sid, key)
                self.app.rebuild_shortcuts()
                self.refresh()
                self.app.update_status(f"{label} is now {key}.")

    def reset_all(self):
        reset_shortcut_overrides(self.app.settings)
        self.app.rebuild_shortcuts()
        self.refresh()
        self.app.update_status("Keys reset to the selected layout.")


class VoiceTrackDialog(QDialog):
    """Voice track recorder. Recording: Enter stops. Review: P plays it back, Enter keeps it, R records it
    again, Escape discards it. The music keeps playing the whole time."""

    def __init__(self, parent, recorder, description, settings, default_underlay=6):
        super().__init__(parent)
        self.recorder = recorder
        self.settings = settings
        self.recorded_seconds = 0.0
        self.state = "recording"
        self.preview = None
        self.setWindowTitle("Voice track")
        self.setModal(True)
        layout = QVBoxLayout()
        self.info = QLabel("")
        self.info.setWordWrap(True)
        layout.addWidget(self.info)
        self.time_label = QLabel("Recorded: 0 seconds")
        self.time_label.setAccessibleName("Recorded time")
        layout.addWidget(self.time_label)
        form = QFormLayout()
        self.underlay_spin = QSpinBox()
        self.underlay_spin.setRange(0, 30)
        self.underlay_spin.setValue(int(default_underlay))
        self.underlay_spin.setAccessibleName("Seconds of the next song's intro that play under the end of this voice track. "
                                             "Zero starts the song as the voice ends.")
        form.addRow("Next song's intro under the end of the voice track, seconds:", self.underlay_spin)
        layout.addLayout(form)
        self.primary = QPushButton("")
        self.primary.setDefault(True)
        self.primary.clicked.connect(self.on_primary)
        layout.addWidget(self.primary)
        self.play_button = QPushButton("Play it back (P)")
        self.play_button.clicked.connect(self.toggle_preview)
        layout.addWidget(self.play_button)
        self.again_button = QPushButton("Record it again (R)")
        self.again_button.clicked.connect(self.record_again)
        layout.addWidget(self.again_button)
        self.cancel_button = QPushButton("Discard (Escape)")
        self.cancel_button.clicked.connect(self.reject)
        layout.addWidget(self.cancel_button)
        self.setLayout(layout)
        self.description = description
        QShortcut(QKeySequence("P"), self).activated.connect(self.toggle_preview)
        QShortcut(QKeySequence("R"), self).activated.connect(self.record_again)
        self.timer = QTimer(self)
        self.timer.setInterval(500)
        self.timer.timeout.connect(self.tick)
        self.timer.start()
        self.show_state()

    def show_state(self):
        recording = self.state == "recording"
        if recording:
            text = (f"Recording a voice track {self.description}. Speak now. "
                    "Press Enter when you are finished.")
            self.primary.setText("Stop recording (Enter)")
        else:
            text = (f"Recorded {int(round(self.recorded_seconds))} seconds. Press P to play it back, "
                    "R to record it again, Enter to keep it, or Escape to discard it.")
            self.primary.setText("Keep this voice track (Enter)")
        self.info.setText(text)
        self.info.setAccessibleName(text)
        self.play_button.setEnabled(not recording)
        self.again_button.setEnabled(not recording)
        self.primary.setFocus()

    def tick(self):
        if self.state == "recording":
            seconds = int(self.recorder.seconds())
            self.time_label.setText(f"Recorded: {seconds} seconds")
            if seconds >= self.recorder.MAX_SECONDS:
                self.finish_recording()

    def finish_recording(self):
        self.recorded_seconds = self.recorder.stop()
        self.state = "review"
        self.time_label.setText(f"Recorded: {int(round(self.recorded_seconds))} seconds")
        self.show_state()

    def on_primary(self):
        if self.state == "recording":
            self.finish_recording()
        else:
            self.stop_preview()
            self.accept()

    def toggle_preview(self):
        if self.state != "review":
            return
        if self.preview is not None:
            self.stop_preview()
            return
        try:
            self.preview = QMediaPlayer()
            output = QAudioOutput()
            device = get_selected_output_device(self.settings)
            if device is not None:
                output.setDevice(device)
            output.setVolume(1.0)
            self.preview.setAudioOutput(output)
            self._preview_output = output
            self.preview.setSource(QUrl.fromLocalFile(self.recorder.path))
            self.preview.mediaStatusChanged.connect(
                lambda status: self.stop_preview() if status == QMediaPlayer.MediaStatus.EndOfMedia else None)
            self.preview.play()
            self.play_button.setText("Stop playback (P)")
        except Exception:
            self.preview = None

    def stop_preview(self):
        if self.preview is not None:
            try:
                self.preview.stop()
            except Exception:
                pass
            self.preview = None
        self.play_button.setText("Play it back (P)")

    def record_again(self):
        if self.state != "review":
            return
        self.stop_preview()
        if self.recorder.start(self.recorder.path):
            self.state = "recording"
            self.time_label.setText("Recorded: 0 seconds")
            self.show_state()

    def done(self, result):
        self.timer.stop()
        self.stop_preview()
        if self.state == "recording":
            self.recorded_seconds = self.recorder.stop()
        super().done(result)


def break_window_seconds(settings):
    try:
        return max(10, min(300, int(float(settings.value("break_window_seconds", BREAK_WINDOW_DEFAULT)))))
    except Exception:
        return BREAK_WINDOW_DEFAULT


# ---------------------------------------------------------------------------
# First-run setup wizard: point VisionStudio at every folder before anything starts
# ---------------------------------------------------------------------------

WIZARD_STEPS = [
    ("music_library_folder", "Music folder",
     "Choose the folder that holds your music. Every subfolder inside it becomes its own rotation, "
     "and a 24 hour schedule is built from them."),
    (":00", "Top of the hour",
     "Choose the folder of top of the hour jingles and legal station identification. "
     "They play at the start of every hour."),
    (":15", "Quarter past jingles",
     "Choose the folder of jingles that play at quarter past the hour."),
    (":30", "Station identifications (half past)",
     "Choose the folder of station identifications that play at half past the hour."),
    (":45", "Quarter to jingles",
     "Choose the folder of jingles that play at quarter to the hour."),
    ("ad_break_folder", "Commercials",
     "Choose the folder of commercials. They play between two jingles in the scheduled breaks."),
]


FOLDER_SETTINGS = [
    ("music_library_folder", "Music library"),
    (":00", "Top of the hour jingles"),
    (":15", "Quarter past jingles"),
    (":30", "Station identifications (half past)"),
    (":45", "Quarter to jingles"),
    ("ad_break_folder", "Commercials"),
    ("playlist_output_folder", "Playlist"),
]


class SetupIntroPage(QWizardPage):
    def __init__(self):
        super().__init__()
        self.setTitle("Welcome to Vision Studio setup")
        label = QLabel("This short setup asks where your music, jingles, station identifications and "
                       "commercials live. Nothing starts playing until you choose Start Rotation yourself. "
                       "Every step can be skipped by leaving the folder blank, and you can run this setup "
                       "again any time from the Settings tab.")
        label.setWordWrap(True)
        layout = QVBoxLayout()
        layout.addWidget(label)
        self.setLayout(layout)


class SetupFolderPage(QWizardPage):
    def __init__(self, key, title, description, initial=""):
        super().__init__()
        self.key = key
        self.setTitle(title)
        layout = QVBoxLayout()
        text = QLabel(description + " Leave it blank to skip this step.")
        text.setWordWrap(True)
        layout.addWidget(text)
        self.edit = QLineEdit(initial)
        self.edit.setAccessibleName(f"{title} folder path")
        self.edit.textChanged.connect(lambda _t: self.completeChanged.emit())
        layout.addWidget(self.edit)
        browse = QPushButton(f"Browse for {title} Folder")
        browse.clicked.connect(self.browse)
        layout.addWidget(browse)
        self.note = QLabel("")
        self.note.setWordWrap(True)
        layout.addWidget(self.note)
        self.setLayout(layout)

    def browse(self):
        folder = QFileDialog.getExistingDirectory(self, f"Choose the {self.title()} folder", self.edit.text())
        if folder:
            self.edit.setText(folder)

    def path(self):
        return self.edit.text().strip()

    def isComplete(self):
        path = self.path()
        ok = (not path) or os.path.isdir(path)
        if not path:
            self.note.setText("")
        elif ok:
            self.note.setText(f"{len(scan_audio_files(path))} audio files found, including subfolders.")
        else:
            self.note.setText("That folder does not exist. Choose another or clear the box.")
        return ok


class SetupFinishPage(QWizardPage):
    def __init__(self, wizard, playlist_folder):
        super().__init__()
        self.owner = wizard
        self.playlist_folder = playlist_folder
        self.setTitle("Ready to finish")
        self.label = QLabel("")
        self.label.setWordWrap(True)
        layout = QVBoxLayout()
        layout.addWidget(self.label)
        self.setLayout(layout)

    def initializePage(self):
        lines = []
        for key, title, _d in WIZARD_STEPS:
            path = self.owner.results().get(key, "")
            lines.append(f"{title}: {path if path else 'not set'}")
        lines.append(f"Playlists will be saved in: {self.playlist_folder}")
        lines.append("Choose Finish to save these choices. Nothing starts until you press Start Rotation.")
        self.label.setText("\n".join(lines))


class SetupWizard(QWizard):
    def __init__(self, parent, current, playlist_folder):
        super().__init__(parent)
        self.setWindowTitle("Vision Studio Setup")
        self.setWizardStyle(QWizard.WizardStyle.ModernStyle)
        self.addPage(SetupIntroPage())
        self.folder_pages = []
        for key, title, description in WIZARD_STEPS:
            page = SetupFolderPage(key, title, description, current.get(key, ""))
            self.folder_pages.append(page)
            self.addPage(page)
        self.addPage(SetupFinishPage(self, playlist_folder))

    def results(self):
        return {page.key: page.path() for page in self.folder_pages}


# ---------------------------------------------------------------------------
# Tagging: fills in missing licensing tags (album, record label, ISRC) from MusicBrainz, using the
# artist and title already in the file. No account is needed. Existing tags are never changed.
# ---------------------------------------------------------------------------

LICENSE_FIELDS = ("artist", "title", "album", "label", "isrc")
TAG_MIN_SCORE = 95                      # MusicBrainz search score needed before a match is trusted
TAG_REQUEST_GAP_SECONDS = 1.1           # MusicBrainz asks for no more than one request per second
MUSICBRAINZ_URL = "https://musicbrainz.org/ws/2/"


def tag_checked_path():
    return os.path.join(get_logs_folder(), "tag_checked.json")


def _first(values):
    if isinstance(values, (list, tuple)):
        return str(values[0]).strip() if values else ""
    return str(values).strip() if values is not None else ""


def read_licensing_tags(path):
    """Artist, title, album, record label and ISRC as stored in the file (blank when missing)."""
    tags = {key: "" for key in LICENSE_FIELDS}
    tags["year"] = ""
    if not (MUTAGEN_AVAILABLE and path and os.path.isfile(path)):
        return tags
    try:
        audio = mutagen.File(path, easy=True)
        easy = audio.tags if audio is not None else None
        if easy:
            tags["artist"] = _first(easy.get("artist"))
            tags["title"] = _first(easy.get("title"))
            tags["album"] = _first(easy.get("album"))
            tags["isrc"] = _first(easy.get("isrc"))
            tags["label"] = _first(easy.get("organization")) or _first(easy.get("label"))
            tags["year"] = _first(easy.get("date"))
    except Exception:
        pass
    if path.lower().endswith((".m4a", ".mp4", ".aac")):
        try:
            from mutagen.mp4 import MP4 as _MP4
            mp4 = _MP4(path)
            for key, atom in (("label", "----:com.apple.iTunes:LABEL"), ("isrc", "----:com.apple.iTunes:ISRC")):
                if not tags[key] and atom in (mp4.tags or {}):
                    raw = mp4.tags[atom][0]
                    tags[key] = (raw.decode("utf-8", "replace") if isinstance(raw, (bytes, bytearray)) else str(raw)).strip()
        except Exception:
            pass
    return tags


def tags_complete(tags):
    return all(tags.get(key) for key in LICENSE_FIELDS)


def _normal(text):
    return re.sub(r"[^a-z0-9]+", " ", (text or "").lower()).strip()


_last_request = [0.0]


def _musicbrainz_get(path_and_query):
    wait = TAG_REQUEST_GAP_SECONDS - (time.monotonic() - _last_request[0])
    if wait > 0:
        time.sleep(wait)
    _last_request[0] = time.monotonic()
    request = urllib.request.Request(
        MUSICBRAINZ_URL + path_and_query,
        headers={"User-Agent": f"VisionStudio/{APP_VERSION} (https://github.com/deejaymnunez/VisionStudio)",
                 "Accept": "application/json"})
    with urllib.request.urlopen(request, timeout=20) as response:
        return json.loads(response.read().decode("utf-8", "replace"))


def lookup_musicbrainz(artist, title, album=""):
    """Returns {'album','label','isrc','year'} for a confident match, or None. Raises on network errors."""
    query = f'recording:"{title}" AND artist:"{artist}"'
    data = _musicbrainz_get("recording/?" + urllib.parse.urlencode({"query": query, "fmt": "json", "limit": 5}))
    best = None
    for rec in data.get("recordings", []):
        try:
            score = int(rec.get("score", 0))
        except Exception:
            score = 0
        if score < TAG_MIN_SCORE or _normal(rec.get("title")) != _normal(title):
            continue
        credit = " ".join(str(c.get("name", "")) + str(c.get("joinphrase", ""))
                          for c in rec.get("artist-credit", []) if isinstance(c, dict))
        if _normal(credit) != _normal(artist) and _normal(artist) not in _normal(credit):
            continue
        best = rec
        break
    if best is None:
        return None
    result = {"album": "", "label": "", "isrc": "", "year": ""}
    isrcs = best.get("isrcs") or []
    if isrcs:
        first = isrcs[0]
        result["isrc"] = (first.get("id", "") if isinstance(first, dict) else str(first)).strip()
    releases = best.get("releases") or []
    chosen = None
    if album:
        for rel in releases:
            if _normal(rel.get("title")) == _normal(album):
                chosen = rel
                break
    if chosen is None:
        official = [r for r in releases if str(r.get("status", "")).lower() == "official"]
        chosen = (official or releases or [None])[0]
    if chosen is not None:
        result["album"] = str(chosen.get("title", "")).strip()
        result["year"] = str(chosen.get("date", ""))[:4]
        try:
            rel_data = _musicbrainz_get(f"release/{chosen['id']}?" + urllib.parse.urlencode({"inc": "labels", "fmt": "json"}))
            for info in rel_data.get("label-info", []):
                name = (info.get("label") or {}).get("name", "")
                if name:
                    result["label"] = str(name).strip()
                    break
        except Exception:
            pass
    if not result["isrc"] and best.get("id"):
        try:
            rec_data = _musicbrainz_get(f"recording/{best['id']}?" + urllib.parse.urlencode({"inc": "isrcs", "fmt": "json"}))
            codes = rec_data.get("isrcs") or []
            if codes:
                result["isrc"] = str(codes[0]).strip()
        except Exception:
            pass
    return result


def write_missing_tags(path, values):
    """Writes only the fields in `values` (callers pass blanks only). Returns the list of fields written."""
    values = {k: v for k, v in values.items() if v}
    if not values or not MUTAGEN_AVAILABLE:
        return []
    ext = os.path.splitext(path)[1].lower()
    written = []
    if ext == ".mp3":
        from mutagen.id3 import ID3, ID3NoHeaderError, TPE1, TIT2, TALB, TPUB, TSRC, TDRC
        try:
            id3 = ID3(path)
        except ID3NoHeaderError:
            id3 = ID3()
        frames = {"artist": TPE1, "title": TIT2, "album": TALB, "label": TPUB, "isrc": TSRC, "year": TDRC}
        for key, cls in frames.items():
            if values.get(key):
                id3.add(cls(encoding=3, text=[values[key]]))
                written.append(key)
        if written:
            id3.save(path, v2_version=3)
    elif ext in (".flac", ".ogg", ".opus"):
        audio = mutagen.File(path)
        if audio is None:
            return []
        names = {"artist": "artist", "title": "title", "album": "album", "label": "label", "isrc": "isrc", "year": "date"}
        for key, name in names.items():
            if values.get(key):
                audio[name] = [values[key]]
                written.append(key)
        if written:
            audio.save()
    elif ext in (".m4a", ".mp4", ".aac"):
        from mutagen.mp4 import MP4 as _MP4, MP4FreeForm
        mp4 = _MP4(path)
        if mp4.tags is None:
            mp4.add_tags()
        atoms = {"artist": "\xa9ART", "title": "\xa9nam", "album": "\xa9alb", "year": "\xa9day"}
        for key, atom in atoms.items():
            if values.get(key):
                mp4.tags[atom] = [values[key]]
                written.append(key)
        for key, atom in (("label", "----:com.apple.iTunes:LABEL"), ("isrc", "----:com.apple.iTunes:ISRC")):
            if values.get(key):
                mp4.tags[atom] = [MP4FreeForm(values[key].encode("utf-8"))]
                written.append(key)
        if written:
            mp4.save()
    return written


def tag_one_file(path, lookup=lookup_musicbrainz, writer=write_missing_tags):
    """Returns (status, detail). Statuses: complete, no_tags, no_match, tagged, nothing_new, error."""
    tags = read_licensing_tags(path)
    if tags_complete(tags):
        return "complete", ""
    if not (tags["artist"] and tags["title"]):
        return "no_tags", "needs an artist and title in the file first"
    try:
        found = lookup(tags["artist"], tags["title"], tags["album"])
    except Exception as e:
        return "error", f"lookup failed: {e}"
    if not found:
        return "no_match", ""
    fill = {key: found.get(key, "") for key in ("album", "label", "isrc") if not tags.get(key)}
    if not tags.get("year") and found.get("year"):
        fill["year"] = found["year"]
    fill = {k: v for k, v in fill.items() if v}
    if not fill:
        return "nothing_new", ""
    try:
        written = writer(path, fill)
    except Exception as e:
        return "error", f"could not write tags: {e}"
    return ("tagged", ", ".join(written)) if written else ("nothing_new", "")


class LibraryTagger(QObject):
    """Walks the music library on a background thread and fills in missing tags. Safe to stop and
    start again: files that were checked and have not changed are not looked up twice."""

    progress = pyqtSignal(str)
    finished_scan = pyqtSignal(str)

    def __init__(self, busy_paths=None, lookup=lookup_musicbrainz, writer=write_missing_tags):
        super().__init__()
        self.busy_paths = busy_paths or (lambda: set())
        self.lookup = lookup
        self.writer = writer
        self.thread = None
        self.stop_flag = threading.Event()
        self.running = False

    def start(self, folder):
        if self.running or not folder or not os.path.isdir(folder):
            return False
        if not MUTAGEN_AVAILABLE:
            self.progress.emit("Tagging needs the mutagen library, which was not found.")
            return False
        self.stop_flag.clear()
        self.running = True
        self.thread = threading.Thread(target=self._run, args=(folder,), daemon=True)
        self.thread.start()
        return True

    def stop(self):
        self.stop_flag.set()

    def _load_checked(self):
        try:
            with open(tag_checked_path(), "r", encoding="utf-8") as handle:
                return json.load(handle)
        except Exception:
            return {}

    def _save_checked(self, checked):
        try:
            with open(tag_checked_path(), "w", encoding="utf-8") as handle:
                json.dump(checked, handle)
        except Exception:
            pass

    def _run(self, folder):
        counts = {"complete": 0, "tagged": 0, "no_match": 0, "no_tags": 0, "nothing_new": 0, "error": 0, "skipped": 0}
        checked = self._load_checked()
        files = []
        try:
            for root, _dirs, names in os.walk(folder):
                for name in names:
                    if name.lower().endswith(SUPPORTED_AUDIO):
                        files.append(os.path.join(root, name))
        except Exception:
            pass
        total = len(files)
        network_failures = 0
        for number, path in enumerate(files, 1):
            if self.stop_flag.is_set():
                break
            try:
                mtime = os.path.getmtime(path)
            except OSError:
                continue
            if checked.get(path) == mtime:
                counts["skipped"] += 1
                continue
            if path in self.busy_paths():
                counts["skipped"] += 1
                continue
            status, detail = tag_one_file(path, self.lookup, self.writer)
            counts[status] = counts.get(status, 0) + 1
            if status == "tagged":
                RUN_LOG.write("TAG", f"{os.path.basename(path)}: added {detail}")
                try:
                    checked[path] = os.path.getmtime(path)
                except OSError:
                    pass
            elif status in ("complete", "no_match", "no_tags", "nothing_new"):
                checked[path] = mtime
            elif status == "error":
                network_failures += 1
                if network_failures >= 5:
                    self.progress.emit("Tagging stopped: the lookup service could not be reached.")
                    break
            if number % 25 == 0 or status == "tagged":
                self.progress.emit(f"Tagging: checked {number} of {total} files, {counts['tagged']} updated.")
                self._save_checked(checked)
        self._save_checked(checked)
        summary = (f"Tagging finished: {counts['tagged']} files updated, {counts['complete']} already complete, "
                   f"{counts['no_match']} not found in the database, {counts['no_tags']} without an artist and title, "
                   f"{counts['error']} errors.")
        if self.stop_flag.is_set():
            summary = "Tagging stopped. " + summary
        RUN_LOG.write("TAG", summary)
        self.running = False
        self.finished_scan.emit(summary)


# ---------------------------------------------------------------------------
# Live-show recording: the program mix is written to one MP3 (128 or 320 kbps), with an optional
# cue sheet (.cue) and a licensing list (.csv) listing artist, title, album, label and ISRC.
# ---------------------------------------------------------------------------

RECORD_BITRATES = (128, 320)


def cue_timestamp(seconds):
    """mm:ss:ff where ff is 75ths of a second, as cue sheets require."""
    seconds = max(0.0, float(seconds))
    total_frames = int(seconds * 75)
    minutes, rest = divmod(total_frames, 75 * 60)
    secs, frames = divmod(rest, 75)
    return f"{minutes:02d}:{secs:02d}:{frames:02d}"


def clock_timestamp(seconds):
    seconds = int(max(0.0, float(seconds)))
    return f"{seconds // 3600:02d}:{(seconds % 3600) // 60:02d}:{seconds % 60:02d}"


def _cue_text(text):
    return str(text or "").replace('"', "'")


def build_cue_sheet(mp3_name, entries, show_title="Vision Studio recording"):
    """entries: list of dicts with start (seconds), kind ('music' or 'other'), artist, title, album,
    label, isrc. Non-music items are written as labeled tracks so the times line up with the file."""
    lines = [f'REM GENERATOR "Vision Studio {APP_VERSION}"',
             f'TITLE "{_cue_text(show_title)}"',
             f'FILE "{_cue_text(mp3_name)}" MP3']
    for number, entry in enumerate(entries, 1):
        lines.append(f"  TRACK {number:02d} AUDIO")
        if entry.get("kind") == "music":
            lines.append(f'    TITLE "{_cue_text(entry.get("title"))}"')
            lines.append(f'    PERFORMER "{_cue_text(entry.get("artist"))}"')
            lines.append(f'    REM ALBUM "{_cue_text(entry.get("album"))}"')
            if entry.get("label"):
                lines.append(f'    REM LABEL "{_cue_text(entry.get("label"))}"')
            isrc = re.sub(r"[^A-Za-z0-9]", "", str(entry.get("isrc") or "")).upper()
            if len(isrc) == 12:
                lines.append(f"    ISRC {isrc}")
            elif isrc:
                lines.append(f'    REM ISRC "{isrc}"')
        else:
            lines.append(f'    TITLE "{_cue_text(entry.get("title"))}"')
            lines.append('    REM TYPE "not music"')
        lines.append(f"    INDEX 01 {cue_timestamp(entry.get('start', 0))}")
    return "\n".join(lines) + "\n"


def build_licensing_csv(entries):
    import csv
    import io
    buffer = io.StringIO()
    writer = csv.writer(buffer, lineterminator="\r\n")
    writer.writerow(["Start", "Type", "Artist", "Title", "Album", "Record label", "ISRC"])
    for entry in entries:
        writer.writerow([clock_timestamp(entry.get("start", 0)),
                         "music" if entry.get("kind") == "music" else "not music",
                         entry.get("artist", ""), entry.get("title", ""), entry.get("album", ""),
                         entry.get("label", ""), entry.get("isrc", "")])
    return buffer.getvalue()


class ProgramRecorder(QObject):
    """Records whatever the stream mixer is producing. It is fed by the mixer like an encoder is."""

    message = pyqtSignal(str)
    state_changed = pyqtSignal(bool)

    def __init__(self, settings):
        super().__init__()
        self.settings = settings
        self.mixer = None
        self.process = None
        self.feed_queue = None
        self.writer_thread = None
        self.stderr_tail = deque(maxlen=6)
        self.recording = False
        self.started_by_schedule = False
        self.started_at = 0.0
        self.entries = []
        self.mp3_path = ""
        self.cue_on = False

    # --- settings ---
    def bitrate(self):
        try:
            value = int(float(self.settings.value("record_bitrate", 0)))
        except Exception:
            value = 0
        return value if value in RECORD_BITRATES else 0

    def cue_enabled(self):
        return str(self.settings.value("record_cue", "false")).lower() == "true"

    def folder(self):
        chosen = str(self.settings.value("recordings_folder", "") or "").strip()
        return chosen or get_recordings_folder()

    def setup_done(self):
        return str(self.settings.value("record_setup_done", "false")).lower() == "true" and self.bitrate() != 0

    # --- command line ---
    def build_command(self, mp3_path, bitrate):
        return [get_ffmpeg_path(), "-hide_banner", "-loglevel", "warning", "-y",
                "-f", "s16le", "-ar", str(STREAM_SAMPLE_RATE), "-ac", str(STREAM_CHANNELS), "-i", "pipe:0",
                "-vn", "-acodec", "libmp3lame", "-b:a", f"{bitrate}k",
                "-ar", str(STREAM_SAMPLE_RATE), "-ac", str(STREAM_CHANNELS),
                "-id3v2_version", "3", "-metadata", f"title=Vision Studio recording {time.strftime('%Y-%m-%d %H:%M')}",
                "-f", "mp3", mp3_path]

    # --- start / stop ---
    def start(self, mixer, current_meta=None, by_schedule=False, current_path=None):
        """Returns (ok, message)."""
        if self.recording:
            return True, "Already recording."
        bitrate = self.bitrate()
        if not bitrate:
            return False, "Choose a recording bitrate first."
        if mixer is None or not mixer.available:
            reason = mixer.unavailable_reason() if mixer is not None else "no mixer"
            return False, f"Recording needs the live mix, which is unavailable ({reason})."
        folder = self.folder()
        try:
            os.makedirs(folder, exist_ok=True)
        except OSError as e:
            return False, f"The recordings folder cannot be used: {e}"
        base = time.strftime("Recording_%Y-%m-%d_%H%M%S")
        self.mp3_path = os.path.join(folder, base + ".mp3")
        copy = 2
        while os.path.exists(self.mp3_path):
            self.mp3_path = os.path.join(folder, f"{base}_{copy}.mp3")
            copy += 1
        try:
            self.process = subprocess.Popen(
                self.build_command(self.mp3_path, bitrate), stdin=subprocess.PIPE,
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, creationflags=SUBPROCESS_FLAGS)
        except FileNotFoundError:
            self.process = None
            return False, "Recording cannot start: ffmpeg was not found."
        except Exception as e:
            self.process = None
            return False, f"Recording cannot start: {e}"
        self.stderr_tail.clear()
        threading.Thread(target=self._drain_stderr, args=(self.process,), daemon=True).start()
        self.feed_queue = queue.Queue(maxsize=400)
        self.writer_thread = threading.Thread(target=self._writer_loop, args=(self.process, self.feed_queue), daemon=True)
        self.writer_thread.start()
        self.entries = []
        self.cue_on = self.cue_enabled()
        self.started_at = time.monotonic()
        self.started_by_schedule = by_schedule
        self.recording = True
        self.mixer = mixer
        mixer.register_encoder(self)
        if current_meta:
            self.note_track(current_meta, current_path)
        self.state_changed.emit(True)
        RUN_LOG.write("RECORD", f"Recording started at {bitrate} kbps: {self.mp3_path}")
        return True, f"Recording started at {bitrate} kbps."

    def _drain_stderr(self, proc):
        try:
            for line in iter(proc.stderr.readline, b""):
                text = line.decode("utf-8", "replace").strip()
                if text:
                    self.stderr_tail.append(text)
        except Exception:
            pass

    def _writer_loop(self, proc, feed_queue):
        try:
            while True:
                data = feed_queue.get()
                if data is None:
                    break
                proc.stdin.write(data)
        except Exception:
            pass
        try:
            proc.stdin.close()
        except Exception:
            pass

    def feed(self, data):
        """Called by the mixer with 20 ms of program audio."""
        queue_ = self.feed_queue
        if queue_ is None:
            return
        try:
            queue_.put_nowait(data)
        except queue.Full:
            pass

    def elapsed(self):
        return time.monotonic() - self.started_at if self.recording else 0.0

    def stop(self, wait=False):
        """Finishes the file cleanly. With wait=True the call returns once ffmpeg has closed it."""
        if not self.recording:
            return ""
        self.recording = False
        mixer, self.mixer = self.mixer, None
        if mixer is not None:
            try:
                mixer.unregister_encoder(self)
            except Exception:
                pass
        proc, feed_queue, writer = self.process, self.feed_queue, self.writer_thread
        self.process = self.feed_queue = self.writer_thread = None
        path = self.mp3_path
        try:
            feed_queue.put(None, timeout=1)
        except Exception:
            pass
        self.write_cue_files()

        def finalize():
            try:
                if writer is not None:
                    writer.join(timeout=15)
                if proc is not None:
                    try:
                        proc.wait(timeout=20)
                    except Exception:
                        proc.kill()
            except Exception:
                pass

        if wait:
            finalize()
        else:
            threading.Thread(target=finalize, daemon=True).start()
        self.state_changed.emit(False)
        RUN_LOG.write("RECORD", f"Recording stopped: {path}")
        return path

    # --- cue sheet ---
    def note_track(self, meta, path=None):
        """Called when a song starts on air."""
        if not self.recording:
            return
        tags = read_licensing_tags(path) if path else {}
        entry = {"start": self.elapsed(), "kind": "music",
                 "artist": meta.get("artist") or tags.get("artist", ""),
                 "title": meta.get("title") or tags.get("title", ""),
                 "album": meta.get("album") or tags.get("album", ""),
                 "label": tags.get("label", ""), "isrc": tags.get("isrc", "")}
        self.entries.append(entry)
        self.write_cue_files()

    def note_other(self, label):
        """Called when a jingle, commercial or voice break starts."""
        if not self.recording:
            return
        self.entries.append({"start": self.elapsed(), "kind": "other", "title": label})
        self.write_cue_files()

    def write_cue_files(self):
        if not self.cue_on or not self.mp3_path:
            return
        base = os.path.splitext(self.mp3_path)[0]
        try:
            with open(base + ".cue", "w", encoding="utf-8") as handle:
                handle.write(build_cue_sheet(os.path.basename(self.mp3_path), self.entries))
            with open(base + ".csv", "w", encoding="utf-8-sig", newline="") as handle:
                handle.write(build_licensing_csv(self.entries))
        except OSError as e:
            self.message.emit(f"The cue sheet could not be written: {e}")


# ---------------------------------------------------------------------------
# Live-show recording times (entirely optional; the list is empty until you add a show)
# ---------------------------------------------------------------------------

WEEKDAY_NAMES = ("Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday")


def parse_clock(text):
    match = re.fullmatch(r"\s*(\d{1,2}):?(\d{2})\s*", str(text))
    if not match:
        return None
    hour, minute = int(match.group(1)), int(match.group(2))
    if hour > 23 or minute > 59:
        return None
    return hour * 60 + minute


def load_show_times(settings):
    try:
        data = json.loads(str(settings.value("record_shows", "[]")))
    except Exception:
        return []
    shows = []
    for item in data if isinstance(data, list) else []:
        try:
            start, end = parse_clock(item["start"]), parse_clock(item["end"])
            days = [int(d) for d in item.get("days", [])]
            if start is None or end is None or not days or start == end:
                continue
            shows.append({"name": str(item.get("name", "Live show")), "days": days,
                          "start": start, "end": end, "enabled": bool(item.get("enabled", True))})
        except Exception:
            continue
    return shows


def save_show_times(settings, shows):
    def clock(minutes):
        return f"{minutes // 60:02d}:{minutes % 60:02d}"
    settings.setValue("record_shows", json.dumps(
        [{"name": s["name"], "days": s["days"], "start": clock(s["start"]), "end": clock(s["end"]),
          "enabled": s.get("enabled", True)} for s in shows]))


def active_show(shows, now):
    """The show whose time window contains `now`, as (index, window_key), or None. Windows that run past
    midnight belong to the day they started on."""
    minutes = now.hour * 60 + now.minute
    weekday = now.weekday()
    for index, show in enumerate(shows):
        if not show.get("enabled", True):
            continue
        if show["start"] < show["end"]:
            if weekday in show["days"] and show["start"] <= minutes < show["end"]:
                return index, f"{index}:{now.date()}"
        else:
            if weekday in show["days"] and minutes >= show["start"]:
                return index, f"{index}:{now.date()}"
            if (weekday - 1) % 7 in show["days"] and minutes < show["end"]:
                return index, f"{index}:{(now - timedelta(days=1)).date()}"
    return None


class ShowRecordingController:
    """Decides, once every few seconds, whether the schedule wants recording on or off. Pressing R
    during a show wins: the schedule will not start that same show again."""

    def __init__(self):
        self.suppressed_window = None
        self.schedule_window = None

    def decide(self, shows, now, recording, started_by_schedule):
        active = active_show(shows, now)
        key = active[1] if active else None
        if self.schedule_window and key != self.schedule_window:
            self.schedule_window = None
        if not recording:
            if key and key != self.suppressed_window:
                self.schedule_window = key
                return "start", shows[active[0]]["name"]
            if not key:
                self.suppressed_window = None
            return None, ""
        if started_by_schedule and not key:
            return "stop", ""
        return None, ""

    def user_stopped(self, current_key=None):
        """R was pressed to stop during a scheduled window: the schedule leaves that show alone."""
        key = current_key or self.schedule_window
        if key:
            self.suppressed_window = key


class FirstRecordingSetupDialog(QDialog):
    """Asked once, before the first recording: bitrate, and whether to write a cue sheet."""

    def __init__(self, parent, bitrate=128, cue=False):
        super().__init__(parent)
        self.setWindowTitle("Recording setup")
        self.setModal(True)
        layout = QVBoxLayout()
        intro = QLabel("Before the first recording, choose how recordings are made. You can change these "
                       "later in Settings, in the Recording section.")
        intro.setWordWrap(True)
        layout.addWidget(intro)
        form = QFormLayout()
        self.bitrate_combo = QComboBox()
        self.bitrate_combo.setAccessibleName("Recording bitrate")
        self.bitrate_combo.addItem("128 kbps (smaller files)", 128)
        self.bitrate_combo.addItem("320 kbps (best quality, for podcast platforms)", 320)
        self.bitrate_combo.setCurrentIndex(1 if int(bitrate) == 320 else 0)
        form.addRow("Bitrate:", self.bitrate_combo)
        layout.addLayout(form)
        self.cue_check = QCheckBox("Write a cue sheet (artist, title, album, label and ISRC for each song)")
        self.cue_check.setChecked(bool(cue))
        layout.addWidget(self.cue_check)
        buttons = QHBoxLayout()
        ok = QPushButton("Save And Continue")
        ok.setDefault(True)
        ok.clicked.connect(self.accept)
        cancel = QPushButton("Cancel")
        cancel.clicked.connect(self.reject)
        buttons.addWidget(ok)
        buttons.addWidget(cancel)
        layout.addLayout(buttons)
        self.setLayout(layout)

    def chosen_bitrate(self):
        return int(self.bitrate_combo.currentData())

    def chosen_cue(self):
        return self.cue_check.isChecked()


class ShowTimeDialog(QDialog):
    """Adds one live show: a name, the days it airs, and when recording starts and stops."""

    def __init__(self, parent):
        super().__init__(parent)
        self.setWindowTitle("Add a live show")
        self.setModal(True)
        layout = QVBoxLayout()
        form = QFormLayout()
        self.name_edit = QLineEdit("Live show")
        self.name_edit.setAccessibleName("Show name")
        form.addRow("Show name:", self.name_edit)
        self.start_edit = QLineEdit("20:00")
        self.start_edit.setAccessibleName("Recording starts at, hours and minutes, 24 hour clock")
        form.addRow("Start recording at (HH:MM):", self.start_edit)
        self.end_edit = QLineEdit("22:00")
        self.end_edit.setAccessibleName("Recording stops at, hours and minutes, 24 hour clock")
        form.addRow("Stop recording at (HH:MM):", self.end_edit)
        layout.addLayout(form)
        self.day_checks = []
        for number, name in enumerate(WEEKDAY_NAMES):
            check = QCheckBox(name)
            check.setChecked(number < 5)
            self.day_checks.append(check)
            layout.addWidget(check)
        self.error_label = QLabel("")
        self.error_label.setWordWrap(True)
        layout.addWidget(self.error_label)
        buttons = QHBoxLayout()
        ok = QPushButton("Add Show")
        ok.setDefault(True)
        ok.clicked.connect(self.try_accept)
        cancel = QPushButton("Cancel")
        cancel.clicked.connect(self.reject)
        buttons.addWidget(ok)
        buttons.addWidget(cancel)
        layout.addLayout(buttons)
        self.setLayout(layout)

    def try_accept(self):
        start, end = parse_clock(self.start_edit.text()), parse_clock(self.end_edit.text())
        if start is None or end is None or start == end:
            self.error_label.setText("Enter two different times like 20:00 and 22:00.")
            return
        if not any(c.isChecked() for c in self.day_checks):
            self.error_label.setText("Choose at least one day.")
            return
        self.accept()

    def show_entry(self):
        return {"name": self.name_edit.text().strip() or "Live show",
                "days": [i for i, c in enumerate(self.day_checks) if c.isChecked()],
                "start": parse_clock(self.start_edit.text()), "end": parse_clock(self.end_edit.text()),
                "enabled": True}


def describe_show(show):
    def clock(minutes):
        return f"{minutes // 60:02d}:{minutes % 60:02d}"
    days = ", ".join(WEEKDAY_NAMES[d][:3] for d in sorted(show["days"]))
    return f"{show['name']}: {days}, {clock(show['start'])} to {clock(show['end'])}"


# ---------------------------------------------------------------------------
# Schedule screens: hour detail, dated schedules, and voice tracking one hour at a time
# ---------------------------------------------------------------------------

def time_label(minutes):
    return datetime(2000, 1, 1, minutes // 60 % 24, minutes % 60).strftime("%I:%M %p").lstrip("0")


def date_label(day):
    return day.strftime("%A, %B %d, %Y")


class HourDetailDialog(QDialog):
    """One hour of the everyday schedule: its rotation, which break marks run, and where the change applies."""

    def __init__(self, app, hour):
        super().__init__(app)
        self.app = app
        self.hour = hour
        self.setWindowTitle(f"Schedule for {hour_label(hour)}")
        self.setModal(True)
        layout = QVBoxLayout()
        library = app.rotation_library
        self.rotation_combo = QComboBox()
        self.rotation_combo.setAccessibleName("Rotation for this hour")
        for rotation in library.rotations:
            self.rotation_combo.addItem(rotation.name, rotation.id)
        current = app.rotation_schedule.hours[hour % 24]
        self.rotation_combo.setCurrentIndex(max(0, self.rotation_combo.findData(current)))
        form = QFormLayout()
        form.addRow("Rotation:", self.rotation_combo)
        self.scope_combo = QComboBox()
        self.scope_combo.setAccessibleName("Where this change applies")
        self.scope_combo.addItem("This hour only", "hour")
        self.scope_combo.addItem("Entire schedule (all 24 hours)", "all")
        self.scope_combo.addItem("A range of hours", "range")
        form.addRow("Apply to:", self.scope_combo)
        self.from_combo, self.to_combo = QComboBox(), QComboBox()
        for combo, name in ((self.from_combo, "First hour of the range"), (self.to_combo, "Last hour of the range")):
            combo.setAccessibleName(name)
            for h in range(24):
                combo.addItem(hour_label(h), h)
        self.from_combo.setCurrentIndex(hour % 24)
        self.to_combo.setCurrentIndex(hour % 24)
        form.addRow("Range from:", self.from_combo)
        form.addRow("Range to:", self.to_combo)
        layout.addLayout(form)
        marks_label = QLabel("Breaks (jingle, ads, jingle) that run in this hour:")
        layout.addWidget(marks_label)
        self.mark_checks = []
        flags = app.break_marks.grid[hour % 24]
        for slot, flag in zip(BreakMarks.SLOTS, flags):
            check = QCheckBox(f"{slot} break")
            check.setChecked(bool(flag))
            self.mark_checks.append(check)
            layout.addWidget(check)
        summary = QLabel(self.summary_text())
        summary.setWordWrap(True)
        summary.setAccessibleName("What plays in this hour")
        layout.addWidget(summary)
        buttons = QHBoxLayout()
        ok = QPushButton("Apply")
        ok.setDefault(True)
        ok.clicked.connect(self.apply)
        cancel = QPushButton("Close")
        cancel.clicked.connect(self.reject)
        buttons.addWidget(ok)
        buttons.addWidget(cancel)
        layout.addLayout(buttons)
        self.setLayout(layout)

    def summary_text(self):
        app = self.app
        lines = []
        day = datetime.now().date()
        event = app.event_library.event_for_hour(day, self.hour)
        if event is not None:
            lines.append(f"Today this hour is covered by the dated schedule {event['name']}.")
        jingles = [c["name"] for c in app.category_library.categories
                   if c["type"] in ("jingle", "sweeper") and app.category_library.is_active(c)]
        ads = [c["name"] for c in app.category_library.categories
               if c["type"] == "ad" and app.category_library.is_active(c)]
        lines.append("Jingle categories: " + (", ".join(jingles) if jingles else "the jingle folders set for each mark"))
        lines.append("Ad categories: " + (", ".join(ads) if ads else "the commercials folder"))
        return "\n".join(lines)

    def hours_in_scope(self):
        scope = self.scope_combo.currentData()
        if scope == "all":
            return list(range(24))
        if scope == "range":
            first, last = self.from_combo.currentData(), self.to_combo.currentData()
            if first <= last:
                return list(range(first, last + 1))
            return list(range(first, 24)) + list(range(0, last + 1))     # a range that crosses midnight
        return [self.hour]

    def apply(self):
        rotation_id = self.rotation_combo.currentData()
        flags = [c.isChecked() for c in self.mark_checks]
        hours = self.hours_in_scope()
        for h in hours:
            if rotation_id:
                self.app.rotation_schedule.hours[h % 24] = rotation_id
            self.app.break_marks.grid[h % 24] = [1 if f else 0 for f in flags]
        self.app.rotation_schedule.save()
        self.app.break_marks.save()
        self.accept()
        self.app.schedule_tab.refresh()
        self.app.rotation.check_rotation_for_hour()
        self.app.announce(f"Schedule updated for {len(hours)} hour(s).")


class EventDialog(QDialog):
    """A dated schedule: when it starts and ends, what plays, and whether it comes back every year."""

    def __init__(self, app, event):
        super().__init__(app)
        self.app = app
        self.event = event
        self.setWindowTitle(f"Dated schedule: {event.get('name', '')}")
        self.setModal(True)
        layout = QVBoxLayout()
        form = QFormLayout()
        self.name_edit = QLineEdit(event.get("name", ""))
        self.name_edit.setAccessibleName("Schedule name")
        form.addRow("Name:", self.name_edit)

        self.rotation_combo = QComboBox()
        self.rotation_combo.setAccessibleName("Rotation to play")
        for rotation in app.rotation_library.rotations:
            self.rotation_combo.addItem(rotation.name, rotation.id)
        self.rotation_combo.setCurrentIndex(max(0, self.rotation_combo.findData(event.get("rotation_id"))))
        form.addRow("Rotation:", self.rotation_combo)

        self.jingle_combo = QComboBox()
        self.jingle_combo.setAccessibleName("Jingles for this schedule")
        self.jingle_combo.addItem("The regular jingles", None)
        for c in app.category_library.categories:
            if c["type"] in ("jingle", "sweeper"):
                self.jingle_combo.addItem(c["name"], c["id"])
        self.jingle_combo.setCurrentIndex(max(0, self.jingle_combo.findData(event.get("jingle_category_id"))))
        form.addRow("Jingles:", self.jingle_combo)
        self.ad_combo = QComboBox()
        self.ad_combo.setAccessibleName("Ads for this schedule")
        self.ad_combo.addItem("The regular ads", None)
        for c in app.category_library.categories:
            if c["type"] == "ad":
                self.ad_combo.addItem(c["name"], c["id"])
        self.ad_combo.setCurrentIndex(max(0, self.ad_combo.findData(event.get("ad_category_id"))))
        form.addRow("Ads:", self.ad_combo)

        start = parse_moment(event.get("start")) or datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
        end = parse_moment(event.get("end")) or start.replace(hour=23, minute=45)
        self.start_date, self.start_time = QComboBox(), QComboBox()
        self.end_date, self.end_time = QComboBox(), QComboBox()
        today = datetime.now().date()
        days = [today + timedelta(days=i) for i in range(731)]
        for needed in (start.date(), end.date()):
            if needed not in days:
                days.append(needed)
        days.sort()
        for combo, name in ((self.start_date, "Start date"), (self.end_date, "End date")):
            combo.setAccessibleName(name)
            for day in days:
                combo.addItem(date_label(day), day)
        for combo, name in ((self.start_time, "Start time"), (self.end_time, "End time")):
            combo.setAccessibleName(name)
            for minutes in range(0, 24 * 60, 15):
                combo.addItem(time_label(minutes), minutes)
        self.start_date.setCurrentIndex(self.start_date.findData(start.date()))
        self.end_date.setCurrentIndex(self.end_date.findData(end.date()))
        self.start_time.setCurrentIndex(self.start_time.findData(start.hour * 60 + start.minute // 15 * 15))
        self.end_time.setCurrentIndex(self.end_time.findData(end.hour * 60 + end.minute // 15 * 15))
        form.addRow("Start date:", self.start_date)
        form.addRow("Start time:", self.start_time)
        form.addRow("End date:", self.end_date)
        form.addRow("End time:", self.end_time)
        layout.addLayout(form)

        self.one_day_check = QCheckBox("Just one day (the end date follows the start date)")
        self.one_day_check.setChecked(bool(event.get("start")) and start.date() == end.date())
        self.one_day_check.toggled.connect(self.on_one_day)
        self.start_date.currentIndexChanged.connect(self.on_start_date_changed)
        layout.addWidget(self.one_day_check)
        self.repeat_check = QCheckBox("Repeat every year (it comes back by itself as the season gets close)")
        self.repeat_check.setChecked(bool(event.get("repeat")))
        layout.addWidget(self.repeat_check)
        voice_form = QFormLayout()
        self.voice_combo = QComboBox()
        self.voice_combo.setAccessibleName("Voice tracking")
        self.voice_combo.addItem("No voice tracking", False)
        self.voice_combo.addItem("Voice tracking: a voice track slot after every 3 songs", True)
        self.voice_combo.setCurrentIndex(1 if event.get("voice") else 0)
        voice_form.addRow("Voice tracking:", self.voice_combo)
        layout.addLayout(voice_form)
        layout.addWidget(QLabel("Breaks that run while this schedule is on:"))
        self.mark_checks = []
        marks = (list(event.get("marks", [1, 1, 1, 1])) + [1, 1, 1, 1])[:4]
        for slot, flag in zip(BreakMarks.SLOTS, marks):
            check = QCheckBox(f"{slot} break")
            check.setChecked(bool(flag))
            self.mark_checks.append(check)
            layout.addWidget(check)
        self.error_label = QLabel("")
        self.error_label.setWordWrap(True)
        self.error_label.setAccessibleName("Problems")
        layout.addWidget(self.error_label)
        buttons = QHBoxLayout()
        ok = QPushButton("Save Schedule")
        ok.setDefault(True)
        ok.clicked.connect(self.try_save)
        cancel = QPushButton("Cancel")
        cancel.clicked.connect(self.reject)
        buttons.addWidget(ok)
        buttons.addWidget(cancel)
        layout.addLayout(buttons)
        self.setLayout(layout)
        self.on_one_day(self.one_day_check.isChecked())

    def on_one_day(self, checked):
        self.end_date.setEnabled(not checked)
        if checked:
            self.end_date.setCurrentIndex(self.start_date.currentIndex())

    def on_start_date_changed(self, _index):
        if self.one_day_check.isChecked():
            self.end_date.setCurrentIndex(self.start_date.currentIndex())

    def build_values(self):
        s_day, e_day = self.start_date.currentData(), self.end_date.currentData()
        s_min, e_min = self.start_time.currentData(), self.end_time.currentData()
        start = datetime(s_day.year, s_day.month, s_day.day, s_min // 60, s_min % 60)
        end = datetime(e_day.year, e_day.month, e_day.day, e_min // 60, e_min % 60)
        return {"name": self.name_edit.text().strip() or "Dated schedule",
                "rotation_id": self.rotation_combo.currentData(),
                "jingle_category_id": self.jingle_combo.currentData(),
                "ad_category_id": self.ad_combo.currentData(),
                "start": format_moment(start), "end": format_moment(end),
                "repeat": self.repeat_check.isChecked(), "voice": bool(self.voice_combo.currentData()),
                "marks": [1 if c.isChecked() else 0 for c in self.mark_checks]}

    def try_save(self):
        values = self.build_values()
        probe = dict(self.event)
        probe.update(values)
        problem = self.app.event_library.validate(probe)
        if problem:
            self.error_label.setText(problem)
            return
        if not probe.get("rotation_id"):
            self.error_label.setText("Choose a rotation.")
            return
        self.event.update(values)
        self.accept()


class ScheduleTab(QWidget):
    """The everyday 24-hour schedule (press Enter on an hour for its detail) and the dated schedules."""

    def __init__(self, app):
        super().__init__()
        self.app = app
        layout = QVBoxLayout()
        self.live_label = QLabel("")
        self.live_label.setWordWrap(True)
        self.live_label.setStyleSheet(f"color: {COLOR_ON_AIR_GREEN}; font-weight: bold;")
        layout.addWidget(self.live_label)
        self.table = QTableWidget(24, 4)
        self.table.setHorizontalHeaderLabels(["Hour", "Rotation", "Breaks", "On air"])
        self.table.setAccessibleName("24 hour rotation schedule. Press Enter on an hour to change it.")
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        self.table.itemActivated.connect(lambda item: self.open_hour(item.row()))
        self.table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self.hour_menu)
        layout.addWidget(self.table)
        row = QHBoxLayout()
        self.rotation_combo = QComboBox()
        self.rotation_combo.setAccessibleName("Rotation to assign")
        row.addWidget(self.rotation_combo, 1)
        assign = QPushButton("Assign To Selected Hour")
        assign.setStyleSheet(BUTTON_STYLE_CONSOLE)
        assign.clicked.connect(self.assign_selected)
        row.addWidget(assign)
        assign_all = QPushButton("Assign To Entire Schedule")
        assign_all.setStyleSheet(BUTTON_STYLE_CONSOLE)
        assign_all.clicked.connect(self.assign_all)
        row.addWidget(assign_all)
        layout.addLayout(row)
        edit_hour = QPushButton("Edit Selected Hour (Enter)")
        edit_hour.setStyleSheet(BUTTON_STYLE_CONSOLE)
        edit_hour.clicked.connect(lambda: self.open_hour(self.table.currentRow()))
        layout.addWidget(edit_hour)
        regen = QPushButton("Regenerate Schedule Evenly")
        regen.setStyleSheet(BUTTON_STYLE_CONSOLE)
        regen.clicked.connect(self.regenerate)
        layout.addWidget(regen)

        heading = QLabel("Dated schedules: holidays and one-day shows. They replace the everyday schedule "
                         "between their dates, then it comes back by itself. Press Enter to edit.")
        heading.setWordWrap(True)
        layout.addWidget(heading)
        self.event_list = QListWidget()
        self.event_list.setAccessibleName("Dated schedules")
        self.event_list.itemActivated.connect(lambda _item: self.edit_event())
        layout.addWidget(self.event_list)
        buttons = QHBoxLayout()
        for text, handler in (("Add Dated Schedule", self.add_event), ("Edit Selected (Enter)", self.edit_event),
                              ("Remove Selected", self.remove_event)):
            btn = QPushButton(text)
            btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
            btn.clicked.connect(handler)
            buttons.addWidget(btn)
        layout.addLayout(buttons)
        self.setLayout(layout)
        self.refresh()

    # --- everyday schedule ---
    def refresh(self):
        now = datetime.now()
        now_hour = now.hour
        schedule = self.app.rotation_schedule
        library = self.app.rotation_library
        selected = self.table.currentRow()
        self.rotation_combo.clear()
        for rotation in library.rotations:
            self.rotation_combo.addItem(rotation.name, rotation.id)
        for hour in range(24):
            rotation = library.find(schedule.rotation_id_for(now.date(), hour))
            live = hour == now_hour
            flags = self.app.break_marks.grid[hour]
            marks = " ".join(s for s, f in zip(BreakMarks.SLOTS, flags) if f) or "none"
            cells = [hour_label(hour), rotation.name if rotation else "(none)", marks, "LIVE NOW" if live else ""]
            for col, text in enumerate(cells):
                item = QTableWidgetItem(text)
                if live:
                    font = item.font()
                    font.setBold(True)
                    item.setFont(font)
                    item.setForeground(QBrush(QColor(COLOR_ON_AIR_GREEN)))
                self.table.setItem(hour, col, item)
        self.table.setCurrentCell(selected if selected >= 0 else now_hour, 0)
        live_rotation = library.find(schedule.rotation_id_for(now.date(), now_hour))
        event = self.app.event_library.event_at(now)
        self.live_label.setText(f"On air now: {hour_label(now_hour)}, "
                                f"{live_rotation.name if live_rotation else 'no rotation'}"
                                + (f" (dated schedule: {event['name']})" if event else ""))
        self.live_label.setAccessibleName(self.live_label.text())
        self.refresh_events()

    def open_hour(self, hour):
        if 0 <= hour < 24:
            HourDetailDialog(self.app, hour).exec()
            self.table.setFocus()

    def hour_menu(self, position):
        menu = QMenu(self)
        row = self.table.currentRow()
        menu.addAction("Edit this hour...", lambda: self.open_hour(row))
        menu.addAction("Assign the chosen rotation to this hour", self.assign_selected)
        menu.addAction("Assign the chosen rotation to the entire schedule", self.assign_all)
        menu.exec(self.table.viewport().mapToGlobal(position))

    def assign_selected(self):
        hour = self.table.currentRow()
        rotation_id = self.rotation_combo.currentData()
        if hour >= 0 and rotation_id:
            self.app.rotation_schedule.set_hour(hour, rotation_id)
            self.refresh()
            self.app.rotation.check_rotation_for_hour()
            self.app.announce(f"Hour {hour_label(hour)} set.")

    def assign_all(self):
        rotation_id = self.rotation_combo.currentData()
        if rotation_id:
            for hour in range(24):
                self.app.rotation_schedule.hours[hour] = rotation_id
            self.app.rotation_schedule.save()
            self.refresh()
            self.app.rotation.check_rotation_for_hour()
            self.app.announce("The entire schedule now plays that rotation.")

    def regenerate(self):
        self.app.rotation_schedule.regenerate_even()
        self.refresh()
        self.app.rotation.check_rotation_for_hour()
        self.app.update_status("Schedule rebuilt evenly across the 24 hours.")

    # --- dated schedules ---
    def refresh_events(self):
        row = self.event_list.currentRow()
        self.event_list.clear()
        for event in self.app.event_library.events:
            self.event_list.addItem(self.app.event_library.describe(event))
        if self.event_list.count():
            self.event_list.setCurrentRow(max(0, min(row, self.event_list.count() - 1)))

    def selected_event(self):
        row = self.event_list.currentRow()
        events = self.app.event_library.events
        return events[row] if 0 <= row < len(events) else None

    def add_event(self):
        rotations = self.app.rotation_library.rotations
        draft = {"id": uuid.uuid4().hex[:8], "name": "New schedule", "rotation_id": rotations[0].id if rotations else None,
                 "jingle_category_id": None, "ad_category_id": None, "start": "", "end": "", "repeat": False,
                 "voice": False, "marks": [1, 1, 1, 1], "active": False, "created": time.time()}
        self.run_event_dialog(draft)

    def edit_event(self):
        event = self.selected_event()
        if event is not None:
            self.run_event_dialog(event)

    def run_event_dialog(self, event):
        if EventDialog(self.app, event).exec() != QDialog.DialogCode.Accepted:
            return
        library = self.app.event_library
        was_new = library.find(event["id"]) is None
        problem = library.save_event(event)
        if problem:
            self.app.announce(problem)
            return
        overlaps = library.overlaps(event)
        note = f" It overlaps {', '.join(overlaps)}; the one created last wins." if overlaps else ""
        self.app.announce(f"Schedule {event['name']} saved.{note}")
        self.app.on_events_changed(event)

    def remove_event(self):
        event = self.selected_event()
        if event is None:
            return
        answer = QMessageBox.question(self, "Remove schedule", f"Remove the schedule {event['name']}?")
        if answer == QMessageBox.StandardButton.Yes:
            self.app.event_library.remove(event["id"])
            self.app.announce("Schedule removed.")
            self.app.on_events_changed(None)


class VoiceTrackHourTab(QWidget):
    """Voice track one hour at a time: pick the date and the hour, record into each slot, save."""

    def __init__(self, app):
        super().__init__()
        self.app = app
        self.day = None
        self.hour = None
        self.path = None
        self.entries = []
        layout = QVBoxLayout()
        intro = QLabel("Voice tracking one hour at a time. Choose the date and the hour, press Load, select a "
                       "voice track slot and press Ctrl+T to record into it, then Save Hour. Saving fits the "
                       "last song so the hour ends on the top of the hour.")
        intro.setWordWrap(True)
        layout.addWidget(intro)
        form = QFormLayout()
        self.date_combo = QComboBox()
        self.date_combo.setAccessibleName("Date of the hour to voice track")
        today = datetime.now().date()
        for i in range(15):
            self.date_combo.addItem(date_label(today + timedelta(days=i)), today + timedelta(days=i))
        self.hour_combo = QComboBox()
        self.hour_combo.setAccessibleName("Hour to voice track")
        for h in range(24):
            self.hour_combo.addItem(time_label(h * 60), h)
        self.hour_combo.setCurrentIndex((datetime.now().hour + 1) % 24)
        form.addRow("Date:", self.date_combo)
        form.addRow("Hour:", self.hour_combo)
        layout.addLayout(form)
        self.list = QListWidget()
        self.list.setAccessibleName("Playlist for the chosen hour")
        layout.addWidget(self.list, 1)
        self.projected_label = QLabel("Choose a date and hour, then press Load This Hour.")
        self.projected_label.setWordWrap(True)
        self.projected_label.setAccessibleName("Projected end of the hour")
        layout.addWidget(self.projected_label)
        for text, handler in (("Load This Hour", self.load_hour),
                              ("Record Into Selected Slot (Ctrl+T)", self.record_into_selected),
                              ("Add Voice Track Slots (every 3 songs)", self.add_slots),
                              ("Clear Selected Recording (back to an empty slot)", self.clear_selected),
                              ("Save Hour", self.save_hour),
                              ("Discard And Rebuild This Hour", self.rebuild_hour)):
            btn = QPushButton(text)
            btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
            btn.clicked.connect(handler)
            layout.addWidget(btn)
        self.setLayout(layout)

    # --- loading ---
    def chosen(self):
        return self.date_combo.currentData(), self.hour_combo.currentData()

    def load_hour(self):
        day, hour = self.chosen()
        generator = self.app.playlist_generator
        path = generator.current_hour_playlist(day, hour)
        if path is None:
            path = generator.generate_hour(day, hour)
        if not path:
            self.app.announce("No rotation is scheduled for that hour, so there is nothing to load.")
            return
        self.day, self.hour, self.path = day, hour, path
        self.entries, _missing = read_m3u(path)
        self.refresh_list()
        self.app.announce(f"Loaded {date_label(day)}, {time_label(hour * 60)}: {len(self.entries)} entries.")
        self.list.setFocus()

    def entry_text(self, entry):
        if is_hour_marker(entry):
            return format_track_display(entry)
        return f"{format_track_display(entry)} ({int(get_track_duration(entry))} seconds)"

    def refresh_list(self, keep_row=None):
        row = self.list.currentRow() if keep_row is None else keep_row
        self.list.clear()
        for number, entry in enumerate(self.entries, 1):
            self.list.addItem(f"{number}. {self.entry_text(entry)}")
        if self.list.count():
            self.list.setCurrentRow(max(0, min(row, self.list.count() - 1)))
        self.update_projection()

    def projected_total(self):
        _voice, _signoff, break_seconds = self.app.playlist_generator.hour_options(self.day, self.hour)
        slot_seconds = self.app.playlist_generator.voice_slot_seconds()
        songs = [e for e in self.entries if is_song_entry(e)]
        total = timeline_length(songs, get_track_duration)
        for e in self.entries:
            if is_voice_marker(e):
                total += slot_seconds
            elif not is_hour_marker(e) and not is_song_entry(e):
                total += get_track_duration(e)
        return total + break_seconds

    def update_projection(self):
        if self.day is None:
            return
        total = self.projected_total()
        end = datetime(self.day.year, self.day.month, self.day.day, self.hour) + timedelta(seconds=total)
        diff = int(round(total - 3600))
        if abs(diff) <= 12:
            verdict = "on the hour"
        else:
            verdict = f"{abs(diff)} seconds {'early' if diff < 0 else 'late'}"
        self.projected_label.setText(f"This hour is projected to end at {end.strftime('%I:%M:%S %p').lstrip('0')}, {verdict}. "
                                     f"Breaks are counted at about {int(self.app.playlist_generator.hour_options(self.day, self.hour)[2])} seconds.")

    # --- editing ---
    def selected_index(self):
        row = self.list.currentRow()
        return row if 0 <= row < len(self.entries) else None

    def record_into_selected(self):
        index = self.selected_index()
        if index is None or self.day is None:
            self.app.announce("Load an hour and select a slot first.")
            return
        entry = self.entries[index]
        if is_voice_marker(entry):
            where = "into the voice track slot"
        elif is_song_entry(entry):
            where = f"before {format_track_display(entry)}"
        else:
            self.app.announce("Select a voice track slot or a song.")
            return
        clip = self.app.capture_voice_clip(where)
        if not clip:
            return
        if is_voice_marker(entry):
            self.entries[index] = clip[0]
        else:
            self.entries.insert(index, clip[0])
        self.refit_end()
        self.refresh_list(keep_row=index)
        self.list.setFocus()

    def clear_selected(self):
        index = self.selected_index()
        if index is not None and not is_song_entry(self.entries[index]) and not is_hour_marker(self.entries[index]):
            self.entries[index] = VOICE_MARKER_TOKEN
            self.refit_end()
            self.refresh_list(keep_row=index)

    def add_slots(self):
        if self.day is None:
            return
        base = [e for e in self.entries if not is_voice_marker(e)]
        _voice, signoff_hint, _b = self.app.playlist_generator.hour_options(self.day, self.hour)
        event = self.app.event_library.event_for_hour(self.day, self.hour)
        signoff = bool(event and self.app.event_library.is_last_hour_of_show(event, self.day, self.hour))
        self.entries = insert_voice_markers(base, VOICE_MARKER_EVERY, signoff)
        self.refit_end()
        self.refresh_list(keep_row=0)
        self.app.announce("Voice track slots added after every 3 songs.")

    def refit_end(self):
        """Swaps the last song or two so the hour ends on the top of the hour, given what is recorded."""
        if self.day is None:
            return
        tail_start = len(self.entries)
        while tail_start > 0 and is_song_entry(self.entries[tail_start - 1]):
            tail_start -= 1
        tail = self.entries[tail_start:]
        if not tail or tail_start == 0:
            return
        head = self.entries[:tail_start]
        _v, _s, break_seconds = self.app.playlist_generator.hour_options(self.day, self.hour)
        slot_seconds = self.app.playlist_generator.voice_slot_seconds()
        used = timeline_length([e for e in head if is_song_entry(e)], get_track_duration)
        for e in head:
            if is_voice_marker(e):
                used += slot_seconds
            elif not is_hour_marker(e) and not is_song_entry(e):
                used += get_track_duration(e)
        gap = 3600.0 - break_seconds - used + overlap_seconds()
        rotation = self.app.rotation_library.find(self.app.rotation_schedule.rotation_id_for(self.day, self.hour))
        if rotation is None or gap < FIT_MIN_SECONDS:
            return
        taken = set(self.entries)
        candidates = [p for p in rotation.track_paths() if p not in taken]
        best, score = choose_fill(gap, candidates, get_track_duration, get_track_artist, max_songs=max(1, min(2, len(tail))))
        current = timeline_length(tail, get_track_duration)
        current_score = (gap - overlap_seconds() - current) if gap - overlap_seconds() >= current \
            else (current - (gap - overlap_seconds())) * 3
        if best and score is not None and score < current_score:
            self.entries = head + best

    def save_hour(self):
        if self.day is None or not self.path:
            self.app.announce("Load an hour first.")
            return
        self.refit_end()
        write_m3u(self.path, self.entries)
        recorded = [e for e in self.entries if not is_hour_marker(e) and not is_song_entry(e)]
        if recorded:
            set_hour_locked(self.app.settings, self.day, self.hour, True)
        self.refresh_list()
        self.app.reload_hour_if_current(self.day, self.hour)
        total = self.projected_total()
        diff = int(round(total - 3600))
        self.app.announce(f"Saved. {len(recorded)} voice track(s) recorded; the hour is "
                          + ("locked so it will not be rebuilt. " if recorded else "not locked yet. ")
                          + (f"Projected to end on the hour." if abs(diff) <= 12
                             else f"Projected to end {abs(diff)} seconds {'early' if diff < 0 else 'late'}."))

    def rebuild_hour(self):
        if self.day is None:
            return
        answer = QMessageBox.question(self, "Discard and rebuild",
                                      "Throw away this hour's playlist, including any voice tracks recorded in it, and build a new one?")
        if answer != QMessageBox.StandardButton.Yes:
            return
        set_hour_locked(self.app.settings, self.day, self.hour, False)
        self.path = self.app.playlist_generator.generate_hour(self.day, self.hour)
        self.entries, _missing = read_m3u(self.path) if self.path else ([], 0)
        self.refresh_list(keep_row=0)
        self.app.announce("The hour was rebuilt.")


# ---------------------------------------------------------------------------
# Logo: the Vision Studio turntable (icon and banner are drawn into the program, no image files needed),
# the station's own logo option, the Windows icon file, and keyboard navigation helpers
# ---------------------------------------------------------------------------

LOGO_PNG_B64 = {
    "16": (
        "iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAACwElEQVR42o2TzWtcZRTGf+d933tnppkkM9NN/CgiiiDBjbRooJBF"
        "hATElUIo4kIMCP0XXAVdiRu30kV14cqtqIUSF1JdKEEQtNoyWdhEHclk7nXuvTPvx3HTRJQu/K3P8/BwznOE+6ytrb1S1/XFlBIP"
        "whiDqmqWZeKcu7O5uXl9d3c3yPr6uiuK4v0QwtUQwtnwfzk19t5jraXT6ey1Wq0rdmFh4eUQwrt1XccQgsYYtaoqLYpCJ5OJTqdT"
        "9d6riKj3XldWVhSIdV0/MZ/Pl0wI4bkYYxIRnHPWOWePj49tNS1tDI2dNZUdj8d2NBpZY4zd2dmx29vbtqqqlFK65ETEq6oxxkTn"
        "HNZaBoMev947AbXglKUOJFUODg7Y39+nKApSSkZEggMEQEQwxmBEIBvw0vMll1ZnfP295bNvHb0lIaVECIHhcEiWZcQYxaWUsNYy"
        "Go2AhGsN2NkoeOf1EhYFyjlX3zNcu7mIESHPc1qtFqp6unCDqhKCp/yrZl79zpubnvFkkQ8/UsbFIm+92qNtG5IqqHJ4eEie56gq"
        "7p9DCdZAkpw3fr6F5Mv8dPApH//wIn72Bxeeeo0nLzyGGMNkMqHb7RJCwA4GgxeMMZebptEQ1cS6pJjO6K5eYeWZZ5n+2aVe/Zzz"
        "TzcMP/mOm199Sb/XVxERVT08S9DpdKiqCtta4GT/A+6WB3Qfv0wzvEX/m3sczTO8TTzy0MOIyFluZ4zRlBKdTufMxLWXmNy9wcnt"
        "G2BBxo/S6y9juufw3hNjPNWrA1pAUlX6/T4AdV0jrovkBo2R4+kJ7aVzSORfYlXNnYj8KCImhOABGQwGzGYzmqYhxogxOXmeE7w/"
        "i66qMcuyDPhFtra2WkdHR19479f/zzOdli7P89/a7fa6AGxsbJwvy/Ltpmku3i+I8GCSiIhz7s7y8vLu3t7e7b8B3tduDL+rAY4A"
        "AAAASUVORK5CYII="
    ),
    "32": (
        "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"
    ),
    "48": (
        "iVBORw0KGgoAAAANSUhEUgAAADAAAAAwCAYAAABXAvmHAAAMO0lEQVR42s2aW4xd11nHf+uyb+ccz5mxx3Yst05QjOM4LcFFDY0T"
        "Z5S42CooDZI5ASNRHkBEICEhRB8qERxDHqiQEMoDICIiVPkFWSD1wRMURwqJ47TEUZHt2DVVrcSOPb7N5cyc276ttXiYs3fO2DOe"
        "Y0dquqSlc9t77e/yX9/3/751YPkhAcXPzxB9mZb9YcloNBrqyJEjpv9+89WrV7+aZdmXrbU/U4mllHied2ZkZOT/Jicnf3yrbCsp"
        "oACzZ8+ebc1m8zvdbnd/lmVr8jxHCPEzN7uUEq21qVarb0VR9OKJEyd+2PeEvU2BQrsnnnji+YWFhX8yxqxN0xTACCHc54Eb55wA"
        "lNYaKWVeq9VePnny5CHnnOor4dSg8Lt3797fbDaPxHEc5XmeF9hzzn0us8C9tdZYa6Ux5ukHHnhgdGpq6vVGo6HOnTvnxMGDB+Wh"
        "Q4fc3r17H7x06dL73W63Hoahy/Nc3QtslrvHOVe+3isUpZQuz/NMKeVv2rTpt44fP/4fExMTWgHq4sWLtl6v/0Oz2fxVKaXRWmtr"
        "7aoPKwSSUpbXWmvJ8xxrLdZanHMopZBSIqUcygDFWlLKUnlASClFp9MRQohfmZiYeHVycjLXb7/9dt5oNO47c+bM/iRJbLVaVcNa"
        "WilFnud0Oh3iOCbLMpxzpWLFw6WUKKUIw5AwDPE8DwBjzBIjCSHI8xxjDEEQ0O12CYJg8BpprTVxHD94/fr1p4FJDTA1NbUrz/MK"
        "YFaKt7cKn2UZ7XabJElwzuF5Hp7nrQgh5xztdptWq4Xv+9RqNcIwLL0kpSTLMtauXcvu3bsZGRnhypUrvPvuu+R5jlKlXV2WZa7T"
        "6ewFJiVAkiRf7lvDrSa4tZYsy5ibmyNJEoIgIAgCnHPkeU6WZUtmmqZkWYYxBt/3iaIIay3T09PMzMyUELPW4vs++/btw/M8Ll++"
        "zObNm5mYmCDLstIwQghhjBFZln2pyLgIIcywVnfOUavVWLduHVpr0jTFGINSCs/z6Ie8Evee5+H7Plpr8jyn1+sBUK1WSdOU69ev"
        "kyQJxhjGx8fxfR8hBM899xxzc3Ns2rSJMAwH90IxDANwEasJX8CkWq0CEEVRCZvC/YUyA9bCGFN6odgHAL1ejyAI8DyPmzdvYoyh"
        "2WzSbDZ5+OGHmZiYYMOGDUxNTZEkyXLQFNwN3oUQpSWKTTo2NkaapqX7iz1gjCmnEKL0grWWOI7LtQpvRFHE7Ows8/PzvPHGG4yP"
        "j3Pjxg3Onz/P8ePH0Vov5wFWVaDAvBCCIAgY5EOFR0ZHR3HOkSQJBeXQWpdwKiJLkiSlsNZakiQhiqLSAEEQ0Gq1uHTpEhcuXKDb"
        "7XL06FGstXcMv3K1OG+tpVKprGiBWq2G1pogCNBagzNYk2LyBGtSwKD1InSEEPR6PZRSaK2J47hUAkBrTa/XY+vWrZw9exbf9wej"
        "z7JDr2b9YlMtp4C1Fq019XqdG9evIYSgHYv+9upjVhjCMMfXIJVPGIbEcYzneQRBQBzHVCoVut0utVoN5xzr16/n8uXLGLNqbFlZ"
        "gQLnvu8vwf1yStaqEddklSTu8sQjll3bDfUq5Bmc/Knk3bOK+ZagVkvJc0kYRiRJXEItSZJSsSAIMMbQ6XSGoh16JevneU6z2WRs"
        "bKyM9UXSWYJB4ZjvefzaV0L+9Ndn+fpOC14fnG4x2J37SPK3/+5x+C2PSuCI4x5RFNHr9QjDkDzPkVKSpin33Xcf27Zt45VXXik3"
        "/l0pUFi61+thraXZbCKlJAxDarVambSccyjpmO9qvvXkTf76d68htMN1wfQGFYQdWyzf+8uEp3ZY/uSfAwLPkvaTYJqm+L5fJsVu"
        "t1uG5WHIn1yJTcZxXMJHCMHCwgIzMzNMT0+TpilaQiv22PPIAn/ze1dxmcO0QQjQ6tMpJdgYsib84fMZL/1OSrsjcc4seV4Rrrds"
        "2UIcx5w9e7YMnysFkBUVMMaUrpNSlps5z3PiOObatat8MnUN7doc3H8VZ8BZwWDAGHymlKAlmFn49vMpX9lm6CUCY7IyQ3ueRxzH"
        "bNmyhUqlwtzcHMOUscuG0cVa5vZcUEQdgWVuNubRTVe4/4sZJhZICQ6xOJ1AKHBOlN8hBNYIvJrg958x5JkAa8p1C+qstabVapWs"
        "9J4gdAt5uo1SLH5Q7PvlDJRDCYcYnJ6j3ZMIb+n3nnKQOZ5+JCWIHLlZWgM453j88ceZmpqi2WzeETpDJbKVOJG1IJRly+YarXiM"
        "BTNKKx9lPq3T9sY48o7HL/6B4sg7Hm1vjPm0TisfXbwuHmXtujrjawSZAXBlsVNk7jvlnqHzwJ2GRRLILi999J+s1U9hkg5CKJwz"
        "qKjCxY9fZyb9Noc+/jv+7cNvYHpdxCKmEEqT9eZpu6fx9SxSapzLWVhYIM9zNm7cyOnTp4cuP+9KgWJRISQYy/T1KdSDY+RZiJD9"
        "pdow9qUDfHXrXmS4jtm2Adb077coGdC5/glJ8wZxltHpLmbiJ598kmeffZYDBw5w6NChssi5awUKkjZYiN9anBdktnvxGHrXH4PI"
        "GayFnEmRQR1neugBKzqX42nNTPMtonrAN5/ZT6Oxn0cffZS1a9dy+vRpXnjhBY4dO0a1Wr21Jh7eA1rrJUIXC336CvgR8z99k87V"
        "s0QbtmPSHkKqUjtnc0DiPq1mIali7/8R9d+4ybbvvMh3Nxzg5Ds/4OWXX+a9997jwoULOOcYGRkpi6J78kBRTQ0StizL8DxvMWZr"
        "TWwcLmnzyRt/wUPfeh2hNM5kn0JpsEZydjExSIVRlwk3VpifNnxz/29y/n9OY4RDK8X69etJkgTP8+j1ekuQMHQUKm4Iw7Csopb7"
        "XUmQQY35n/wXH33/BaRU6GgNOIuz+cA0SK+CqtTonf1Xeu+9hmsHZJ/MkvdSHn5kBw899BAbN24s2zF5nqO1RmvNau0dvVKoLChu"
        "QbI8zyNN05ICF2RMhWu4efJf6F0/w+Y9hxh54BmEpxCin40dtKdO0T31j6ipY7jzIcmJK5AaRGLJhUUKwejoKJVKhTiOmZ2dpVar"
        "rdgoW3UPFNShoA9KqTICGWPKtB9FEXEcI4M1dC7/kJ987xvUvvA1ql/8GjqsY/OU7tUf0fr4ONK2+cIv7EAKcM3eImmSovRqYfWR"
        "kZHyecNQiRXptDGGkZERbt68SRRFJVssOHtRPRV0OBc1nLO0Lp1g4aMTS0Cq/IhcVGktLDA6WscqiRB9un2L5/M8HzqErlrQBEFA"
        "tVql2+2WBcdgReX7fvk+CgOMtVjPx1o3QOQESi62H9vtFlEUlix3uXZ6t9u9q/7pHdU0xlCv18t9MKhEQbaiKMI5RxzHmDxHCvC0"
        "xPcUnpZIQclinXN0Op1lhR+sQYa1/tBcaHx8vIwOgzCSUpatkQJWgx26Ag5F0Q/QbDZJkmSJkFLK8p47tVDuSYEiL2zYsAFjDFmW"
        "lZ0E5xxhGJYeKqoopVQ5nXNl00tKSRRFzM3NlQW7EIIkSciybEVoDaOAG0aJ9evXI4Sg2+3i+z5SSpIkwVpb7olC6MH7iqaXMWYR"
        "asbQ6/VKDxYeuUvhXbmJ+0c2Q3tiYWGBdruNUqqskY0xywowaGmtNb7vk6Yp09PTJd7vxfKF8TWA7/sf9i0gVlMCoF6vE0XRbe11"
        "pdQd2+sF7HzfZ2RkpGxF3o3wzjnXz9I/LhUYGxs7PTMzY4bd1EUyW7duXRlhhjngKM4EigOO5do0w9RVnudRqVR+UDAu5ZyzO3fu"
        "/O8bN2485fu+8X1fDXO0OnjENNiKHOyoFdAp1lqty7DK2ZtttVqMj4/P7dy58/7Dhw93ZaPRQAjhxsbG/rxSqWR2MQu5u1h0yXlY"
        "cSZQzCIsDl5zT0f1i8W/WbNmjRwdHX3p8OHDnYmJCaXOnTvnGo2GOnr06JWtW7dK59wzxhjTt6642wcWFh6cn+k/BotQtEKIXCnl"
        "VavVVz/44IMXG42GmpycNIMYUc45+9hjj/19p9P5s35/3wghnJRSfFZB7lFwZ60VUkoVBAFKqVdPnTr1R/0zZAfcFnUE4Hbt2vXb"
        "7Xb7r9I03VGcunweo8ghvu9PRVH03ffff/+VQeFXOlpSgDl48KD/5ptv7ovjeCLLsl/6LIfU9/AXA4QQzvf9D33f/9/t27d//7XX"
        "XmsVBl51gUaj8fP0V5s7yvT/TwnezIdpUfkAAAAASUVORK5CYII="
    ),
    "64": (
        "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"
        "vGIt839WLZow+gJSgwAAAABJRU5ErkJggg=="
    ),
    "128": (
        "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"
    ),
    "256": (
        "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"
    ),
    "banner": (
        "iVBORw0KGgoAAAANSUhEUgAAA9QAAACWCAYAAAA/rMB+AACtyklEQVR42ux9d7hcVbn+u9vMnt7OyTnppBFSIEJoSSCRGhIQUYoi"
        "AparKHp/Xhvq1XtRFPV6sVxsCCqIgCBFIcEQaaGkEHoSEhNIQsLJqXOm99nl98fJt9gzmXZqzgnrfZ55IHNm9uy99lprf+9X3k9A"
        "4xAvvfRS4f7779cBYOHChU673b7QNM3lAE4SRXEqgKNN0xQEQQAHBwcHBwcHBwcHBwcHx2iBaZoQBMEEsMswjH0AXhQEYW0+n3/5"
        "5ZdfzgDApZdeKt1///0mAKORYzbEfA8eVAeAJUuWzANwlWmal4iiOF2WZRiGAdM0USwW+V3i4ODg4ODg4ODg4ODgGLVQFAWCIEAU"
        "RWiaBsMw9giC8ACAO9evX/9GOQceDKGmv5uLFi2aLwjCV0RR/LiiKIqmacjlcshkMnoulxMMwxCKxSIPTXNwcHBwcHBwcHBwcHCM"
        "ZkJtiqJoqqpqOp1OSVVVyLKMYrFYNAzjLtM0f7Zx48ZtVj7cb0JtZeSLFi36riiK31IUxZbL5ZBKpbR0Oi3l83nBMN6NhPNUbw4O"
        "Dg4ODg4ODg4ODo7RDNN8lx+Logi73W66XC7d7XbLqqqiWCwWDMP40caNG79bzo0bItT0hZNOOimkKMrdiqIs1zQNsVhMi8fjkqZp"
        "Av24IAglJ8TBwcHBwcHBwcHBwcHBMdpBXJaCxLIsmz6fT/f7/fLBiPXaYrF4xYsvvthbjVQL1cj0okWLThJF8W5FUWal02ktHA5L"
        "2WxWoFxzTqI5ODg4ODg4ODg4ODg4jhRyTdpgDofDbGpq0l0ul1wsFt80DOOKjRs3vliJVIvWf1x//fXi/fffry9evPhESZLWyrI8"
        "KxqNau3t7XI2mxUkSeIRaQ4ODg4ODg4ODg4ODo4jCgcVwCFJErLZrNDe3i5Ho1FNluVZkiStXbx48Yn333+/fv3115dwaGuEWjBN"
        "EyeffHJQUZQXFUWZ1tvbq4XDYVkQBF4fzcHBwcHBwcHBwcHBwfGeIdimaaKpqUkLhUJysVjcWywWT9q8eXPkIDc2AUuE+tJLLxUF"
        "QYAsy/fabLZpsVhMC4fDMtVJc3BwcHBwcHBwcHBwcHC8F0ClzuFwWI7FYprNZpsmy/K9giDg0ksvZTxaOkimpYOp3tfb7fZPpdNp"
        "raurS6YDcXBwcHBwcHBwcHBwcHC8F5HNZkVVVTWHwzFzwoQJ5tq1a5++9NJLpe3bt5vC9ddfL37ve98zFy9efLQgCFtN05Q6OjqE"
        "bDYriKLIR4+Dg4ODg4ODg4ODg4PjPQvDMOBwOMzx48ebgiDopmkeu2HDhl3XX3+9IAGQ9u3bZ0yaNOlnNpvthEgkoicSCYmTaQ4O"
        "Dg4ODg4ODg4ODo73OgRBQLFYFERR1D0ej6Jpmretre1vACQBABYtWnSMJEmva5omt7W1CbquCzzVm4ODg4ODg4ODg4ODg4OjT6RM"
        "kiRz0qRJpizLmq7rCzZu3Pgv8eAfP60oii2VShmapvFUbw4ODg4ODg4ODg4ODg6OgxBFEZqmCalUylAUxWaa5qcBQFy4cKFTFMVL"
        "NU1DOp0mgs1HjIODg4ODg4ODg4ODg4PDwpHT6bSoaRpEUbx04cKFTlFRlJMEQZiUy+XMfD4v8ug0BwcHBwcHBwcHBwcHB0cpRFFE"
        "Pp8Xc7mcKQjCJEVRThIBnKMoipTJZAzDMHibLA4ODg4ODg4ODg4ODg6OMgiCAMMwkMlkDEVRJADniABONE0T+XxeAHi6NwcHBwcH"
        "BwcHBwcHBwdHOYgr5/N54eD/nygKgjDTMAzous5D0xwcHBwcHBwcHBwcHBwcNaDrunAwu3umLIrijGKxiGKxOKStsnike/gxXOn5"
        "/N6N3FjTsU3T5OM+gveSxpyDg4ODg4ODg4Ojv7ZksVgUisUiJEmaIQ/lwQ3DAADIsswN1hG4kaZpQtM0AH0F8oOFrusQBIHfvwpj"
        "res6G5+hFO4zTRO6rkMURciyzMd8BO6lpmlszLlmBAcHBwcHBwcHx2AwJISaSIDH44HH4+GEbIQJdTKZRCqVYu/39ziGYUAURQQC"
        "AbhcLkiSxO9fhTleKBSQSCSQzWYHTaqJpNtsNni9XqiqCkmS+JiPwLrRdR25XA6JRAKFQoGPOwcHBwcHBwcHx+Ej1IZhQJIktLa2"
        "QpZlZDIZpFIpbqCOEDmw2+0IBoPwer3o7OxkkbdGv69pGhwOB1paWqDrOrLZLAqFAh/cMoiiCFVV0dLSgnQ6jZ6enkGRak3T4Pf7"
        "EQwGkc/nkU6nWbYBxzBverIMh8OBiRMnIhKJIBaLQZIkPjAcHBwcHBwcHBwjS6hN04QkSZgwYQIKhQKi0ShM0+Q1iiNEpk3TRLFY"
        "RDqdhsfjwYQJE9De3o5G25/pug6n04mWlhYWeaVjc5SOta7ryOfzSKVSCAQCaGlpQVdX14BIta7rCAQC8Pv96O3tRaFQYOnHfM0M"
        "/73M5/PIZrOw2WwIBoMQBAHRaJSTag4ODg4ODg4OjpEl1ADQ2tqKYrGIeDzOUoWtxivH8JIDGuN4PA6/34/W1la0t7fX/a5pmlAU"
        "BS0tLYjH48hms5xQ1BlrGp/e3l40NzejqakJPT09/Ro3wzDgdrsRCATQ09PDMjz4mhn5e6lpGsLhMJqbm5ljaijr4zk4ODg4ODg4"
        "OI58DNh6JGIgyzIj06MZpKJsfQ3l5w83JElCPB6HLMtwu91MIK4aoTAMA4FAAIVCgZPpARCyaDQKt9sNm83Wr7khCAICgQASiQQT"
        "ORtLa6bWtY61NUOZB4lEAoFAgDszODg4ODg4ODg4+o1BRag9Hg8ymcyoJQPMayCKkCSJpdWS4VzL4Ld+xjRNGIbBXuWfGU3IZDLw"
        "eDxIJpM1nSGyLENVVcTjcR6VGwAR0zQNmqbB4/Ggt7e3IYVuwzDgcDggSRJyudyoG3fr+VMUl7JOrHO92nWWrxlSMLeS69G2ZkRR"
        "RC6Xg9vthqqqQyI4x8HBwcHBwcHBwQl1XcObjO1UKjVqjGQy2uncyDDWdR2apiGXy+Fgz21WS1nt2hRFgWmasNvtkGUZiqJAlmWm"
        "CEzHHE1Ega6JFKOr1VKbpgmbzQYAbCw4+o9cLgdVVRuqfabPOBwOFItFpqw+WtYMtUuzKrxrmoZsNsvqxwEwR0KlOWO321kpAa0Z"
        "RVGYI8swDNZ+bDSRa8MwUCwW4XA4kMlkeC07BwcHBwcHBwfH8BJqMoZHg+FZTqIpepjL5ZDP55HL5VAoFGAYBhNMI1QjNFYCYXUY"
        "SJIEu90OVVWhqiojC1ZyfbhJglUUrhZ4FG7oxro/EEVxVJA1OndFUZiTqFAoIJ1OszWj6zrLyKDrrDW3qHWb9fiiKEJRlEPWDRH2"
        "0UKuTdPka4KDg4ODg4ODg2PkCPVoIARAXwscWZahaRpSqRRr+USkgKJjVCNsTT+tV2dMBMiayprJZJBOp1lEz+FwwOVysUglkffR"
        "QBI4OCqtGVEUYbPZ2HyNRqMse8NKhOlVvlaqrZtKpJuIej6fZ1oLNpsNbrcbLpcLiqJA13UUi0W+Zjg4ODg4ODg4ODihHilSQGml"
        "2WwWsViMpWcHAgHY7XbEYjH09PSwVFMy1iliRmTcGpUiMmFNS9U0jUW36RhEzg3DQDKZRCKRgM1mg8vlgtfrhd1uZxG+sUoSOLE5"
        "dM6NZVDdvM1mg6ZpSCQSJQ6o8nltXTMUybbWVZdH56mFGwC2fqxrxtoWjNpWRSIROJ1OuN1uOBwOGIZRcj4cHBwcHBwcHBwcnFAP"
        "MbGhFNVUKsWEnTweDxwOR0mdpt1uhyRJjETIsswMeyLIlNJqjazRb9jt9pLaT6qzLBQKJendREI0TUM0GkUikWDEWlVVFItFaJo2"
        "ZtJJ6XqJHPXne1bnRX+Je39JK93HkfgtK4kci84AURThdDqh6zoikQhTGCexPiLRpDpOtc/W+me6diLL5WRaEAQ4nU52b6zHLBQK"
        "KBaLzMEkiiITcUulUkgmk3A4HPD7/ew8ObHm4ODg4ODg4ODghHoISQEJheXzeUQiEUiSBL/fz4SQysmVoigIBoPQNA3FYhGZTIYR"
        "4f4QMUp7JWLu8XhYnXY+n2eRaCtJSCaTSCaT8Pl88Pv97LxHQ411PVDUfSCEeiBkdaB1+CP5PVEU4fV6G1LyHk1rBugTCjMMo4RI"
        "k6PJMAxomsa0Aex2OxRFYe/ncrmSaHOj126NZJOavNvthmmaTNtA0zTmrACAfD6Pjo4ORqxJvG20txZ7L6IRjQbrfjIW0agDdCy0"
        "h+Pg4Bi9+wLfazg4OKEeMWJApKC3txemaSIYDMJmszHDv9y4IwJeLBYZ+baSPmvP5UobVHn0zTAM5HI55HI59n2bzcbqp3VdRyqV"
        "YudCx4/FYkgmkwgGg/B4PDUVkkeLoUxR+IFG1AdybQMdj5H6nmEYyOfzkOWxkdBhmiZT2U4kEohEIocQaV3X2RymNHASJSOyayVP"
        "5aUR9caVfoPE/ajUwmazwefzwTRNZLNZ5HI5FkWXZZkRa6fTiebm5jHljBrquTecxtNAz8O6R9RzTgmCwLQlxhIMw2i4HSR1geCG"
        "7nsDtB/WaiNYrbMGJ0RjH5lMpq72Dj1/KdjD9xoODk6oDzspEEURqqoimUwinU7D6/XC7XaXEOlKDy96T1VVlupd6YFW7fvWmmn6"
        "XLk4WTabRTabhSRJUFUVPp8PQJ/ScT6fZ6Jlpmmip6cHyWQSzc3NUFWVEfPRTKw5xuaYmKbJSg3a29vZHCUibRgGU9yWZRmFQgGx"
        "WIyRaGsauLUHuxW11PHLx8yaMk7iZIIgwG63w+l0wuFwoFAoIJPJMNIviiKy2Sza2tpYlsdod0Y1StQajdhaHXPDAWvLv3qwCtQl"
        "k0lceuml+MQnPoFkMllxLpBDM5PJ4LrrrkMsFhsThqAgCMjlcpg3bx6++93vMqdBtXXmcDjwwx/+EJs3b4bL5Rqz0XiO+vOCujPQ"
        "HmbNsCm3I8h+oPlAeyrpvlgds+W2BsfovP+GYUCSJPz85z/H5MmTq+4NhmHA7XZj3bp1+NnPflZ1X+B7DQcHJ9QjZnjabDaIooiu"
        "ri4oioLW1lYmGNYIwaHINn3H2keaxMiqtTCi71CUjdLGrb9tJR3pdBqZTIaRBLfbjWQyiXw+z36vUCigra0NwWAQfr8f+Xy+ap9o"
        "Do7BOKASiQTL5iAio+s6ZFmGx+OBoihIpVJIJBLse5UEySiqTLoFRHYrRSbJ6LC2w6I1Y62dpjVHwmSKosDj8aCpqQmpVIr1gaaa"
        "9UgkgkKhgGAwCLvdzgj5WLw/LpcLNputoZ7lxWKRdRMYjnPxer11CTvNDbpXdF5TpkzBkiVLqmZtGIYBRVEQj8cbut7RZDhrmga/"
        "348zzjgDxWKxpvPIZrPhlltuGfOOHo7qoEy3eDwORVEwYcIEHH300Zg5cyYmTZqEpqYmuN1u2Gw25qjKZrNIJpOIRqMIh8Po6OhA"
        "Z2cnOjo60Nvbi3g8zpyHdrudfXcgpUiNZJLR/s8x+P1h0aJFmDVrFgqFQsX9U9M02O12hMPhmvsC32s4ODihHhHDU1VV5PN5RKNR"
        "+P1+uN3uEtXg/hAMv99/iHo3pZla++yWDIpFwIxqQF0uFyML5S2GyPinvtcOhwNerxfFYrGEtJimid7eXuRyOTQ3N1dNWefg6O+a"
        "ochHd3c3kskkI79Ug+z1emGz2ZBOpxGNRg8huGRw0XwnVW/6G6Vv0xqoZCAQuSISrqoqI1gU2SkXJiOhNEVR4HK50NTUhEQiwUTJ"
        "xo0bB4fDgXA4DLfbDbfbzTI8xgoosrto0SLccsstjJxWu5eSJCGbzeKyyy5DW1vbkJFSivzPnj0b99xzT12hPdM0YbPZ8IlPfAKb"
        "N2+G1+tlrdZ0XUcikahoVNJ8TCaTYy76RoauNdOoEigSxffvIxO0L0ajUbS0tOCSSy7BihUrcNxxx6G5uZm1HawUYS5PCyebIx6P"
        "o6urC3v27MGOHTuwdetW7Nq1C21tbczx3h+dikwmU3MvsX6W1i7H4JBKpZBOp5HNZisSYF3X4ff7mWOY7zUcHJxQHzZi4HA4kEql"
        "kEql0NLSwnpM93cjIcNUlmWEw+FDWl9ZN7VykCBXedo31cW43W4A73qjqeaYNliqDXW73QgEAkin08jn84xEZDIZHDhwABMmTIDN"
        "ZquZ7sPBUW+eE+Fqa2tDsVgsiUrb7XZ4vV7k83kWtbaq11OkxBplIRG/YrFY4nCyquFXOg8iwVQ3DYClOtrtdtYai/QIDMMoIdYU"
        "0aTzNQwDHo8HANDa2ore3l4UCgWEQiFks9kxU1dtmiacTidefvll9Pb2YsaMGaxDQSXouo6JEyfirLPOwm9/+1uoqjokESZKMzzv"
        "vPMwdepUxOPxqroAhmHA6XTitddew5YtW+BwOA5pHUivanvvWOlsUGmc6NpqRZhq/Z1j7IIcWoIg4HOf+xw++9nPYubMmYwYZzIZ"
        "pNPphtY9zQ8StgyFQliwYAEuvvhiFAoF9Pb2Yvfu3fja176G3bt3N1R3K4oiMpkMTj/9dCxduhSZTKbqWiMn2p///GdW/sNTzAfn"
        "aLFma1WbP43ufXyv4eDghHpY4HA4EIlEoGkaxo8fz0jBYISuqHbUKqxED5RqIiHWh6D14Uip33RcikRT1Jq8jPTQSiQSUBSFtdCK"
        "x+NsQ9Z1HW1tbWhpaWF11XzD5OgvUaOe511dXYwcU/2ex+NhPdkpRY0iL5qmsXRrRVGYp9yaeVFex2tdN7XWXPm6IQItiiJsNlvF"
        "2mlySBWLRYTDYXi9XrS0tJT81rhx49Db24vu7m6EQiGWWj7a1w214uvp6cHq1avx1a9+tWrKIJHZQqGAlStX4o477hiyejld1+Hx"
        "eLB8+XKWLVDtXmqaBrfbjYcffhiJRAKhUIgb4hzvCTKdSqUwceJE/PznP8fZZ5+NTCZzSFbPQED2g9Ux5XK5cNppp6G5uRn/+te/"
        "oKpqQ4Q6m83i9NNPx1e+8hW271dDIpHA/fffj3Q6Pay6DBwcHBycUI8SMh0OhyGKIlpaWpgRORhjmWqxbTZbCWElskC11JUefERK"
        "rA8/KynXdR3JZBKCIMDhcMDn86FYLCKZTLK+09aUVo/Hg1AohGg0yiJzhmGgo6MDra2tcDgcnFRz9IukqaqKbDaLzs5ORn6JnAaD"
        "Qei6jnA4XCKQR3/3er1wOp3MWKT3rXO8XESL/q4oSsXzoVRwq9ZAud5AvdppSlMn/QOrcalpGoLBIJLJJLq7u9HS0sJ+byy0o1NV"
        "FWvWrME111xTUzGeImQnnHAC5s6di23btsHpdA6KWIuiiFQqhVNPPRXz589n0apqsNlsiEQi+Oc//8ki5GM14szB0SiZTqfTmD59"
        "Ov7yl79g5syZ6O3trZqJ0V9UEkEt7xDSn2NRK9De3t6K+wk58qLRKHeGcXBwcLwXCLWqqgiHw5AkiRGBoSIdkiTB4XBA13U4nU72"
        "4LEqf1cyPun7lMpaKBRYRMxKPEzTRCaTQSaTYT10C4UCqx+kzySTSdjtdoRCIcTjcRahMk0TnZ2dnFRz9Gte2+12RqZpPpJ4icfj"
        "YXPSSmYpjdflciGXy6Gnp6eknVY5iabWW0RurUS7mrFI64lqrq1ifla16Eq108lkEtlsFj6fD16vt+LvaJoGj8fDBAspij3aDUbD"
        "MOBwOLBlyxa88sorWLx4MVKpVM2072AwiOXLl+Pll1+Gy+UatDFfLBaxYsUKOJ1O5HK5qiRB13X4fD489thj2LVr1yGqsta6+mrz"
        "k0oKxur6ouurVdfYX10PjtEL0gbw+Xz4wx/+gOnTp6O3t7ei83Cof9faQaQ/IKd9uXK4dR6TECsH32s4ODiOYEJNUTbqFT2UZNpK"
        "mqnmWdd1ZLNZVhtaj1BbW1243W5GWqzHoBRua19dj8eDYDCIRCLB1BslSUI+n0csFoPH40EqlSpJw+3s7MT48eN5TTVH3TVDc6Sc"
        "TCuKAr/fj1gsxhSYaY4LgoBAIAAArC81GWTWbAwqZSBDktS6iRhXaqNlJdQUDSdRMhLzo7RvMhysxJpqpz0eD1RVZUKC1da0pmmM"
        "YHZ3d2PcuHElddujFZSquXr1aixdurRuD+d8Po/ly5fj17/+9aD2RSLTTU1NOPvss6sK6pR/Z9WqVSgWi4f03LXZbJAkCV6vt6bK"
        "Nx1nrK0v2u/tdntd5V3eF/bIgCiKSKfTuOGGG7BgwQKEw+G6ZLp8L6zVm3qgpJnjyH6W872Gg4MT6iEj06lUCqZpIhQKHWK8DRUk"
        "SUIikSgx5q3EudK5ASipmQbeVUB2u93sAWwVVyqvnfb5fMjlciwSJYoiNE1DLBZjfauJVAuCgK6uLkyaNGnAQmxDZ10IQH9/2wTA"
        "N/sReQCbpomuri5GYOmB63K5EA6HWWYGGXwkTJZKpRiZsv6dIt4ul4tFaqz11FbCTOup2vlZe7XSGrPZbKylHNVq0/ymNUgCPVOm"
        "TGG6B7XIHpFqXdfR29uLpqamhhRvDycoSv3EE0+gq6uLnX+lcybyPXfuXJxwwgl4/vnn4Xa7BxT1JZXxpUuXYtasWTUj4zQX9u/f"
        "j3Xr1pVEpymFdP/+/Vi/fn1DfajHknOQ1lcsFsPTTz/dUG/YSCTCDd0jhEwvXLgQH/3oR1mLrFqgshSHw8Ecg+XlMVZnJ2W5WbN1"
        "OMHmz3K+13BwcEI96M2EomzJZBKTJk0aNgJJxp3T6WR9XRtNES1PxzIMA6lUCkBfjaHD4WBp2qQ6TGSFapv8fj8CgQCi0Sh7yBqG"
        "gXg8Dp/PB9M0USwWWf1rR0cHJk2aVLEdx4gZ/ukCBAiA0PAgQ1AkCDapj1hzDJvhJ8sy2traWKo2RaZdLhfi8XiJsqyu63C73XA6"
        "nSwqbe03TeTJ6XQCADKZDGuNVS7iVy0yXW/dWNvJUZ9sr9cLXdeRTqeZ3gAA+P3+umS6nFRTe7p4PA6v1zuqSybIibhnzx4899xz"
        "uPjiixGLxWqKkzkcDqxcuRJPP/30oK7LNE2cf/75dQ0yKgt4+umnceDAAQQCAUYCqH3LI488ggceeKBiP/Lye6Sq6phRFqb1sGvX"
        "Lnz4wx9u6Du0fsZqejvHu9kgl156Kbxeb9WaZCv8fj8OHDiAF154AW+88Qba29sRj8dZlwUqY5k0aRKmT5+OmTNnYuLEifD5fNB1"
        "nXVR4HjvEmq+13BwcEI9JASXIrKGYSAcDiMYDA6L0UUkV1VVJJNJljpDvaYrGZgkSlYsFlndtJUsA32thQqFAnt4Ursvqk0k4zca"
        "jbKHayQSYWTFNE3E43EEAgEkk0lGqovFIrq6utDa2jry/XZFAUa2iNBHjkfowwugZ4oQxNpGvGkYkDwqev/6KiL3vQLJo8I0OKse"
        "LjLW3d3N5h2J7vn9fhaZtjp/aE2Fw2FGyIloy7IMr9cLAKytG32mvDe1KIqst7RVzM8avaYIDaWIW2tsrcek3qkk5KdpGuLxOFRV"
        "7fceQL8bCoXQ3d2NXC4HRVGGLdNlqIx30zSxatUqfOhDH6p5nhSlPvPMMzFu3LgBtb2hjIOJEydi2bJlNVvsWD+/atWqqi2xqK6+"
        "EQw2Vd36qteVwfqZeor0tSBJEmvXVtf5OISOz/L+xZXOv/xvQ60f0Oi6qVWSUa7yX37cw+ksrgQSO1y6dGnNdnYERVHw85//HLfd"
        "dhs6OzuZU7D83hDxURQFgUAA06ZNw8KFC7F06VKceOKJaGlpYeU09cajvNVnf/e3SnNrIPd2MHNjsHNuoOu50r5Kv1neGrX83g03"
        "3st7DQcHJ9RDAJvNxh5EkiQxFcqmpqZhMRAoZSYYDLJ/k8FfqfZSURSIogin08k2FWqNRb12y2tAKcWb2mNZVcFTqRQEQUBTUxN6"
        "enpKziuZTMLn87EewaQ0SmnhIxZxEwUYmQJcx09Cy48ugChJfcS4zk+bugEl5EZq8z6YReNgqjjfdIeDTCcSCSSTSeYEEgQBHo8H"
        "sVjskMh0KBRiDh2rgUip0m63G8lkkhEsa+TaMAzIsgyn08l6U9Nxac2Ui1SR+I3dboeqqkyUiqLTlNpMhJCItdvtRjAYZFHygcBK"
        "qpuamiBJ0qj14huGAZfLhfXr12P37t2YMmUKa7dXae/K5XKYMWMGFi1ahNWrV7MIV3+Mx3Q6jQsvvBCTJ09uKCK+Y8cObN68GU6n"
        "s+JvkdOkkQj1QASRyOAtFotM2I4cmpWIi7V0geYyaV9YnZuNGqSGYTQcPRyK/rB0TZqmIZ/Po1AoVL1eclrRc8put7M1Olj9kXJV"
        "//7cVzpPUvE3DKOkHy+dNzm3qT3U4V6n1NN55syZmDx5MvL5fFVCbRgGvF4vfvzjH+O73/0uQqEQc0rW27+z2SxeffVVvPDCC7jt"
        "tttw1FFH4YwzzsCFF16IJUuWQFGUmnOTnPx0PNJw6Y/TgOb0QNastYvDUK8J67XVu1eD6TRAGV1UzmR97pFNSJFjayr/cD8PRnKv"
        "oeulsiz6bTp2uVOBWs6SJopVc4WDg+MwEmrarBKJBNLpNIuyKYoCSZLQ3t6OpqYm2Gy2IV2wFFWh2tByb285rCSbNhOqQzUMg6V4"
        "U+001UaHw2HWHisWi7G/y7LMVL+bm5tZxJCiQYlEAoFAAL29vWyTj0QiTJV8xOqpNROyTwVMQItmIEhiXWps6gYEWYaZ1xpPEefo"
        "19yVZRnFYpG1cKEHcTAYZHWqVsOVyLT183SsQCAAQRAQDocZcbaSDTImZFlmfaILhUJV8R0COZro7+W103Qsmst0XvF4nPViH8w8"
        "F0URfr8f0WgUoVBo1KZ+017U1dWFxx9/HF/84heRyWSqppgSsbrggguwevXqAf2eJEk4//zz6xqt5LhZs2YNYrFYRZFI+ozD4Wjo"
        "eKSR0eg9JCejYRhobm7Gsccei5kzZ2LKlCkYN24cvF4vm5/ksEmlUojFYgiHw+jo6EBbWxs6OjrQ09PD2hhKksQMwkbWG2lc1COW"
        "6XR6wBkRtGZJUyAQCGD27NmYPXs2pk2bhpaWFvj9fuagohKpnp4e7N+/H7t27cKuXbvQ2dnJxDepVeNAnXYDua9UL5/P5zF16lSc"
        "eOKJOO644zBp0iT2zEylUjhw4ADeeOMNvPjii9i7dy/ba4abtNS7h5qmYcqUKczJWE0XwGazYf/+/bjjjjvQ1NQERVEaPndJkpgj"
        "0zRNHDhwALfeeivuvPNOnHbaaWhra4PNZqs49qZpwuPxMNJNpKaRe0XXSEKPtYg7jUU6na64Z9USi7SCSnkaXRMkbliP6NMzpL9r"
        "jcrsotEovF4vlixZgoULF2LGjBkIhUKQZRnZbBbd3d3YtWsXXnrpJbzxxhvI5/Pw+XzD1rFgJPcacibEYjEIgoCWlhbMmjULRx99"
        "NKZOnYrm5mZ4vV42B0lAt6urC2+//TZ27tyJt956iynfk9AvJ9YcHIeBUJNhR+1yrJ5Bn8+HdDqNbDaLjo4OjBs3jnmwh+q3KW3V"
        "GiWrtXlZQendqVQKiqLA4XBAVVXkcrmS/rkkSEbpq7FYjHlCZVlmZD4YDLKe26IoIp/Pw2azwefzIR6Ps7Hp6enBhAkTRs7gEABT"
        "O5iiJ4mAKNTnyKYAQRqAiBlHw1AUBe3t7Wwe67oOj8fDavGIJGiaBr/ffwiZpuh1MBhkBKRcmMxaS53NZlkUurw3daNrhqIylKZM"
        "Dilr7TQAeDwedi2DIcC6rsPhcCCfz7MWdtUiv6OFVD/66KP41Kc+VTOKSxG0008/HZMnT0ZPT0/daJb1nlgj3PXSvWVZRjwex5o1"
        "a2C32w/5Dcomuuqqq/Ctb30L0Wi0ajSLnIgXX3xxQ+dMpMw0TZxxxhn40Ic+hFNOOQUTJ06E0+lk+2ulDKbylm75fB6JRAKdnZ3Y"
        "vXs3tm/fjq1bt+KNN95g66Jad4d0Oo1TTjkFd9xxR835Q5kG11xzDZ588kk2txslcSQUJwgCTj31VFx44YU47bTTMHXqVCZ6WSkS"
        "ZH3W5HI5dHR04OWXX8aqVavw1FNPlQheNmrsDvS+Uq1xNBrF/Pnz8ZnPfAbnnnsuxo8fz7JErCnftHd1d3dj7dq1+OUvf4k333wT"
        "fr//sJJqwzDQ1NRUUsZSi1CT6Gh/zrl83tpsNqiqCsMw8Mwzz8Bms1Uk1JTh9tOf/hTLly9HIpFg85fK2Ko5iYggu91uPPTQQ3W1"
        "E1wuF1566SVcffXVbL1KkoR4PI4LLrgAN998c01BQ9Jf+OQnP4n169fXFVGkLJRf/vKXWLhwIdLpdMVjUxu/VatW4f/9v//Xr7VG"
        "GX82mw2f+cxn8PGPfxxz5sxhzohyITkASCaTeOWVV/DHP/4Rq1evhqIoJZlaQ4GR2mvomqi7zIUXXogPfOADOPHEEzF+/Hg4HA7m"
        "MKimTG8YBtLpNPbt24cNGzbg4YcfxqZNm2AYBjwez6gr4eDgOOIJNT1EqG6ayLXH44Gmachms8y73tnZiUmTJkFRlCHxgNFG5XA4"
        "mHBTf79PxyivnW5qamJiJEScSbHY7/cjl8shnU5DkiRIksQi1eVCZclkEqFQCHa7nSl/53I5JJNJeDyekYu4HeG8WJDEvms0+zEe"
        "h8kLa83ooPVB5Ndut7Pe7WQYUGu38kg2lSMkEgkWzab6Y1EUEQgEmOFmraUebP9Sq6gZpXhTWyzK8ggGg0NzXw9ej9frRTgcZm1I"
        "RuODngzPV199FVu2bMEJJ5xQ1ZikyMyECROwbNky3HnnnSVCYfXGP5vN4qyzzsK4ceNKHJmVjFav14t169Zh+/btVcVvyJCnyE0t"
        "4tVoiiIZ7XPnzsX111+PM888E4qiIJfLsUhJf+ed0+nE7Nmzceyxx+Kiiy6CKIq455578PnPf75m2jydOzmfahm5bre7YeeG9dwM"
        "w0AkEsFpp52GL33pS1i2bBnrDd6f6xVFES0tLbj44ovx4Q9/GFu2bMFvfvMbPPjgg6wjRaOGd3/vK2XNaJqGr3zlK/jSl76EYDCI"
        "VCqFeDxe87fcbjc+8YlPYMWKFfjGN76Bhx566LCSaor21purtB/T2A/mfK0aFRS1rkXmqRWnta90f1L0/X5/zeuj+VwphZ0cgKFQ"
        "CDabrS6h7q8StdfrZbZPNULt9XpZC8ZGQfvKsccei5/85CdYvHgxK0nIZrM1v3faaadh6dKleOSRR/Cf//mfaG9vH7Jn1UjtNWRD"
        "apqGyy67DNdeey2OO+44iKLIyhcb1emRJAkzZ87E/PnzceWVV+LZZ5/FL37xCzz//PPwer1sX+Pg4IR6BB5YNpsNmUyGkUsy9BVF"
        "YYYePVT8fj9LLQmFQkNSV03nMNgUamurong8DrvdDo/Hg2KxyCIOtLnEYjE0NzezdB0iKeQxdbvdzOMrCAJTKqYaOmvq92iuCx1L"
        "0KIZoIHa8HfnDSDIItDiHPFzpXtuXR9kgFDqlnVuU2sNa2Sa1lAkEmGOGqqHczqdcDqdyGazJZkWwwE6LkW/nU4nJk6cOORtQARB"
        "gMvlYmUUozX1m4y9Rx99FKeeeirrHlBr/zr//PPxl7/8peHxoproFStWNJQqKEkSVq9eze5PrePWquOk/bqRmksah7PPPhu/+93v"
        "EAwGmdOT9sWBOHZ0XYemaazMIBgMNhxlomurNWZU+9hfMk2lEd/73vfw+c9/Hna7Hclkks3T/jqyqM4cAObOnYtbb70VH/jAB/DN"
        "b34THR0d8Hq9Dde+NnpfqexJURT89re/xUUXXYREIsEcefXOn1rdud1u/P73v4eiKLjvvvsOK6muN0bWNnbHHnssNmzYgHHjxjFS"
        "O5g9rJHnuqZprA6aPt/fOuV650AOknprohah7u+aoHOrdWzS7ujP3JAkCbFYDGeddRZuu+02ZlNSAKPeHE0kEgCAiy66CPPmzcPV"
        "V1+NXbt2DdrJPFJ7jSzLSCQSaG1txY9//GNceOGFrLyQ5nN/91ayE0RRxNlnn42lS5fit7/9Lf7nf/4HAIa8VJODgxPqKkYubXDW"
        "jYSiZlaSSl5ISo+mWtHBGsVEUO12e5+itihAqJSpbPYFLw2zdltlMn5I3MHn88Hv9yORSDAhB9M00dPTg2AwWLJpiqKIWCyGUCiE"
        "fD7PVELpweL1elnqt6ZpSCQSCAaDo77P7qiGacI0gXGfWQQ56ISpGfXT1A0ToiojvbUdhXVvQ3A6YermCJ1uH0mmdleUveH1epmY"
        "iNX48Hg8h7TNEgQBXq/3EDJtmia8Xi8URUEsFmOR6gYWMgQcjPAf4pEwIJgG6gm8U2aKtRZwKEFREvLMj1ZHFJHdtWvX4ktf+hLs"
        "dnvV86R06JNPPhmzZs3C7t2765bEUKr4/PnzccIJJ9RM96a51t7ejieffBIOh6PumNVTDW5EUZjSHhcsWIDf//73UFUV0Wi0bp1z"
        "fxyf1t/qrzr6YK+v/FrJUfHb3/4WK1asQCwWY10hBmqoW41iclhfeOGFmDNnDj75yU9i27Zt/U5Hr3VtoiiiWCzC6XTil7/8Jc45"
        "5xxGpBu9b9QpgMpKbrrpJuzatQvbtm07LG2BRFFEPB6v+7u0Zn/+85/ji1/8Il5++WVWm09CplbHw1A7Cvuj1F3p+4O578OxJhq9"
        "tv5etyRJSCQSOO200/CnP/2JlbL0Z1+hNdXb24ujjjoKf/nLX3D55ZfXTHkfins7FONKTsr58+fj9ttvx6xZsxCJRAbsnCx3igN9"
        "2ieiKOIrX/kK5s6di8997nPIZDI1n2McHJxQDxExoJRPIgZOpxOapjFDnwSSVFVlUTZBEBgJb25uHuRDyoQkifC4D7a3KgooFgFU"
        "WvsSYJNN2BRAEvsyfisRBSIvdJ5utxt+v79Eddk0TfT29iIYDCKRSJREx+PxODweD2unRWm3lNpFqfGJRAI+n49HqQf8JBBgJAuY"
        "8J/nYPxXz4CRLTZY8913Dw1dR9dXHkXh6b0QXDZgBNqCEfG01szJsgybzcY87WTkUf9lK8k2TRPBYBDJZJKleVN0yev1QhAERCKR"
        "+sqpggBBkGCaBky9AEPLwzRKnU0CAEMEdMEFuw2QpT7HlG5UNkptNhuam5uHdc9xuVxIp9Pw+/2j0hFFaaZvvvkmNm7ciJUrV5bo"
        "J5SjWCyiqakJ55xzDt544w24XK6aUSdSXF6+fDl8Pl/NdG9yQjzyyCPYt2/fiEUKac/77ne/C5/PV5dMW8+pWruXwZCO4XQoa5oG"
        "u92OO+64A+9///sRDoeZGGe9Map0fbUM3t7eXkydOhX33nsvLrnkErz55ptwuVyDvqfW37355puxaNGihno219rjCoUC/H4/vv3t"
        "b+Pyyy8f8RINcrS3tbXVVPim8c1ms5g1axYefvhhrF69Gv/4xz/w+uuvo6uri2UZUM0tabbQGuN1piPjHMnlcpg0aRJ+85vfMNuz"
        "kTlaaa1RpHfChAm45ZZbYLPZRk4kdoBrKp1OY86cObj33nsxbty4htZof/YZq8MhHA7jvPPOw+23344rr7ySObH5XOfghHqYjAmK"
        "TpNRL4oi3G43M+hpQXu93pLUR6oXVRQF+/fvx7hx4wakCiqJJkxTQCorIFXoS5+e0qJj6jgTC6YY8HsAQwdEGdjfJWB3u4g3uwR0"
        "9Aoo5AVINhMuex+JqMalZFlmKowkLmYl1db2WDQuFLX2eDxIJpOMMGezWfh8PoTDYZaiHo/HeZR6kKTatWAitHgOeiLXJ6TWCDQD"
        "UrMLjnnjkV+7G4J7+NuCVYtOk3gfrSHDMJhycSKRKCHZfr+fteApJ9+k5FrTmBcOCpIUs9CLRQiSAJt3EuzBWbAHZ8AemAJT1yAI"
        "IjRdh9izHp7sJrx1AEgkBEAEXA4TktS3tqwjFgqFhtU5RLWOmUwGxWJxwMrHIwFd17Fq1Sqcf/75dffRQqGAFStW4Lbbbqt7PTRf"
        "zj333IbE2eg8RmpvId2IZcuWYcmSJTUjSLSPklORep7TuFj7nFPrKUqRHA17pSAIyGaz+M1vflNCpuvdD1EU2fOP3qOMplprl4TD"
        "Wltb8bvf/Q4XXXQRi4QP1tAlNfLm5mYkEgl2z2g+WstQGikhob1r2bJlOP3007Fu3TomdDRShNput2PPnj3o7u5Gc3NzzfRbItWS"
        "JOGKK67ARz7yEXR2dmLXrl3Yvn07tm/fjp07d+Kdd95BJBJhJF1VVdjt9qoCUI3sE5T2Td/tTxspygqqBsMwoGnakOyTh5tMFQoF"
        "3HDDDTjqqKMaIpM012itUbYkrTUSlJ0xYwZM00ShUBiVNhg9I3w+H2699Va0tLSUrNFac0OWZdjtdravUCkJBXWqQVEUhMNhnHHG"
        "Gfjxj3+ML37xi/B4PJxQc3BCPRwPK0VRkMlk2AOd0laJTFoj1iTXb31IWMWUOjs7EQwGG16w4sE9L56RoEgmTp6RwlnzEzhtVhZT"
        "xulwugFIAMSDHEkAoAMoAvGkgB1tAv7+gow1L0rYsluCqJhwO/oi1uU/TySHauSIVFs3ulwuB5/Px5wLFJEOhUIlvTszmQzcbjdU"
        "VWUR/GQyycQf+GY1MBjZPmIoyCIEsR8PRBMw88URE2yj9H+rk4Ue9iRkR3PA5XKx2n0yDqh/ujU9zUqmM5lMjYekAEGUoBdSMHUd"
        "9tA0BOddBu/0s+AYNx+KezwECRDEd9dYUgNOdb+Anx+1GDsPCHjpLRH3PyfhqdclpNMCnC4TsggUNAMBv39E0jpN04TT6UQ6nWbX"
        "PdqMILpXzzzzDPbt24eWlpaqxhoZ8gsWLMCxxx6LV155BS6Xq+I40r6yZMkSzJs3D9lstma6tzVSXq339HAYf5qm4YwzzoDdbq+a"
        "SknOJU3T8Oijj+Kll15CW1sbE3e02Wzw+/1oaWnB1KlTMWPGDEybNg3jxo2DzWZjqvb1CMVwgRS0P/7xj+NjH/sY0wapNy98Ph8K"
        "hQL27t2Lrq4u6LqOQCCA6dOnIxAIIJFI1HQYyLKMWCyGBQsW4Fvf+ha+9rWvDVnmAdVQk1OPnB20b5Ghnc/n6zvuLPf4wgsvxJNP"
        "Pjmi65R+u6OjAy+88AIuvfRS5PP5usr71IaJuicsW7YMZ511FlNE7uzsxJ49e/DGG2/gtddew5YtW/DOO++wtP/+9OGmYIPdbmdq"
        "5ACYwFYj6dz1BLVoLlGXiIGu6cNpm1gVyS+88EJEIpGGyCS1gNq7dy86OjpYtwzrWqMAiNVpNNpAZT433ngjjj322LqOO7rngUAA"
        "sVgMb7zxBpvTLS0tmDZtGhNFreW4IR2kK664As8++yz+8pe/NCycycHBCXV/fkCWWd9l2ozsdntJaw5BEKCq6iH11GRU5PN5lgId"
        "iURYi4laG7gsmkgXRJiGgDPmJfGZs3qx5JgUoADQ+kizkTmY8W1NXz1YV+1zmjh1volT31fA9z4G3PesjP97WMErb0pwOE0oUuWU"
        "ViLVkiQd0h6LyLPD4WBebsMwkMlk4HK5SlI+U6kUXC4Xcrkci1KnUilWQ8uj1AN54gxwzASMWFswMvCoPIDmvcPhYNkbtD6obILW"
        "B6WFu91uNu/IaCBDifq/V1o3giDCNA1omTicE96HlkX/D4FjPgjZHQQMwNCKMIppmAWTLRpJ0JAvejDO9Tpk0cC8qRLmHV3E1ecU"
        "sXW3iF+vVnD30zISaRPNATuCwcCIRJ8o8kRkajQ6osprlz/96U8zx2MlaJoGn8+H8847D5s2baoaySPjb+XKlSV7TTVyRLXc4XC4"
        "Yu/p4bz2OXPmMA2JSp+RZRm9vb34/Oc/j2effbaklZv1GsihqaoqWlpacMwxx2Dx4sU47bTTMHv2bJaGO5JzgO5DS0sLvvKVr9Rt"
        "W0bX7PF4sHr1atxyyy3YsWMH0uk0u0+TJ0/G5Zdfjk9/+tMsIl/tWUAaCVdccQXuv/9+vPzyy1WdMAMx3snRJwgCHnvsMTz99NN4"
        "5513YJomZsyYgUsuuQQLFiyo2tvZOk75fB4nn3wy0xsZyfVKc+eee+7BRRdd1NCz1VqPSp0/rH25J06ciGnTpmH58uXQNA09PT14"
        "/fXX8fjjj+Pxxx/H3r17Wd/vWuuN9rG//vWveO211xjZp1Z6S5curTmvyBF32223sX2gWq9rm82Gtra2QdcIH659lubjZz/72YbO"
        "gRxXL7zwAn7+85/jlVdeYRo4qqpi8uTJuOKKK/DpT3+aiaKNZjKdTCaxZMkSXH755YjFYnXJNDkbfvnLX+Lee+/F/v37mYPG7Xbj"
        "mGOOwec+9zlccMEFTNOo1nrI5XL4yle+gieeeKLmXOPg4IR6AJsqtdagCAmRgEKhwNLW6D1KaSKSSTVI1tZAAOD3+9Hd3Q1VVZmC"
        "NnnJrWS6Ny1j7oQcvnNxB5bOS/X1WM4BRl6AIJgQBEAU+4LTFc9fB8yDgtB2CbhqpYaPvl/D79cq+K8/2RDNCPA6TWh69YeYLMsl"
        "vaVJyTsQCCCfz7MHObUTstZN03s2m40RglQqxdqacByZIIcSRewoy4PmBL1ndUJZ26j4/X4kk8mS1nSkEl+uFl7yu6IEvZCGICmY"
        "ePZ30XradZDsDuj5PLRM0iJIJpb4FgRBAEQZ89yvwBQALS9AzPX5Lo6dbuCWr+fx6fM0fOUWG3ZGx0EUBRi6AXMEwv2iKMLlcrGo"
        "0Gh1RJG69sc//vGa50f1geeccw5uvvnmiqmpROLGjRuHM888s2Z0mn47lUrh0UcfHVHCSQSxFoGn/qs//elPsXbtWkycOLGujoZh"
        "GOju7sb+/fuxZs0aeL1ezJ07F5dddhnLiBqpayTxyauuugqzZs2qm35KfV1vuukm3HjjjZBlGQ6HoyRV+K233sJ1112HzZs34ze/"
        "+U1JlLjWOH/605/G5s2bh2z+E+kIh8P46le/irVr1zJnBznx/vjHP+LHP/4xrrzyypJ9qtI45fN5TJo0CVOnTsUbb7zBMtZGai66"
        "3W4888wzeOihh3D55Zc3lJZfvmdbQYEA2qs9Hg/OPvtsLF++HB0dHVi1ahV+//vfY8eOHczZWYvo/vWvf2XZK5Qm/53vfAfnnHNO"
        "zewO2jN++tOfsuyIWu25ZFkeVMourc+R3metWTknn3xy3cwICtg88sgj+NznPodsNguXy1Wy1nbv3o2vf/3rePXVV3HzzTePervL"
        "MAx8+tOfhqqqNR2zNC90Xce1116LBx98EB6PBzabja27QqGAF154AevXr8d3vvMdfO1rX6sZqabo+DHHHIMPfehDuPXWW3mUmuM9"
        "B3E4D07GmvWBr6pqSZoSEYN0Ol1Sf2VNZaUNzuVyoVAosBZVHR0djDgw77BoIpKWcfFJMdz/1T1YelwKRk6Ake0LMkqiCVGon71L"
        "hFuW+mJxegKwmcC1lxTx1E+yWDhNRzwl9Akw1fAYUh0cGRuapiGXy7FIAUXZre/RGBQKBaa4S5FvIurc83fkgQyaQqHAap/JIKYI"
        "CM0XimxQhIq886ZplniHqScvqXJWnOuiDC2XhD04E7OvfhyTzrkeMNFHpE0dgihDEKSKUXrTFKCIwFH2f0EwAUnoq5sWRMDIA3oM"
        "OOkYHc/8bw5fviCBVFaACWHYAv7WtnXJZBLRaLRqj+fRAHJ4vPjiizX7P1sddccccwxOPPHEiqn7ZNgsWrQIM2bMqNk2jOYW9cMe"
        "KYVlmsOSJDXUW7WzsxOqqrL7ahhGSSsd64scUD6fj3WHePnll/HVr34VP/rRj0ZURZrSST/0oQ+VaBnUMvAffPBBfP/734ff74fH"
        "4ykRE6TnZ2trK+6//3786Ec/gtvtrnk9pKR+xhlnYMaMGUOiwUH7VDqdxic+8QmsWrUKPp8PgUAAPp8PPp8PTU1NEAQB1113XUOR"
        "cXq+T5ky5bCUZ1Af7v/+7//G66+/ziLlg92HJEliz/1EIoFoNAqv14trrrkG//jHP/DlL38ZuVyuZqcFSvlubm5GU1MTmpqa4PV6"
        "a7a2Kz+XYDDIvlvt1dzcPKiUb+v5Hg5HdLFYxHnnnVc36k+lNjt27MCXvvQlmKaJQCDAnpnla+3uu+/GL37xi36p5Y/0tedyORx9"
        "9NF4//vfX/d5Rw6kG2+8EQ888ABaW1uhqir7m9UJ5Pf78f3vfx9///vf4fV66+41hUIBH/rQhxrqFMHBwQl1PxY5ALa4KepM3lvy"
        "kNHCo7Q/IgYAWD01fZd6dtKDKpvNor29naVFS6KJcFLGJ5f24v8++w58dh16SoAomhiMPS0AILtViwALZhp44n9yWHyMjniyOqkW"
        "BAHJZBIej4cZkWTg2Gy2EpE2IspEluk9asdBD6lGatIO8+7+bop01ZflcxyHOKGoVyQ92Gw2W0mkkYw/6h1N7zmdzpL3KKUtm81W"
        "NQQEUYaWjcM96RTM+czz8Ew9DcVUEoAJQZRR6yYJMKGbMnxSDBPsewATEIR3jSlR6Fs3RgaAZuJbl3fify4/gHRe7OvvPYT3n9KA"
        "c7kc0uk0IpEIOjo6WO9Ma9uw0QZq67JmzRrmFKllrNpsNpx//vlV76lpmli5cmVdxxsd69FHH61TVz/05IXKFmoJQJGRfMkll8Dt"
        "dqO7u5v1laZ7Ti2niLjQPmvtW+t2uxEIBIa8lVG9+ZjNZjFnzhzMnTu3bqaALMuIRqP42c9+BofDwUh2+fnSs7K5uRl/+tOf8Npr"
        "r9V0ElgzFhYvXsxqnwcDMshvuukmbNiwAa2trYc4NorFInOe/+1vf2toXsuyjNbW1sNiiJMjJhqN4qqrrsKrr76KpqYm5rwZCnuI"
        "5qmmaejt7YXdbsf3v/99/O53v2Oku9pasIqS0as/41Tp+5Veg73WRuvCh8N55fV6ccopp9RVa6d971e/+hUikQgcDkeJ2Fv5WguF"
        "QvjDH/6AXbt2weFwjLpnCO01p512GkKhUN2e1m63Gy+//DLuvPNONDc3V51LNBdUVcVPf/rTmlkm1vOYP38+Zs+eXXfP4+DghLrB"
        "TZUeHNZ6KBLZssJut5d4zSsRA2sbHOt7kiSheFCsLJtJIpJW8G/vD+OGK9qhZwQYOiBJQ7v5yTKgp/pqrB/9QQ6L51SPVJPwTqFQ"
        "KIlIG4aBQqHADCEyAq0RaTI4yZlARmgulxs16rWHEGkAZlGHqRkwNb3Gy2Cf4yidL5StQP9vt9uZsVMeiaa1Vc0JRelr1WrsBFGC"
        "lkvAPflUHH3lasiqH1ouWZdIW1Y6NFNGQOmBXwkfLKs2Kzxo+46mxQVcekYUN11xAJmCOGh/CmkTCIKARCKBjo4OdHR0MHV8a7Sa"
        "nG6jEbQ3PvbYY4jFYjXPk4yW97///Rg/fnyJiBnVok6ePBlLly6tGakgAtHV1YXHH398QN0ThsIIpB7GlYxUcj6efvrpeOSRR/DZ"
        "z34WCxYsYFG0VCqFaDSKSCSCeDxeIuxIBJuMyJGOLJEQ5QknnACPx1Pz9ymS/cwzz+Bf//pX3Sg6PfsSiQQefvjhuj3JCSeffPKQ"
        "RKcdDgd27dqF++67D4FAoGokl9SDd+3aVbfcwqrkXiuFfThBkcsDBw7g4osvxh/+8Ac4HA74fL4+Z3o/SWytuUHlXeFwGBdffDF+"
        "+tOfIp/Pj/ln2Eg6raz7RKFQwKRJk3DUUUfVnGv0TN23bx+eeuopuN3uujXsiqKgp6cHa9asGbWRV1EUcfLJJ9cde7In//a3vyGV"
        "StV1Mluj+c8//3zd9nuUafO+971v1Kqhc3CMKUINgEWQre1NZFlmHnLySJPhYSUBVFNlTXml1iPl/UcFUYQoGHhrdw8uPaENN1zV"
        "AT0HiDAHrEFV/9oAIwf4D5LqhTN0JDMCJLHyRpdKpaCqakkabjqdZmmM5RFp6zXm83lGoMiLPeqibYIAM98XNZJDLsh+R/1XwAnZ"
        "5+BR6jIjmfQFaF7Y7fYSJxSRL6vxRQ6ncseU2+0ucUKV3jIJeiEDtWkWZn18NSTVD72QO0imG73tJgqmhKPU7VClLAxThFClpZgg"
        "ALJkopgQcMkZUdxwcTsiaQmyaPZzqr1br5jJZNDZ2YloNIpEIsEcB5Q+SRHaSnvHaALtcdu3b8fmzZtrKm2TU+2oo47CkiVLSpwl"
        "lO69dOlSTJw4saZBQym269evx+7duxsmZUNNOHfs2FEzkk575XHHHYef/exnePjhh/HYY4/h73//O/70pz+xVi3nnXceZs2axaL9"
        "kUiEPWsOV0aPIAiYO3duw59dv359w8Y6GcabNm2qm+JJUeqjjz560CruNFeffPJJ9PT01M2CIJXzRiPjlMV2uEBZc/l8Hl/+8pdx"
        "ySWXYM2aNRBFEaFQiKVZUyR+MP2lqWd1b28vPvrRj+Kqq66q2Yt+LD3LDofzaurUqfD5fDXFw2j+vv766+ju7m6o5ISezRs3bqwZ"
        "/T1ce4yu6/B4PJg1a1bd86OWeps2bWKliI1A0zSsX7++obnZn32Pg+NIgjycC52MWMMwmMBHuRiZNdWGyEIulzuEQFQzGkQRyORE"
        "nDRbx/evjMDIjYwosygBeg7we0386at5LP2GA7li3/mU788UIXM6nawVEqVgUeouRfSBPnVWij7m83nmULAei1oBjQYyDU2H3OTC"
        "9D98DO5FR8HIFGrfANOEIIvQ4jns/tid0OJZCLJ06MC9xyBJElP0pciroihs7pNThfpiljumyqPThmFUSX8TYJo6BEnBtItuh+IK"
        "WSLT/bj1MKGZwEzHNkAETF0EhNoPaFkyoSUEXHlWBK/sdeKBFwMIujRoRvWIgrWfbaFQYJGdQqHA9hESHaPv6LoOVVXZOFFPzdHa"
        "do6MwtWrV+Occ85p6PMXXHAB/va3v5Xsn7Is44ILLqh7jZQBsWrVqsMSEaRzffrpp3HttdfWJFvkKKByl+bmZowfPx4nnHBCidJy"
        "IpFAe3s7tm/fjk2bNmHDhg3YtWsXaxk3ktEzimxNnjy5rjowCUft2rWrYX0MSlvdv38/wuEwmpqaqhrTVrVxEskcjA6Hrut46aWX"
        "GiLIdO8KhQJUVa07FiTeeTjXKGU5+P1+rF+/HuvXr8fxxx+P888/H+9///sxa9YsBAIBth+RE5T2qkoiZY2M0Re+8AWsWrWK2QNj"
        "TSeF7tvhyKAzDAMTJkyoS5DpGbpz586Ga/XJefX2228jHo/DbrePKsVvSktvaWmpeU3WFnFtbW0NOROsDoVGMk1of5gyZQrX+uHg"
        "hHpIyOZBo94aeaZeolbYbDYmx08bnaIorE66UsS6AjeDABP/95kC3B5AT75b7zz8BAjQksC8uQa+dUkBX/+DHT7vocrfFGUJBoNI"
        "p9Ml6duU3k4gw8NaZ07GGRlM1M96VDxERQF6Mo/QR46HqCowizpEVQZM1CbUigSA11GXGySU7k1OKKrjsvajpugIOWZcLheKxWIJ"
        "sXK5XCVlE6X3TEQxk8Cks78H74zFKKb6T6aJUksCMFXd2Y9vAKJgwtSA/7qkE5v3uhBOyFBk8xB/CtUdapqGdDqNVCqFdDoNv9/P"
        "rlVRFFZSQUYojSMJrVhLL6zraDSBUuueeuopHDhwAH6/v6pxRAb44sWLcdRRR6G9vR12ux25XA6zZs3CKaecUrOVDjkp9+zZg+ee"
        "e27IWin193rdbjc2bNiA559/HmeccQYikUhVZWXrtZS3KaJ7rCgKZs2ahXnz5uGyyy5DJBLBxo0bceedd+Lxxx9nvdxH4lopElZP"
        "6ZaM1XQ6jZ6enoaJFD0vU6kUent70dra2lBGgsfjaag/by3Cm8lksH///oZq9InMjzW1X3LKUY/i1157DZs3b4bP58OsWbOwYMEC"
        "nHDCCZg7dy6mTp2KYDDI2lvmcjmWVdRIRI8cKjNmzMCZZ56Je++9lysk9/O5aRgGE8KrNSfps52dnf16BlCmRSKRYJoBo+XaKc26"
        "XvYJ7TW9vb0NpXuXX39PT09dZw+dTyAQqKubwMFxpGHIU76t9dNWLx610LIqvNLDlt6jFlHWumKHw1ESsS7xBkhAKiXgk+doWLRQ"
        "hzaCZJptNDKgx4H/d1ER75upI50VKgqgETFSVZVdHzkJrESgUCgcYuxomsbqqKleaFTVUR88DSNTsNRH8xrq/j4YqY6eoqjlTih6"
        "r7xmUVGUkrpra8T60LZKIvRCBq4Jx6F1ydehZbIQRGmAa12EIhqYYnuzT5AMjT08RQHQCwKCIQ3Xnd+FdEHsI9nmu+q4dP6RSIQp"
        "+pMzStO0EnEYqpG1ag0Ui0W2x9DYjeaaLkrv379/P9atW1eT5NI+0draijPOOAOZTAaKoiCbzeKss86qGa20kr0nnngCXV1dDUcq"
        "hmvOX3/99YhEIvB4PA0pK1sVlK310oZhIJvNIhaLIRqNQlEUrFixAvfccw9+97vfsRZqwy2UY3WINSJiRPezv8Jw9CxoRMWenLJW"
        "3Y6BzFEqTaLU5EbmjfWZPtZAqvIulwvBYBAAsHXrVvzxj3/Ev//7v+ODH/wgVq5ciauvvho/+clP8NRTTyEej8Pv9/c7K0IQBCxb"
        "tozXnQ4QJObXyDymDjL9XWvkpB5NRJH2c9rH62WApNPpfj0LrU4/+l49R5qqqsx5yeczByfUgzQoKDWT/k31oeXk2doKyG63l6Rt"
        "ktFUqf5KAFDUAY/bxNcuKsIsYNhqputySR2wuYGvX1SEVqyc7UxRMxKPomsuFossPdfqYLCSbOqfavUAUtRyVHkAxUYUvrnK90Cc"
        "UMyJVOaYonlhFSijDIfKc0OAqWtoWfRlyKoDpqFhIDdCIEEyKYyJ6m7AAAShcQeJJJkwMsCKhXEcPzWDbFGGIvdlZJQLjFkF1sig"
        "t5Jlun6rQWHN7KC1Va910WhxrKxataqhKLqu6zj//POhqio0TYPT6cSKFSvqfpfGcPXq1Yc1LY+IyrZt2/CJT3wCPT09LMpEAlD9"
        "Obdyom0YBuLxOBKJBC677DLcfvvtbKxGwsij82nE+TlQ4TQifI04LqylE4O5Jk3TGu7pTs6FsR6pst4fp9OJQCAAv98PQRCwb98+"
        "rF69GjfccAMuv/xyrFixAp/97GeZ2F8ja4ye87Nnz2ZCWWONiPT3Hlvn5GDmBx3HaiPVGmfaOwfyO6OVIJY/D+s9NwYSkKG9pt73"
        "rAEzDg5OqIfAkKAHrnVxWSPPiqKURN+spJs2WDKGK21+kgRkMgIuXaJj1iwDRhY4XLayKAFmCrh4qYZjZ+jIZIVDyL3VoLc+QIgI"
        "WA0fim7QZzRNY1FH2ti4guIRthAPesCtTigSoSt/SFkVv62OKQKlQR8yPwQBupaDPTQNgWMugp7P9/WXHtAaN5E3FUxSd8OrRGCa"
        "QsMRanJEGYYAm9PExSdF0RvLIRzuxoEDB9DT04NsNsvGRdO0EqcT7QdEmqwR6XIDgN6j9TcqFfItho7L5cKmTZvqtmih1NuFCxdi"
        "7ty56O3txXHHHYfjjz++Zro3RTO2bNmCV155ZUT7Mle7Zq/Xi+effx7nn38+/vSnP7GaQLfbze5xuQhUIwa4tVVRT08Pli5diq99"
        "7Wusrn64yTRlJTUS0Wq0J3clw7Ve+jbNeTqfoSJP/YlwHUmwzkegr1MJ9T13Op3o6urCX//6V1x++eX4t3/7N6TT6bqkmvaw5ubm"
        "uqrwo90h2Iij32oHDlYQ0ZrdVW++WUuF+jvfy4UuR9OYN6pAT2PeXycGOe8bvbfW8+Fp3xycUA9ygdMDgR765UY/ReToQU9pe+SZ"
        "rZTyWvJQMwFRNHD5aTkYuggNMgxTgnkYwp4CAF0H7F7gopN1aEVUTfu2kmV6iJYre1O7kfJoW/lnOKE+smA1okjYxroeiFxYvcRE"
        "qK0PfVEUK0YpBUGCUSwgOO8jUNx+GHphEOp9JnRTwET7XkiiDnMAW4kkmDALwHnHxaAU2xCOJGEYOrsGKxG2kgYiVFSjReNk7UNc"
        "bR2NdpDq79q1a1l5SDUUi0UEAgEsX74cmUwGK1asqGuMU7T/H//4BxNIHA3z3uv1oqOjA//+7/+OlStX4oYbbsDGjRuRyWTgdrsR"
        "DAYRCATgdrtht9vZfCBiU89oUxQFiUQCH/vYx1iP1OHaP63lO40ocNM9cbvdDUfArFldXq+37ty2ns9YFLwazbD2Pafnu9/vh8/n"
        "w7333ovrr7++IdJIqbKjtTVTQ3v6QQdPI/OLdCOoXnyw6zGdTjdm9Ioi/H5/v8aYMr9ojY6muUcaPdZgVK291uPxlDioG7XnG/2e"
        "VYiQ96Hm4IR6kGS6vBZUluUSo5/IgjX1jj5j3Qwqpbz2/QZQKJpoCUmYM8MPUTNgt2kQJR0CTBimBN2UYUDESOUVCwIADTj7fToE"
        "2YRRZU+z1kOXk2X6L6VzW8fTMAzWu9Jaf81xhCzEg8J7ZGDTvbbODXqvkqFc/plKD33TNCBKArzTz4JpmIOSwhdgQjdNTFO3AwJg"
        "msKA1oxZAFpbDZw0y0SxKEEShUOuj9LZrcZC+RqhsbISaGvUmtYavTdaCUV/CC9lNZx99tlobW3FmWeeWTcVtz+EfaRJtc1mg9/v"
        "x1tvvYWf/OQnuOSSS1h96g033IC7774b69evx549e9jY+P1+BINB2Gy2mtdC+2ooFMIZZ5yBbDY7rPsnCU3V6rNtvXa3243W1tZ+"
        "RZA1TYPf70coFKqbxk59qxOJxJhvyzScxGQo5oSVYI8bNw5r167Fnj176oo0WVOXx6LDg5y+5Dyol3pdLBYxceLEupoPjd677u7u"
        "umSPzmvixIn9sml1XUdTU1NDzqvD4cSIxWJMzLfedTQ3N7P2Yv25/tbW1roZTTQHwuEwt1E53nOQR+JHyr1mRKitKSGkkFn+cKu8"
        "0UoQ9CTM5uW4pu0uTO98Ace5N+IU7xOY5dwCVT6omm0CMADd7DMgRMGEAKNsA+iLdgsHPy4NcP2LAoACMH+KgUlNJrpjAhS5tBMU"
        "PUSs6sNWrzalLOm6zmqtaTzo8xzvDVjFtKwPTuuaoTVSKQW8Ens19QJs3olwjJsHQ9MgDMKfZhp97qrJyr9gGOhXuncJgTQBUQaW"
        "zDHw6ObKHJ8cBFYHW6FQYD1haTxoTMqNp7GE8pTsxYsXV01RJifM9OnTce2112Lq1Kk1jRhSg33sscewa9euw6Lu3QgRcTgczHDb"
        "v38/3nrrLTzyyCMQRZFFcn0+H5qbm3HUUUfhfe97H8455xxMmzatat91628cf/zxI5LyXSwWsXfv3roElrKx5s+fj8cee4xpIdQ7"
        "fqFQwIwZMxAKheqquiuKgvb2diQSCa6+W4WUZDIZFokbiowW2n+y2Sy6urowbdq0mg4v+s3RFtlrdCxo/7V2YahlE+bzeZx00klw"
        "u92IRqMDdvSQ/djW1laXxNHzcu7cuQ33Yaa1dvTRR8Pj8YyqXuFEYOPxODo6OjBp0qSq5YDWsoLp06ejvb2dBXcacXjOnz+/obIU"
        "URSxZ88erlLP8Z7DsESoyyNk1lRu+kz5oqzVO68yOTDhaD0BMYTwXHQl/q/t+/i3nc/jo2+8jm+8eR9WdV+NPdk50CFDknVIsg5B"
        "MGBCOBi9lvrqPiVA8gCiE5Dcg7luwCgCwZCJo8cbyBeEiiJpjRj5lQh0eT3oQIUlOEYneSYyQffTSp7LP9fIsQ55HyIMLQ97aCYU"
        "dyvMwaR7mwZg8yHoEnDyuNchKhhwD3FB6HN6LZyhAzBrHqaRdVO+Zqw9YcvHeNRuyv0QDSMnyhe+8IWG69saFT0bqblfbgBTjSql"
        "NFN9qt/vZ+3B2tvb8fLLL+O+++7DN77xDZxzzjlYs2ZNXXV0XdcxceLEho3pwV7btm3bGiLHxWIRy5YtazhrgIjBsmXLGop8yrKM"
        "7du3D3tkfizuvYVCAS0tLbjllluwZMkSJJNJxONxAH1ZcoMdL0mSGnJeUeputXaHldb+SCGXyzVEvCRJwsSJE+ueG6V7f/CDHxz0"
        "XkQOqX379iEajdbcM8nBcdxxx2Hq1KkNa9GYpolly5aNyrVDzqAdO3bUJbyUur5s2TKW+dXItTscDixdurSh8dJ1Hdu2beP7DAcn"
        "1IP1lhF5tqbe0HvWh3u5YqIsyxVTVytvDiYEEVCDMyHDhFuOI6gkYRPy6ChMw9rIZfjO3jtw1fYXccX2l/CDvbdhXeRD6CxMgSCY"
        "kBQNotiXmh3PCfj+7QpWfEvFXWtkGBJgDvj6AcjArAlmXxuhCsJkFE20Ep/yNHBN0w6pByVCbU1n5TiyUN5WrtwokSSp5DMk2mdd"
        "R1ZtgnJKbRqAPTgLgjSIth+mCVFRkdjzFHb9+QJc98s27G4TIdqNAXFqKpWYOs6E193Xw73S87q8HrpSGriu64cofZcT6tHYg7qS"
        "0dPftlaNCFNRW65nnnlmVESnqXSF2kVVUoa1ps8SyZYkCTabDS6XC36/H83NzYhGo/jFL35R1+AjQ77RyMxgnoWqquKVV15Bb29v"
        "zXtIROrUU0/FqaeeikQiUfN+UnRv4sSJ+OAHP9hQ2yxd17Fx40Zu5Na4XytXrsSDDz6Iu+66CytWrAAA9Pb2snr7anO02ty22WxI"
        "JBKYM2cOjj766IrdSqy/rygKuru7WTlDtflSbgPUm+82mw1Op7NkL+zPuFAEtJEUXl3XWQZItc/abDaEw2FcfPHFOPnkkxuav/XO"
        "UVEUdHR0YNeuXTUdTDRuLS0tuOiii5BKpWquNeoyM3PmTJx77rkjImg40L10w4YNDTltMpkMPvzhD2P8+PF176ksy0gkEliyZAlO"
        "OumkhjJhenp68Prrr4+qkiIOjjFHqId6g6BFWvGBIgJ2/1EwDQEG+mqmTQiwCXn45BT8cgqAhN3Z43B/97/hy28+hMvfeB3X7FyH"
        "P7R9By9Ez0BW9uCbf1Dw339W8fgWGVfepOLPT9phOGUU9f4PjXlwRKe1mFVZubWGfCjG5z07cYW+PuT9eY32IRuKe2otpSjj04DZ"
        "t2YEkc3Wfk5wA6JiR6ZrG968awWi/3oUt65RcPGNdmTyAiD2P1BNbecmBEz4nIBu1HbWjYYxHgnjXlVV7NmzB88//3xD5LceOSQi"
        "+fTTT6OtrW3YCWWjZHrevHk47rjjEI1GEY/Hoet6SW/pSveL0vutassOhwOZTIYZiIc7pZkiQbt378ZLL73UcO3hd77zHTidTtZb"
        "nMaAIvnkVEokErjuuuswZcqUmmnE5EjZt28fXnjhhcOu6j6aEY/HUSgUcN555+HPf/4zHnnkEXzta1/D7NmzUSgUEIlEkEgkWGmW"
        "tUUbKSDTvNU0Dd3d3WhpacEPfvCDujX+FETYtWtXQ/3IBUFAMpmsqxxOugFz585FOBxm7xPhLX9VO69wOMxqdGs5hlKpFM444wyc"
        "dtpp6OzsLBkXuqaOjg4sWbIE3/3ud5HL5YZkT6asnmeffZY5mmt9NplM4pprrsGxxx6LSCRSda3puo50Oo3rrrsO48aNG5UOWdrb"
        "N2zYgHfeeaeuQyGXy+Goo47C17/+dcTjcXaPy69fURRkMhm4XC58+9vfrpshR+fx4osvYu/evby0hIMT6rEEUy9WILUCdFM6WDdt"
        "wCFm4JeT8Mgp5E0HXkouw//t/z6+sOcpXPr8s7hvkwtutwGf04QoS3jgmTwkUYMi9m3Iutl/9fCixifWcJPpTEFAT0xAT7yxV29a"
        "QEEb/aT6cKyZxomeAVGREH3jAeiFImRXCMGAgdf3injhDRGCA1XF+OpB0wGdP3tLDB/TNPHII48MSe9TSm1dtWrVqKj/IwP4lFNO"
        "wZo1a3DbbbfhggsugMvlQiwWQzQaRTqdZtkWVqNclmVmqBN5CYfDOOuss+Dz+WoKdJHRPxJtB4nQ3HfffQ2NRyqVwkknnYRbb70V"
        "Xq8XPT09yGQyKBaLKBaLyGaziEQiyGaz+N73voerrrqqbj0ntWJbtWoV2tvbuZFbAxR9jsfjSKVSmD9/Pr773e9i9erVeOCBB/Dt"
        "b38bZ511FlpbW2GaJpLJJKLRKCKRCMLhMCKRCGKxGNLpNHw+Hz7+8Y/jkUcewcKFCxuKwpqmiU2bNjW8frq7u+uK0VFE9pvf/CbO"
        "Pfdc5shKpVKHvDKZTMVzosh5R0dHTUccOXMVRcFvfvMbnHfeeUgkEmyMYrEYBEHApz71Kdx1113wer1DRlDJCbl27VqW9l1vXfr9"
        "fvz+97/HnDlz0NXVxZSyrWstn8/jhz/8IS699NJRVTtdfu02mw1tbW149NFH4XK5atYvU8bBJz/5SXzve98r2Vdor8lkMujp6YHX"
        "68Vtt92GE044oeE5fN99943aft0cHMMJeUyfvVDPHyDAgACYfZ+ToMMlpSCIBkxBRo84F3BOgpbYCtEdhKBF0OFYjn90T8YJ0mNo"
        "VdsgyRoTNzNMEaYpQhAMCDCrCjHxrLphNHpEIJ4RsHi2hhWnFGEUULFWvWSTFwSgoGFzq4HOogBFGHha/9hnaoOZnJQ2PgOmbkI0"
        "88jkALsCTAiZwCAcFqII8MfvuzAMAy6XC+vXr8fu3bvrRiLrHcvhcGDHjh3YvHkznE7nqBCMoXpGu92Oiy++GJdccgnefvttvPDC"
        "C3jhhRewbds2tLW1IRaLIZ/PH9KDmqIooVAI3/zmN/H1r3+9ptFHkZi3334buVwODodjWMeB2oGtWbMGGzduxCmnnFJTuZ0M3RUr"
        "VmD27Nm48847sXHjRvT09EDXdfj9fsyfPx8f//jHsXjx4rqqvmRod3Z24o477hg1932sEOtMJsN6SC9atAhLly5FPp9HOBzGgQMH"
        "0N7ejq6uLiSTSRQKBdYua/LkyZg9ezYTCayn1m8lRM8991xD2QyyLGPfvn11U5CJQE+fPh0PPPAA9uzZg56enpKSMfr9AwcO4D//"
        "8z9ZyRmtM1KR3rp1K44//via7alI3X7cuHG455578Pzzz2Pbtm2sTn3hwoWYN28estlszRT4gexxTqcT27Ztw+OPP45LL720ptAZ"
        "pT4fffTRePjhh/GnP/0JTz31FDo7O6FpGnw+H+bPn4+rrroKixYtQiKRGNXlErTH//GPf8Qll1zC1notx2I6ncZXv/pVLFq0CPfc"
        "cw+2bt3KnB7Nzc049dRT8YlPfALTp09vyHHn9XqxYcMG/POf/xzTvdQ5ON6ThNo0Cv37PASYpgRAgmnocDgkTDrrBrz98OdQSPfA"
        "P/lYGCf9Gt/eOQMBIYJpjn9hvusFnOh5CgvcG+BVIoBoAAYR7L7INRFsoC/Vu8Aj1MMCikzPnazj799Jwj+uj8Q1xMRM4OvjdOwr"
        "ADbBPCz9ysfiminl4iL0Qg7BeZci/r5H0LH1n7DLIr7z0TxmzzBgpAfuTCpqA49uH5H36WBkqKurC0888QS+8IUvIJPJ1K2VrnYs"
        "VVWxZs0axGIxBIPBUWPskKJ1LBaDLMuYMGECPvaxj+FjH/sYUqkUuru7GXEJh8Ml/Va9Xi8mT56MefPmYerUqUilUg21zdm4ceOI"
        "Xl+hUMAPf/hDPPjggyU6GNXIXCKRwKRJk/CDH/wAyWQSyWSSEQa/3w9d1xuKlhEJv/HGG7F7927W75ej8XtHcyaVSrH7RgrzCxcu"
        "PKQsgWr+8/k8IyeN3qff//732L9/f931Sa319u3bh/3792P27Nk1U6cpzVcQBMycORPHHHNMyWepZd3u3btrrp2nnnoKV1xxRUPj"
        "Rs6/M888E+eeey4bm3w+j0QiwdKKDcMYMqJKZRO//e1vsWLFirrjTqTa7XbjG9/4Br74xS8iHo+XrDVN09haG80isCQctnPnTtx8"
        "88248cYbEQ6HoShKTWdLPB7HKaecgiVLliAej7MuCR6PB16vF5lMpm6rPRr3QqGAG2+8kXWy4XsNByfUI7T4y+uIrTWSVvGuSput"
        "IIgwNCDbvRWBuSv7Cjf7uc8JggQtl4P/mIswd/xCZLt3wD1lMSSbCmgJ5EwXXk8txouJxbir68tosbVjhroVp/rW4nj3c5ju2H5I"
        "ey4TMgy9LwW2rzdvZSOZIi3W67VuPpTuyVW8y+8ZkC8AM8cb8AdMFHoAsYEMLAMCRMNEIXgwgjpGiVultlA0X6zGkSzLh0YzTROC"
        "BGQ6t8DQ+9bQAO4AYBowBTvmffRO3PrR2Tg60IFZMwAzMzAybZiApABvdojoigpwOvpExCsRDavRWGmNDEWrm9FIqlevXo1PfvKT"
        "A043lGUZ8Xgca9asGZUpv0Q6iHzmcjl2z8ePH48pU6awqGH5fqjrOnK5HGKxWNWaayIhVNP85JNPwu12j0gtMbVheu655/CjH/0I"
        "N9xwAyKRSM1zJeM0l8tBkiR4vV52DY2StGKxiKamJjz00EO47bbb+tV3lqM6uQb6RESLxSJbR+UtQenzjaxXXdfhdDqxZ88e3HLL"
        "LQ3PS1mWEYlE8Mwzz2DBggUskl7v/LPZ7CHnTNHNVCpVde243W6sW7cOO3fuxIwZM+qqxdPfyBlEY2O16eh3C4XCkOxJdJ4vvvgi"
        "br31Vnz1q19Fb29v3XHRNI2tyWprjfYP630fbSDHzC233IKTTjoJF110UV1SLUkS0uk0y3rw+/3sWDQm9ci0rusIhUL4zne+gw0b"
        "NnDHHcd79zkx1IYRKe1aWxdUUrEuV7q2qvhaSXflVdxn2+eiew6S1gGSTkGEXkhDcY+Hf/a5ECQZRjEPAwok6HCKaQSUJFxSGtFi"
        "M9bHl+N/9v8Mn/zXxortuRS7BrFgYH+PCEk2K/K2av2FaUysKujWMbCqoJOHupE2SkciqS4UAVMDZPnIECWj+0ytfKjetdwQKFe6"
        "rqQGX128y4QgSigm3oFRyADCwOTsBQCaAbjNdpx/QgyzppnQ04PowGUCkIC9XQIMvXr6fvk1Vloj5evIqoJOxtNItEsaKlCk5NVX"
        "X8WWLVsGJChFBvuLL76I7du3j3pRKmu9NAAUCgWkUilWV93b28tekUgE8XgcxWKxpvoyzROn04lf/OIX6OnpaUg5fagN3Ztvvhm/"
        "+tWvEAwGmahavXGg56emaazTQ700b03T0NTUhGeeeQb/8R//UdOg5ii9T43MCSKF5TX9VgGuRhzhZCsJgoCvfe1rdWuUy++zqqq4"
        "5557EI1G6wpxWQmk9dytr3qlEpFIBL/73e/6pd5M4l5WzQNy+AQCATz22GPYtm0bHA7HkOxLhmHA6/XipptuwrPPPotgMFi3Iwqt"
        "NXqmlq81OtfHH38cb731FlRVHdV2l6Io+NKXvoRnnnkGTU1N0DSt5vnSfDAMg10/PU/rKcibpolQKIRf/epX+NWvfsUyaDg4OKE+"
        "zMZjpehTpfYRJgyIsoT0O5ug57IQRHnAUUdBEGHqBWi5VF9o7GDkzoQAA+JBUTIRslCEW04hICdhEwpl7blewhXbX8Kv23+O+7af"
        "jbfaNdgUAeXPB3owVdpwuFBM/0g1D9zjEMcTGQSVPMp9a8aOXHgn8r27Ico29NUu9HfsDRRMGdMcO2DkM9ByIiRx4HOXbuOzb0iA"
        "KVR0jZEBW6+X/ZEISZKQSqXw6KOPDliZW5IkrF69esA12MM9f2sRmcGSF9prg8Egfv3rX+Puu+8+LNFa0zThcrnwX//1X/jRj34E"
        "j8cDVVXrGrs0BvU6QxCRFkURoVAIjzzyCK666irkcrkRdR6MWUNIFOH3+5kaN7X+HC5bR9M0uN1uCIKAz3/+83j88cf7NS/J2bZ9"
        "+3b87//+L7xeLwtoDMe91nUdPp8P99xzD1atWoVQKDSg1p00tk1NTVi7di0+//nPsxKOoVpn5Fi99tprsWPHjoZIdaW1Rm0Wm5qa"
        "sG7dOnzpS19ic2K0ridyJGezWVx11VV4+OGHEQqF2JjUU4VvpAMN7TWqqsLr9eLHP/4x/uu//gsul4vvMxycUA8HyiNpZORThNUw"
        "jEM+Y43IkaFV2RjoIwf5yG7ke9+EKCsDIgdWhiYIEmpFuk0IMMxq7blEvJWZhz90/Qeu23AN8tkCJEmsOi7kAaRoYqXImrVvN21y"
        "VkVPazSf48ggxjT/K0WfSa3V+hnyEFvXCPVnPuShaAKCqEDPZZBqfwmiLMI0B0CoYUIzgZmObRBlQBjkFiJKgJYBXnhThKSYMKqk"
        "e9N+QONhs9lK1ghFXqx9usudV/SZsaRASmmR//znPxEOh5ljodGXJEk4cOAAnnzyySGLApX3hq72aqTVl91uh6IobA5bv2sVIOvP"
        "uZHRDoCRpBtvvBH//d//3ZDR1+j19Ye80Bp2uVz44Q9/iKuvvhrvvPMOQqEQm8vW6+7vfZAkCcFgEJqm4frrr8enPvUp5PP5fmVk"
        "DNV9rUWkhmo8h9pWiUajuPvuu9HR0QGPx4NgMMh6N5ef32DmJK3nUCiEN954A5dccgkefPDBAaXJkhDUb3/7W/zgBz+Aw+GA3++H"
        "JEn92iP6c18lScJ//Md/YP369WhqamLX1UjbPk3TYLfbEQwGceedd+KTn/wkisUiFEWBpmlDNu9ojDs6OvDRj34UL774IpqamhgR"
        "bGT9k83a1NSERx99FFdffTVzTg3luQ7HXkMZjPl8Hp/+9Kfx3//93ygUCoxYD2StWc/TZrMhFAqhra0NV199NW688Ua4XK73ZMYk"
        "B0fJs2Q4iAGl0ND/0wO/fNHLsswMYCIQVnVJ2mwrsFsIooJiOo74nifgmnQc9IIxwLrQAV7nwfZc9C+HmIEiu9Gz58+s528lDyDV"
        "rFjJMz1waYwkSSrxqFqJAI0PJ9RHJqGmNWNNU7aWRZR7kKlNCdVbklFGKVzW45u6BlMQkNr1dzSfcNWA66glAZiq7hz0NesGILqA"
        "9S9J2Pa2CKf9UGEyql0rNwDKa6ppnKwp79bxoMiF9b2xMi9IbGbz5s1YuXIlCoVCQ/WZZMCuWbMG+/btG5J0PHJmUG1vpfpEmpO0"
        "59Ui01u3bsXjjz+OGTNmYPz48XA4HMygLRaLLP2yfC5b91T6L6l+2+12yLKMZDKJf/zjH/jlL3+JDRs2wOfzHfL9auvQ7XbDbrdX"
        "jZyRYdmffZg+FwgEsGrVKmzatAmf/OQn8ZGPfATTp09nYk6FQqFkvpdrJdC12mw22O12SJKErq4uPPjgg/jd736HrVu3wu/3V+9J"
        "P4z3tbK/uk/kyOfzMYdfOShtf6Rr/Gm/IMXj1tZWnHjiiVi6dClOOukkTJ8+HX6/n9Xa0pwsJ9fV5qQgCJBlGTabDTabDcViEf/6"
        "179w99134+6770YqlRrUuqTMh5/85CfYuHEjPvvZz2LRokWMPNUrLbDOZbfb3dAcSSaTuOKKK/D9738fH/nIRyDLMmvvVqlkT5Ik"
        "OJ1O2O127N27FzfddBPuvvtuOJ1OKIoCVVWhqmrVel1N06AoCpxOZ8Nzg9rFtbe345JLLsG3vvUtXHnllfD7/chkMigUCiXRZuu5"
        "2u12OBwOhMNh/PznP8evfvUrAIDT6YTD4YDL5YKiKIM+1+Hca2ityrKMn/3sZ1i7di2uueYarFy5Ei0tLTAMA/l8HsViscSJV2mv"
        "kSSJ7TUAsHfvXtx33324/fbb0dXVxWumOTiGi1DToiSiaI2+WskBRaTpgUZePSLZJFCjqmrlh7dpQFRkRLb8GeNOvKYv7fuwGb0G"
        "RMWJZPt2RN9aB8nurBj9ow1Y13V2zYqiHJKOJEkSMpnMIbWg1s2Op/EdeYSa6uno37QeqHa+fB1RSxRVVQ/xJNtstpI5JMsynE4n"
        "XK4W2PM7oYV3QgweDWj5frXSMk0Rimhgiu3NPsfWYBTezL5S7juflqEVBYgOE0aF57J1jdB10/5QbY3QOqI0ZyLm1oj/WMOdd94J"
        "r9dbt1WO1ahyuVz4y1/+UrF0ZqBzdP/+/Vi/fn3Vtk2075PhWmmsKYr00ksv4bLLLkNLSwtmzpyJefPmYc6cOYxgBwIBZsBWE6mk"
        "KFk2m0V3dzd2796NTZs24YknnsDrr78OQRAaMvponcRiMTz99NM1e1WToyMSifTbuUk11el0Gj/+8Y9xxx13YNmyZTjzzDOxYMEC"
        "TJgwAW63G7IsH3K9tL6z2Sw6Ojrwr3/9C88++yyeeOIJvPnmm7DZbEwluj9Ef6juayUyXSwW8cwzz7D+uJW+R9HW3bt3H5ZnG6V8"
        "JxIJPProo1i1ahW8Xi+OOuoozJ8/H/Pnz8fs2bMxadIkNDU1weVyMRJUbU4SaYnFYti/fz9effVVrFu3Dps2bUIkEoHX6x2S9kKm"
        "acLv92PDhg1Yv349ZsyYgQULFuDoo4/GhAkT4PP5ahI2a9usRiLNdrsduVwO//7v/46HHnoIV155JU4++WQ0NzfDZrMdIpKZSqWw"
        "ZcsWrF69Gvfddx8OHDjAxK+KxSJeeuklpNNpZLPZqnuF2+3G1q1b+7XWdF2Hw+GApmn4xje+gQceeABXXnklli5digkTJhwyJrSu"
        "9uzZgyeffBJ33XUXduzYwRxxuq5j06ZNOHDgQM19ze12Y9u2bTXPdST2GnIYBINB7NmzB1/60pfwy1/+EmeddRaWLVuGOXPmYNy4"
        "cfB4PBXnMe2rqVQK77zzDrZs2YKnnnoK69atQ0dHB9xuN6+Z5uCwPu+WLFli6rqOtra2mn3rKj1YJ0yYgGg0WvI92pzz+Tw6OztZ"
        "RCgQCCCVSrF0Z0VR4Ha7EYlE2Ge8Xi8Mw0AqlWLvBYNBpFIpFskuOXlRQjGTwPSL78C4k65GMZ08LMTaNDQoLg/2PPhv6H7xD1Cc"
        "PpiGVnGjFUWRtSEgwyqXyzHDXxAE+P1+RCIRRgRcLhdrp0KkfOLEiRUjN5IkIRAIoL29ver9pGOGQiGEw+G+z4gCzFQB6qIpaLr5"
        "ApiZYv0GzwO3ACDIErRYFrs+eBu0WBaCLB0qi17ukBCBWFrAyoVFPHx9Eka2MWVpUvn+j6M+hec9c+A2sjAaTVXWDYgBB+K/eQHx"
        "X2+CGHAAusFq2FRVxYEDB+oSHCLEzc3NUBSFqRJb/07puVYDU9d1pNPpkvmSz+dZdJbauJAiqWEYsNlscDgciMVicDgccLvdcDqd"
        "fVEnQYSejUI95mNwnf5jmNlUY1Lp6CPPuinDLcVw37z5CCg9ME1hQKTaMABBBXbvF3HClx3Qqwj1m6aJYDCIWCzGIkKKosDlcrE+"
        "o+V7BzkcrN+jPYjGrzzK7/f7USwW0dPTMyqzP0iozprS3sh3aD8eKpJCBMnqzKj12aoOUctn6JgUMREEAQ6HAz6fD01NTWhqakIo"
        "FILf7y+J5lB7okQigXA4jM7OTnR0dCAcDiOXy8Fut8PpdJYYl40aoqQ0Xg8UDR/I2JKDoFgsst6+gUAAEydOxKRJk9DS0gKfz8fG"
        "sFAoIJlMoqenB+3t7XjnnXcQDodRKBTgcDhYdH8gKdlDfV/L13Aul6t7TFrbA9UKGKp1Rvsyza98Ps8yKrxeb8mcDAQC8Hg8JfMg"
        "n88jlUqht7eXtX3r7u5mdo3L5YIsy/1K72/UKQCA2ROU0VZLUb78+1bnbL1xEgQByWQSADBp0iQcffTRmDJlCvx+P6vj7ejowJtv"
        "vom33noLiUQCbre7pFyHzreeQB8R0IFkMNA9pZZ748ePx+zZszFt2jSEQiHIsoxcLoeuri7s2bMHb731FsLhMFtTw3muI7XX0BzI"
        "5XLIZDJQFAVNTU2YNGkSJk6ciObmZni9XthsNnad8XgcXV1dOHDgANra2hCNRpntSFoDPKjD8V4Gca5Jkyb1abwMx49Q5LXc+2e3"
        "21n0mQwna2p4Pp+H2+0uad9QKBTgdDoZYSgnZqJiQ+f6/0HgmAshKg6YhjGiilWmoUO2u5B8ezN6t9wLWXUdQqYJqqqyHox0I6wR"
        "SGttqDV1VVGUkkgbpeaRc4LjyFmY1vlQLBZZmhWBUsqobQk5TWw2G/PwU/SPjBeaW32fNSDYPMjvfhj2WZdDbj4WZjHbUJRaEEzk"
        "DQXHqLvhVSIDJtNAX2q3LAM33KsgmRbg9Zgod3STZ57O3dq+pHzuy7KMVCp1iFK+tdyEjICxOj+saXf9/e5QGT5W0tMoOW3k3GRZ"
        "LsnQMAwDyWQS0WgUO3bsKKmpLk+vtQqX2Ww2qKrKUi4Hcr9FUayb/joUY2udn9aI3a5du/DGG29UrCMnw5jSiF0uF2u1NJhI0VDf"
        "13KS4XK5RnyuDuaeEBwOB3PKkGPg7bffxltvvVWS9l1pTpJ9QxoBwWCQjd1wRPXonlDKsvWa+nuMRu+Tx+MBAPT09LCgjLVNFpVh"
        "qKqKYDBY8dppfIdrbtA97cvQciGRSOD555/HunXrDjlXWZbZuZbPheE415Haa+g6aX80TRPJZBKvv/46XnnllUP2Guu+SvOXIvXD"
        "NX85OMY6hpxQW0mfoigVyQF9hmr8MpkMS+Ek45i8q5lMBoFAoEoKmgFJcSDTsQOdG36Kyct/gGIqAUEaqTYh76aOtj35LRjFDGS7"
        "B6apH7IR2u126LrO6h9pg7e2aKB0KhoHaz16ecss3qf6yCPUZAzl83m2HpxOZ0mKdy6XY4qu9L10Og2Hw8Gi1VSPVv4QZnNFEGFq"
        "WaQ3fxfeFffi3aJ/oe58100BE+17IYk6DF2CgP4/WDUNkP3A356Q8eenFHjdh5Jp67ohzQGCoigljimq9yRnHTnvrKSbyNZYJdSj"
        "gWwM53lUOiaR7JK5W/b/1u9Yyc1gDb6RnCfW8xVFsYTEVbteus6hPM/hnF9jdd2VnzfpMJRH6EdiTg7UKTAS40POGKvGh3Wu1iJh"
        "IzU36HeszrtK51pr/IbjXA/XXlPuxKw3hzmJ5uAYYUJtJYL1yEE+n4fD4WC1noZhoFgswuFwIJlMMuJZLBbhcrkq1naZhgbZ6UHH"
        "c/8Dz9Sl8B9z7oiRatPQoLi92L/2u4i/+VTFVG8aD7fbfQgxUFW1pM6VPKTWtFWr+i1F80d7H0SOgT9YVVVFPB5nYn5krFBrEYqK"
        "kNaAqqpwu93weDzMQKibimUaEGxuaF0vIfPS/8K9+DswMkmgTrlEX8o3ME3dDgiAaQr9bgGv64DsBvbtF/G539rgUM1DhMisZJqE"
        "mqwOJyLP5Y4p6zVba8itAi2N1n5ycAcCv2aOSvennHBwjK15y9cYHwcOjuHAsMliU40pAEYOKHJNhJpIAhFFURSRzWZL0lSp9sVm"
        "s9WsUxVEGXsevBLJfZshO70w9eLwjpyhQXJ4kdl2L/JbfgnJ7qpKpiminMvlmFq3LMvMqVCe7m1tD6SqaknEmrzjjda7c4wN0BpR"
        "VbWkTopa31i9/MViEYFAAOPHj8fEiRNL1Isb9nYbOgS7D7ntf0Tujb9AcHgAo04Jgdmn8D3NvmNAgmS6DkgqEEsKuPx/7OiJi1Dk"
        "yqXzpmnC6XSWOKEoBTybzZZ81mazsZpyWiMASrI6qAUONyA4ODg4ODg4ODhGPaEmASaq9a1EDsoj0tQbltpSWN8jcZCqipimAVGy"
        "QctGsevP5yP1zmYormEi1aYJmDoEhwe5HX9Bav03ERo3gfU5LE/Dpjojqu+k91wuF7LZLPs8kQVrKyCqlaP3rPXTPP3myANlIVBW"
        "AjmYyPnicDjQ2tqKYDAIj8czqDrRvokICLIDqQ3fQn7HXyA6PYBp9L0qnZ8pwyulMNO5te+7QuPkVNMAyQXEMgLO/46KjTskeF0m"
        "dKMymaYU9nInFI0JRayp5pOccxTlJ8E+itqTE4qDg4ODg4ODg4Nj1BNqAKwumIxbURSRy+WYUVwpIg2ARaStLW7oPaqDrBRlMk0d"
        "ks0BPRfHm3ddgMTe56G4vYBpwDSGyJA2NECUINjdyL1xF1Lr/xOC4oKum/B6PRg/YUKJUBQpIhYKhZJomSzLkCSJEQNK4bVGrK3R"
        "fOrRTVE7HmU7ckHlAZS2TX0xJ0+ejNbWVng8HqYxMPjaq766aUFxIbXh28i8/nsINhcE2X5ItoUAExpk+OVehJSOg33WzQb2gYNp"
        "3n5gd7uI87+jYsMOCX6vCa3GsnQ6naxO2uqEsqoFW51QVqiqWiLQRqI41HaMg4ODg4ODg4ODY9QTaiLVbre7JCKtaRoj2RSRpn6B"
        "REQ1TWPvWUlDMplk6a0V6YFxkFTnE9h5xznoeO7nkGxOyKrbQqz7S0b7ItIAIKgewMgj/dw3kd7YR6b7FMX7apwdqoqJEydCVVUU"
        "i0VmyFtrv2lMrMSAiDe9Z41Y5/N5Rh4kSYLb7ebE4AgFzX2n0wm73Y6WlhZMnDgRDoejRLV6aB0qB0m17ET2he8h8eQXUEx1QnF5"
        "Dq4pra/NmWCgYMiYYN8Dh5SBYYpVU75NAPpBIi2qgOQB7n9CxmlfdmDjTgk+j4lilexyXdfh8/mQy+XYPCcnlCzLhzihrI4pckKR"
        "Y4oi1i6Xi6d7c3BwcHBwcHBwjC1CTWTZ4XAwdV1S7aZ0TuDQiLT1PZfLxYgoHS+Xy8Hv91eNzpmGDkGyQRAl7H/0K9j5p3MRf+uf"
        "EG0uyA43IEgwDR2mofWpcZvmQdJM/zVK/y7aINjdAAzkd/0V8dUXI7fzbgi2g8TeoqBM0bDW1lZ4vV643W7Wp5FIMdXIZjKZqsSg"
        "GllwOp083fsIB6V9OxwO2O12RgQPUeoeUvTNfdERQvuLf8D23y1B94u3AzCguDwQJBtg6tB0DRNsu2EKBgxT6Kt+OPjSjXdJtIC+"
        "9G7JC2zfL+KqH9lx2Q9VxLKAx1k5Mk3rh8TV0ul0iVK5z+dDJpMpcdZVi1hbPyeKIlwuF28xx8HBwcHBwcHBMSyQh/PgFG11uVyI"
        "RqNMmZjqQYlUWiPS1vcymQx8Ph8ikQgkSYIoikilUvD7/XC5XCVGdxmrBiBAdnqR2P0EEnuegG/mCjSf9Dm4pyyG4mk6aJUDhq6X"
        "1IwKogxBEiCIgKEDWuIdFNufR/5fd0ELbwEkFYI9wKLW5aDIe2trK+LxOFMoJni93pKe2oZhwOv1lhADitIVi8WSqJrb7eZk+j0A"
        "UrOOx+NoamoakYwEURQRj0WQLioQC13Y+8Cn0L3plwgt+Bj8cy+BMzAFkiLilOZXIaqAmBVK3HGSAuDgNNcywDMvSbjraRkPrZeR"
        "SAvwuvvUvHWjuiOBemRGIpGSjA6XywXDMEqcSxSxTiQSJU4om83G3qM9xSpaxsHBwcHBwcHBwTFmCDVFlb1eLxKJBCPYlLpNkSSK"
        "SAcCAUYsrereLpeL9aoWRRGxWAxerxdOp5O9X4FV96WA270wYSL+5hrE3lwDe2AGvNPfD2frcVBDx8AemA7R7gVMDYIooZjsQj6+"
        "H5nOrRASO6Cmt0NPdwGSvY9IW1LAa0HTNHi9XgBAOByGrusIhULIZDKs5Q+lqMqyjFgsxogB9XTs6elhNdmqqsLpdLLaUI4jE6R+"
        "T/d6JMg0/WY0GoUAA5AUyC47Ml1bkHr0VXQ8/79wjz8eyqQzsD/1HHZOFTHObwJ6n+NJ04B/dYjY0yXguTckvPymhK1vC9CKApwu"
        "s6/PtFHbgUDrPBKJlJQ9KIoCh8NRQrJN04TX6y2JROu6fohjiiLbY7n3NAcHBwcHBwcHx3uYUJOha7PZ4PV6WZQ6n8+zdHCKOlFE"
        "2u12I5FIMPIcj8cRDAaZ+rcgCBBFEYlEgqVVU9/mSjAPkl/J3kdui4n96HnxD31EQgRkZxME2d7Xm1cUoecS0HJJGBrgcMmYOHVm"
        "v4i0laRQ9FmWZSSTSRiGwaLqZPS73W7Wd5jGi1TBSdjNNE34/f6RiU6PdJmpMHKnKAzm4g5D+S31Yw8EAsNKrE3TZE4fURQB04Rp"
        "6hAVJyRb35qI7loL7FyLzz7hgMflgNdpwjT6JAQME+iKCTCKfecnKSYcdkBymNB11CXTqqrC4XAgHo8fopLv8/lKnHFWbQVrxFpR"
        "FEiShHg8XhKddjqdPDrNwcHBwcHBwcExdgk1Rb+shrEoikgmk/D7/YdEpAOBAOx2O1PFNk0TiUQCHo8H0WiUGdZEqv1+P/x+P+Lx"
        "OACUkNVKxFqQ7ZAV58H3DBjFNMzCu3XOgihBVr19wkoCUNQM2G0Db01kGAYcDgdUVUVHR0cJMfB4PCgWiyURa7vdDlmWDx8xkA4e"
        "Xx8AgzQbJMimCRgmTM2AWezfuJomIIsmE75q5CwN9GX1F0ypj/0ZZuMMmT4viyO2KGnNuFwuhMPhYSPTtO5isVhJ/f67HzBgmgYE"
        "UYasegFBgAc6dN1EOF56Pi47IKhmH8E2+oasloo31YW7XC6oqlqytmnd+Hw+ZLNZ1hILACRJgtPpRCwWK0kLDwQCJRFrqxOqnKRz"
        "cHBwcHBwcHBwjBlCDVSOUmuahnw+z4S7JEli6eCBQAC9vb0l5CKdTqOpqQnhcLiEVEejUbjdboRCIcTjcRQKhZKa5UqMzDQtAkWC"
        "BEGUSkihafapjeuajnwuB/vB9lUDNcrpu62treju7kYqlYLT6YTNZkNvby9zAlDLpHQ6XdIuaMSIgSjASOYBARB9Ksz+hGUFAYIA"
        "mIbZyIBAkETIogtKkwtGIgdBFPqYb+2fgCILiKUlCAAUd2MkXoIJ6MAUewoveOwQdR1mo3p8hgnBocCIZQ8quo8MqL80RW5DodCQ"
        "ZyhQOUE0Gq3rKekT8OsbblEARPlQv0PDPoqDAoV+vx+mabI1YM3SCIVCKBaLSKVSbD0bhoFgMIhMJsPE23Rdh9PZ5yDLZDKQZZlH"
        "pzk4ODg4ODg4OI4sQk1tbHw+H1KpFDOGk8kkgsEgbDYbEyvTNA2pVArBYBDhcBiiKEKSJOTzeWQyGTQ3N5eQakmSkE6nUSgU4PF4"
        "oOs6S68mI712uxyzIhGg72SzWaY8PFiCJIoiWltbmchaPB4/pJ2WpmnI5XKMLLhcLtZrd1iJgWFCcCoobOtC9MZ1cK6cDTNb7GNP"
        "tbkWBFGAkdNgJvOQxrlh6kZtkntwvEVFwqRFcxFP/AuCXWaK6bUQEoG3IiL+6y4nzj85BiNf/xQNCBBhYu4bT8I2zo202wFBN2AK"
        "DYyJKqOwvRvph96A6LHVzl8e4jVDUeru7m7k83koijJkrZ8oSyIajbLoLs2xevOswRbUFYk00FfmoKoq0uk0stlsSbmGYRgIhUIA"
        "UOJo0zSNOZasCvmiKMLj8bA1RaA0eR6d5uDg4ODg4ODgGPOEmgxlQRAQCATQ3d3NyC6lfofD4T6SJYrMyA4EAsxQJuJMqaDJZBKa"
        "pjH1b03TEI1G4XK5EAgEWFRb07SS6NdAHAFEzgdLZuj7TU1NSCQS7Nys4kvkRCAiEAwGR67lz0ECmX54B9J/396/iKxpwjT6Is/9"
        "+Q7UPlV1s1hs+Gs2Cfj9Uy784Sl34ynmggDJ0GEz/lmfgVcaF4d8WBYoEclYLIaWlpYhS/8WBAGxWAyxWAyqqsLtdjOVfep9Xk2X"
        "oL9znuay0+mEqqqMyFPNNukNAGDq9tS7ncg0ObVIvI/2lEAggFQqxfYCTdPg8/mYPgMn0xwcHBwcHBwcHEcEoSZySoJbVLNZLBZZ"
        "e6xoNMoIMil8h0Ih9Pb2svez2Sx0XWeGNEWriITSe0SsKeJbKBRKevk2amgXCgXkcjm4XK4hiw5S/bQkSeju7mZOAqoDJxIRCoWg"
        "KMqIp60KTmVg3xsgiadr7g88DrOhiLaF2sEUBJiwDdjZMNKgeUC9y0mIb7Cp3+TISiQSUBQFxWIRkUgEdrsdTqcTLpcLhUKBrTXr"
        "/akbvbb0zAbAHEWUim11JBFh13UdiqKwmmlK86brd7vdcDqdzNlEZNrtdsM0TaTTaciyzNppBYNB5hTg4ODg4ODg4ODgOCIItZWg"
        "Njc3o62tDaZpssiz3+9n9cNkbEciEYRCoRJSTSQ8EonA5/OxvrMURaZUUIpwORwOuFwuJgBWKBSg6zqrSa4kNkaRMVIOrp82PgB+"
        "ZhhwOp1obW1FOp1maeuU6q2qKnw+H/L5/MhH2Q4Deez/+A3gSwPNVT6MIEeU3+9Hd3c37Hb7kKR+J5NJ6LrOtAhM00ShUEA+n4fN"
        "ZoPD4UAgEIBpmkyVX9d1GIZxCGmm8xQEgfWHlmUZdrudHZeINJVp0BogYTKHw4FEIoFCoQBZ7tuWiEy7XC709PSw36E2W3a7vSTV"
        "2zAMtLS0sHXNo9McHBwcHBwcHBxHFKGmuk1ZltHU1ISuri7IsszaYzU3N7N2OESOe3t7DyHVoijCMAxEIhF4PB40NTUhmUyW1IAS"
        "sSayKssy6+8syzIzzCsRE2vtdaFQQCqVgqqqw0AK+1oG2Ww2dHR09HG+g+mx48aN4zWgHGxOaJqGYDCISCSClpaWQa3BcDgMVVVh"
        "t9uRSCRY6jUR62KxiHw+D0mSoCgKFEWB0+lka6oWoaaocrFYRDweZ3OY1jPNe2p1RX2iqf80/QZlcTidTvT09JSI9CmKgkAgwMpE"
        "6DcDgcCo7tXer3IIjvfWGjeMsebr4+Dg4ODg4DgchJqMX1L3LhQKTPWbeuH6fD7ous5a5UiShEgkwpS8Y7EYEzWjllq5XA4ej6di"
        "DSgZ8bquQ9M0ZLNZ9jfr360gEkCEWxRF+Hw+2O32AbfPqgaKEk6YMAG9vb2IxWIYP348E2LjZJqDCKPdbofL5UJvby/GjRvHhPwa"
        "hSRJiMViTAyvmt6AlVxT1NpKmskhVe4coqyP8tIKOhatJ1mWWX/2TCbDHGjWz/n9fkb+6VgUdaYWepSVQqrewWBw9Kp6myb0aHbI"
        "M104xvriBmACossGQRE5qebg4ODg4OCEunGCkMvlEAwGUSgUWB20YRiIx+Pw+XwAwEg19a12u90IBoNIJBIsgkYtuMprQLPZLHK5"
        "HDPCybB/1741GQmodH5EQCiqns/nWQrrUBrsFAmn/rqiKI7qKNtIz5P+8xbziB0LqyOqt7eXCdY1Mk6iKCKXy5WkSJfrDRSLRWSz"
        "WRQPCsSVrxsa22IVAblKn6dosyiKLJWczoX60ludXpIkIRgMQtd11muaMlIEQWCdAqg8guqmW1pamE7CqFs3pgnBLiN4xQkQVaWx"
        "1nIc7w2YJgSbhMTq7Sjuj0GwSZxUc3BwcHBwcELdOPEpFApoaWlBW1sbisViTVIty3JJeyy73Y5UKgXDMJhBTtE0iuQ5nU7ous5E"
        "yazkuZbIEhEHikYbhoFcLgev1zssxrq1LVgoFOK9cw8SQE3TGq6FJSKlKMqQZxGMJlJNjqienh4kk0l4PJ6GSDWtN9IgqKQ34HK5"
        "4PV62WdzuRyrm663ZiqtG7ofqqpCUfqE7rLZLLLZLMv8ILJMmgJOpxOZTIY52cihpSgKEzSk66DfGz9+PCPuo27dCICpmxBVBU1f"
        "XAIp4ISpGQNU8OM44mCYEN025La0o/BWuOH2gRwcHBwcHBycUDNDWRAEjB8/HgcOHGApnESqKYWT+tFSW5xIJAKv14tQKIRUKsUI"
        "KEXGiAzIsgxVVaGqKlPppnRyMuIrRagVRWF12DabraR9j9WQHwqnAhGcRCKBQCDA1YkPzg0SqlNVtSGCTCnBPT09UFX1iHZI5HI5"
        "NDU1sfZzLperKqmmORaJRFiLOmpLRZFjK7EGALvdDrvdDq/Xy45RLBZRLBbZGqpUQ03rRlEUpo1A300kEiyybSXSuq7DZrPB4/EA"
        "ACvpoDIQ+nsgEEA0Gi0h04ZhoLW1FaIoolAojO57bhgovB2FFM1yQs1RSqidNhhZrf/t/Dg4ODg4ODje24SajHBN06AoCiZOnHgI"
        "qSbi7Pf7EY/HS+ox4/E47HY7a6mTTqdLaqfJIE+n0+w9EliykuRqJISMeSISxWIRNpsNTqdzSAi1lUzH43HW4uu9rk5MLdM+/OEP"
        "47rrrmMp8Y1EYG02Gx544AH85Cc/gc1mO2LTv4mkjhs3Dl1dXQBQlVRLkoRcLod4PA7TNNHb2wuXy8XKLVKpVAmxJocU1e+TU4lK"
        "EugeVeaMBls35Vkh5erelKrt8/kgSVJJLbWVMLvdbtjtdoTDYZaNYiXTDodjdGd0mH1iZEa6gLbP3t/X290EJ9QcbH5AAMxMEaJq"
        "GxMdFjg4ODg4ODhGEaEmQ7tYLDJS3d7eXhIJjsVi8Hg8CIVCTDWYCDO1z3I4HPB6vUx0LJ/PM2JKRny5wBL9NhH0SoTaSvJM00Qu"
        "l2OEejAGPJHpXC6HVCrFyPSoTFk9DA4Wv9+P6667DuPHj2ckqxY5trY1u/baa/HPf/4TL730Elwu1xGZ/k3ZHQDQ0tKC7u5u6Lpe"
        "sUe1ruvo6uoqIaPUB56yPEhvQNM0Nt+t/Z4zmcwhTo9qhNp6juUkms7NZrMxlXEr2bfWUouiyNp2RSIR9rv0G2OCTJcRJz2e408c"
        "jsprWhS5k4WDg4ODg4MT6sGTalmWMXHiRHR3dyOTybC00WQyCbvdDp/Ph1wuh3Q6XZLiTXWZVDvtcrkYeaY0VSuBthrg1dpmlZNr"
        "wzBYGvJgDXhZllmqOifTh5Iyu90OQRCQyWT6NS7UisntdldM5T8SSbVpmmhpaUE4HEaxWEQoFGLvi6KITCYDt9tdMcWbBMqsomS0"
        "bqyR5UbWDIAS51U5wabyC8oOSafTSCaTVWupqV46nU6X1FJLkoQJEyYwYbOxtGYEmbfN4qjucOHg4ODg4ODghHrQBIEi062trUx0"
        "iWqnC4XCIX2nrWmpwLupqmS8u91uAChJ3SaRpUbSgYlMyLIMh8MBu90+6GsEgGg0CtM0WY34aO41PZLnVa7EblV3bvT7VtX0ain9"
        "Ddu4ozxlnOrGqaY6Ho+ju7sbwWAQiqIgkUigq6uLpXhnMpmSEggqi0gmk0in07DZbLDb7XA4HDAMg60ZKkVodDyIINtsNtb3HehT"
        "BydRMevnKtVSRyIRaJrGzlHTNDgcDrS0tLBskzHngOKkiYODg4ODg4ODE+rhJghEeMeNGwdVVdHb21uSrppIJGCz2eDz+aBpGpLJ"
        "JFMtJjKm6zpSqVTfBcoyq5smsSoiaYZhlNSdEmEgRWIiZGTwp9Nppjbc34iyKIpMnElVVTgcDtYaazSTaU3TRqwftrXf8kDJPClh"
        "U2RzoJFqQRCgquqoX8A0RpTCncvlEA6H4Xa7EYlEmMBbLpdjvdwpo4P0Cmht5fN55HK5Er0BauUGgK0byvqwrhtyfFHEmbI6isUi"
        "crlcyXf6U0tNnwkEAqzum2dzcHBwcHBwcHBwcELdAEHweDxQVRU9PT3I5XLMaC8Wi+jp6YHT6WRKxFZRsnKjnQgEkVdZltl/y+tB"
        "qd8vEXtr2yCqJ/V4PP2OmmYyGeRyOXg8njGRrkrOjUQiMWIEhsga9fseKIhQy7I8YEJNhJDU4ccCsc5ms7DZbAiFQgiHw6zlnFWP"
        "gNS7yaFDrbGsPaTL9QZoPUmSxCLb1vlAc4WyLcqzQMp7UzdaS00R6paWFjidzlGfzcHBwcHBwcHBwcEJ9agiCNT6asKECYjFYojH"
        "46yOEgCLZlFbLI/Hw0TJSGCpvAaUFJIB1GxRZY0c0+8RaWmkfRZ9n5SUFUVhLYvGSroqEaNqIlTDcc+HImJvPc5gjkVzaKyAsiBE"
        "UURLSwu8Xi8j1pIkMSG/cDgMWZbhdruZ3kA2m2UlEbRerPfdKipWbd5b+1RbCbSVRJNauMPhYNFzqqW2ipIBgN/vh9/vB4BRn83B"
        "wcHBwcHBwcHBCfWoJNUk2OX3+1kaK9WBkgFOEWiqAaWoNZFXIgrlhn8tokhEwEoeJEmCoigsBb0WmdM0jYlqUUQ7l8uV/D7H6MZY"
        "vE9UQ07rYeLEiYjFYkgkEswRJIoidF1HLBaDJElwOBxwuVwlNdmappU4FKxkudq4VBIjo0wQu90Om83G1kYqlWIOrfIUcIfDgUAg"
        "AIfDUaLYz8HBwcHBwcHBwcEJ9QBJDaV8t7a2IpPJIBqNMoJKETVr9Jfqpp1OJyMZFHGlCLWmaRWjbUQ6KF2WXvQbuVwOiqKUpJ9a"
        "iXQ6nYamaXC5XLDZbCgUCpwUcIz4uqG1EAgE4PP5EI/HDyHW1EYLACO+qqqW9Hsmck3/rpRGT2uOjmNdM7TWMplMyVqwRqRN04TD"
        "4YDf74fT6WQt8I7UqHSlazqcpQXlGQXW8yThuCO1rztH6Rw4ElsNcnBwcHBwvKcJtdWw03UdmUwGiqJg/PjxyOfzSCQSSKfTJS2B"
        "gHej02QokDiZLMuw2WxMPKkSyKgkglwsFlm0WdM01taHiLxhGMjn88hms5AkCXa7HW63G5qmsVrpsUoK3ss1q2OdQJQ7o4LBIHw+"
        "H2KxGFKpFBPks85jyv4ggkzEmAT9as1lMsR1XYeu60yLoLz8gsTGqKe8qqqMSOu6jmw2W5V0HinzqhppISdEObEdbtD+5nA4mDOF"
        "9CRI14CciEeSU+NwjPXhvNZq8470QQRBgMPh4JYRBwcHBwfHkUiorQY2tfNRFAXNzc0IBAJIJpMsAmbtbUsGk5VgEyoRajI6yg0s"
        "OpYsy0ywSRRFFAoFFAoFyLIMp9PJhLCsgk5j1egn5wNF9Efqdwdr3FrT9QdzrMG2SRuNzihZlhEIBBAIBJDJZJBKpZDNZpkwmVVv"
        "gJxJlSKWlca13FgnI96a0k0kXlEU1jPeZrOxVPMj3YFjmiZrJVY+P2kMCoUC7HZ7XZ2GoZwbS5Yswbhx47Bx40b09vayevsFCxZg"
        "+vTpeOWVV/DOO+8cUaSa5rcsy6y125GKfD7P5l75+jIMA263G+eeey7S6TQ2bdrEsxE4ODg4ODiOVEJdjVhLksRIQj6fZ4ra1GKn"
        "3MC3GhTlBnx55JqMXiLZRBBSqRTrs0vRO2oxNZaJdLkTwePxjJg4F42h1+tljpCBEBaXywWfzwev1zuotllHEnmgeU/RY0EQ4HQ6"
        "4Xa7USgUkMvlSlS/aa6Xk+xqa8ZKnK211ESySX/A4XDA4XBAVVUmombVFjiSybQoishkMjjnnHNw5plnIpfLlSjaFwoF9PT0YOfO"
        "nVi/fj1r0zfcc9AwDCxZsgQLFizAzp070dnZyRxpxx9/PM4//3z09vZi9+7dLLvnSHAwBQIBjB8/HpFIBF1dXSPiwDhc1ztz5kwo"
        "ioL9+/eXiGLSWHg8Hnz4wx9GZ2cnXnjhBV6ixMHBwcHBcaQT6nJibSUJRK6JnBFZIPJt/Wy19DdrKiARAXo5HA7m5ad6UmuP3SPJ"
        "CKFrstlsI3Y/qQfyQA1ba2SdUpYHc/1HonFNsIqCud1ueDweGIbBsi7oRWvG6mCqRhhpzYiiCLvdzsTIKOJKBjxlkhwpzqf+zCmb"
        "zQav14t0Oo29e/cyB57b7cbRRx+NefPmYcGCBbj11luRSCRYNLvW/ezvXC13WGUyGSSTyZIWeaIoIh6Po729nfUG788xh2quDvU6"
        "pFT2uXPn4rOf/SzWrFmDP//5z3A6nQ391mCus953+3vsep+n9fjxj38cTU1N+NGPfoT29vZDHCOapqGzsxPhcHhY78tQzxEODg4O"
        "Dg5OqIeBJJCAEpEzu91eUhNmJQdWo76cGJDBYe1VTZFqItDlomRHMgkYKZCTw2azMYX3RoxQurc2m43V6L4XaiOHYt2QBgDNfUVR"
        "YLfbD2k1R06qShkLVscLEWrr8SuR6PdqBEzXdciyjF27duEPf/gDHA4HIz6zZ8/GRz7yEcyYMQPLly/HPffcc4iDiRwX5RkAtZyE"
        "1jG3tsOjvc1aImMl/o8//jjWrVuHfD4Pu91+yPHLz4WcmgNde1ZhLNqn6dyqHbMewSvPpqD3DMNgbRDLs5cqlfz05zqtx6k27jSW"
        "1nVS6e+V7mH5uVh1ECp9vryvvPX8FEVBNBrFTTfdxI5bvjatNdjl96WWY5p+gz5nbZ830s8WDg4ODg6O9wShHsqHK6l6l7f+sfbI"
        "rSS+YjVWSNW7kvLtUJ8zT69717jr7e3Fa6+9huXLlzdcU0uf27JlC7Zt29ZwtIk7Ow51aFRrMUf3x5qmXMkZQorg1dbMUJ33WF8z"
        "JPamqirbb15++WVMmTIFF110EWbOnAm3282cGTTGFC1WVbWk/rxQKLBU+kqEsFAoQNM0uN1uSJKEXC6HdDoNWZYrjiX1Cdc0raTu"
        "2/r3TCYDURThdDohSRITcCRxxv4oRpumiUwmA9M02bgAfZkU6XS64jkA7zpGFUWpeB3kBLLWSlPWkiRJTAiP2smRQ3Uw10nZUHa7"
        "HcVikXV9kGUZ2WwW+XyelQqReB/dF+vfy6+VtEBkWYbD4WCaHZlMhrWcszoNKDOL/k2lHVTWQQ5IXdcRiUQgCMIh2hHWbC8q1wDe"
        "bVdJPeWt52qaJvL5PMvwovvndDqZ+CE54Tip5uDg4ODghHoI4fV6R6RmsD9pfcNttAuCgGw2yxRWOfrG5Otf/zo2bdoEl8tVt57P"
        "ep8eeOAB9Pb2wuFwHPHtX8gg9ng8I2aUNrp2RuI8EonEmL/HVvE8Ulhub2+HpmlQVZX14pZlmRGmk046CcceeyzGjx/PWoz19PRg"
        "y5YtWL9+PXRdL6kHFkURuVwOra2tOOecczBjxgw4HA4kk0m8+OKLWLt2bUmqN93DQqGAs846CyeeeCIeffRRbN26tYTk5fN5HH/8"
        "8Tj11FMxceJEqKqKVCqFvXv34rnnnsPevXsrksJaDoYFCxZgwYIFmDp1KpvXsVgMO3fuxLPPPotoNFpCwkzTxGWXXYbx48fjvvvu"
        "Q1dXV0lLw1wuh9NPPx2nnXYaHn/8cbz44otwu9249tprMXXqVMTjcRx77LH41re+xQje/v37cf/99zPy3p/rpHFbsWIF5s+fj/vu"
        "uw+pVAoXX3wxpk6dCkEQ0NPTg3Xr1uG1116DaZqYNGkSVq5cyf4eDofx1FNP4bXXXitxXhmGgaamJrzvfe/DMcccg+bmZthsNuRy"
        "ObS3t2Pz5s147bXXoCgKRFFENpvF8ccfj/POO4+Vc3zqU59iBNtms+Hvf/87duzYgQkTJuDSSy9FLBbD/fffXxL5zufz8Pl8WLZs"
        "GebMmYNAIABd19HT04PXXnsN69evZw4LIv10vLa2Nvz1r3/F0qVLcfrppzOdk7a2Nvzzn//E22+/XdVBx8HBwcHBwQl1P0Aqo/TQ"
        "f6+B0putYjHvVVCkKZlM4le/+lW/v+t2u1nE773gePD7/TVrbI9UUJZJNBods2uGCIs17ZqimvT/1vKVVCqF5cuX4/LLL8c777yD"
        "3t5eRCIROBwOTJ8+HcceeyxmzpyJO+644xBCNHnyZHzuc59Da2srOjs78c4778DlcuGyyy5Dc3NzxdRlwzAwfvx4HHfccVi/fn2J"
        "Yyufz+OCCy7A+eefD0EQsG/fPnR1dWHcuHFYtmwZjj/+eNx999146aWX6jq3iPzNnTsXX/3qVxGNRtHd3Y0DBw6wFomzZ8/Gcccd"
        "h1tuuYWpkNP5Tp8+HTNmzMDDDz9c8juUojxu3DgsWLAAr7zyyiGOg3r3p7/XSdlNU6dOxZw5czB//nwsXrwYNpsN+/btg8fjwdFH"
        "H41Zs2bh17/+NRKJBL7xjW8gmUziwIED8Hq9mDVrFqZPn45bb70Vr7/+OjtusVjExz72Mbzvfe/D/v37EYlEoGkafD4fjj/+eJxw"
        "wgl4+OGH8eijj8LpdPbr+Wu32zF37lx0dXWVZKXk83m0trbiM5/5DKZOnYre3l60tbVBlmVMmzYN8+bNwzHHHIM77riDKaaT4+fY"
        "Y48FAFxyySU477zzsHv3brzzzjtobW3FSSedhBkzZuBXv/oV2traeKSag4ODg4MT6qEykN+rNa/v5XrSasRYlmUEg8GGMgWsKY6U"
        "yvhemjfvRSfUkaBCTKm6dD2GYUCWZZxwwglQFAWdnZ1IJBKMbCiKggMHDuDmm2/Gtm3bkM/nYRgGJEnChAkTcNlll+GUU07Bzp07"
        "8dRTT8HtdkPXdSiKwojzs88+i4ceegipVAoAMHfuXFx99dWMPJaPKaU2U+kMEfsTTzwR559/PlKpFO6//368/PLLzBmwfPlyLF++"
        "HB/5yEfQ3t5eEjWutn5JAf3OO+/Eq6++ilQqxdKvfT4fPvCBD+D000/HypUrcfvtt5e0uaLODtWOb70G2k9+85vf4IwzzsA111yD"
        "9evX484774TL5WK/qaoqMplMv6+T0qULhQLi8TjOPvtsbNiwAY888ghzmJ533nn4wAc+gAsuuAAOhwPPPPMM/v73v7Pzu+CCC7By"
        "5Uqcc8452L59O5vriqLg1VdfxWOPPYZ9+/aVpLrPmzcPl112Gc477zzs2LEDe/fuhcPhwJYtW/D666/jW9/6FpqamnD77bfjwIED"
        "bE6RaCClvVOdNc1JWZbx0Y9+FJMnT8bmzZvx17/+FbFYDAAwdepUXHHFFVi4cCHC4TDuu+8+KIrC7mk0GsX48ePR1NSEm266CW++"
        "+SZznn/0ox/FqaeeijPPPBO33347Fyvj4ODg4BjTEPkQcIxWUk0ROvpvtRcJzVHtLgfHWHAIeDwezJ07F7Nnz8YxxxyDk08+GZ/7"
        "3Ofwvve9D/F4HP/85z9L0n3tdjtef/11bNq0ibU3o97eW7duxX333Yd8Po/jjjuOEZtcLoc5c+Zg5syZ2LdvH+6//36kUimmwP7y"
        "yy/jkUceKam9LXfalIuVKYqC0047DbIs4+mnn8azzz4LWZahqip0Xcff//53bNmyBcFgEIsXLy6pAa+21slZ8OSTTyIej5dc24ED"
        "B3DXXXfhnXfewZw5cxAKhRj5tJ5jLcdTees3qj8nMTiqDXY4HCwFebDX6XQ6sWfPHvz1r3+FpmlM6G/dunXo6OjAtGnT0Nvbi7/8"
        "5S+sbhwAnnrqKYTDYUyYMAHNzc0sRVsURTzzzDPYuXMnCoUCc8Lk83k8+eSTWLNmDTweD+bNm8d0EKjWms6LRDrpZR036xhRmcDc"
        "uXMxa9YstLe347777kMkEmFzZ+fOnXjooYeQTqdx4oknorW1lZ0rjbuqqrj//vvx+uuvw2azweFwIB6PY+3atUin05g6dSq8Xm/J"
        "/eTg4ODg4BhrkPkQcHCMrKOA4719byiV9uijj8aJJ55YUg9cKBSwa9cu3Hvvvejs7CypL6XMDVKzDwaDTCSL0mxTqRSCwSAcDgcT"
        "VJw+fTpUVcXWrVuRSCTg8XhY6rPH48HWrVtx7rnnIhgM1jxvErkKhUKYOHEiYrEYXnnlFTidTpYpoSgKCoUCXnrpJZxwwgk46qij"
        "GtYzkCQJmqZBkiQEg0F4PB6mGF8sFpFKpdDU1AS/349IJFISpR7IvS4X0bLWsheLRTQ1NfX7Oq1dCSRJwpYtW/D/2zuz2CiuNY//"
        "q7qqu7qrF9PeMNgKxGCzxUkAOzY2GBOUBEcZsoxJlJhRFEbKUyJl3ubtSiPdydMkeckD0lUimImulO0GKcmgTMSQxHTAmC1AnDgG"
        "B2y8u+12L9Vd2zzAOVPtfQEuwd9PaoFU1eVzTp2uOv/zbZZlcSuwJEnQNA3Dw8MoKSlBW1sbtz4zbwJN0zA4OIh169bB7/dnZQOX"
        "JIknOMvJyYGiKHC5XMhkMvzfgoKCrMoU0/VzLp4/paWlUBQFFy9exPDwMPd6AG7mPOno6MDvv/+O8vJyPPDAA1n1vGVZxsDAAH79"
        "9VcEg0HuDq8oCqLRKEZHRxEIBOD1enmCN4IgCIJYMoKaZf1kC7vblVBrqe5Q365+syRVzFo7ndXG6d7JMrySdWD+eDwepNNpvjCd"
        "rR4sS5KkquptG29nGR36zSz8WrIsIxaL3ZWxZGLj6tWr+PLLL3lpvhUrVmDjxo3Izc1FXl4eent7s0IeWEmlxsZGVFdXIy8vL0uE"
        "MGsly2bNRFZubi5M0+TxsU6BzjJYR6NRHks90ziZpolgMAhVVdHb24tYLMYFPWuDy+XC4OAgkskkQqEQd592Jkqb6tqZTAZVVVVo"
        "aGhAcXFxVvZxlnGcvXPuZMLIhfaTCUPn/RgfH580p5jl3bZtxOPxaY+LosjvL9uEycnJwZ49e1BRUYFAIMCf8c7SWM6Sd4uBbWzY"
        "to2+vr5Jm05s42FgYACbNm3i5zo3juLxOLfcT+yjrutZfSQIgiCIJSWo2Ys1mUxCVdWsRcRCYPFzrCzKUiORSNy2hGRerxeJRGLW"
        "hTErv8Ky/ZKgnv+cdbvdvNTMXLNfp1IpADcT0S32nluWxS2OSw3DMHgc8O3YhAJulgG6WxnKZVlGb28v/va3v/ESb7ZtY8eOHXjl"
        "lVfw6quv4t133+UJm4CbMdcvvfQSdu3ahY6ODnz++ecYGhpCOp2GYRjw+Xx4+eWXs8pmMasmEzBT1Rd2Jj+b00tDknjpqOksz2zD"
        "lZ070++DJSWrr69Hc3MzRkZG8M0336Cnp4fHRhuGgb1792LNmjV3bfNovv2cagNzNsv8XPMfmKYJVVXx+uuvo7S0FGfOnMGFCxcw"
        "NjYGwzCgaRpWr16Nffv23dbxcc6d6eZyJpPhAnymzUSCIAiCIEE9xSIoFoshGAzC5/MhkUgsaqeZ1cGcqobq/Qxb0C52wcEWXC6X"
        "C7FYbMaYQvZ3R0dHsXz5cl6XlBY9cx9rVv5F07RZx3rivR4fH0coFMLAwMCixpxZFzVNW1LjP7FW/GLFbSgUQiwW4+Wm7gbMfZu5"
        "vDJhdfz4caxevRoNDQ3Ys2cPDh48yD0bVq9ejerqanR0dOC9995DNBrltZeZi/JM9YCnipNmrslzrRnNLKG6rkNRFO6CPvGaHo8H"
        "siwjHo9nJQOb7vfk9/uxa9cuJBIJHDx4EJcuXcoqRcWstlPdb+fmwVTtne89dZa/mm8/7wQsnrm2thZlZWU4duwYPvjgg6z+JZNJ"
        "7v5/O2HPN6/XO+18YBtCTFgTBEEQxFJjwUnJmDjo7+/ni8LFZFhmiyHLsibFed3Pn8WKApa8y+v1IhAIoL+/f07imFmFRkZGEA6H"
        "uTsjxfhOD0sCFAwGIUnSggSxy+VCNBqFpmnIzc3lc2Cx4nKp/WYWa/Vi18jNzYWmaYhGo3fd9ZT1hX2YQDt27BhGRkZ4SSIWVlBY"
        "WAhFUdDZ2YlYLMZjpVVVhSRJWLVqFc9U7XxGs3laUlLCM2qzZ4BpmgiFQsjLy5vVSs3EdzQa5X8/NzcXuq7zsWNx0CtXroTP58Pw"
        "8DCSyeSM4SeGYWDZsmXIycnhJb1Y3/x+P9xuNwoLC1FYWDjJys6s65Ik8QzbLLkWOy8/P3/W3xgrX8a+u9B+zmaNX+g8EUURy5cv"
        "h2VZ+PnnnyEIAt/MVlUVbrcba9asmdVbxpmgbbaNQFZrGgBKSkr4953VBbxeL1asWIFMJoOBgYEltyFOEARBEIsS1GxRkUql0N/f"
        "j1AohHA4zMuj0OfufGRZRjgcRigUQn9/P1Kp1JyFgSiKGB0dxejoKPLy8ngSIBrXyQIOuJkZOC8vD263Gzdu3FjwZogoiujv74eu"
        "6ygoKODJjmis786HWdUKCgqg6zr6+/vn7GVwpwW22+1Gd3c3zpw5A1VVsWPHDi5SLMuCaZrIzc0FACSTSZimiXg8DpfLhYaGhikF"
        "8C+//IJ4PI6KigoUFxdjbGyM1zVOJBKoq6vjicpma58kSRgZGcHVq1fh9/tRV1cHXde56I/H4/D7/aipqQEAtLe3I51Oz5qFmwnj"
        "QCAAn8/Hy2Zpmobx8XHU19cjGAxmtZGJ8aGhIciyjNLSUl4ey7IsRKNRrF27FuXl5VN6kmiaBsuyoKoqNE1DMpnkHh+yLM+7n5lM"
        "5o7MI/ZsYH3Pz8+HpmnIZDIwDAMjIyMoKirCY489Nqn0GRvbdDrNQ6ri8TgvNTbTRoPL5UJ7ezvi8Tg2bdqEBx98EKOjo7yqwtjY"
        "GLZu3Yri4mL09/ejq6uL6kkTBEEQS5JFBSyzBVsqlUJ3dze3MtAL9e7B3H4HBgZ4htz5jL/L5cLY2BgymQxycnIQDofvixq/t1Pk"
        "sHEGgHg8jtHR0UVbSJmoDgQCCAaDPJsvjfudv5+iKMIwDAwPD2N8fPyui2kmjqYSM+yZ+sMPP2DLli1Yv349SktLcfHiRXR3dyMW"
        "i6G8vBx79+5FJBKBrutYsWIF9u7di+LiYoyOjmaVuPJ4PPjtt99w9uxZ1NXVYf/+/Thy5Ah6e3shSRIaGxuxfft2DA4OTvnsZm2d"
        "mGzq22+/xYYNG1BTUwNN0/D9999D0zQUFRWhsbERZWVl6OrqQiQS4a7bM4n0oaEh9PX1Ye3atXjhhRfw9ddfI5FIQFEU7Ny5E9u2"
        "bcPg4OCkxFcAcOnSJWzfvh11dXUYHh7G5cuXIYoiKioq8Nxzz2F8fHyS0JMkCX19fUgmkygvL8dTTz2Fnp4e/j7r7e2ddz+dbvNs"
        "82O6fs/3uCAIuHLlCgzDQG1tLYaHh9He3g4AWLduHfbt28eT0k2c68lkEn19fVi/fj2eeOIJqKrKk5719fUhGo3yv+lsv8fjQWdn"
        "J1pbW9HQ0IDm5mZ88cUXuH79OkRRRE1NDZ555hleViwajcLv92f1YSbBPttxgiAIglgSgtq5wGKuhcz1jly/7ryQZgsotjhaqDBg"
        "7t+pVAqyLMPtdi/JzNEzjbVhGMhkMjzO9nYIX1EUMT4+zhf8ZN25O/cyk8nweM+/h5h2u90IBoPTxjR7PB5cu3YN586dw9NPP43G"
        "xkZ0dXWhp6cHX331FZ5//nk8++yz2L17N98IGxkZweHDh7F///5J2bElScInn3yCQCCAiooKvPXWW4jFYvB4PFBVFYcOHcLDDz+M"
        "NWvWZD23WVuCwWCW55Hb7cbVq1dx+PBhvPjii2hsbER9fT00TUMgEIAsy+js7MShQ4eQSCRmndfsnhw5cgQHDhxAbW0tNm/ezJNe"
        "SpKEDz/8EFu3bkVZWRlvo23b8Hq9+Omnn3D8+HE0NDTgtdde4zkkli1bhs8++wyiKKK5uRmSJHFLv9vtRk9PD44dO4bdu3ejubmZ"
        "X+/SpUt4++23oSjKgvrJrsNCQ6bq+2zHfT4fP26aJnw+H86dO4eWlhbU1dXhwIEDGB8fBwCEw2GcPXsWP/74I9544w1cu3Zt0gbN"
        "sWPHUFpaisrKSlRXV3N37XfeeQcnTpyAJEnw+/1IJBLZCwRJwqeffgqPx4Oqqiq8+eabfHxDoRASiQSOHDmC7777Lms+i6LIvQ2m"
        "Q1VV+P1+2kQkCIIg/vjry9raWts0TXR3dy86MZUzWRBxd2DxcLdLiE2sW0r8/9y+kyWqaNzv/r38e/xdXdexbt06rFu3Dl1dXTh/"
        "/vwkUcXOy8/PR2VlJUzTRCQS4W7Q5eXleOSRRxAOh2EYBq5fv45IJIJEIoHHH38cpmmipaWFxxuzDSFJklBZWYm1a9fC5/MhGo2i"
        "tbUV7e3tqKurQ0FBASKRCIaHh3md5Yceeohnlb527RoX1ixRWn5+PjZv3oySkhJ4vV7EYjFcuXIFZ86cQSqVmvMmESvlV1RUhKqq"
        "KixfvhyiKGJgYACnT59GZ2cntm/fntVGVhGCWTo3b96M9evXIxAIYHx8HOfPn8fp06dRUVGBDRs24Pz58+js7Mxqk2EYWLVqFYqL"
        "i6EoCnf1bm1t5c/W+fSTjfWjjz6KkpISnDp1Cr29vVnjZhgGtm7diqKiIpw8eRL9/f1Zx03TRGVlJQoLCxGJRDA0NMSzbdu2jS1b"
        "tvAa1alUCh0dHYhEIsjJycH27dtx48YNnD59ms8rtmERCARQVlaGnJwcuFwuSJKEs2fP4saNG1i2bBm2bduGRCKBSCSSZRlnlvKN"
        "Gzdi/fr1WWXYLly4gM7OTh6/DtyMvQ6Hw6ipqcHIyAhOnjw56ffGLNxerxctLS08qSk9AwmCIIg/AmzDuri4+Kahraam5jdJkkq7"
        "u7vtVCol3AuxhARBEPermGcWckmSpnWHZsJL0zQIggCv18vFMYv9ZQLENE14PB5IksQtjOx85/Usy+KxxEwosQzOLB7b6/Xy6zKR"
        "q+s6z2Y90fWbld9j7w22MaQoyry9lNhGAqtPzMQZG6ep2uiEZbtnHlMsVj6dTvP6zBMFPusjE43sBakoyoL7ye6RYRg8Q/jEtjLP"
        "oumOa5oG0zSzjrPNPGc/mchmmeJTqVRWgjZnm1gstdMDwZnB3DnXJn4XuFlWzpnUjs1Bj8czqf2sLRPH0gm73sS5ShAEQRD3Orc8"
        "vezi4mLBMIxOobq6+r89Hs+TPT09VjweF0lQEwRB3FlR7Uw0NtN5zuoHToHHBBE7jwk8p9iZCud3nddmIntipn/W1ukqADjb6Lzm"
        "Qj0uJnqBTOzbVG2crW/z6YPzRbmYfs6lrQs9Pls/p5tXU/XT2f75zJ2J92am82e7Hnm0EQRBEH9EQe33+62VK1eK6XT6qATgtCAI"
        "T3o8Hjsej1PsLEEQxB3EmbF5tvOmehZPFCDOc2YTJ87jc/nebG2d2MbFvjtmut5C+zbfPtyOfs6nrfM9fqf6Od823ekxIAiCIIh7"
        "EbY57fF47Fv/Py0C+EbXddPn84mUSIwgCIIgCIIgCIIgJsO85nw+n6jrugngG1HX9VbbtrsVRRE8Ho9Fu8YEQRAEQRAEQRAEkc2t"
        "0pKWoiiCbdvduq63im1tbUnLsj6WJAmqqloAKEEIQRAEQRAEQRAEQdyCaWRVVa1bFTg+bmtrS4q3Dv5F1/WM3+8XJUmyyUpNEARB"
        "EARBEARBEDexLAuSJNl+v1/UdT0jCMJfAECsr6+XIpFIu2maf1UURQyFQibFURMEQRAEQRAEQRDETWzbRigUMhVFEU3T/GskEmmv"
        "r6+XxJ07d1oABEEQ/qzruh4KhUSv10tWaoIgCIIgCIIgCGLJw2pPh0IhUdd1XRCEPwMQdu7cabmOHz9uNzU1uY4ePTpYUlIiut3u"
        "BlmWzUQiITrrXBIEQRAEQRAEQRDEUsK2bbhcLhQWFpper9dlmua/nThx4tOmpibX+++/b7kA4PLly0xU/29RUVGt1+tdI4qiEY/H"
        "RRLUBEEQBEEQBEEQxFIV1AUFBUYwGJTS6fT/RCKRf25qanJ9/PHHJgA41bJg2zaqqqrCsiy3yrK8enh42BgaGpIEQSBLNUEQBEEQ"
        "BEEQBLFkhLRt28jLyzNyc3MlXdev6rpeeerUqZFb2tgGANeE74kfffRRsqSkpAVAk6qqqiRJRiqVEi3LgiiKNLIEQRAEQRAEQRDE"
        "fYkgCLAsCy6XCwUFBUY4HJZM04zatv0PJ0+e7AQgHj9+nGfxnmR2ZubrmpqaSlEU/0uW5bWJRMIYGhpypVIpQRAEiKIIygROEARB"
        "EARBEARB3E9C2rZteL1eOy8vz1RVVdJ1vcOyrFcikUir09WbMdFC7Yyn7l6+fPlHAB5WFKVMVVVBFEUjk8kIpmkKLGEZuYITBEEQ"
        "BEEQBEEQf0QRDYALaUmS7GXLlpn5+fkuj8cj6rp+VNf1xpMnT/42lZgGprBQM5xfqKmp+ZMoiv8qy7Jb0zTE43EjkUi40um04Cyv"
        "ReKaIAiCIAiCIAiCuJdxeluLogiPx2Orqmr6/X5JURToup6xLOvfI5HInyZq4zkL6gnH7Zqamk2CIPyLKIrNsizLhmFA0zQkk0lT"
        "0zTBsixB13VS1ARBEARBEARBEMQ9iyzLtiiKtqIots/ncymKAkmSoOu6blnWf9q2/R+RSOSiUw/PJphnxKnIa2trNwL4J9u2/1EU"
        "xQclSeImcl3X6e4QBEEQBEEQBEEQ97KgBssNZhgGLMu6IgjCJwAOtbS0XJqogWdiPhZlsampSWAX3bJli8/j8WyxbftJAJWiKD4A"
        "oMy2bYFcvwmCIAiCIAiCIIh7iVt5wGwAv1qW9TuAVkEQjqbT6ba2trakQ0jbAKy5XPP/AK35StxMhgx2AAAAAElFTkSuQmCC"
    ),
}


def logo_png(key):
    return base64.b64decode("".join(LOGO_PNG_B64[str(key)]))


ICON_SIZES = (16, 32, 48, 64, 128, 256)


def write_icon_file(path):
    """Writes a Windows .ico holding the logo at every size (PNG inside). Used by the build."""
    images = [logo_png(size) for size in ICON_SIZES]
    header = struct.pack("<HHH", 0, 1, len(images))
    offset = 6 + 16 * len(images)
    entries = b""
    for size, data in zip(ICON_SIZES, images):
        dim = 0 if size >= 256 else size
        entries += struct.pack("<BBBBHHII", dim, dim, 0, 0, 1, 32, len(data), offset)
        offset += len(data)
    with open(path, "wb") as handle:
        handle.write(header + entries + b"".join(images))


def default_app_icon():
    icon = QIcon()
    for size in ICON_SIZES:
        pixmap = QPixmap()
        if pixmap.loadFromData(logo_png(size), "PNG"):
            icon.addPixmap(pixmap)
    return icon


def get_logo_folder():
    """A copy of the station's own logo is kept here, next to Logs and Playlists."""
    if getattr(sys, "frozen", False):
        candidate = os.path.join(os.path.dirname(sys.executable), "Logos")
        if _writable_dir(candidate):
            return candidate
    fallback = os.path.join(os.path.expanduser("~"), "VisionStudio", "Logos")
    if _writable_dir(fallback):
        return fallback
    return tempfile.gettempdir()


LOGO_BANNER_HEIGHT = 72


def load_banner_pixmap(settings):
    """The picture shown across the top of the program: the station's logo when chosen, else the default."""
    custom = str(settings.value("logo_custom_path", "") or "")
    if str(settings.value("logo_mode", "default")) == "custom" and custom and os.path.isfile(custom):
        pixmap = QPixmap(custom)
        if not pixmap.isNull():
            return pixmap.scaledToHeight(LOGO_BANNER_HEIGHT, Qt.TransformationMode.SmoothTransformation), True
    pixmap = QPixmap()
    pixmap.loadFromData(logo_png("banner"), "PNG")
    return pixmap.scaledToHeight(LOGO_BANNER_HEIGHT, Qt.TransformationMode.SmoothTransformation), False


def load_window_icon(settings):
    custom = str(settings.value("logo_custom_path", "") or "")
    if str(settings.value("logo_mode", "default")) == "custom" and custom and os.path.isfile(custom):
        icon = QIcon(custom)
        if not icon.isNull():
            return icon
    return default_app_icon()


class KeyboardNavigationFilter(QObject):
    """Up and Down move between controls in Settings and in dialogs, the way Tab and Shift+Tab do.
    Space or Enter opens a combo box's list. Lists, tables, number boxes and sliders keep their own arrows."""

    MOVERS = (QCheckBox, QPushButton, QComboBox, QLineEdit)

    def __init__(self, app_window):
        super().__init__()
        self.app_window = app_window

    def in_scope(self, widget):
        window = widget.window()
        if isinstance(window, QDialog):
            return True
        page = getattr(self.app_window, "settings_page", None)
        pages = getattr(self.app_window, "pages", None)
        try:
            return (page is not None and pages is not None and pages.currentIndex() == 1
                    and page.isAncestorOf(widget))
        except Exception:
            return False

    def eventFilter(self, obj, event):
        try:
            win = self.app_window
            section_list = getattr(win, "section_list", None)
            if (event.type() == QEvent.Type.KeyPress and section_list is not None
                    and getattr(win, "pages", None) is not None and win.pages.currentIndex() == 1):
                key = event.key()
                shift = bool(event.modifiers() & Qt.KeyboardModifier.ShiftModifier)
                if obj is section_list and ((key == Qt.Key.Key_Tab and not shift) or key in
                                            (Qt.Key.Key_Return, Qt.Key.Key_Enter, Qt.Key.Key_Right)):
                    if win.focus_settings_content():
                        return True
                elif (key == Qt.Key.Key_Escape and isinstance(obj, QWidget) and obj is not section_list
                      and win.settings_page.isAncestorOf(obj) and not isinstance(obj, QComboBox)):
                    section_list.setFocus()
                    return True
            if event.type() != QEvent.Type.KeyPress or not isinstance(obj, self.MOVERS):
                return False
            if event.modifiers() & (Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.AltModifier):
                return False
            key = event.key()
            if isinstance(obj, QComboBox) and key in (Qt.Key.Key_Space, Qt.Key.Key_Return, Qt.Key.Key_Enter):
                obj.showPopup()
                return True
            if not self.in_scope(obj):
                return False
            if isinstance(obj, QPushButton) and key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                obj.click()
                return True
            if key in (Qt.Key.Key_Up, Qt.Key.Key_Down):
                going_down = key == Qt.Key.Key_Down
                tab = QKeyEvent(QEvent.Type.KeyPress, Qt.Key.Key_Tab if going_down else Qt.Key.Key_Backtab,
                                Qt.KeyboardModifier.NoModifier if going_down else Qt.KeyboardModifier.ShiftModifier)
                QApplication.sendEvent(obj, tab)
                return True
        except Exception:
            return False
        return False



# ---------------------------------------------------------------------------
# Main application window
# ---------------------------------------------------------------------------

class BroadcastingApp(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Vision Studio")
        self.resize(760, 720)
        self.setStyleSheet(MAIN_WINDOW_STYLE)
        self.settings = QSettings("VisionRecords", "VisionRadio")
        self.deck_widgets = {}
        self.encoder_last_state = {}
        self.encoder_problems = {}
        self.blink_on = True
        self.is_muted = False
        _CRASH_NOTIFIER["callback"] = self.update_status

        output_device = get_selected_output_device(self.settings)

        self._rescan_in_progress = False
        self._closing = False
        self._shutdown_done = False
        self._quitting = False
        self._voice_recording = False
        self.tray = None
        self.menu_actions = {}
        self.break_deck_widgets = {}
        self.day_generated = set()
        self.append_attempted = set()
        self.last_schedule_hour = datetime.now().hour
        self.rescan_counter = 0
        RUN_LOG.write("START", f"Vision Studio started. Version {APP_VERSION}, build {BUILD_NUMBER} ({BUILD_ID}).")
        if str(self.settings.value("startup_defaults_v2", "")) != "done":
            # Earlier builds could save these two as ticked. They start unchecked now and stay that way until you tick them.
            self.settings.setValue("start_in_tray", "false")
            self.settings.setValue("autoplay_on_boot", "false")
            self.settings.setValue("startup_defaults_v2", "done")
        self.rotation_library = RotationLibrary(self.settings, on_changed=self.on_rotations_changed)
        _mode = str(self.settings.value("hour_mode", ""))
        if _mode == "mix" or (_mode not in ("volume", "fixed")
                              and str(self.settings.value("rotate_all_volumes", "true")).lower() != "false"):
            self.rotation_library.ensure_mix(str(self.settings.value("music_library_folder", "")))
        self.rotation_schedule = RotationSchedule(self.settings, self.rotation_library)
        self.category_library = CategoryLibrary(self.settings, on_changed=self.on_categories_changed)
        self.playlist_generator = PlaylistGenerator(self.settings, self.rotation_library, self.rotation_schedule)
        self.event_library = EventLibrary(self.settings, on_changed=self.refresh_schedule_views)
        self.rotation_schedule.events = self.event_library
        self.break_marks = BreakMarks(self.settings, self.event_library)
        self.playlist_generator.events = self.event_library
        self.playlist_generator.marks = self.break_marks
        self.shortcut_objects = []
        RUN_LOG.write("START", "Step 1: libraries loaded.")
        self.migrate_old_playlists()

        self.normalizer = NormalizeManager(self)
        self.normalizer.progress.connect(self.on_normalize_progress)
        self.normalizer.batch_done.connect(self.on_normalize_done)

        RUN_LOG.write("START", "Step 2: loudness manager ready.")
        self.mixer = ProgramMixer(self.update_status)
        # Safety switch (Audio Settings tab): turn the live stream mix off if it ever
        # interferes with playback on a particular computer. Takes effect on restart.
        if str(self.settings.value("use_live_mix", "true")).lower() == "false":
            self.mixer.available = False

        RUN_LOG.write("START", "Step 3: stream mixer ready.")
        self.rotation = RotationEngine(
            self.settings, self.update_status, self.on_now_playing,
            self.on_track_ending, self.on_crossfader_move, self.on_deck_update,
            normalizer=self.normalizer, output_device=output_device
        )
        self.rotation.rotation_library = self.rotation_library
        self.rotation.rotation_schedule = self.rotation_schedule
        self.rotation.on_queue_changed = self.refresh_queue_list
        self.rotation.on_rotation_swapped = self.on_rotation_swapped
        self.rotation.folder_rotor = self.playlist_generator.rotor
        RUN_LOG.write("START", "Step 4: decks ready.")
        self.sequence_player = SequencePlayer(
            self.settings, self.update_status, self.on_sequence_done, output_device
        )
        self.sequence_player.category_library = self.category_library
        self.sequence_player.on_changed = self.on_sequence_changed
        self.sequence_player.on_item_ending = self.on_item_ending
        self.sequence_player.event_provider = lambda: self.event_library.event_at(datetime.now())
        self.scheduler = SchedulerEngine(self.settings, self.on_crossfade_start, self.update_status)
        self.scheduler.on_break_upcoming = self.on_break_upcoming
        self.encoder_bank = EncoderBankWidget(
            self.settings, self.update_status, self.get_current_input_source,
            self.mixer, self.on_encoder_state_changed
        )
        RUN_LOG.write("START", "Step 5: encoders ready.")
        self.recorder = ProgramRecorder(self.settings)
        self.recorder.message.connect(self.update_status)
        self.recorder.state_changed.connect(self.on_recording_state_changed)
        self.show_controller = ShowRecordingController()
        self._seq_was_active = False
        self._vt_recording = False
        self.tagger = LibraryTagger(busy_paths=self.decks_busy_paths)
        self.tagger.progress.connect(self.on_tagging_progress)
        self.tagger.finished_scan.connect(self.on_tagging_finished)
        self.microphone = MicrophoneEngine(
            self.settings, self.update_status, self.on_mic_started, self.on_mic_stopped,
            self.on_mic_failed, self.on_mic_audio_chunk, self.on_mic_signal_changed
        )

        # Tap each audio source so the encoders stream exactly what goes on air.
        if self.mixer.available:
            self.mixer.attach_player("deck_a", self.rotation.deck_a.player,
                                     lambda: self.rotation.deck_a.audio_output.volume())
            self.mixer.attach_player("deck_b", self.rotation.deck_b.player,
                                     lambda: self.rotation.deck_b.audio_output.volume())
            self.mixer.attach_player("sequence", self.sequence_player.player,
                                     lambda: self.sequence_player.audio_output.volume())
            self.mixer.add_source("mic", lambda: 1.0)       # muting the speakers never mutes the microphone on the stream

        RUN_LOG.write("START", "Step 6: audio sources connected.")
        self.warning_beep = HostBeep(get_or_create_warning_beep_path(), output_device)
        self.connect_beep = HostBeep(get_or_create_connect_beep_path(), output_device)
        self.disconnect_beep = HostBeep(get_or_create_disconnect_beep_path(), output_device)

        RUN_LOG.write("START", "Step 7: sounds ready.")
        self.check_ffmpeg_availability()
        RUN_LOG.write("START", "Step 8: music folder scan.")
        # Pointing at a music library folder builds one rotation per subfolder.
        root = self.settings.value("music_library_folder", "")
        if self.setup_complete() and root and os.path.isdir(root):
            self._rescan_in_progress = True
            try:
                self.rotation_library.sync_from_root(root)
            finally:
                self._rescan_in_progress = False
        self.rotation_schedule.ensure_valid()
        self.rotation_library.detect_new_files()  # first look: remember what is already there
        try:
            self.category_library.sync_music(self.rotation_library)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
        RUN_LOG.write("START", "Building the window.")
        self.setup_ui()
        RUN_LOG.write("START", "Window built.")
        try:
            self.nav_filter = KeyboardNavigationFilter(self)
            QApplication.instance().installEventFilter(self.nav_filter)
            self.apply_logo()
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
        self.setup_shortcuts()
        RUN_LOG.write("START", "Shortcuts ready.")
        for optional_step in (self.setup_tray, refresh_autostart_path, keep_system_awake):
            try:                      # none of these may ever stop the program from opening
                optional_step()
            except Exception as e:
                _log_exception(type(e), e, e.__traceback__)
        self.apply_processing_settings()
        self.refresh_queue_list()
        self.refresh_status_tree()
        # Folders are set in the Settings tab. Once a music folder is known, the hour's playlist
        # is built and shown in the queue right away (nothing starts playing by itself).
        if self.setup_complete() and self.rotation_library.rotations:
            QTimer.singleShot(1500, lambda: self.ensure_hour_playlists(force=True))
        QTimer.singleShot(6000, self.encoder_bank.resume_saved)
        self.report_ready.connect(self.on_library_report_ready)
        QTimer.singleShot(2500, lambda: threading.Thread(target=self.rotation.warm_up, daemon=True).start())
        QTimer.singleShot(8000, self.resume_after_start)

        RUN_LOG.write("START", "Ready to show.")
        self.console_timer = QTimer()
        self.console_timer.setInterval(60)
        self.console_timer.timeout.connect(self.refresh_console)
        self.console_timer.start()

        self.vinyl_timer = QTimer()
        self.vinyl_timer.setInterval(30)
        self.vinyl_timer.timeout.connect(self.on_vinyl_tick)
        self.vinyl_timer.start()

        self.clock_timer = QTimer()
        self.clock_timer.setInterval(1000)
        self.clock_timer.timeout.connect(self.on_clock_tick)
        self.clock_timer.start()

        self.blink_timer = QTimer()
        self.blink_timer.setInterval(600)
        self.blink_timer.timeout.connect(self.on_blink_tick)
        self.blink_timer.start()

        self.show_timer = QTimer()
        self.show_timer.setInterval(5000)
        self.show_timer.timeout.connect(self.on_show_timer)
        self.show_timer.start()
        self.tag_timer = QTimer()
        self.tag_timer.setInterval(30 * 60 * 1000)
        self.tag_timer.timeout.connect(self.on_tag_timer)
        self.tag_timer.start()
        QTimer.singleShot(20000, self.maybe_start_first_tag_scan)
        QTimer.singleShot(40000, self.on_tag_timer)

        if not MUTAGEN_AVAILABLE:
            QTimer.singleShot(500, lambda: self.update_status(
                "Note: mutagen isn't installed, so album artwork and now-playing text won't be available."
            ))
        if not self.mixer.available:
            QTimer.singleShot(800, lambda: self.update_status(
                f"Live stream mix is unavailable ({self.mixer.unavailable_reason()}). "
                "Encoders will stream only the current track file."
            ))
        # Finish analysing any imported files that were not loudness-matched yet.
        QTimer.singleShot(3000, self.analyze_all_imported_folders)

    # --- startup checks ---
    def check_ffmpeg_availability(self):
        self.ffmpeg_ok = True
        try:
            subprocess.run([get_ffmpeg_path(), "-version"], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=8, check=True,
                           creationflags=SUBPROCESS_FLAGS)
        except Exception:
            self.ffmpeg_ok = False
            NORMALIZATION_STATE["ffmpeg_missing"] = True
            QTimer.singleShot(500, lambda: self.update_status(
                "Warning: ffmpeg was not found. Loudness matching and streaming will not work until it is installed or bundled."
            ))

    def analyze_all_imported_folders(self):
        paths = []
        for key in ("music_library_folder", ":00", ":15", ":30", ":45", "ad_break_folder"):
            paths += scan_audio_files(self.settings.value(key, ""))
        if paths:
            self.normalizer.start(paths)

    def on_normalize_progress(self, done, total, name):
        self.loudness_label.setText(f"Loudness: analysing {done} of {total}")
        self.loudness_label.setStyleSheet(f"color: {COLOR_WARNING_AMBER};")

    def on_normalize_done(self, ok, failed):
        if not self.ffmpeg_ok or NORMALIZATION_STATE["ffmpeg_missing"]:
            return
        text = f"Loudness: matched {ok} file(s)"
        if failed:
            text += f", {failed} could not be matched"
        self.loudness_label.setText(text + ".")
        self.loudness_label.setStyleSheet(f"color: {COLOR_ON_AIR_GREEN};")

    def get_current_input_source(self):
        """Fallback only: used when the live mix is unavailable."""
        return self.rotation.current_track_path or ""

    def setup_shortcuts(self):
        self.rebuild_shortcuts()

    def shortcut_handlers(self):
        return {
            "insert_tracks": self.insert_tracks,
            "insert_tracks_alt": self.insert_tracks,
            "automation_toggle": self.automation_toggle,
            "stop_fade": self.stop_with_fade,
            "start_rotation": self.start_rotation,
            "stop_rotation": self.stop_everything,
            "mute_all": self.toggle_mute,
            "open_options": self.open_options,
            "toggle_recording": self.toggle_recording,
            "new_item": self.new_item,
            "generate_now": self.generate_now,
            "say_elapsed": self.say_elapsed,
            "say_remaining": self.say_remaining,
            "say_current": self.say_current,
            "say_status": self.say_status,
            "say_hour_remaining": self.say_hour_remaining,
            "say_mute": self.say_mute,
            "say_encoders": self.say_encoders,
            "voice_track_before": self.voice_track_before,
            "voice_track_after": self.voice_track_after,
        }

    def rebuild_shortcuts(self):
        """(Re)creates every shortcut from the saved layout. Station Playlist keys by default."""
        for shortcut in self.shortcut_objects:
            try:
                shortcut.setEnabled(False)
                shortcut.setParent(None)
                shortcut.deleteLater()
            except Exception:
                pass
        self.shortcut_objects = []
        bindings = load_shortcut_bindings(self.settings)
        handlers = self.shortcut_handlers()
        if self.menu_actions:
            self.refresh_menu_labels()
        for sid, handler in handlers.items():
            key = bindings.get(sid, "")
            if not key:
                continue
            shortcut = QShortcut(QKeySequence(key), self)
            shortcut.setContext(Qt.ShortcutContext.WindowShortcut)
            shortcut.activated.connect(handler)
            self.shortcut_objects.append(shortcut)

    def migrate_old_playlists(self):
        """Earlier builds saved playlists in Documents\\VisionStudio. They move to the program folder
        (Playlists next to Logs) and the Documents folder is removed."""
        try:
            documents = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.DocumentsLocation)
            if not documents or not isinstance(documents, str):
                documents = os.path.join(os.path.expanduser("~"), "Documents")
            old_root = os.path.join(documents, "VisionStudio")
            old_playlists = os.path.join(old_root, "Playlists")
            saved = str(self.settings.value("playlist_output_folder", "") or "")
            if saved and os.path.normcase(os.path.normpath(saved)) == os.path.normcase(os.path.normpath(old_playlists)):
                self.settings.setValue("playlist_output_folder", "")
            new_folder = self.playlist_generator.output_folder()
            if not os.path.isdir(old_root) or os.path.normcase(os.path.normpath(new_folder)) == \
                    os.path.normcase(os.path.normpath(old_playlists)):
                return
            moved = 0
            if os.path.isdir(old_playlists):
                os.makedirs(new_folder, exist_ok=True)
                for name in os.listdir(old_playlists):
                    source = os.path.join(old_playlists, name)
                    target = os.path.join(new_folder, name)
                    if os.path.isfile(source) and not os.path.exists(target):
                        shutil.copy2(source, target)
                        moved += 1
            # remove the old folders only if nothing but playlists was in them
            leftovers = [f for _root, _dirs, files in os.walk(old_root) for f in files
                         if not f.lower().endswith((".m3u", ".m3u8"))]
            if not leftovers:
                shutil.rmtree(old_root, ignore_errors=True)
            RUN_LOG.write("MOVE", f"Moved {moved} playlist file(s) from {old_playlists} to {new_folder}.")
        except Exception as e:
            RUN_LOG.write("ERROR", f"Could not move the old playlist folder: {e}")

    # --- first-run setup wizard ---
    def setup_complete(self):
        return str(self.settings.value("setup_complete", "false")).lower() == "true"

    def run_setup_wizard(self):
        current = {key: self.settings.value(key, "") for key, _t, _d in WIZARD_STEPS}
        wizard = SetupWizard(self, current, self.playlist_generator.output_folder())
        if wizard.exec() == QDialog.DialogCode.Accepted:
            self.apply_setup(wizard.results())
        elif not self.setup_complete():
            self.update_status("Setup was not finished. It will ask again next time you open Vision Studio.")

    def apply_setup(self, results):
        """Saves every folder from the wizard and creates the playlist folder. Never starts playback."""
        for key, path in results.items():
            if path:
                self.settings.setValue(key, path)
        playlist_folder = self.playlist_generator.output_folder()
        try:
            os.makedirs(playlist_folder, exist_ok=True)
        except OSError as e:
            self.update_status(f"Could not create the playlist folder: {e}")
        self.settings.setValue("playlist_output_folder", playlist_folder)
        self.playlist_folder_label.setText(f"Playlist folder: {playlist_folder}")
        self.settings.setValue("setup_complete", "true")
        root = results.get("music_library_folder", "")
        if root and os.path.isdir(root):
            self._rescan_in_progress = True
            try:
                self.rotation_library.sync_from_root(root)
            finally:
                self._rescan_in_progress = False
            self.rotation_schedule.regenerate_even()
            self.rotation_library.detect_new_files()
        self.rotations_tab.refresh()
        self.schedule_tab.refresh()
        self.refresh_queue_list()
        self.analyze_all_imported_folders()
        self.refresh_status_tree()
        self.announce("Setup saved. Choose Start Rotation when you are ready to go on air.")

    # --- status tree ---
    def build_status_tree(self):
        tree = QTreeWidget()
        tree.setHeaderHidden(True)
        tree.setAccessibleName("Station status tree. Up and Down move between items, Right opens a group, "
                               "Left closes it.")
        tree.setMinimumHeight(170)
        self.status_tree = tree
        self.status_items = {}
        self.encoder_tree_items = {}
        groups = [
            ("onair", "On Air", [("deck_a", "Deck A"), ("deck_b", "Deck B"),
                                 ("rotation", "Rotation"), ("break", "Break")]),
            ("next", "Up Next", [("upnext", "Next track")]),
            ("time", "Time", [("hour_left", "Left in this hour"), ("elapsed", "Elapsed on the air track"),
                              ("remaining", "Remaining on the air track")]),
            ("audio", "Audio", [("mute", "Mute"), ("mic", "Microphone"), ("feed", "Stream feed"),
                                ("proc", "Processor")]),
            ("enc", "Encoders", []),
        ]
        for group_key, title, children in groups:
            group = QTreeWidgetItem(tree, [title])
            self.status_items[group_key] = group
            for key, label in children:
                self.status_items[key] = QTreeWidgetItem(group, [label])
            group.setExpanded(True)
        tree.setCurrentItem(self.status_items["onair"])
        return tree

    def _set_tree(self, key, text):
        item = self.status_items.get(key)
        if item is not None and item.text(0) != text:
            item.setText(0, text)

    @staticmethod
    def _track_text(path):
        if not path:
            return ""
        if path not in _QUEUE_TEXT_CACHE:
            try:
                _QUEUE_TEXT_CACHE[path] = format_track_display(path)
            except Exception:
                _QUEUE_TEXT_CACHE[path] = os.path.splitext(os.path.basename(path))[0]
        return _QUEUE_TEXT_CACHE[path]

    def refresh_status_tree(self):
        if not hasattr(self, "status_tree"):
            return
        rot = self.rotation
        for name, deck in (("A", rot.deck_a), ("B", rot.deck_b)):
            path = deck.current_track_path
            if not path:
                text = f"Deck {name}: empty"
            else:
                playing = deck.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState
                if name == rot.live_deck_name and playing:
                    state = "ON AIR"
                elif playing:
                    state = "fading out"
                elif name == rot.live_deck_name:
                    state = "on air, paused"
                else:
                    state = "cued"
                text = f"Deck {name}: {self._track_text(path)}, {state}"
            self._set_tree("deck_" + name.lower(), text)
        self._set_tree("rotation", f"Rotation: {rot.active_rotation_name() or 'none'}"
                       + (", automation on" if rot.automation_on else (", song finishing, automation off" if rot.is_running else ", stopped")))
        sp = self.sequence_player
        if sp.active and sp.items and 0 <= sp.item_index < len(sp.items):
            break_text = (f"Break {sp.slot}: item {sp.item_index + 1} of {len(sp.items)}, "
                          f"{os.path.basename(sp.items[sp.item_index])}")
        elif rot.is_paused_for_sequence:
            break_text = "Break: playing now"
        elif rot.break_target is not None:
            seconds = max(0, int((rot.break_target - datetime.now()).total_seconds()))
            break_text = f"Break: {rot.break_slot} armed, {speak_duration(seconds)} to the mark"
        else:
            break_text = "Break: none pending"
        self._set_tree("break", break_text)
        upcoming = rot.get_upcoming_track_path()
        self._set_tree("upnext", f"Next track: {self._track_text(upcoming)}" if upcoming else "Next track: none")
        now = datetime.now()
        self._set_tree("hour_left", f"Left in this hour: {speak_duration(3600 - (now.minute * 60 + now.second))}")
        live = rot.get_live_deck()
        if live.current_track_path and live.player.duration() > 0:
            elapsed = int(live.player.position() / 5000) * 5
            remaining = int(max(0, live.player.duration() - live.player.position()) / 5000) * 5
            self._set_tree("elapsed", f"Elapsed on the air track: about {speak_duration(elapsed)}")
            self._set_tree("remaining", f"Remaining on the air track: about {speak_duration(remaining)}")
        else:
            self._set_tree("elapsed", "Elapsed on the air track: nothing playing")
            self._set_tree("remaining", "Remaining on the air track: nothing playing")
        self._set_tree("mute", "Mute: ON" if self.is_muted else "Mute: off")
        self._set_tree("mic", self.console_mic_label.text().rstrip("."))
        self._set_tree("feed", self.console_feed_label.text().rstrip("."))
        master = self.mixer.master_processor
        if master is not None and master.enabled and self.mixer.available:
            self._set_tree("proc", f"Processor: on, {master.preset_name} preset")
        else:
            self._set_tree("proc", "Processor: off")
        # one child per encoder
        group = self.status_items["enc"]
        slots = list(self.encoder_bank.slots)
        for slot in list(self.encoder_tree_items):
            if slot not in slots:
                group.removeChild(self.encoder_tree_items.pop(slot))
        for slot in slots:
            item = self.encoder_tree_items.get(slot)
            if item is None:
                item = QTreeWidgetItem(group, [""])
                self.encoder_tree_items[slot] = item
                group.setExpanded(True)
            state = {"live": "LIVE", "connecting": "connecting"}.get(slot.state, "offline")
            problem = self.encoder_problems.get(slot)
            text = f"{slot.stream_name}: {state}" + (f", problem: {problem}" if problem else "")
            if item.text(0) != text:
                item.setText(0, text)
        if not slots:
            self._set_tree("enc", "Encoders (none set up)")
        elif group.text(0) != "Encoders":
            group.setText(0, "Encoders")

    # --- recording ---
    def decks_busy_paths(self):
        paths = set()
        for deck in (self.rotation.deck_a, self.rotation.deck_b):
            if deck.current_track_path:
                paths.add(deck.current_track_path)
        return paths

    def toggle_recording(self):
        if self.recorder.recording:
            self.stop_recording(by_user=True)
        else:
            self.start_recording()

    def start_recording(self, by_schedule=False, for_voice=False):
        """Returns True when recording is running. The first time, asks for bitrate and cue sheet.
        With "record only scheduled shows" on (the default), only a scheduled show or a voice track can start one."""
        if (not by_schedule and not for_voice
                and str(self.settings.value("record_only_scheduled", "true")).lower() != "false"
                and active_show(load_show_times(self.settings), datetime.now()) is None):
            self.announce("Recordings only start during a scheduled show. Add the show time in Settings, Recording, "
                          "or turn off Record only scheduled shows.")
            return False
        if not self.recorder.setup_done():
            if by_schedule:
                self.announce("A scheduled recording was skipped. Press R once to finish the recording setup.")
                return False
            dialog = FirstRecordingSetupDialog(self, bitrate=self.recorder.bitrate() or 128,
                                               cue=self.recorder.cue_enabled())
            if dialog.exec() != QDialog.DialogCode.Accepted:
                self.announce("Recording was not started.")
                return False
            self.settings.setValue("record_bitrate", dialog.chosen_bitrate())
            self.settings.setValue("record_cue", "true" if dialog.chosen_cue() else "false")
            self.settings.setValue("record_setup_done", "true")
            self.refresh_recording_controls()
        path, meta = None, None
        try:
            deck = self.rotation.get_live_deck()
            if deck.current_track_path and self.audio_is_playing():
                path = deck.current_track_path
                meta = get_track_metadata(path)
        except Exception:
            pass
        ok, message = self.recorder.start(self.mixer, meta, by_schedule, path)
        self.announce(message)
        return ok

    def stop_recording(self, by_user=False):
        if not self.recorder.recording:
            return
        if by_user:
            try:
                active = active_show(load_show_times(self.settings), datetime.now())
                self.show_controller.user_stopped(active[1] if active else None)
            except Exception:
                pass
        path = self.recorder.stop()
        self.announce(f"Recording stopped. Saved to {path}" if path else "Recording stopped.")

    def on_recording_state_changed(self, active):
        try:
            if active:
                self.record_label.setText(f"RECORDING at {self.recorder.bitrate()} kbps.")
                self.record_label.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
                self.record_btn.setText("Stop Recording (R)")
            else:
                self.record_label.setText("Recording: off.")
                self.record_label.setStyleSheet(f"color: {COLOR_TEXT_DIM}; font-weight: bold;")
                self.record_btn.setText("Start Recording (R)")
        except Exception:
            pass

    def on_show_timer(self):
        try:
            shows = load_show_times(self.settings)
            if not shows and not self.recorder.started_by_schedule:
                return
            action, name = self.show_controller.decide(shows, datetime.now(), self.recorder.recording,
                                                       self.recorder.started_by_schedule)
            if action == "start":
                if self.start_recording(by_schedule=True):
                    self.announce(f"Live show recording started: {name}.")
                else:
                    self.show_controller.suppressed_window = self.show_controller.schedule_window
            elif action == "stop":
                self.stop_recording()
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def build_recording_tab(self):
        page = QWidget()
        layout = QFormLayout()
        intro = QLabel("Recording captures the program mix to an MP3. Press R anywhere to start or stop. "
                       "Nothing records by itself unless you add a live show time below.")
        intro.setWordWrap(True)
        layout.addRow(intro)
        self.record_bitrate_combo = QComboBox()
        self.record_bitrate_combo.setAccessibleName("Recording bitrate")
        self.record_bitrate_combo.addItem("128 kbps (smaller files)", 128)
        self.record_bitrate_combo.addItem("320 kbps (best quality, for podcast platforms)", 320)
        self.record_bitrate_combo.currentIndexChanged.connect(self.on_record_options_changed)
        layout.addRow("Bitrate:", self.record_bitrate_combo)
        self.record_cue_check = QCheckBox("Write a cue sheet and a licensing list with each recording "
                                          "(artist, title, album, label and ISRC)")
        self.record_cue_check.toggled.connect(self.on_record_options_changed)
        layout.addRow(self.record_cue_check)
        self.record_custom_folder_check = QCheckBox("Use a different recordings folder (otherwise the Recordings folder "
                                                    "made by the installer is used)")
        self.record_custom_folder_check.toggled.connect(self.on_record_custom_folder_toggled)
        layout.addRow(self.record_custom_folder_check)
        self.record_folder_label = QLabel("")
        self.record_folder_label.setWordWrap(True)
        layout.addRow("Recordings folder:", self.record_folder_label)
        self.record_folder_btn = QPushButton("Choose Recordings Folder")
        self.record_folder_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.record_folder_btn.clicked.connect(self.choose_recordings_folder)
        layout.addRow(self.record_folder_btn)
        open_btn = QPushButton("Open Recordings Folder")
        open_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        open_btn.clicked.connect(self.open_recordings_folder)
        layout.addRow(open_btn)
        self.record_only_check = QCheckBox("Record only scheduled shows (and voice tracking if switched on below)")
        self.record_only_check.toggled.connect(self.on_record_options_changed)
        layout.addRow(self.record_only_check)
        self.record_vt_check = QCheckBox("Also record the program while I am voice tracking")
        self.record_vt_check.toggled.connect(self.on_record_options_changed)
        layout.addRow(self.record_vt_check)
        toggle_btn = QPushButton("Start Or Stop Recording (R)")
        toggle_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        toggle_btn.clicked.connect(self.toggle_recording)
        layout.addRow(toggle_btn)
        layout.addRow(QLabel("Live show times: recording starts and stops by itself at these times."))
        self.show_list = QListWidget()
        self.show_list.setAccessibleName("Live show recording times")
        self.show_list.setMaximumHeight(140)
        layout.addRow(self.show_list)
        show_buttons = QHBoxLayout()
        add_show = QPushButton("Add Live Show")
        add_show.setStyleSheet(BUTTON_STYLE_CONSOLE)
        add_show.clicked.connect(self.add_live_show)
        show_buttons.addWidget(add_show)
        remove_show = QPushButton("Remove Selected Show")
        remove_show.setStyleSheet(BUTTON_STYLE_CONSOLE)
        remove_show.clicked.connect(self.remove_live_show)
        show_buttons.addWidget(remove_show)
        layout.addRow(show_buttons)
        page.setLayout(layout)
        self.refresh_recording_controls()
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(page)
        return scroll

    def refresh_recording_controls(self):
        self._loading_record_options = True
        try:
            index = self.record_bitrate_combo.findData(self.recorder.bitrate() or 128)
            self.record_bitrate_combo.setCurrentIndex(max(0, index))
            self.record_cue_check.setChecked(self.recorder.cue_enabled())
            self.record_vt_check.setChecked(str(self.settings.value("record_voice_tracking", "false")).lower() == "true")
            self.record_only_check.setChecked(str(self.settings.value("record_only_scheduled", "true")).lower() != "false")
            custom = bool(str(self.settings.value("recordings_folder", "") or "").strip())
            self.record_custom_folder_check.setChecked(custom)
            self.record_folder_btn.setEnabled(custom)
            self.record_folder_label.setText(self.recorder.folder())
            self.show_list.clear()
            for show in load_show_times(self.settings):
                self.show_list.addItem(describe_show(show))
        finally:
            self._loading_record_options = False

    def on_record_options_changed(self, *_args):
        if getattr(self, "_loading_record_options", False):
            return
        self.settings.setValue("record_bitrate", self.record_bitrate_combo.currentData())
        self.settings.setValue("record_cue", "true" if self.record_cue_check.isChecked() else "false")
        self.settings.setValue("record_voice_tracking", "true" if self.record_vt_check.isChecked() else "false")
        self.settings.setValue("record_only_scheduled", "true" if self.record_only_check.isChecked() else "false")
        self.announce("Recording options saved.")

    def on_record_custom_folder_toggled(self, checked):
        if getattr(self, "_loading_record_options", False):
            return
        self.record_folder_btn.setEnabled(checked)
        if not checked:
            self.settings.setValue("recordings_folder", "")
            self.record_folder_label.setText(self.recorder.folder())
            self.announce("Recordings go to the installer's Recordings folder.")

    def choose_recordings_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Choose the recordings folder", self.recorder.folder())
        if folder:
            self.settings.setValue("recordings_folder", folder)
            self.record_folder_label.setText(folder)
            self.announce(f"Recordings folder: {folder}")
        elif not str(self.settings.value("recordings_folder", "") or "").strip():
            self.record_custom_folder_check.setChecked(False)

    def open_recordings_folder(self):
        folder = self.recorder.folder()
        try:
            os.makedirs(folder, exist_ok=True)
            if sys.platform == "win32":
                os.startfile(folder)
            else:
                self.announce(f"Recordings folder: {folder}")
        except Exception as e:
            self.announce(f"The folder could not be opened: {e}")

    def add_live_show(self):
        dialog = ShowTimeDialog(self)
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return
        shows = load_show_times(self.settings)
        shows.append(dialog.show_entry())
        save_show_times(self.settings, shows)
        self.refresh_recording_controls()
        self.announce("Live show added. Recording will start and stop at those times.")

    def remove_live_show(self):
        row = self.show_list.currentRow()
        shows = load_show_times(self.settings)
        if 0 <= row < len(shows):
            del shows[row]
            save_show_times(self.settings, shows)
            self.refresh_recording_controls()
            self.announce("Live show removed.")

    # --- tagging ---
    def build_tagging_tab(self):
        page = QWidget()
        layout = QFormLayout()
        intro = QLabel("Tagging fills in a song's missing album, record label and ISRC using the artist and title "
                       "already in the file, looked up in the free MusicBrainz database. No account is needed. "
                       "Tags that are already there are never changed, and songs with every tag are skipped. "
                       "It needs an internet connection and never touches a song that is loaded on a deck.")
        intro.setWordWrap(True)
        layout.addRow(intro)
        scan_btn = QPushButton("Tag My Music Library Now")
        scan_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        scan_btn.clicked.connect(self.start_library_tagging)
        layout.addRow(scan_btn)
        stop_btn = QPushButton("Stop Tagging")
        stop_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        stop_btn.clicked.connect(lambda _checked=False: self.tagger.stop())
        layout.addRow(stop_btn)
        self.tag_new_check = QCheckBox("Also tag new songs added to the library (checked at startup and every 30 minutes)")
        self.tag_new_check.setChecked(str(self.settings.value("tag_new_songs", "false")).lower() == "true")
        self.tag_new_check.toggled.connect(self.on_tag_new_toggled)
        layout.addRow(self.tag_new_check)
        self.tag_status_label = QLabel("Tagging: idle.")
        self.tag_status_label.setAccessibleName("Tagging status")
        self.tag_status_label.setWordWrap(True)
        layout.addRow(self.tag_status_label)
        page.setLayout(layout)
        return page

    def on_tag_new_toggled(self, checked):
        self.settings.setValue("tag_new_songs", "true" if checked else "false")
        self.announce("New songs will be tagged." if checked else "New songs will not be tagged automatically.")

    def start_library_tagging(self):
        folder = self.settings.value("music_library_folder", "")
        if not folder or not os.path.isdir(folder):
            self.announce("Choose the music library folder in Settings, General, first.")
            return
        if self.tagger.start(folder):
            self.tag_status_label.setText("Tagging: started.")
            self.announce("Tagging started in the background.")
        else:
            self.announce("Tagging is already running." if self.tagger.running else "Tagging could not start.")

    def on_tagging_progress(self, text):
        try:
            self.tag_status_label.setText(text)
            self.update_status(text)
        except Exception:
            pass

    def on_tagging_finished(self, summary):
        try:
            self.tag_status_label.setText(summary)
            self.announce(summary)
        except Exception:
            pass

    def maybe_start_first_tag_scan(self):
        """Once, a little after the first launch with a music library: offers to tag the whole library."""
        try:
            if str(self.settings.value("tag_first_scan_done", "false")).lower() == "true":
                return
            folder = self.settings.value("music_library_folder", "")
            if not (folder and os.path.isdir(folder)) or not self.isVisible():
                QTimer.singleShot(60000, self.maybe_start_first_tag_scan)
                return
            box = QMessageBox(self)
            box.setWindowTitle("Tag your music library?")
            box.setText("Vision Studio can fill in missing album, record label and ISRC tags in your music library "
                        "for licensing. Tags that are already there are never changed. It runs in the background "
                        "and needs the internet. Tag the library now?")
            box.setStandardButtons(QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
            self.settings.setValue("tag_first_scan_done", "true")
            if box.exec() == QMessageBox.StandardButton.Yes:
                self.start_library_tagging()
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def on_tag_timer(self):
        try:
            if str(self.settings.value("tag_new_songs", "false")).lower() != "true" or self.tagger.running:
                return
            folder = self.settings.value("music_library_folder", "")
            if folder and os.path.isdir(folder):
                self.tagger.start(folder)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    # --- shortcut actions ---
    def open_options(self):
        """Ctrl+O: opens Settings, or goes back to the on-air screen when Settings is already open."""
        if self.pages.currentIndex() == 1:
            self.show_onair()
        else:
            self.show_settings()

    def show_settings(self, section=None):
        if section is not None:
            self.section_list.setCurrentRow(section)
        self.pages.setCurrentIndex(1)
        self.section_list.setFocus()
        self.announce("Settings. Use the up and down arrows to choose a section, then Tab. "
                      "Press Ctrl+O or Escape to go back to the on-air screen.")

    def show_onair(self):
        self.pages.setCurrentIndex(0)
        self.queue_list.setFocus()
        self.announce("On-air screen.")

    def on_escape_pressed(self):
        if self.pages.currentIndex() == 1:
            self.show_onair()

    def new_item(self):
        """Ctrl+N: creates whatever belongs to the Settings section you are on."""
        if self.pages.currentIndex() == 0:
            self.insert_hour_marker()
            return
        current = self.tabs.currentWidget()
        if current is self.rotations_tab:
            self.rotations_tab.new_rotation()
        elif current is self.categories_tab:
            self.categories_tab.import_folder()
        elif current is self.schedule_tab:
            self.schedule_tab.regenerate()
        else:
            self.insert_hour_marker()

    def say_elapsed(self):
        deck = self.rotation.get_live_deck()
        if not deck.current_track_path:
            self.announce("Nothing is playing.")
            return
        self.announce(f"Elapsed {speak_duration(deck.player.position() / 1000.0)}.")

    def say_remaining(self):
        deck = self.rotation.get_live_deck()
        if not deck.current_track_path or deck.player.duration() <= 0:
            self.announce("Nothing is playing.")
            return
        remaining = max(0, deck.player.duration() - deck.player.position()) / 1000.0
        self.announce(f"Remaining {speak_duration(remaining)}.")

    def say_current(self):
        path = self.rotation.current_track_path
        self.announce(f"Playing {format_track_display(path)}." if path else "Nothing is playing.")

    def say_status(self):
        deck = self.rotation.get_live_deck()
        playing = deck.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState
        if self.rotation.is_paused_for_sequence:
            text = "A scheduled break is on."
        elif playing:
            text = "Rotation is playing."
        elif self.rotation.is_running:
            text = "Rotation is running but paused."
        else:
            text = "Automation is off."
        self.announce(text)

    def say_hour_remaining(self):
        now = datetime.now()
        seconds = 3600 - (now.minute * 60 + now.second)
        self.announce(f"{speak_duration(seconds)} left in this hour.")

    def say_mute(self):
        self.announce("Audio is muted." if self.is_muted else "Audio is not muted.")

    def say_encoders(self):
        self.announce(self.console_encoders_label.text())

    # --- queue ---
    def insert_tracks(self):
        """Insert: pick files and add them after the selected queue row (or at the end). Never auto-plays."""
        files, _ = QFileDialog.getOpenFileNames(
            self, "Insert tracks into the queue", self.settings.value("music_library_folder", ""),
            "Audio files (*.mp3 *.wav *.flac *.m4a *.aac *.ogg *.wma *.opus);;All files (*.*)")
        if not files:
            return
        # Like Station Playlist: the song on air is the first row. Insert with it selected puts the new
        # tracks straight after it, ahead of whatever was about to play. Insert on a later row goes
        # right after that row. With nothing selected the tracks go to the end.
        row = self.queue_list.currentRow()
        header = self.queue_list.header_count
        index = max(0, row - header + 1) if row >= 0 else None
        for offset, path in enumerate(files):
            self.rotation.insert_queue_item(path, None if index is None else index + offset)
        self.normalizer.start(files, priority=True)
        where = "next, ahead of the song that was about to play" if index == 0 else (
            f"at position {index + 1}" if index is not None else "at the end")
        self.announce(f"Inserted {len(files)} track(s) {where}.")
        self.queue_list.setFocus()

    def insert_hour_marker(self):
        row = self.queue_list.currentRow()
        header = self.queue_list.header_count
        self.rotation.insert_queue_item(HOUR_MARKER_TOKEN, max(0, row - header + 1) if row >= 0 else None)
        self.announce("Hour marker inserted into the queue.")

    def refresh_queue_list(self):
        if hasattr(self, "queue_list"):
            passed = []
            for path, state in self.rotation.passed_rows():
                try:
                    title = format_track_display(path)
                except Exception:
                    title = os.path.basename(path)
                passed.append(f"{'Played' if state == 'played' else 'Skipped'}: {title}")
            self.queue_list.show_queue(self.rotation.queue_snapshot(), self.queue_headers(), passed=passed)
            self.queue_label.setText(f"Queue: {len(self.rotation.shuffled_queue)} tracks"
                                     + (f", rotation {self.rotation.active_rotation_name()}"
                                        if self.rotation.active_rotation_name() else ""))

    def queue_headers(self):
        """Rows above the queue: the song on air, then each item of a break with its folder, so you can
        see exactly which files are being pulled."""
        rot = self.rotation
        path = rot.current_track_path
        now = f"Now playing: {self._track_text(path)}" if path else "Nothing is playing"
        if rot.is_paused_for_sequence:
            now += " (music paused for the break)"
        headers = [now]
        sp = self.sequence_player
        if sp.active and sp.items:
            for i, item in enumerate(sp.items):
                state = "done" if i < sp.item_index else ("playing now" if i == sp.item_index else "waiting")
                headers.append(f"{sp.slot} break {i + 1} of {len(sp.items)}, {state}: "
                               f"{os.path.basename(item)} from {os.path.dirname(item)}")
        return headers

    def on_queue_play(self, row):
        index = row - self.queue_list.header_count
        if index < 0:
            return
        if self.rotation.play_item_now(index):
            self.announce("Playing the selected song now." + ("" if self.rotation.automation_on
                          else " Automation is off, so the music waits for you after it."))
        else:
            self.update_status("That item cannot be played.")

    def on_queue_check_changed(self, row, checked):
        """Space on a row: unchecking an upcoming song skips it, checking a played or skipped song puts it next."""
        header = self.queue_list.header_count
        start = self.queue_list.passed_start
        if row >= header and not checked:
            QTimer.singleShot(0, lambda i=row - header: self._apply_uncheck(i))
        elif start <= row < header and checked:
            QTimer.singleShot(0, lambda i=row - start: self._apply_recheck(i))

    def _apply_uncheck(self, index):
        item = self.rotation.uncheck_queue_item(index)
        if item is not None:
            self.announce("Unchecked. This song will not play.")
        self.refresh_queue_list()

    def _apply_recheck(self, passed_index):
        path = self.rotation.recheck_passed(passed_index)
        if path is not None:
            self.announce("Checked. This song plays next.")
        self.refresh_queue_list()

    def on_queue_move(self, row, delta):
        index = row - self.queue_list.header_count
        if index < 0:
            return
        new_index = self.rotation.move_queue_item(index, delta)
        self.queue_list.setCurrentRow(new_index + self.queue_list.header_count)
        self.update_status(f"Moved to position {new_index + 1}.")

    def on_queue_remove(self, row):
        index = row - self.queue_list.header_count
        if index < 0:
            return
        removed = self.rotation.remove_queue_item(index)
        if removed is not None:
            self.update_status(f"Removed {format_track_display(removed)} from the queue.")

    def import_m3u(self):
        path, _ = QFileDialog.getOpenFileName(self, "Import M3U playlist", "", "Playlists (*.m3u *.m3u8)")
        if not path:
            return
        entries, missing = read_m3u(path)
        added = self.rotation.load_queue_entries(entries, replace=False)
        note = f" {missing} entries were not found." if missing else ""
        self.announce(f"Imported {added} entries from the playlist into the queue.{note}")

    def export_m3u(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export queue as M3U", "queue.m3u8", "Playlists (*.m3u8 *.m3u)")
        if not path:
            return
        write_m3u(path, self.rotation.queue_snapshot())
        self.announce(f"Queue exported to {path}.")

    # --- rotations, schedule, categories ---
    def on_rotations_changed(self, kind):
        if not self._rescan_in_progress and kind in ("added", "removed", "folder"):
            self.rotation_schedule.regenerate_even()   # editing a rotation rebuilds the day
        else:
            self.rotation_schedule.ensure_valid()
        try:
            if getattr(self, "category_library", None) is not None:
                self.category_library.sync_music(self.rotation_library)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
        if hasattr(self, "rotations_tab"):
            self.rotations_tab.refresh()
            self.schedule_tab.refresh()
        if hasattr(self, "rotation"):
            self.rotation.check_rotation_for_hour()

    def on_categories_changed(self):
        if hasattr(self, "categories_tab"):
            self.categories_tab.refresh()

    def on_rotation_swapped(self, old_name, new_name):
        if hasattr(self, "schedule_tab"):
            self.schedule_tab.refresh()
        self.announce(f"Rotation changed to {new_name}." if not old_name
                      else f"Rotation changed from {old_name} to {new_name}.")
        self.refresh_queue_list()

    def rescan_library(self):
        """Picks up new songs and new subfolders without rebuilding the schedule."""
        if not self.setup_complete():
            return
        root = self.settings.value("music_library_folder", "")
        self._rescan_in_progress = True
        try:
            if root and os.path.isdir(root):
                added, removed = self.rotation_library.sync_from_root(root)
                if added:
                    self.announce("New rotation found: " + ", ".join(added) + ".")
                    for rotation in self.rotation_library.rotations:
                        if rotation.name in added:
                            self.normalizer.start(rotation.track_paths())
            new_files = self.rotation_library.detect_new_files()
        finally:
            self._rescan_in_progress = False
        total = 0
        for rotation_id, paths in new_files.items():
            self.normalizer.start(paths)
            total += self.rotation.add_new_tracks(rotation_id, paths)
        if new_files:
            self.update_status(f"{sum(len(v) for v in new_files.values())} new song(s) found.")

    # --- clock-driven chores (once a second) ---
    def on_clock_tick(self):
        try:
            hour = datetime.now().hour
            self.rotation.check_rotation_for_hour()
            self.refresh_status_tree()
            if hour != self.last_schedule_hour:
                self.last_schedule_hour = hour
                self.schedule_tab.refresh()
                self.on_hour_changed()
            self.maybe_append_next_hour()
            self.played_counter = getattr(self, "played_counter", 0) + 1
            if self.played_counter >= 30:
                self.played_counter = 0
                self.refresh_played_list()
            self.rescan_counter += 1
            if self.rescan_counter >= 60:
                self.rescan_counter = 0
                self.rescan_library()
            if (self.rotation.is_running and self.rotation.automation_on and not self.rotation.is_paused_for_sequence
                    and self.rotation.break_target is None):
                now = datetime.now()
                mark = SchedulerEngine.next_mark(now)
                slot = {0: ":00", 15: ":15", 30: ":30", 45: ":45"}[mark.minute]
                if (mark - now).total_seconds() <= break_window_seconds(self.settings) and not self.rotation.break_recently_taken(slot):
                    self.on_break_upcoming(slot, mark)
            job = self.playlist_generator.due_job()
            if job is not None:
                self.run_generation_job(job)
            # Safety net: a break that never got its turn (for example the deck was paused by hand).
            target = self.rotation.break_target
            if target is not None:
                late = (datetime.now() - target).total_seconds()
                live_playing = (self.rotation.get_live_deck().player.playbackState()
                                == QMediaPlayer.PlaybackState.PlayingState)
                if (late > 5 and not live_playing) or late > 900:
                    slot = self.rotation.break_slot
                    self.rotation.disarm_break()
                    self.start_break(slot)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def refresh_console(self):
        try:
            if hasattr(self, "console") and self.console.isVisible():
                self.console.update_state(self.console_state())
        except Exception:
            pass

    def console_state(self):
        playing_state = QMediaPlayer.PlaybackState.PlayingState
        live_mix = self.mixer.available
        rot = self.rotation
        channels = {}
        names = {}
        for key, deck, label in (("deck_a", rot.deck_a, "DECK A"), ("deck_b", rot.deck_b, "DECK B")):
            playing = deck.current_track_path is not None and deck.player.playbackState() == playing_state
            loaded = deck.current_track_path is not None
            if playing:
                status, color = "PLAYING", COLOR_ON_AIR_GREEN
            elif loaded:
                status, color = "CUED", COLOR_WARNING_AMBER
            else:
                status, color = "EMPTY", COLOR_TEXT_DIM
            if live_mix:
                vu = self.mixer.recent_peak(key) if playing else 0.0
            else:
                vu = deck.audio_output.volume() * 0.6 if playing else 0.0
            channels[key] = {"label": label, "on": playing or loaded, "status": status, "color": color,
                             "vu": vu, "fader": deck.manual_volume}
            names[key] = f"{label.title()} {status.lower()}"
        mic = self.microphone
        if mic.is_live and mic.is_muted:
            mic_status, mic_color, mic_on = "MUTED", COLOR_WARNING_AMBER, True
        elif mic.is_live:
            mic_status, mic_color, mic_on = "ON AIR", COLOR_LIVE_RED, True
        else:
            mic_status, mic_color, mic_on = "OFF", COLOR_TEXT_DIM, False
        channels["mic"] = {"label": "MIC", "on": mic_on, "status": mic_status, "color": mic_color,
                           "vu": self.mixer.recent_peak("mic") if (live_mix and mic.is_live and not mic.is_muted) else 0.0,
                           "fader": None}
        seq = self.sequence_player
        seq_playing = seq.active and seq.player.playbackState() == playing_state
        if seq.active and seq.items:
            seq_status = f"{seq.slot} {min(seq.item_index + 1, len(seq.items))}/{len(seq.items)}"
        else:
            seq_status = "IDLE"
        channels["seq"] = {"label": "JINGLES / ADS", "on": seq_playing, "status": seq_status,
                           "color": COLOR_ON_AIR_GREEN if seq_playing else COLOR_TEXT_DIM,
                           "vu": (self.mixer.recent_peak("sequence") if live_mix else 0.7) if seq_playing else 0.0,
                           "fader": None}
        if self.is_muted:
            m_status, m_color, level = "MUTED", COLOR_LIVE_RED, 0.0
        elif rot.is_ducked:
            m_status, m_color, level = "DUCKED", COLOR_WARNING_AMBER, MIC_DUCKING_LEVEL
        elif rot.is_running or seq_playing:
            m_status, m_color, level = "ON AIR", COLOR_ON_AIR_GREEN, 1.0
        else:
            m_status, m_color, level = "IDLE", COLOR_TEXT_DIM, 1.0
        master_vu = max(channels[k]["vu"] for k in ("deck_a", "deck_b", "mic", "seq"))
        channels["master"] = {"label": "MASTER", "on": m_status != "IDLE", "status": m_status, "color": m_color,
                              "vu": master_vu, "fader": level}
        encoders = []
        for slot in self.encoder_bank.slots:
            state = "problem" if slot in self.encoder_problems else slot.state
            encoders.append((slot.stream_name, state))
        live_names = [n for n, s in encoders if s == "live"]
        summary = (f"{names['deck_a']}. {names['deck_b']}. Microphone {mic_status.lower()}. "
                   f"Jingles and ads {seq_status.lower()}. Master {m_status.lower()}. "
                   + (f"Encoders live: {', '.join(live_names)}." if live_names else "No encoders live."))
        return {"channels": channels, "crossfader": self.crossfader_slider.value(),
                "encoders": encoders, "summary": summary}

    def on_vinyl_tick(self):
        try:
            self._vinyl_tick()
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def _vinyl_tick(self):
        sp = self.sequence_player
        current = sp.current_deck_name()
        playing_now = bool(sp.active and sp.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState)
        for name, widgets in self.break_deck_widgets.items():
            widgets["vinyl"].set_spinning(playing_now and current == name)
            widgets["vinyl"].tick()
        for name, deck in (("A", self.rotation.deck_a), ("B", self.rotation.deck_b)):
            widgets = self.deck_widgets.get(name)
            if not widgets:
                continue
            vinyl = widgets["vinyl"]
            playing = (deck.current_track_path is not None and
                       deck.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState)
            vinyl.set_spinning(playing)
            vinyl.tick()

    # --- playlist generation ---
    def run_generation_job(self, job):
        try:
            if job[0] == "day":
                if job[1] not in self.day_generated:    # already made today (for example at 23:50)? keep it
                    self.generate_day(job[1])
            else:
                self.append_hour(job[1], job[2])
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
            self.update_status(f"Playlist generation failed: {e}")

    def generate_now(self):
        self.ensure_hour_playlists(force=True)

    def playlists_enabled(self):
        return str(self.settings.value("playlist_autoload", "true")).lower() != "false"

    def generate_day(self, day):
        """Writes every hour from 0000 through 2300 for that day, replacing earlier playlists for it."""
        files = self.playlist_generator.generate_full_day(day)
        self.day_generated.add(day)
        self.write_day_report(day, files)
        hourly = max(0, len(files) - 1)
        self.announce(f"Playlists for {day.strftime('%A %B %d')} saved, 0000 through 2300: {hourly} hourly "
                      f"files in {self.playlist_generator.output_folder()}. Earlier playlists for that day were replaced.")
        return files

    def write_day_report(self, day, files):
        """Saves the folder report for that day's playlists in the Reports folder."""
        try:
            folder = get_reports_folder()
            os.makedirs(folder, exist_ok=True)
            text = day_folder_report(self.rotation_library, self.playlist_generator.rotor, day, files, self.rotation_schedule)
            with open(os.path.join(folder, f"{day.strftime('%Y-%m-%d')}_folder_report.txt"), "w", encoding="utf-8") as handle:
                handle.write(text)
        except Exception as e:
            RUN_LOG.write("ERROR", f"Could not write the folder report: {e}")

    def queue_lead_seconds(self):
        try:
            return max(0, int(float(self.settings.value("queue_lead_seconds", 600))))
        except Exception:
            return 600

    def maybe_append_next_hour(self):
        """Near the end of the hour, the next hour's playlist is put at the bottom of the queue."""
        if not self.rotation.playlist_driven or not self.playlists_enabled():
            return
        now = datetime.now()
        if 3600 - (now.minute * 60 + now.second) > self.queue_lead_seconds():
            return
        nxt = now + timedelta(hours=1)
        key = (nxt.date(), nxt.hour)
        tag = marker_for(nxt.date(), nxt.hour)[len(HOUR_MARKER_TOKEN):]
        if key in self.append_attempted or self.rotation.queue_has_tag(tag):
            return
        self.append_attempted.add(key)
        self.append_hour(nxt.date(), nxt.hour)

    def ensure_hour_playlists(self, force=False):
        """Makes sure the queue holds this hour's playlist, and next hour's once the hour is near its end."""
        if not self.rotation_library.rotations or not self.playlists_enabled():
            return False
        now = datetime.now()
        tag = marker_for(now.date(), now.hour)[len(HOUR_MARKER_TOKEN):]
        if force or not self.rotation.queue_has_tag(tag):
            path = None if force else self.playlist_generator.current_hour_playlist()
            if path is None:
                self.generate_day(now.date())    # the whole day, replacing anything made before
                path = self.playlist_generator.current_hour_playlist()
            if not path:
                self.update_status("Could not build this hour's playlist: no rotation is scheduled for it.")
                return False
            entries, _missing = read_m3u(path)
            count, passed = self.rotation.join_hour(entries, now, locked=is_hour_locked(self.settings, now.date(), now.hour))
            self.rotation.playlist_driven = count > 0
            self.update_status(f"This hour's playlist is ready: {count} entries"
                               + (f", {passed} song(s) the clock has passed are unchecked" if passed else "")
                               + f", saved to {path}")
        self.maybe_append_next_hour()
        return True

    def append_hour(self, day, hour):
        """Builds that hour's playlist and puts it at the bottom of the queue."""
        if not self.playlists_enabled():
            return
        tag = marker_for(day, hour)[len(HOUR_MARKER_TOKEN):]
        if self.rotation.queue_has_tag(tag):
            return
        path = self.playlist_generator.current_hour_playlist(day, hour)
        if not path:
            self.generate_day(day)
            path = self.playlist_generator.current_hour_playlist(day, hour)
        if not path:
            return
        entries, _missing = read_m3u(path)
        count = self.rotation.load_queue_entries(entries, replace=False,
                                                 locked=is_hour_locked(self.settings, day, hour))
        self.rotation.playlist_driven = True
        self.announce(f"The {hour_label(hour)} playlist is ready at the bottom of the queue: {count} entries.")

    def on_hour_changed(self):
        """The hour turned over: what is left of the old hour goes, the new hour's playlist leads."""
        if not self.playlists_enabled() or not self.rotation_library.rotations:
            return
        now = datetime.now()
        tag = marker_for(now.date(), now.hour)[len(HOUR_MARKER_TOKEN):]
        if self.rotation.queue_has_tag(tag):
            dropped = self.rotation.drop_before_marker(tag)
            if dropped:
                self.update_status(f"New hour: {dropped} unplayed track(s) from the last hour were removed.")
        else:
            self.ensure_hour_playlists(force=True)
        if self.rotation.is_running:
            self.rotation.drop_stale_cue()
        self.refresh_status_tree()

    def load_current_hour_playlist(self, announce=True):
        path = self.playlist_generator.current_hour_playlist()
        if not path:
            if announce:
                self.announce("No generated playlist for this hour yet. Choose Generate Now first.")
            return
        entries, _missing = read_m3u(path)
        now = datetime.now()
        count, passed = self.rotation.join_hour(entries, now, locked=is_hour_locked(self.settings, now.date(), now.hour))
        self.announce(f"Loaded this hour's playlist: {count} entries"
                      + (f"; {passed} song(s) the clock has passed are unchecked." if passed else "."))

    def choose_playlist_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Choose the playlist output folder")
        if folder:
            self.settings.setValue("playlist_output_folder", folder)
            self.playlist_folder_label.setText(f"Playlist folder: {folder}")

    # --- stream processing ---
    def apply_processing_settings(self):
        per_source = {
            "deck_a": str(self.settings.value("proc_deck_a", "false")).lower() == "true",
            "deck_b": str(self.settings.value("proc_deck_b", "false")).lower() == "true",
            "sequence": str(self.settings.value("proc_sequence", "false")).lower() == "true",
            "mic": str(self.settings.value("proc_mic", "false")).lower() == "true",
        }
        try:
            ceiling = float(self.settings.value("proc_ceiling_db", -1.0))
        except Exception:
            ceiling = -1.0
        self.mixer.configure_processing(
            str(self.settings.value("proc_master", "true")).lower() != "false",
            str(self.settings.value("proc_preset", "Broadcast")), ceiling, per_source)

    def ensure_on_screen(self):
        """Makes sure the window can be seen: visible, and not stranded on a screen that is gone."""
        try:
            if not self.isVisible():
                self.showNormal()
            if not self.isMaximized():
                screens = QApplication.screens()
                frame = self.frameGeometry()
                if screens and not any(s.availableGeometry().intersects(frame) for s in screens):
                    area = QApplication.primaryScreen().availableGeometry()
                    self.resize(min(self.width(), area.width()), min(self.height(), area.height()))
                    self.move(area.topLeft())
            self.raise_()
            self.activateWindow()
            RUN_LOG.write("START", "Window is on screen.")
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def show_remembered(self):
        """Opens maximized the first time. After that it opens the way it was last closed."""
        maximized = True
        try:
            saved = self.settings.value("window_maximized", None)
            if saved is not None:
                maximized = str(saved).lower() in ("true", "1")
                geometry = self.settings.value("window_geometry", None)
                if not maximized and geometry:
                    self.restoreGeometry(geometry)
        except Exception:
            maximized = True
        if maximized:
            self.showMaximized()
        else:
            self.show()
        QTimer.singleShot(800, self.ensure_on_screen)

    def remember_window(self):
        try:
            self.settings.setValue("window_maximized", self.isMaximized())
            if not self.isMaximized():
                self.settings.setValue("window_geometry", self.saveGeometry())
        except Exception:
            pass

    # --- menu bar (Alt+F) ---
    def build_menus(self, layout):
        self.menu_bar = QMenuBar()
        file_menu = self.menu_bar.addMenu("&File")
        file_menu.setAccessibleName("File menu")
        voice_menu = self.menu_bar.addMenu("&Voice Track")
        voice_menu.setAccessibleName("Voice Track menu")

        def add(menu, key, text, handler, checkable=False):
            action = QAction(text, self)
            if checkable:
                action.setCheckable(True)
                action.toggled.connect(handler)
            else:
                action.triggered.connect(lambda _checked=False, h=handler: h())
            menu.addAction(action)
            self.menu_actions[key] = (action, text)
            return action

        add(file_menu, "insert_tracks", "Insert tracks into the queue", self.insert_tracks)
        add(file_menu, "automation_toggle", "Automation on or off", self.automation_toggle)
        add(file_menu, "stop_fade", "Stop with fade (the record stays on the deck)", self.stop_with_fade)
        add(file_menu, "stop_rotation", "Stop everything at once", self.stop_everything)
        add(file_menu, "mute_all", "Mute or unmute all audio", self.toggle_mute)
        add(file_menu, "toggle_recording", "Start or stop recording", self.toggle_recording)
        add(file_menu, "open_options", "Open or close Settings", self.open_options)
        file_menu.addSeparator()
        add(file_menu, "send_to_tray", "Send to the system tray (keeps playing)", self.hide_to_tray)
        file_menu.addSeparator()
        add(file_menu, "exit", "Exit Vision Studio", self.exit_program)

        add(voice_menu, "voice_track_before", "Record a voice track before the selected queue item", self.voice_track_before)
        add(voice_menu, "voice_track_after", "Record a voice track after the selected queue item", self.voice_track_after)
        layout.setMenuBar(self.menu_bar)
        self.refresh_menu_labels()

    def refresh_menu_labels(self):
        """Shows each command's current shortcut key in its menu text."""
        try:
            bindings = load_shortcut_bindings(self.settings)
        except Exception:
            bindings = {}
        for key, (action, text) in self.menu_actions.items():
            shortcut = bindings.get(key, "")
            action.setText(f"{text} ({shortcut})" if shortcut else text)

    def on_close_to_tray_toggled(self, checked):
        self.settings.setValue("close_to_tray", "true" if checked else "false")
        self.announce("Closing the window now sends it to the system tray." if checked
                      else "Closing the window now exits the program.")

    def on_autostart_toggled(self, checked):
        ok, message = set_autostart(checked)
        self.settings.setValue("autostart_requested", "true" if checked else "false")
        if hasattr(self, "autostart_check"):
            self.autostart_check.blockSignals(True)
            self.autostart_check.setChecked(autostart_enabled() if ok else not checked)
            self.autostart_check.blockSignals(False)
        action = self.menu_actions.get("autostart", (None, ""))[0]
        if action is not None:
            action.blockSignals(True)
            action.setChecked(autostart_enabled() if ok else not checked)
            action.blockSignals(False)
        self.announce(message)

    # --- system tray ---
    def make_app_icon(self):
        pixmap = QPixmap(64, 64)
        pixmap.fill(QColor(20, 24, 33))
        painter = QPainter(pixmap)
        painter.setPen(QColor(255, 255, 255))
        painter.drawText(pixmap.rect(), Qt.AlignmentFlag.AlignCenter, "VS")
        painter.end()
        return QIcon(pixmap)

    def setup_tray(self):
        try:
            icon = self.make_app_icon()
            self.setWindowIcon(icon)
            if not QSystemTrayIcon.isSystemTrayAvailable():
                return
            self.tray = QSystemTrayIcon(icon, self)
            self.tray.setToolTip("Vision Studio")
            menu = QMenu()
            for text, handler in (("Show Vision Studio", self.show_from_tray),
                                  ("Automation on or off", self.automation_toggle),
                                  ("Stop with fade", self.stop_with_fade),
                                  ("Mute or unmute all audio", self.toggle_mute),
                                  ("Exit Vision Studio", self.exit_program)):
                action = menu.addAction(text)
                action.triggered.connect(lambda _c=False, h=handler: h())
            self.tray_menu = menu
            self.tray.setContextMenu(menu)
            self.tray.activated.connect(self.on_tray_activated)
            self.tray.show()
        except Exception as e:
            self.tray = None
            RUN_LOG.write("ERROR", f"System tray could not start: {e}")

    def on_tray_activated(self, reason):
        if reason in (QSystemTrayIcon.ActivationReason.Trigger, QSystemTrayIcon.ActivationReason.DoubleClick):
            if self.isVisible() and not self.isMinimized():
                self.hide_to_tray()
            else:
                self.show_from_tray()

    def hide_to_tray(self):
        if self.tray is None:
            self.showMinimized()
            self.announce("No system tray is available, so the window was minimized instead.")
            return
        self.remember_window()
        self.hide()
        self.tray.showMessage("Vision Studio", "Still running in the system tray. Click the icon to open it.",
                              QSystemTrayIcon.MessageIcon.Information, 4000)
        RUN_LOG.write("TRAY", "Window sent to the system tray.")

    def show_from_tray(self):
        if str(self.settings.value("window_maximized", "true")).lower() in ("true", "1"):
            self.showMaximized()
        else:
            self.showNormal()
        self.raise_()
        self.activateWindow()

    def start_in_tray(self):
        """No window, just the tray icon."""
        if self.tray is None:
            self.showMinimized()
        RUN_LOG.write("START", "Running in the system tray.")

    def on_startup_launch(self):
        """Started by Windows at log-in. The window opens as normal unless "open in the system tray" is
        ticked. Playing begins by itself if that option is ticked."""
        in_tray = str(self.settings.value("start_in_tray", "false")).lower() == "true" and self.tray is not None
        RUN_LOG.write("START", "Started with Windows" + (", opening in the system tray." if in_tray else ", window shown."))
        if in_tray:
            self.start_in_tray()
        else:
            self.show_remembered()
        if str(self.settings.value("autoplay_on_boot", "false")).lower() == "true":
            QTimer.singleShot(8000, self.autoplay_after_boot)

    def remember_automation(self, on):
        """Only the person's own choice is saved, so a restart or a shutdown never changes it."""
        try:
            self.settings.setValue("automation_last_on", "true" if on else "false")
        except Exception:
            pass

    def resume_after_start(self):
        """Puts the speakers and automation back the way they were when the program closed."""
        try:
            if str(self.settings.value("speakers_muted", "false")).lower() == "true" and not self.is_muted:
                self.toggle_mute()
            wanted = (str(self.settings.value("resume_automation", "true")).lower() != "false"
                      and str(self.settings.value("automation_last_on", "false")).lower() == "true")
            if wanted and not self.rotation.is_running:
                RUN_LOG.write("START", "Automation was on when the program closed; turning it back on.")
                self.announce("Automation was on when the program closed. Turning it back on.")
                self.start_rotation()
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def stop_everything(self):
        self.remember_automation(False)
        self.rotation.stop()

    def autoplay_after_boot(self):
        if self.rotation.is_running:
            return
        if not self.rotation_library.rotations and not self.settings.value("music_library_folder", ""):
            RUN_LOG.write("START", "Not starting automatically: no music folder is set.")
            return
        RUN_LOG.write("START", "Starting the rotation automatically after Windows started.")
        self.start_rotation()

    def exit_program(self):
        """Really closes the program (asks first if audio is playing, then fades out)."""
        self._quitting = True
        if not self.isVisible():
            self.show_from_tray()
        self.close()
        if not self._shutdown_done and not self._closing:
            self._quitting = False     # the user said no to the close question

    def quit_application(self):
        try:
            if self.tray is not None:
                self.tray.hide()
        except Exception:
            pass
        QTimer.singleShot(0, QApplication.quit)

    # --- voice tracking ---
    def voice_track_before(self):
        self.record_voice_track(after=False)

    def voice_track_after(self):
        self.record_voice_track(after=True)

    def capture_voice_clip(self, where):
        """Records one voice track with the preview, re-record and underlay dialog. Returns
        (file path, seconds, underlay seconds), or None when it was discarded."""
        if self._voice_recording:
            return None
        draft_path = os.path.join(get_voice_folder(), time.strftime("voicetrack_%Y-%m-%d_%H%M%S_draft.wav"))
        recorder = VoiceRecorder(self.settings, self.update_status)
        if not recorder.start(draft_path):
            self.announce("The voice track could not start. Check the microphone in the Settings tab.")
            return None
        self._voice_recording = True
        RUN_LOG.write("VOICE", f"Recording a voice track {where}.")
        try:
            default_under = int(float(self.settings.value("voice_underlay_seconds", 6)))
        except Exception:
            default_under = 6
        dialog = VoiceTrackDialog(self, recorder, where, self.settings, default_under)
        started_recording = False
        if (str(self.settings.value("record_voice_tracking", "false")).lower() == "true"
                and not self.recorder.recording and self.recorder.setup_done()):
            started_recording = self.start_recording(for_voice=True)
            if started_recording:
                self.recorder.note_other("Voice tracking session")
        try:
            accepted = dialog.exec() == QDialog.DialogCode.Accepted
        finally:
            self._voice_recording = False
            if started_recording:
                self.stop_recording()
        seconds = dialog.recorded_seconds
        if not accepted or seconds < 0.5:
            recorder.cancel()
            self.announce("Voice track discarded." if not accepted else "Nothing was recorded, so no voice track was added.")
            return None
        underlay = dialog.underlay_spin.value()
        self.settings.setValue("voice_underlay_seconds", underlay)
        final_path = draft_path.replace("_draft.wav", f"_u{underlay}.wav")
        try:
            os.replace(draft_path, final_path)
        except OSError:
            final_path = draft_path
        RUN_LOG.write("VOICE", f"Voice track of {seconds:.0f} seconds saved: {final_path}")
        return final_path, seconds, underlay

    def record_voice_track(self, after):
        """Records a voice track and drops it into the queue before or after the selected item, like
        Station Playlist. A selected voice track slot is filled instead. The music keeps playing while
        you talk; when the voice track is done the next song fades in by itself."""
        if self._voice_recording:
            return
        if (self.pages.currentIndex() == 1 and self.tabs.currentWidget() is self.vt_hour_tab):
            self.vt_hour_tab.record_into_selected()          # on the Voice Track Hour screen the keys fill its slots
            return
        row = self.queue_list.currentRow()
        header = self.queue_list.header_count
        queue = self.rotation.shuffled_queue
        fill_slot = False
        if row >= header and row - header < len(queue):
            if is_voice_marker(queue[row - header]):
                fill_slot = True
                index = row - header
                where = "into the voice track slot"
            else:
                index = row - header + (1 if after else 0)
                where = f"{'after' if after else 'before'} {format_track_display(queue[row - header])}"
        else:
            index = 0
            where = "as the next item, right after the song on air"
        clip = self.capture_voice_clip(where)
        if clip is None:
            self.queue_list.setFocus()
            return
        final_path, seconds, underlay = clip
        if fill_slot:
            self.rotation.remove_queue_item(index)
        self.rotation.insert_queue_item(final_path, index)
        self.announce(f"Voice track of {int(round(seconds))} seconds added {where}. "
                      + (f"The next song's intro plays under its last {underlay} seconds."
                         if underlay else "The next song starts as it ends."))
        self.queue_list.setFocus()

    def reload_hour_if_current(self, day, hour):
        """After saving a voice tracked hour that is on air right now or next, make sure the queue uses it."""
        now = datetime.now()
        if (day, hour) == (now.date(), now.hour):
            self.announce("That hour is on air now. The saved version plays from the next hour change; "
                          "use Load This Hour's Playlist in the queue area to bring it in now.")

    # --- categories ---
    def import_category_folder(self, folder, kind):
        """Music folders also make a rotation and a draft dated schedule. Nothing is switched on."""
        library = self.category_library
        if kind != "music":
            added = library.import_folder(folder, kind)
            for category in added:
                self.normalizer.start(scan_audio_files(category["folder"]))
            return added
        added = []
        for path in library.audio_folders(folder):
            name = pretty_folder_name(os.path.basename(os.path.normpath(path)))
            rotation = self.rotation_library.add_rotation(name, path, True, auto=False, notify=False, regular=False)
            category = library.add_category(path, rotation.name, "music", active=False, rotation_id=rotation.id)
            added.append(category)
            self.event_library.add_draft(rotation.name, rotation.id)
            self.normalizer.start(rotation.track_paths())
        if added:
            library._changed()
            self.rotation_library._changed("linked")       # no rebuild of the schedule you made
        return added

    def change_category_folder(self, category, folder):
        category["folder"] = folder
        if category.get("type") == "music" and category.get("rotation_id"):
            self.rotation_library.relink_folder(category["rotation_id"], folder)
            rotation = self.rotation_library.find(category["rotation_id"])
            if rotation:
                self.normalizer.start(rotation.track_paths())
        else:
            self.normalizer.start(scan_audio_files(folder))
        self.category_library._changed()
        self.announce(f"{category['name']} now uses {folder}.")

    def set_category_active(self, category, active):
        self.category_library.set_active(category["id"], active)
        rotation = self.rotation_library.find(category.get("rotation_id")) if category.get("rotation_id") else None
        if rotation is not None:
            rotation.regular = bool(active)
            self.rotation_library.save()
        self.announce(f"{category['name']} is now " + ("in the regular schedule." if active else "off the regular schedule."))

    # --- dated schedules ---
    def refresh_schedule_views(self):
        if hasattr(self, "schedule_tab"):
            self.schedule_tab.refresh()

    def on_events_changed(self, event):
        """A dated schedule was saved or removed: playlists for today are rebuilt so they follow it."""
        self.refresh_schedule_views()
        try:
            if event is None or self.event_library.event_for_hour(datetime.now().date(), datetime.now().hour) is not None \
                    or any(self.event_library.event_for_hour(datetime.now().date(), h) for h in range(24)):
                self.generate_day(datetime.now().date())
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
        self.rotation.check_rotation_for_hour()

    def audio_is_playing(self):
        playing = QMediaPlayer.PlaybackState.PlayingState
        try:
            if any(deck.player.playbackState() == playing for deck in (self.rotation.deck_a, self.rotation.deck_b)):
                return True
            if self.sequence_player.player.playbackState() == playing:
                return True
            if self.microphone.is_live:
                return True
        except Exception:
            pass
        return False

    def live_encoder_count(self):
        try:
            return len([s for s in self.encoder_bank.slots if s.state == "live"])
        except Exception:
            return 0

    def closeEvent(self, event):
        """Closing while audio is playing asks first, then fades out so nothing is cut off mid-sound."""
        if self._shutdown_done:
            self.quit_application()
            event.accept()
            return
        if self._closing:
            event.ignore()
            return
        if (not self._quitting and self.tray is not None and self.tray.isVisible()
                and str(self.settings.value("close_to_tray", "false")).lower() == "true"):
            event.ignore()
            self.hide_to_tray()
            return
        encoders = self.live_encoder_count()
        if self.audio_is_playing() or encoders or self.recorder.recording:
            text = "Audio is playing. Are you sure you want to close Vision Studio?"
            if encoders:
                text += f" {encoders} encoder(s) are live and will go off the air."
            if self.recorder.recording:
                text += " The recording will be finished and saved first."
            text += " The sound will fade out first, so nothing is cut off."
            box = QMessageBox(self)
            box.setWindowTitle("Close Vision Studio?")
            box.setText(text)
            box.setStandardButtons(QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
            box.setDefaultButton(QMessageBox.StandardButton.No)
            if box.exec() != QMessageBox.StandardButton.Yes:
                event.ignore()
                return
            event.ignore()
            self.begin_graceful_close()
            return
        self.finish_shutdown()
        self.quit_application()
        event.accept()

    def begin_graceful_close(self):
        self._closing = True
        RUN_LOG.write("CLOSE", "Closing while audio was playing; fading out first.")
        self.announce("Closing. Fading the sound out.")
        rot = self.rotation
        rot.is_running = False          # no new tracks, no crossfades, no breaks while closing
        rot.disarm_break()
        self.sequence_player.queue = []
        self.microphone.set_muted(True)
        for deck in (rot.deck_a, rot.deck_b):
            deck.fader.fade_to(0.0, steps=15, interval_ms=100)
        self._sequence_fade_step = 0
        start_volume = self.sequence_player.audio_output.volume()

        def fade_sequence():
            self._sequence_fade_step += 1
            level = max(0.0, start_volume * (1.0 - self._sequence_fade_step / 15.0))
            self.sequence_player.audio_output.setVolume(level)
            if self._sequence_fade_step >= 15:
                self._sequence_fade_timer.stop()
        self._sequence_fade_timer = QTimer(self)
        self._sequence_fade_timer.setInterval(100)
        self._sequence_fade_timer.timeout.connect(fade_sequence)
        self._sequence_fade_timer.start()
        QTimer.singleShot(1800, self.complete_close)

    def complete_close(self):
        self.finish_shutdown()
        self.close()

    def finish_shutdown(self):
        """Stops everything in order so no file is left half-written."""
        if self._shutdown_done:
            return
        self._shutdown_done = True
        self.remember_window()
        for step in (lambda: self.tagger.stop(),
                     lambda: self.recorder.stop(wait=True),
                     lambda: self.rotation.stop(),
                     lambda: self.sequence_player.player.stop(),
                     lambda: self.microphone.stop(),
                     lambda: self.encoder_bank.shutdown(),
                     lambda: self.normalizer.shutdown(),
                     lambda: self.settings.sync()):
            try:
                step()
            except Exception:
                pass
        RUN_LOG.write("CLOSE", "Vision Studio closed.")

    # --- deck column ---
    def build_deck_column(self, deck_name):
        column = QVBoxLayout()

        title = QLabel(f"Deck {deck_name}")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        title.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-weight: bold; font-size: 14px;")
        column.addWidget(title)

        vinyl = VinylWidget(deck_name)
        column.addWidget(vinyl, alignment=Qt.AlignmentFlag.AlignCenter)

        live_indicator = QLabel("")
        live_indicator.setAlignment(Qt.AlignmentFlag.AlignCenter)
        live_indicator.setAccessibleName(f"Deck {deck_name} on-air indicator")
        live_indicator.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
        column.addWidget(live_indicator)

        artwork_label = QLabel()
        artwork_label.setFixedSize(ARTWORK_PLACEHOLDER_SIZE, ARTWORK_PLACEHOLDER_SIZE)
        artwork_label.setAccessibleName(f"Deck {deck_name}: track artwork")
        artwork_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        artwork_label.setStyleSheet(
            f"background-color: {COLOR_PANEL_DARK}; border-radius: 6px; border: 1px solid {COLOR_BORDER};"
        )
        column.addWidget(artwork_label, alignment=Qt.AlignmentFlag.AlignCenter)

        track_label = QLabel("(no track loaded)")
        track_label.setAccessibleName(f"Deck {deck_name}: track name")
        track_label.setWordWrap(True)
        track_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        column.addWidget(track_label)

        transport_row = QHBoxLayout()
        play_pause_btn = QPushButton("Play/Pause")
        play_pause_btn.setAccessibleName(f"Deck {deck_name}: play or pause")
        play_pause_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        play_pause_btn.clicked.connect(lambda: self.rotation.play_pause_deck(deck_name))
        transport_row.addWidget(play_pause_btn)

        cue_btn = QPushButton("Cue")
        cue_btn.setAccessibleName(f"Deck {deck_name}: cue to start")
        cue_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        cue_btn.clicked.connect(lambda: self.rotation.cue_deck_to_start(deck_name))
        transport_row.addWidget(cue_btn)
        column.addLayout(transport_row)

        insert_btn = QPushButton("Insert (Ins)")
        insert_btn.setAccessibleName(f"Deck {deck_name}: insert tracks into the queue")
        insert_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        insert_btn.clicked.connect(self.insert_tracks)
        column.addWidget(insert_btn)

        volume_label = QLabel(f"Deck {deck_name} Volume")
        volume_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        column.addWidget(volume_label)

        volume_slider = QSlider(Qt.Orientation.Vertical)
        volume_slider.setRange(0, 100)
        volume_slider.setValue(100)
        volume_slider.setAccessibleName(f"Deck {deck_name} volume fader")
        volume_slider.setFixedHeight(100)
        volume_slider.setStyleSheet(SLIDER_STYLE_DECK_FADER)
        volume_slider.valueChanged.connect(
            lambda value, d=deck_name: self.rotation.set_deck_volume(d, value / 100.0)
        )
        column.addWidget(volume_slider, alignment=Qt.AlignmentFlag.AlignCenter)

        self.deck_widgets[deck_name] = {
            "vinyl": vinyl,
            "live_indicator": live_indicator,
            "artwork_label": artwork_label,
            "track_label": track_label,
            "volume_slider": volume_slider,
        }
        return column

    def build_break_deck_column(self, deck_name):
        """Decks C and D: the jingle, the ad break and the closing jingle alternate between them."""
        column = QVBoxLayout()
        title = QLabel(f"Deck {deck_name} (jingles and ads)")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        title.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-weight: bold;")
        column.addWidget(title)
        vinyl = VinylWidget(deck_name)
        column.addWidget(vinyl, alignment=Qt.AlignmentFlag.AlignCenter)
        live_indicator = QLabel("")
        live_indicator.setAlignment(Qt.AlignmentFlag.AlignCenter)
        live_indicator.setAccessibleName(f"Deck {deck_name} on-air indicator")
        live_indicator.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
        column.addWidget(live_indicator)
        item_label = QLabel("(idle)")
        item_label.setAccessibleName(f"Deck {deck_name}: break item")
        item_label.setWordWrap(True)
        item_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        item_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        column.addWidget(item_label)
        row = QHBoxLayout()
        play_btn = QPushButton("Play/Pause")
        play_btn.setAccessibleName(f"Deck {deck_name}: play or pause the break")
        play_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        play_btn.clicked.connect(lambda: self.sequence_player.toggle_pause())
        row.addWidget(play_btn)
        stop_btn = QPushButton("Stop")
        stop_btn.setAccessibleName(f"Deck {deck_name}: stop the break and bring the music back")
        stop_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        stop_btn.clicked.connect(lambda: self.sequence_player.stop_break())
        row.addWidget(stop_btn)
        column.addLayout(row)
        self.break_deck_widgets[deck_name] = {"vinyl": vinyl, "live_indicator": live_indicator, "item_label": item_label}
        return column

    def refresh_break_decks(self):
        sp = self.sequence_player
        for index, name in enumerate(sp.deck_names):
            widgets = self.break_deck_widgets.get(name)
            if not widgets:
                continue
            mine = list(range(index, len(sp.items), 2)) if sp.active else []
            if sp.active and sp.item_index in mine:
                widgets["live_indicator"].setText("● ON AIR")
                widgets["item_label"].setText(os.path.basename(sp.items[sp.item_index]))
            else:
                widgets["live_indicator"].setText("")
                waiting = [i for i in mine if i > sp.item_index]
                widgets["item_label"].setText(f"Next: {os.path.basename(sp.items[waiting[0]])}" if waiting else "(idle)")

    def refresh_played_list(self):
        if not hasattr(self, "played_list"):
            return
        separation = self.rotation.separation_seconds
        rows = self.rotation.play_history.recent(separation)
        self.played_list.clear()

        def clock(stamp):
            return time.strftime("%I:%M %p", time.localtime(stamp)).lstrip("0")
        for path, played, available in rows[:80]:
            self.played_list.addItem(f"{format_track_display(path)}: played {clock(played)}, available again at {clock(available)}")
        self.played_label.setText(f"Played: {len(rows)} song(s) held back for {separation / 3600:g} hours")

    def build_folder_tab(self):
        page = QWidget()
        layout = QVBoxLayout()
        self.rotate_folders_check = QCheckBox("Rotate through every folder: each folder takes a turn before any folder repeats")
        self.rotate_folders_check.setChecked(str(self.settings.value("rotate_folders", "true")).lower() != "false")
        self.rotate_folders_check.toggled.connect(
            lambda on: self.settings.setValue("rotate_folders", "true" if on else "false"))
        layout.addWidget(self.rotate_folders_check)
        self.report_rotation_combo = QComboBox()
        self.report_rotation_combo.setAccessibleName("Rotation to report on")
        layout.addWidget(self.report_rotation_combo)
        build_btn = QPushButton("Build Folder Report")
        build_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        build_btn.clicked.connect(self.build_folder_report)
        layout.addWidget(build_btn)
        self.report_text = QPlainTextEdit()
        self.report_text.setReadOnly(True)
        self.report_text.setAccessibleName("Folder report")
        layout.addWidget(self.report_text)
        page.setLayout(layout)
        self.refresh_report_rotations()
        return page

    def refresh_report_rotations(self):
        current = self.report_rotation_combo.currentData()
        self.report_rotation_combo.clear()
        for rotation in self.rotation_library.rotations:
            self.report_rotation_combo.addItem(rotation.name, rotation.id)
        index = self.report_rotation_combo.findData(current)
        self.report_rotation_combo.setCurrentIndex(max(0, index))

    def build_folder_report(self):
        self.refresh_report_rotations()
        rotation = self.rotation_library.find(self.report_rotation_combo.currentData())
        if rotation is None:
            self.report_text.setPlainText("There is no rotation to report on yet.")
            return
        self.report_text.setPlainText(folder_report(rotation, self.playlist_generator.rotor))
        self.report_text.setFocus()
        self.announce("Folder report ready.")

    def build_version_tab(self):
        page = QWidget()
        layout = QVBoxLayout()
        for text in (f"Vision Studio version {APP_VERSION}", f"Build {BUILD_NUMBER}", f"Built on {BUILD_DATE}"):
            label = QLabel(text)
            label.setAccessibleName(text)
            label.setFocusPolicy(Qt.FocusPolicy.StrongFocus)      # so a screen reader can land on each line
            label.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-size: 16px;")
            layout.addWidget(label)
        layout.addStretch(1)
        page.setLayout(layout)
        return page

    def focus_settings_content(self):
        """Moves focus from the list of sections to the first control of the section chosen."""
        page = self.tabs.currentWidget()
        if page is None:
            return False
        for child in page.findChildren(QWidget):
            if (child.focusPolicy() != Qt.FocusPolicy.NoFocus and child.isVisibleTo(page) and child.isEnabled()
                    and not (isinstance(child, QLineEdit) and isinstance(child.parent(), (QAbstractSpinBox, QComboBox)))
                    and child.objectName() != "qt_scrollarea_viewport"):
                child.setFocus(Qt.FocusReason.TabFocusReason)
                return True
        return False

    report_ready = pyqtSignal(str)

    def build_rules_tab(self):
        page = QWidget()
        layout = QVBoxLayout()
        intro = QLabel("These rules keep the programming inside the US webcasting limits that Live365 publishes, and they are "
                       "never relaxed: a song that would break a rule is skipped, and another song that passes is borrowed "
                       "from the rest of the library. The hours a song and its artist are held back are set in General. "
                       "Change the numbers here if your station is licensed another way.")
        intro.setWordWrap(True)
        layout.addWidget(intro)
        form = QFormLayout()
        self.rules_preset_combo = QComboBox()
        self.rules_preset_combo.addItem("Live365 (US webcasting limits)", "live365")
        self.rules_preset_combo.addItem("Custom (use the numbers below)", "custom")
        self.rules_preset_combo.addItem("Off (no checks at all)", "off")
        self.rules_preset_combo.setAccessibleName("Programming rules preset")
        form.addRow("Preset:", self.rules_preset_combo)
        self.rules_spins = {}
        labels = (("window_hours", "Window, in hours:", 1, 12),
                  ("artist_max", "Most different songs by one artist in the window:", 1, 20),
                  ("artist_run", "Most songs by one artist in a row:", 1, 10),
                  ("album_max", "Most different songs from one album in the window:", 1, 20),
                  ("album_run", "Most songs from one album in a row:", 1, 10),
                  ("song_minutes", "Hold a played song back for (minutes, 0 = no hold):", 0, 600),
                  ("artist_minutes", "Hold a played artist back for (minutes, 0 = only the limits above):", 0, 600))
        saved = ProgramRules(self.settings)
        for key, text, low, high in labels:
            spin = QSpinBox()
            spin.setRange(low, high)
            spin.setValue(saved.values[key])
            spin.setAccessibleName(text.rstrip(":"))
            spin.valueChanged.connect(self.on_rules_value_edited)
            self.rules_spins[key] = spin
            form.addRow(text, spin)
        index = self.rules_preset_combo.findData(saved.preset)
        self.rules_preset_combo.setCurrentIndex(max(0, index))
        self.rules_preset_combo.currentIndexChanged.connect(self.on_rules_preset_changed)
        layout.addLayout(form)
        mode_form = QFormLayout()
        self.hour_mode_combo = QComboBox()
        self.hour_mode_combo.addItem("Mix all the folders in every hour (recommended)", "mix")
        self.hour_mode_combo.addItem("One volume per hour, every volume takes a turn", "volume")
        self.hour_mode_combo.addItem("Use the schedule exactly as set", "fixed")
        self.hour_mode_combo.setAccessibleName("How the hours use the folders")
        self.hour_mode_combo.setCurrentIndex(max(0, self.hour_mode_combo.findData(self.rotation_schedule.hour_mode())))
        mode_form.addRow("How the hours use the folders:", self.hour_mode_combo)
        layout.addLayout(mode_form)
        save_btn = QPushButton("Save Rules")
        save_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        save_btn.clicked.connect(self.save_rules)
        layout.addWidget(save_btn)
        report_btn = QPushButton("Check the Library Tags and Albums")
        report_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        report_btn.clicked.connect(self.start_library_report)
        layout.addWidget(report_btn)
        layout.addStretch(1)
        page.setLayout(layout)
        return page

    def on_rules_preset_changed(self, *_args):
        if self.rules_preset_combo.currentData() == "live365":
            for key, spin in self.rules_spins.items():
                spin.blockSignals(True)
                spin.setValue(RULE_PRESETS["live365"][key])
                spin.blockSignals(False)

    def on_rules_value_edited(self, *_args):
        if self.rules_preset_combo.currentData() == "live365":
            self.rules_preset_combo.blockSignals(True)
            self.rules_preset_combo.setCurrentIndex(self.rules_preset_combo.findData("custom"))
            self.rules_preset_combo.blockSignals(False)

    def save_rules(self):
        preset = self.rules_preset_combo.currentData()
        self.settings.setValue("rules_preset", preset)
        for key, spin in self.rules_spins.items():
            self.settings.setValue("rules_" + key, spin.value())
        self.settings.setValue("hour_mode", self.hour_mode_combo.currentData())
        if self.hour_mode_combo.currentData() == "mix":
            self.rotation_library.ensure_mix(str(self.settings.value("music_library_folder", "")))
        self.rotation.apply_separation_setting()
        self.rotation.check_rotation_for_hour()
        try:
            self.schedule_tab.refresh()
        except Exception:
            pass
        RUN_LOG.write("RULES", f"Programming rules saved: {preset}.")
        self.announce("Programming rules saved." if preset != "off" else "Programming rules saved. They are off.")

    def start_library_report(self):
        self.announce("Checking the library tags. This takes a moment.")
        threading.Thread(target=self._library_report_worker, daemon=True).start()

    def _library_report_worker(self):
        path = ""
        try:
            rotations = [(r.name, r.track_paths()) for r in self.rotation_library.rotations]
            if not rotations:
                rotations = [("Music library", scan_audio_files(self.settings.value("music_library_folder", "")))]
            lines, totals = build_library_report(rotations, self.rotation.rules)
            folder = get_reports_folder()
            os.makedirs(folder, exist_ok=True)
            path = os.path.join(folder, time.strftime("library-report-%Y-%m-%d.txt"))
            with open(path, "w", encoding="utf-8") as handle:
                handle.write("\n".join(lines) + "\n")
            self._library_report_summary = lines[-1]
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
            self._library_report_summary = "The library report could not be written."
        self.report_ready.emit(path)

    def on_library_report_ready(self, path):
        text = getattr(self, "_library_report_summary", "")
        self.announce(f"{text} Saved to {path}" if path else text)

    def build_crossfade_tab(self):
        page = QWidget()
        layout = QVBoxLayout()
        intro = QLabel("By default every song, jingle, ad and sweeper plays to its end and the next one starts right "
                       "after it, with no overlap. The music is only faded out when a break cannot be reached any other way. "
                       "Before each break the program removes queued songs that do not fit, even ones that have not played, "
                       "and puts in songs that bring the break in on time.")
        intro.setWordWrap(True)
        layout.addWidget(intro)
        self.crossfade_check = QCheckBox("Crossfade songs: start the next song about 10 seconds before the current one ends")
        self.crossfade_check.setChecked(str(self.settings.value("crossfade_enabled", "false")).lower() == "true")
        layout.addWidget(self.crossfade_check)
        self.fit_hour_check = QCheckBox("Swap queued songs so the last song ends exactly on the top of the hour")
        self.fit_hour_check.setChecked(str(self.settings.value("fit_end_of_hour", "true")).lower() != "false")
        layout.addWidget(self.fit_hour_check)
        self.fit_quarter_check = QCheckBox("Do the same before the :15, :30 and :45 breaks")
        self.fit_quarter_check.setChecked(str(self.settings.value("fit_quarter_marks", "true")).lower() != "false")
        layout.addWidget(self.fit_quarter_check)
        fit_form = QFormLayout()
        self.fit_early_spin = QSpinBox()
        self.fit_early_spin.setRange(0, 15)
        self.fit_early_spin.setValue(int(float(self.settings.value("fit_early_seconds", FIT_GOOD_ENOUGH_EARLY))))
        self.fit_early_spin.setAccessibleName("Start a break up to this many seconds early instead of fading")
        fit_form.addRow("Start a break up to this many seconds early (instead of fading the song):", self.fit_early_spin)
        self.fit_min_song_spin = QSpinBox()
        self.fit_min_song_spin.setRange(0, 600)
        self.fit_min_song_spin.setValue(int(float(self.settings.value("fit_min_song_seconds", FIT_MIN_SONG_SECONDS))))
        self.fit_min_song_spin.setAccessibleName("Shortest song used when fitting a break, in seconds")
        fit_form.addRow("Shortest song used when fitting a break (seconds):", self.fit_min_song_spin)
        layout.addLayout(fit_form)
        save_btn = QPushButton("Save Settings")
        save_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        save_btn.clicked.connect(self.save_audio_settings)
        layout.addWidget(save_btn)
        layout.addStretch(1)
        page.setLayout(layout)
        return page

    # --- logo ---
    def apply_logo(self):
        pixmap, custom = load_banner_pixmap(self.settings)
        self.logo_label.setPixmap(pixmap)
        self.logo_label.setAccessibleName("Station logo" if custom else "Vision Studio logo")
        icon = load_window_icon(self.settings)
        self.setWindowIcon(icon)
        if self.tray is not None:
            try:
                self.tray.setIcon(icon)
            except Exception:
                pass
        if hasattr(self, "logo_status_label"):
            self.logo_status_label.setText("Using your station logo." if custom else "Using the default Vision Studio logo.")

    def build_logo_tab(self):
        page = QWidget()
        layout = QVBoxLayout()
        intro = QLabel("The logo across the top of the program and in the window and tray icons. You can use your "
                       "own station logo, and switch back to the Vision Studio logo whenever you like. The desktop "
                       "shortcut icon is set when the program is installed and does not change.")
        intro.setWordWrap(True)
        layout.addWidget(intro)
        self.logo_status_label = QLabel("")
        self.logo_status_label.setAccessibleName("Which logo is in use")
        layout.addWidget(self.logo_status_label)
        for text, handler in (("Choose My Station Logo...", self.choose_station_logo),
                              ("Use My Station Logo", self.use_station_logo),
                              ("Revert To The Default Vision Studio Logo", self.use_default_logo)):
            btn = QPushButton(text)
            btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
            btn.clicked.connect(handler)
            layout.addWidget(btn)
        layout.addStretch(1)
        page.setLayout(layout)
        return page

    def choose_station_logo(self):
        path, _filter = QFileDialog.getOpenFileName(self, "Choose your station logo", "",
                                                    "Images (*.png *.jpg *.jpeg *.bmp *.gif)")
        if not path:
            return
        if QPixmap(path).isNull():
            self.announce("That file could not be read as a picture.")
            return
        extension = os.path.splitext(path)[1].lower() or ".png"
        target = os.path.join(get_logo_folder(), "station_logo" + extension)
        try:
            shutil.copyfile(path, target)
        except OSError as e:
            self.announce(f"The logo could not be saved: {e}")
            return
        self.settings.setValue("logo_custom_path", target)
        self.settings.setValue("logo_mode", "custom")
        self.apply_logo()
        self.announce("Your station logo is now in use. Use Revert To The Default Vision Studio Logo to go back.")

    def use_station_logo(self):
        custom = str(self.settings.value("logo_custom_path", "") or "")
        if not (custom and os.path.isfile(custom)):
            self.announce("No station logo has been chosen yet. Choose one first.")
            return
        self.settings.setValue("logo_mode", "custom")
        self.apply_logo()
        self.announce("Your station logo is now in use.")

    def use_default_logo(self):
        self.settings.setValue("logo_mode", "default")
        self.apply_logo()
        self.announce("The default Vision Studio logo is back.")

    def on_deck_update(self, deck_name, track_path):
        widgets = self.deck_widgets.get(deck_name)
        if not widgets:
            return
        if track_path:
            widgets["track_label"].setText(os.path.basename(track_path))
            self.update_artwork_display(widgets["artwork_label"], track_path, f"Deck {deck_name} track artwork")
        else:
            widgets["track_label"].setText("(no track loaded)")
            widgets["artwork_label"].clear()
            widgets["artwork_label"].setText("No\nArtwork")
        self.refresh_live_indicators()

    def refresh_live_indicators(self):
        for name, widgets in self.deck_widgets.items():
            if name == self.rotation.live_deck_name and widgets["track_label"].text() != "(no track loaded)":
                widgets["live_indicator"].setText("● ON AIR")
            else:
                widgets["live_indicator"].setText("")

    def update_artwork_display(self, label, track_path, accessible_fallback_name):
        pixmap = build_artwork_pixmap(track_path) if track_path else None
        if pixmap:
            label.setPixmap(pixmap)
            label.setAccessibleName(f"{accessible_fallback_name}: cover art available")
        else:
            label.setPixmap(QPixmap())
            label.setText("No\nArtwork")
            label.setAccessibleName(f"{accessible_fallback_name}: no cover art available")

    # --- UI ---
    def setup_ui(self):
        layout = QVBoxLayout()
        try:
            self.build_menus(layout)
        except Exception as e:
            self.menu_actions = {}
            _log_exception(type(e), e, e.__traceback__)

        self.alert_label = QLabel("Alerts: none")
        self.alert_label.setAccessibleName("Alerts")
        self.alert_label.setWordWrap(True)
        self.alert_label.setStyleSheet(f"color: {COLOR_WARNING_AMBER}; font-weight: bold;")
        layout.addWidget(self.alert_label)

        top_row = QHBoxLayout()
        self.logo_label = QLabel()
        self.logo_label.setAccessibleName("Vision Studio logo")
        top_row.addWidget(self.logo_label)
        self.settings_btn = QPushButton("Settings (Ctrl+O)")
        self.settings_btn.setAccessibleName("Settings. Keyboard shortcut Control O.")
        self.settings_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.settings_btn.clicked.connect(self.open_options)
        top_row.addWidget(self.settings_btn)
        self.record_btn = QPushButton("Start Recording (R)")
        self.record_btn.setAccessibleName("Start or stop recording. Keyboard shortcut R.")
        self.record_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.record_btn.clicked.connect(self.toggle_recording)
        top_row.addWidget(self.record_btn)
        top_row.addStretch(1)
        layout.addLayout(top_row)

        self.tabs = QTabWidget()
        self.tabs.tabBar().hide()
        self.tabs.tabBar().setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.tabs.setFocusPolicy(Qt.FocusPolicy.NoFocus)

        # --- Tab 1: Music Rotation ---
        self.tab_rotation = QWidget()
        layout_r = QVBoxLayout()

        break_row = QHBoxLayout()
        break_row.addStretch(1)
        break_row.addLayout(self.build_break_deck_column("C"))
        break_row.addSpacing(40)
        break_row.addLayout(self.build_break_deck_column("D"))
        break_row.addStretch(1)
        layout_r.addLayout(break_row)

        player_display = QHBoxLayout()
        player_display.addLayout(self.build_deck_column("A"))

        mixer_column = QVBoxLayout()
        mixer_title = QLabel("Mixer Console")
        mixer_title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        mixer_title.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-weight: bold;")
        mixer_column.addWidget(mixer_title)

        self.crossfader_slider = QSlider(Qt.Orientation.Horizontal)
        self.crossfader_slider.setRange(0, 100)
        self.crossfader_slider.setValue(0)
        self.crossfader_slider.setEnabled(False)
        self.crossfader_slider.setAccessibleName(
            "Crossfader: left is Deck A, right is Deck B. Moves automatically during transitions."
        )
        self.crossfader_slider.setStyleSheet(SLIDER_STYLE_CROSSFADER)
        mixer_column.addWidget(self.crossfader_slider)

        crossfader_labels = QHBoxLayout()
        crossfader_labels.addWidget(QLabel("Deck A"))
        crossfader_labels.addStretch()
        crossfader_labels.addWidget(QLabel("Deck B"))
        mixer_column.addLayout(crossfader_labels)

        try:
            console = MixerConsole()
            mixer_column.addWidget(console, 1)
            self.console = console
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

        self.now_playing_label = QLabel("Now Playing: (nothing yet)")
        self.now_playing_label.setAccessibleName("Now playing")
        self.now_playing_label.setWordWrap(True)
        self.now_playing_label.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT};")
        mixer_column.addWidget(self.now_playing_label)

        self.up_next_label = QLabel("Up Next: (nothing queued)")
        self.up_next_label.setAccessibleName("Up next")
        self.up_next_label.setWordWrap(True)
        self.up_next_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        mixer_column.addWidget(self.up_next_label)

        self.onair_status_label = QLabel("On Air: music rotation idle.")
        self.onair_status_label.setAccessibleName("On air status")
        self.onair_status_label.setWordWrap(True)
        self.onair_status_label.setStyleSheet(f"color: {COLOR_ON_AIR_GREEN}; font-weight: bold;")
        mixer_column.addWidget(self.onair_status_label)

        self.record_label = QLabel("Recording: off.")
        self.record_label.setAccessibleName("Recording status")
        self.record_label.setWordWrap(True)
        self.record_label.setStyleSheet(f"color: {COLOR_TEXT_DIM}; font-weight: bold;")
        mixer_column.addWidget(self.record_label)

        self.console_mic_label = QLabel("Mic: off air.")
        self.console_mic_label.setAccessibleName("Console microphone status")
        self.console_mic_label.setWordWrap(True)
        self.console_mic_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        mixer_column.addWidget(self.console_mic_label)

        self.console_mute_label = QLabel("Mute: off.")
        self.console_mute_label.setAccessibleName("Console mute status")
        self.console_mute_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        mixer_column.addWidget(self.console_mute_label)

        self.console_encoders_label = QLabel("Encoders: none streaming.")
        self.console_encoders_label.setAccessibleName("Encoder connection status")
        self.console_encoders_label.setWordWrap(True)
        self.console_encoders_label.setStyleSheet(f"color: {COLOR_TEXT_DIM}; font-weight: bold;")
        mixer_column.addWidget(self.console_encoders_label)

        feed_text = ("Stream feed: live mix of music, jingles and microphone."
                     if self.mixer.available else "Stream feed: current track file only.")
        self.console_feed_label = QLabel(feed_text)
        self.console_feed_label.setAccessibleName("Stream feed source")
        self.console_feed_label.setWordWrap(True)
        self.console_feed_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        mixer_column.addWidget(self.console_feed_label)

        if self.ffmpeg_ok:
            loudness_text, loudness_color = "Loudness: ready.", COLOR_TEXT_DIM
        else:
            loudness_text, loudness_color = ("Loudness matching is OFF: ffmpeg was not found, so volumes "
                                             "will not be matched.", COLOR_WARNING_AMBER)
        self.loudness_label = QLabel(loudness_text)
        self.loudness_label.setAccessibleName("Loudness matching status")
        self.loudness_label.setWordWrap(True)
        self.loudness_label.setStyleSheet(f"color: {loudness_color};")
        mixer_column.addWidget(self.loudness_label)

        player_display.addLayout(mixer_column, 1)
        player_display.addLayout(self.build_deck_column("B"))
        layout_r.addLayout(player_display)

        automation_hint = QLabel("Press A to turn automation on or off. Press S to fade out and stop. "
                                 "The buttons for these are in Settings (Ctrl+O). Press R to start or stop recording.")
        automation_hint.setWordWrap(True)
        automation_hint.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        layout_r.addWidget(automation_hint)

        tree_label = QLabel("Station status (keyboard tree)")
        tree_label.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-weight: bold;")
        layout_r.addWidget(tree_label)
        layout_r.addWidget(self.build_status_tree())

        self.queue_label = QLabel("Queue")
        self.queue_label.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-weight: bold;")
        layout_r.addWidget(self.queue_label)
        self.queue_list = QueueList()
        self.queue_list.setMinimumHeight(140)
        self.queue_list.move_requested.connect(self.on_queue_move)
        self.queue_list.remove_requested.connect(self.on_queue_remove)
        self.queue_list.insert_requested.connect(self.insert_tracks)
        self.queue_list.play_requested.connect(self.on_queue_play)
        self.queue_list.check_changed.connect(self.on_queue_check_changed)
        layout_r.addWidget(self.queue_list)
        queue_buttons = QHBoxLayout()
        marker_btn = QPushButton("Insert Hour Marker")
        marker_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        marker_btn.clicked.connect(self.insert_hour_marker)
        queue_buttons.addWidget(marker_btn)
        load_hour_btn = QPushButton("Load This Hour's Playlist")
        load_hour_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        load_hour_btn.clicked.connect(self.load_current_hour_playlist)
        queue_buttons.addWidget(load_hour_btn)
        layout_r.addLayout(queue_buttons)

        self.played_label = QLabel("Played: nothing yet")
        self.played_label.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-weight: bold;")
        layout_r.addWidget(self.played_label)
        self.played_list = QListWidget()
        self.played_list.setAccessibleName("Played songs, held back from airing again")
        self.played_list.setMaximumHeight(130)
        layout_r.addWidget(self.played_list)

        mic_row = QHBoxLayout()
        start_mic_btn = QPushButton("Start Microphone")
        start_mic_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        start_mic_btn.clicked.connect(self.start_microphone)
        mic_row.addWidget(start_mic_btn)

        stop_mic_btn = QPushButton("Stop Microphone")
        stop_mic_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        stop_mic_btn.clicked.connect(self.stop_microphone)
        mic_row.addWidget(stop_mic_btn)
        layout_r.addLayout(mic_row)

        self.monitor_check = QCheckBox("Hear the microphone on my speakers while it is live")
        self.monitor_check.setChecked(True)
        self.monitor_check.toggled.connect(self.on_monitor_toggled)
        layout_r.addWidget(self.monitor_check)

        self.mic_status_label = QLabel("Microphone: off air.")
        self.mic_status_label.setAccessibleName("Microphone status")
        self.mic_status_label.setWordWrap(True)
        self.mic_status_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        layout_r.addWidget(self.mic_status_label)

        self.mute_btn = QPushButton("Mute Speakers (Ctrl+Shift+U)")
        self.mute_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.mute_btn.clicked.connect(self.toggle_mute)
        layout_r.addWidget(self.mute_btn)

        self.status_label = QLabel("Status: idle.")
        self.status_label.setAccessibleName("Status messages")
        self.status_label.setWordWrap(True)
        layout_r.addWidget(self.status_label)

        self.tab_rotation.setLayout(layout_r)
        rotation_scroll = QScrollArea()
        rotation_scroll.setWidgetResizable(True)
        rotation_scroll.setWidget(self.tab_rotation)

        # --- Tab 2: Jingles & Scheduler ---
        self.tab_jingles = QWidget()
        layout_j = QVBoxLayout()
        self.slot_labels = {}
        for label, key in {":00 (Top)": ":00", ":15 (Past)": ":15",
                            ":30 (Half)": ":30", ":45 (To)": ":45"}.items():
            btn = QPushButton(f"Set Folder for {label}")
            btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
            btn.clicked.connect(lambda checked, k=key: self.set_jingle_folder(k))
            layout_j.addWidget(btn)
            info = QLabel(describe_folder(self.settings.value(key, "")))
            info.setWordWrap(True)
            info.setAccessibleName(f"{label} folder: {info.text()}")
            self.slot_labels[key] = info
            layout_j.addWidget(info)

        ad_btn = QPushButton("Set Ad Break Folder")
        ad_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        ad_btn.clicked.connect(self.set_ad_break_folder)
        layout_j.addWidget(ad_btn)
        ad_info = QLabel(describe_folder(self.settings.value("ad_break_folder", "")))
        ad_info.setWordWrap(True)
        ad_info.setAccessibleName(f"Commercials folder: {ad_info.text()}")
        self.slot_labels["ad_break_folder"] = ad_info
        layout_j.addWidget(ad_info)
        layout_j.addStretch(1)
        self.tab_jingles.setLayout(layout_j)

        # --- Tab 3: Audio Settings ---
        self.tab_audio = QWidget()
        layout_a = QFormLayout()

        self.input_combo = QComboBox()
        self.output_combo = QComboBox()

        for dev in QMediaDevices.audioInputs():
            self.input_combo.addItem(dev.description(), dev)
        for dev in QMediaDevices.audioOutputs():
            self.output_combo.addItem(dev.description(), dev)

        self.input_combo.setCurrentText(self.settings.value("input_device", ""))
        self.output_combo.setCurrentText(self.settings.value("output_device", ""))

        # Folders: set everything here, in any order.
        self.folder_labels = {}
        for key, title in FOLDER_SETTINGS:
            value = self.settings.value(key, "") or ""
            if key == "playlist_output_folder":
                value = describe_folder(value or self.playlist_generator.output_folder())
            else:
                value = describe_folder(value)
            label = QLabel(value)
            label.setWordWrap(True)
            label.setAccessibleName(f"{title} folder: {value or 'not set'}")
            self.folder_labels[key] = label
            label.setAccessibleName(f"{title} folder: {value}")
            layout_a.addRow(f"{title} folder:", label)
            choose = QPushButton(f"Choose {title} Folder")
            choose.setStyleSheet(BUTTON_STYLE_CONSOLE)
            choose.clicked.connect(lambda _checked=False, k=key, t=title: self.choose_folder_setting(k, t))
            layout_a.addRow(choose)

        log_label = QLabel(RUN_LOG.folder)
        log_label.setWordWrap(True)
        log_label.setAccessibleName(f"Log folder: {RUN_LOG.folder}")
        layout_a.addRow("Log folder (one file per day, plus errors.log):", log_label)

        layout_a.addRow("Microphone/Line-In:", self.input_combo)
        layout_a.addRow("Speaker/Interface:", self.output_combo)

        self.live_mix_check = QCheckBox("Stream the live mix of music, jingles and microphone (restart to apply)")
        self.live_mix_check.setChecked(str(self.settings.value("use_live_mix", "true")).lower() != "false")
        self.break_style_combo = QComboBox()
        self.break_style_combo.setAccessibleName("Break style")
        self.break_style_combo.addItem("Fade the music out so the break starts exactly on the mark (default)", "fade_at_mark")
        self.break_style_combo.addItem("Let the song finish, then start the break", "finish_song")
        style_index = self.break_style_combo.findData(str(self.settings.value("break_style", "fade_at_mark")))
        self.break_style_combo.setCurrentIndex(max(0, style_index))
        layout_a.addRow("Break style:", self.break_style_combo)

        self.top_hour_ads_check = QCheckBox("Also play a commercial break in the top of the hour (otherwise only its jingle plays)")
        self.top_hour_ads_check.setChecked(str(self.settings.value("top_hour_ads", "false")).lower() == "true")
        layout_a.addRow(self.top_hour_ads_check)

        self.autostart_check = QCheckBox("Start Vision Studio when Windows starts (it opens in the system tray)")
        self.autostart_check.setChecked(autostart_enabled())
        self.autostart_check.toggled.connect(self.on_autostart_toggled)
        layout_a.addRow(self.autostart_check)
        self.close_to_tray_check = QCheckBox("Closing the window sends Vision Studio to the system tray instead of exiting")
        self.close_to_tray_check.setChecked(str(self.settings.value("close_to_tray", "false")).lower() == "true")
        self.close_to_tray_check.toggled.connect(self.on_close_to_tray_toggled)
        layout_a.addRow(self.close_to_tray_check)
        self.start_in_tray_check = QCheckBox("When it starts with Windows, open in the system tray instead of showing the window")
        self.start_in_tray_check.setChecked(str(self.settings.value("start_in_tray", "false")).lower() == "true")
        layout_a.addRow(self.start_in_tray_check)
        self.autoplay_check = QCheckBox("When it starts with Windows, begin playing automatically")
        self.autoplay_check.setChecked(str(self.settings.value("autoplay_on_boot", "false")).lower() == "true")
        layout_a.addRow(self.autoplay_check)
        self.resume_automation_check = QCheckBox("When the program starts, turn automation back on if it was on when the program closed")
        self.resume_automation_check.setChecked(str(self.settings.value("resume_automation", "true")).lower() != "false")
        layout_a.addRow(self.resume_automation_check)

        layout_a.addRow(self.live_mix_check)

        # Playlist generation
        self.playlist_mode_combo = QComboBox()
        self.playlist_mode_combo.setAccessibleName("Playlist generation mode")
        for label, value in (("Whole day at midnight, 0000 through 2300 (default)", "midnight_full_day"),
                             ("One hour at a time, ahead of the hour", "hour_lead"),
                             ("At fixed times of day", "fixed_times")):
            self.playlist_mode_combo.addItem(label, value)
        index = self.playlist_mode_combo.findData(str(self.settings.value("playlist_mode", "midnight_full_day")))
        self.playlist_mode_combo.setCurrentIndex(max(0, index))
        layout_a.addRow("Generate playlists:", self.playlist_mode_combo)

        self.playlist_lead_spin = QSpinBox()
        self.playlist_lead_spin.setRange(0, 3600)
        self.playlist_lead_spin.setAccessibleName("Seconds before the target time to generate playlists")
        try:
            self.playlist_lead_spin.setValue(int(self.settings.value("playlist_lead_seconds", 0)))
        except Exception:
            pass
        layout_a.addRow("Seconds early to write playlists (0 = exactly at midnight):", self.playlist_lead_spin)

        self.queue_lead_spin = QSpinBox()
        self.queue_lead_spin.setRange(10, 3000)
        self.queue_lead_spin.setAccessibleName("Seconds before the hour ends to add the next hour to the queue")
        self.queue_lead_spin.setValue(self.queue_lead_seconds())
        layout_a.addRow("Add the next hour to the queue this many seconds before the hour ends:", self.queue_lead_spin)

        self.playlist_times_edit = QLineEdit(str(self.settings.value("playlist_fixed_times", "00:00")))
        self.playlist_times_edit.setAccessibleName("Fixed generation times, hours and minutes separated by commas")
        layout_a.addRow("Fixed times (for example 00:00, 12:00):", self.playlist_times_edit)

        self.playlist_folder_label = self.folder_labels["playlist_output_folder"]

        self.playlist_autoload_check = QCheckBox("Build hourly playlists and keep the queue filled from them")
        self.playlist_autoload_check.setChecked(str(self.settings.value("playlist_autoload", "true")).lower() != "false")
        layout_a.addRow(self.playlist_autoload_check)

        wizard_btn = QPushButton("Run Setup Wizard Again")
        wizard_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        wizard_btn.clicked.connect(self.run_setup_wizard)
        layout_a.addRow(wizard_btn)

        auto_btn = QPushButton("Automation On / Off (A)")
        auto_btn.setAccessibleName("Automation on or off. Keyboard shortcut A.")
        auto_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        auto_btn.clicked.connect(self.automation_toggle)
        layout_a.addRow(auto_btn)
        stop_fade_btn = QPushButton("Stop With Fade (S)")
        stop_fade_btn.setAccessibleName("Stop with fade. The record stays on the deck. Keyboard shortcut S.")
        stop_fade_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        stop_fade_btn.clicked.connect(self.stop_with_fade)
        layout_a.addRow(stop_fade_btn)
        stop_all_btn = QPushButton("Stop Everything At Once (Ctrl+Shift+S)")
        stop_all_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        stop_all_btn.clicked.connect(self.stop_everything)
        layout_a.addRow(stop_all_btn)

        generate_btn = QPushButton("Generate Playlists Now (Ctrl+Shift+G)")
        generate_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        generate_btn.clicked.connect(self.generate_now)
        layout_a.addRow(generate_btn)

        # Break protection
        self.break_hold_spin = QSpinBox()
        self.break_hold_spin.setRange(10, 300)
        self.break_hold_spin.setAccessibleName("Break window: a song that ends this many seconds before a mark starts the break")
        try:
            self.break_hold_spin.setValue(break_window_seconds(self.settings))
        except Exception:
            self.break_hold_spin.setValue(BREAK_WINDOW_DEFAULT)
        layout_a.addRow("Break window, seconds before the mark (a song ending inside it starts the break):", self.break_hold_spin)

        # Processing
        self.proc_master_check = QCheckBox("Process the stream with the broadcast processor (AGC, 5-band compressor, limiter)")
        self.proc_master_check.setChecked(str(self.settings.value("proc_master", "true")).lower() != "false")
        layout_a.addRow(self.proc_master_check)
        self.proc_preset_combo = QComboBox()
        self.proc_preset_combo.setAccessibleName("Processor preset")
        for name in PROCESSOR_PRESETS:
            self.proc_preset_combo.addItem(name)
        self.proc_preset_combo.setCurrentText(str(self.settings.value("proc_preset", "Broadcast")))
        layout_a.addRow("Processor preset:", self.proc_preset_combo)
        self.proc_ceiling_spin = QSpinBox()
        self.proc_ceiling_spin.setRange(-12, 0)
        self.proc_ceiling_spin.setAccessibleName("Limiter ceiling in decibels")
        try:
            self.proc_ceiling_spin.setValue(int(float(self.settings.value("proc_ceiling_db", -1))))
        except Exception:
            self.proc_ceiling_spin.setValue(-1)
        layout_a.addRow("Limiter ceiling (dB):", self.proc_ceiling_spin)
        self.proc_source_checks = {}
        for key, label in (("proc_deck_a", "Also process Deck A on its own"),
                           ("proc_deck_b", "Also process Deck B on its own"),
                           ("proc_sequence", "Also process jingles and ads on their own"),
                           ("proc_mic", "Also process the microphone on its own")):
            check = QCheckBox(label)
            check.setChecked(str(self.settings.value(key, "false")).lower() == "true")
            self.proc_source_checks[key] = check
            layout_a.addRow(check)
        note = QLabel("The processor shapes what goes out to your stream. Your own speakers play the "
                      "loudness-matched tracks without it.")
        note.setWordWrap(True)
        layout_a.addRow(note)

        self.separation_spin = QSpinBox()
        self.separation_spin.setRange(1, 12)
        self.separation_spin.setAccessibleName("Hours a played song and its artist are held back")
        try:
            self.separation_spin.setValue(int(float(self.settings.value("separation_hours", 2))))
        except Exception:
            self.separation_spin.setValue(2)
        # The hold-back times now live in Programming Rules (this old spin box is no longer shown).
        self.break_estimate_spin = QSpinBox()
        self.break_estimate_spin.setRange(0, 600)
        self.break_estimate_spin.setAccessibleName("Estimated seconds one break takes, used when building an hour")
        try:
            self.break_estimate_spin.setValue(int(float(self.settings.value("break_estimate_seconds", DEFAULT_BREAK_ESTIMATE_SECONDS))))
        except Exception:
            self.break_estimate_spin.setValue(DEFAULT_BREAK_ESTIMATE_SECONDS)
        layout_a.addRow("Estimated length of one break, seconds (used to fit a built hour):", self.break_estimate_spin)
        self.voice_slot_spin = QSpinBox()
        self.voice_slot_spin.setRange(5, 120)
        self.voice_slot_spin.setAccessibleName("Seconds reserved for each empty voice track slot")
        try:
            self.voice_slot_spin.setValue(int(float(self.settings.value("voice_slot_seconds", DEFAULT_VOICE_SLOT_SECONDS))))
        except Exception:
            self.voice_slot_spin.setValue(DEFAULT_VOICE_SLOT_SECONDS)
        layout_a.addRow("Seconds reserved for each voice track slot:", self.voice_slot_spin)
        self.break_gap_spin = QSpinBox()
        self.break_gap_spin.setRange(0, 3000)
        self.break_gap_spin.setSingleStep(50)
        self.break_gap_spin.setAccessibleName("Silence in milliseconds between jingle and ad items in a break")
        try:
            self.break_gap_spin.setValue(int(float(self.settings.value("break_item_gap_ms", 250))))
        except Exception:
            self.break_gap_spin.setValue(250)
        layout_a.addRow("Silence between break items, milliseconds:", self.break_gap_spin)

        save_audio_btn = QPushButton("Save Settings")
        save_audio_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        save_audio_btn.clicked.connect(self.save_audio_settings)
        layout_a.addRow(save_audio_btn)
        self.tab_audio.setLayout(layout_a)
        self.tab_audio_scroll = QScrollArea()
        self.tab_audio_scroll.setWidgetResizable(True)
        self.tab_audio_scroll.setWidget(self.tab_audio)

        # --- New tabs ---
        self.rotations_tab = RotationsTab(self)
        self.schedule_tab = ScheduleTab(self)
        self.categories_tab = CategoriesTab(self)
        self.shortcuts_tab = ShortcutsTab(self)

        # --- Settings sections (the old tabs now live here) ---
        self.recording_tab = self.build_recording_tab()
        self.tagging_tab = self.build_tagging_tab()
        self.vt_hour_tab = VoiceTrackHourTab(self)
        self.logo_tab = self.build_logo_tab()
        self.crossfade_tab = self.build_crossfade_tab()
        self.version_tab = self.build_version_tab()
        self.folder_tab = self.build_folder_tab()
        self.rules_tab = self.build_rules_tab()
        sections = (("General", self.tab_audio_scroll), ("Rotations", self.rotations_tab),
                    ("Schedule", self.schedule_tab), ("Categories", self.categories_tab),
                    ("Jingles & Scheduler", self.tab_jingles), ("Keyboard Shortcuts", self.shortcuts_tab),
                    ("Voice Track Hour", self.vt_hour_tab),
                    ("Encoders / Simulcast", self.encoder_bank), ("Recording", self.recording_tab),
                    ("Tagging", self.tagging_tab), ("Crossfade", self.crossfade_tab), ("Programming Rules", self.rules_tab), ("Folder Report", self.folder_tab),
                    ("Logo", self.logo_tab), ("Version", self.version_tab))
        self.section_list = QListWidget()
        self.section_list.setAccessibleName("Settings sections")
        self.section_list.setMaximumWidth(220)
        for name, widget in sections:
            self.tabs.addTab(widget, name)
            self.section_list.addItem(name)
        self.section_list.currentRowChanged.connect(self.tabs.setCurrentIndex)
        self.section_list.setCurrentRow(0)

        settings_page = QWidget()
        self.settings_page = settings_page
        settings_layout = QVBoxLayout()
        back_btn = QPushButton("Back To The On-Air Screen (Ctrl+O or Escape)")
        back_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        back_btn.clicked.connect(self.show_onair)
        settings_layout.addWidget(back_btn)
        body = QHBoxLayout()
        body.addWidget(self.section_list)
        body.addWidget(self.tabs, 1)
        settings_layout.addLayout(body, 1)
        settings_page.setLayout(settings_layout)

        self.pages = QStackedWidget()
        self.pages.addWidget(rotation_scroll)
        self.pages.addWidget(settings_page)
        self.escape_shortcut = QShortcut(QKeySequence("Escape"), self)
        self.escape_shortcut.activated.connect(self.on_escape_pressed)

        layout.addWidget(self.pages, 1)
        self.setLayout(layout)

    # --- Status / rotation callbacks ---
    def update_status(self, message):
        self.status_label.setText(f"Status: {message}")
        RUN_LOG.write("STATUS", str(message))

    def announce(self, message):
        announce_accessible(self.alert_label, f"Alert: {message}")
        self.update_status(message)

    def on_now_playing(self, track_path):
        RUN_LOG.write("PLAY", f"{self._track_text(track_path)} | {track_path}")
        try:
            self.recorder.note_track(get_track_metadata(track_path), track_path)
        except Exception:
            pass
        track_name = os.path.basename(track_path)
        self.now_playing_label.setText(f"Now Playing: {track_name}")
        self.onair_status_label.setText("On Air: music rotation playing.")
        self.refresh_live_indicators()
        self.refresh_queue_list()
        self.refresh_played_list()

        upcoming_path = self.rotation.get_upcoming_track_path()
        if upcoming_path:
            self.up_next_label.setText(f"Up Next: {os.path.basename(upcoming_path)}")
        else:
            self.up_next_label.setText("Up Next: (reshuffling library)")

        # Tell every connected stream what is playing: artist, title and album.
        self.encoder_bank.push_metadata(get_track_metadata(track_path))

    def on_track_ending(self):
        if not self.is_muted:               # while muted nothing beeps, in the tray or out of it
            self.warning_beep.play()
        self.update_status("Track ending in 5 seconds.")

    def on_item_ending(self):
        if not self.is_muted:
            self.warning_beep.play()

    def on_crossfader_move(self, position_0_to_100):
        self.crossfader_slider.setValue(int(round(position_0_to_100)))

    # --- Encoders ---
    def on_encoder_state_changed(self, slot, state, reason):
        previous = self.encoder_last_state.get(slot, "offline")
        self.encoder_last_state[slot] = state
        name = slot.stream_name
        if state == "live":
            self.encoder_problems.pop(slot, None)
            self.connect_beep.play()
            self.announce(f"{name} connected.")
        elif state == "connecting":
            self.encoder_problems.pop(slot, None)
            self.update_status(f"{name} is connecting.")
        elif getattr(slot, "quiet_retry", False) and previous in ("offline", "connecting"):
            # A retry attempt that failed again: already announced the drop once, stay quiet.
            self.encoder_problems[slot] = reason
        else:
            if reason in ("stopped", "removed", ""):
                self.encoder_problems.pop(slot, None)
                if previous != "offline":
                    self.disconnect_beep.play()
                    self.announce(f"{name} disconnected.")
            else:
                self.encoder_problems[slot] = reason
                self.disconnect_beep.play()
                self.announce(f"{name} disconnected: {reason}")
        if reason == "removed":
            self.encoder_last_state.pop(slot, None)
        self.refresh_encoder_indicator()

    def refresh_encoder_indicator(self):
        live = [s.stream_name for s, st in self.encoder_last_state.items() if st == "live"]
        connecting = [s.stream_name for s, st in self.encoder_last_state.items() if st == "connecting"]
        problems = [s.stream_name for s in self.encoder_problems]
        if problems:
            text = "● ENCODER PROBLEM: " + ", ".join(problems)
            color = COLOR_LIVE_RED
        elif live:
            text = "● Encoders LIVE: " + ", ".join(live)
            color = COLOR_ON_AIR_GREEN
        elif connecting:
            text = "Encoders connecting: " + ", ".join(connecting)
            color = COLOR_WARNING_AMBER
        else:
            text = "Encoders: none streaming."
            color = COLOR_TEXT_DIM
        self.console_encoders_label.setText(text)
        self.encoder_indicator_color = color
        self.apply_indicator_color()

    def apply_indicator_color(self):
        color = getattr(self, "encoder_indicator_color", COLOR_TEXT_DIM)
        blinking = color in (COLOR_ON_AIR_GREEN, COLOR_LIVE_RED)
        shown = color if (self.blink_on or not blinking) else COLOR_BORDER
        self.console_encoders_label.setStyleSheet(f"color: {shown}; font-weight: bold;")

    def on_blink_tick(self):
        self.blink_on = not self.blink_on
        self.apply_indicator_color()

    # --- Microphone ---
    def start_microphone(self):
        self.microphone.start()

    def stop_microphone(self):
        self.microphone.stop()

    def on_monitor_toggled(self, checked):
        self.microphone.monitor_enabled = checked

    def on_mic_started(self):
        self.mic_status_label.setText("Microphone: LIVE on air.")
        self.mic_status_label.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
        self.onair_status_label.setText("On Air: microphone LIVE, music ducked.")
        self.console_mic_label.setText("Mic: LIVE.")
        self.console_mic_label.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
        self.rotation.duck_for_microphone()
        self.announce("Microphone is live.")

    def on_mic_stopped(self):
        self.mic_status_label.setText("Microphone: off air.")
        self.mic_status_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        self.onair_status_label.setText("On Air: music rotation playing.")
        self.console_mic_label.setText("Mic: off air.")
        self.console_mic_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        self.rotation.unduck_after_microphone()
        self.announce("Microphone is off.")

    def on_mic_failed(self, reason):
        self.mic_status_label.setText(f"Microphone: could not start. {reason}")
        self.mic_status_label.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
        self.announce("Microphone could not start.")

    def on_mic_signal_changed(self, has_signal):
        if has_signal:
            self.mic_status_label.setText("Microphone: LIVE, signal detected.")
        else:
            self.mic_status_label.setText("Microphone: LIVE, but no signal. Check that it is not muted "
                                          "and that Windows allows desktop apps to use it.")

    def on_mic_audio_chunk(self, data, fmt):
        if self.mixer.available:
            self.mixer.push_raw("mic", data, fmt.sampleRate(), fmt.channelCount(), fmt.sampleFormat())

    def toggle_mute(self):
        """Mutes this computer's speakers only. The stream encoders, the recording and the microphone feed
        keep the full program."""
        self.is_muted = not self.is_muted
        try:
            self.settings.setValue("speakers_muted", "true" if self.is_muted else "false")
        except Exception:
            pass
        self.rotation.set_muted(self.is_muted)
        self.sequence_player.set_muted(self.is_muted)
        self.microphone.set_muted(self.is_muted)
        if self.is_muted:
            self.mute_btn.setText("Unmute Speakers (Ctrl+Shift+U)")
            self.console_mute_label.setText("Speakers muted. The stream is live.")
            self.console_mute_label.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
            self.announce("Speakers muted. The stream is still live.")
        else:
            self.mute_btn.setText("Mute Speakers (Ctrl+Shift+U)")
            self.console_mute_label.setText("Mute: off.")
            self.console_mute_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
            self.announce("Speakers unmuted.")

    # --- Scheduler / sequence callbacks ---
    def start_break(self, slot):
        """Fade the music out (without cutting a song) and run the scheduled sequence."""
        self.rotation.begin_crossfade_out(lambda: self.play_break_sequence(slot))

    def play_break_sequence(self, slot):
        RUN_LOG.write("BREAK", f"{slot} break starting.")
        config = SLOT_CONFIG.get(slot, {"folder_key": slot, "sequence": "simple"})
        jingle_folder = self.settings.value(config["folder_key"], "")
        if not jingle_folder or not os.path.isdir(jingle_folder):
            self.announce(f"No folder is set for the {slot} break, so no jingle will play. "
                          f"Set it in the Jingles and Scheduler tab or run the setup wizard.")
        elif not scan_audio_files(jingle_folder):
            self.announce(f"The {slot} break folder has no audio files in it.")
        sequence = config["sequence"]
        if slot == ":00" and str(self.settings.value("top_hour_ads", "false")).lower() != "true":
            sequence = "simple"      # the top of the hour is just its own jingle; commercials stay at :15 and :45
        self.sequence_player.play_sequence(slot, sequence, jingle_folder)

    def on_break_upcoming(self, slot, target):
        """About two minutes before a mark: the engine starts protecting the song on air."""
        if not self.break_marks.enabled(target.date(), target.hour, slot):
            return          # this mark is switched off for that hour
        if self.rotation.is_running and self.rotation.automation_on and not self.rotation.is_paused_for_sequence:
            self.rotation.arm_break(target, slot, lambda s=slot: self.play_break_sequence(s))
            self.update_status(f"{slot} break coming up. The song on air will not be cut.")

    def on_crossfade_start(self, slot):
        """The clock reached the mark. If the engine is already managing this break, leave it to the engine."""
        if not self.rotation.automation_on:
            return          # automation is off: no jingles or breaks fire by themselves
        now = datetime.now()
        if not self.break_marks.enabled(now.date(), now.hour, slot):
            self.update_status(f"The {slot} break is switched off for this hour.")
            return
        if self.rotation.break_is_armed(slot):
            if self.rotation.break_style() == "fade_at_mark" and not self.rotation.is_paused_for_sequence:
                self.update_status(f"It is {slot}. Fading the music out for the break now.")
                self.rotation._take_break(quick=True)
            else:
                self.update_status(f"It is {slot}. The break starts as soon as the song on air finishes.")
            return
        if self.rotation.break_recently_taken(slot):
            return
        self.start_break(slot)

    def on_sequence_changed(self):
        try:
            active = bool(self.sequence_player.active)
            if active and not self._seq_was_active and self.recorder.recording:
                self.recorder.note_other(f"Jingles and ads ({self.sequence_player.slot})")
            self._seq_was_active = active
            self.refresh_break_decks()
        except Exception:
            pass
        self.refresh_queue_list()
        self.refresh_status_tree()

    def on_sequence_done(self):
        self.rotation.resume_after_sequence()

    # --- Folder pickers: choosing a folder also starts loudness analysis right away ---
    def set_library_folder(self):
        self.choose_folder_setting("music_library_folder", "Music library")

    def set_jingle_folder(self, key):
        titles = dict(FOLDER_SETTINGS)
        self.choose_folder_setting(key, titles.get(key, key))

    def set_ad_break_folder(self):
        self.choose_folder_setting("ad_break_folder", "Commercials")

    def choose_folder_setting(self, key, title):
        """One place that sets any folder: saves it, starts loudness analysis, and (for music) builds
        the rotations, the schedule and this hour's playlist."""
        start = self.settings.value(key, "") or ""
        folder = QFileDialog.getExistingDirectory(self, f"Choose the {title} folder", start)
        if not folder:
            return
        self.settings.setValue(key, folder)
        self.show_folder(key, title, folder)
        if key == "playlist_output_folder":
            try:
                os.makedirs(folder, exist_ok=True)
            except OSError as e:
                self.update_status(f"Could not create that folder: {e}")
            self.announce(f"Playlists will be saved in {folder}.")
            self.ensure_hour_playlists(force=True)
            return
        files = scan_audio_files(folder)
        self.normalizer.start(files)
        if key == "music_library_folder":
            self.settings.setValue("setup_complete", "true")
            self._rescan_in_progress = False
            self.rotation_library.sync_from_root(folder)
            self.rotation_library.ensure_mix(folder)
            self.rotation_schedule.regenerate_even()
            self.rotation_library.detect_new_files()
            self.rotations_tab.refresh()
            self.schedule_tab.refresh()
            self.announce(f"Music library set: {len(files)} tracks and {len(self.rotation_library.rotations)} rotations found.")
            self.ensure_hour_playlists(force=True)
        else:
            self.announce(f"{title} folder set: {len(files)} audio files found.")

    def show_folder(self, key, title, folder):
        text = describe_folder(folder)
        for labels in (self.folder_labels, self.slot_labels):
            label = labels.get(key)
            if label is not None:
                label.setText(text)
                label.setAccessibleName(f"{title} folder: {text}")

    def start_rotation(self):
        if not self.rotation_library.rotations and not self.settings.value("music_library_folder", ""):
            self.announce("No music folder is set. Open Settings with Control O and choose your music library folder.")
            return
        self.ensure_hour_playlists()
        self.rotation.start()
        self.remember_automation(self.rotation.automation_on)

    def automation_toggle(self):
        """A: automation on (the first song goes onto the deck) or off (the song on air finishes)."""
        if self.rotation.automation_on:
            self.rotation.automation_off()
            self.remember_automation(False)
            self.announce("Automation off. The song on air will finish.")
        else:
            self.start_rotation()
            self.remember_automation(self.rotation.automation_on)
        self.refresh_queue_list()

    def stop_with_fade(self):
        """S: fade the record out and stop it. It stays on its deck."""
        sp = self.sequence_player
        if sp.active:
            sp.queue = []
            sp.active = False
            try:
                sp.player.stop()
            except Exception:
                pass
            self.on_sequence_changed()
        self.rotation.stop_with_fade()
        self.remember_automation(False)
        self.announce("Stopping. Fading out.")
        self.refresh_queue_list()

    def save_audio_settings(self):
        self.settings.setValue("input_device", self.input_combo.currentText())
        self.settings.setValue("output_device", self.output_combo.currentText())
        self.settings.setValue("start_in_tray", "true" if self.start_in_tray_check.isChecked() else "false")
        self.settings.setValue("autoplay_on_boot", "true" if self.autoplay_check.isChecked() else "false")
        self.settings.setValue("resume_automation", "true" if self.resume_automation_check.isChecked() else "false")
        self.settings.setValue("top_hour_ads", "true" if self.top_hour_ads_check.isChecked() else "false")
        self.settings.setValue("use_live_mix", "true" if self.live_mix_check.isChecked() else "false")
        self.settings.setValue("playlist_mode", self.playlist_mode_combo.currentData())
        self.settings.setValue("playlist_lead_seconds", self.playlist_lead_spin.value())
        self.settings.setValue("queue_lead_seconds", self.queue_lead_spin.value())
        self.settings.setValue("playlist_fixed_times", self.playlist_times_edit.text())
        self.settings.setValue("playlist_autoload", "true" if self.playlist_autoload_check.isChecked() else "false")
        self.settings.setValue("break_window_seconds", self.break_hold_spin.value())
        self.settings.setValue("break_style", self.break_style_combo.currentData())
        self.settings.setValue("crossfade_enabled", "true" if self.crossfade_check.isChecked() else "false")
        self.rotation.apply_crossfade_setting()
        self.settings.setValue("separation_hours", self.separation_spin.value())
        self.settings.setValue("fit_end_of_hour", "true" if self.fit_hour_check.isChecked() else "false")
        self.settings.setValue("fit_quarter_marks", "true" if self.fit_quarter_check.isChecked() else "false")
        self.settings.setValue("fit_early_seconds", self.fit_early_spin.value())
        self.settings.setValue("fit_min_song_seconds", self.fit_min_song_spin.value())
        self.rotation.apply_fit_options()
        self.settings.setValue("break_estimate_seconds", self.break_estimate_spin.value())
        self.settings.setValue("voice_slot_seconds", self.voice_slot_spin.value())
        self.settings.setValue("break_item_gap_ms", self.break_gap_spin.value())
        self.rotation.apply_separation_setting()
        self.refresh_played_list()
        self.settings.setValue("proc_master", "true" if self.proc_master_check.isChecked() else "false")
        self.settings.setValue("proc_preset", self.proc_preset_combo.currentText())
        self.settings.setValue("proc_ceiling_db", self.proc_ceiling_spin.value())
        for key, check in self.proc_source_checks.items():
            self.settings.setValue(key, "true" if check.isChecked() else "false")
        self.apply_processing_settings()
        device =get_selected_output_device(self.settings)
        self.rotation.apply_output_device(device)
        self.sequence_player.apply_output_device(device)
        for beep in (self.warning_beep, self.connect_beep, self.disconnect_beep):
            beep.set_device(device)
        self.update_status("Settings saved. Output and processing changes apply now; a new microphone applies the next time it starts.")


if __name__ == "__main__":
    if "--make-icon" in sys.argv:             # used by the build: writes the Windows icon file and exits
        _target = sys.argv[sys.argv.index("--make-icon") + 1] if len(sys.argv) > sys.argv.index("--make-icon") + 1 else "VisionStudio.ico"
        write_icon_file(_target)
        sys.exit(0)
    install_crash_guard()
    disable_power_throttling()
    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)      # hiding to the system tray must not end the program
    try:
        window = BroadcastingApp()
        # Only a start-up entry made by the "Start with Windows" setting counts as a Windows start-up launch.
        if ("--startup" in sys.argv or "--tray" in sys.argv) and autostart_enabled():
            window.on_startup_launch()
        else:
            window.show_remembered()
    except Exception as e:
        _log_exception(type(e), e, e.__traceback__)
        QMessageBox.critical(None, "Vision Studio could not start",
                             f"Vision Studio could not start.\n\n{type(e).__name__}: {e}\n\n"
                             f"Details were saved to:\n{ERROR_LOG_PATH}")
        sys.exit(1)
    sys.exit(app.exec())
