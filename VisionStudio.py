import sys
import os
import json
import re
import random
import subprocess
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
from collections import deque
from datetime import datetime, timedelta

from PyQt6.QtWidgets import (QApplication, QWidget, QVBoxLayout, QPushButton,
                             QLabel, QFileDialog, QTabWidget, QFormLayout, QComboBox,
                             QHBoxLayout, QLineEdit, QScrollArea, QMessageBox, QSlider,
                             QCheckBox, QListWidget, QListWidgetItem, QTableWidget,
                             QTableWidgetItem, QHeaderView, QKeySequenceEdit, QSpinBox,
                             QInputDialog, QGroupBox, QDialog, QDialogButtonBox,
                             QAbstractItemView, QWizard, QWizardPage, QTreeWidget, QTreeWidgetItem)
from PyQt6.QtCore import QSettings, QUrl, QTimer, Qt, QThread, QObject, pyqtSignal, QPointF, QRectF, QEvent, QStandardPaths
from PyQt6.QtGui import QPixmap, QKeySequence, QShortcut, QPainter, QColor, QPen, QBrush
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
ERROR_LOG_PATH = os.path.join(tempfile.gettempdir(), "visionstudio_errors.log")
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
BREAK_ARM_SECONDS = 150  # how long before a break the engine starts protecting the song
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
    return entry == HOUR_MARKER_TOKEN


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
    suffix = "AM" if hour < 12 else "PM"
    shown = hour % 12 or 12
    return f"{shown}:00 {suffix}"


def format_track_display(path):
    if is_hour_marker(path):
        return "---- Hour marker ----"
    meta = get_track_metadata(path)
    if meta["artist"]:
        return f"{meta['artist']} - {meta['title']}"
    return meta["title"]


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
    def __init__(self, name, folder, recursive=True, auto=False, rotation_id=None):
        self.id = rotation_id or uuid.uuid4().hex[:8]
        self.name = name
        self.folder = folder
        self.recursive = recursive
        self.auto = auto  # created automatically from a subfolder of the music library

    def to_dict(self):
        return {"id": self.id, "name": self.name, "folder": self.folder,
                "recursive": self.recursive, "auto": self.auto}

    @staticmethod
    def from_dict(data):
        return MusicRotation(data.get("name", "Rotation"), data.get("folder", ""),
                             bool(data.get("recursive", True)), bool(data.get("auto", False)),
                             data.get("id"))

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

    def add_rotation(self, name, folder, recursive=True, auto=False, notify=True):
        rotation = MusicRotation(self.unique_name(name), folder, recursive, auto)
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

        existing = {r.folder: r for r in self.rotations if r.auto}
        wanted_folders = {folder for _, folder, _ in wanted}
        added = []
        removed = []
        for name, folder, recursive in wanted:
            if folder in existing:
                existing[folder].recursive = recursive
            else:
                rotation = self.add_rotation(name, folder, recursive, auto=True, notify=False)
                added.append(rotation.name)
        for rotation in list(self.rotations):
            if rotation.auto and rotation.folder not in wanted_folders:
                self.rotations.remove(rotation)
                self.known_files.pop(rotation.id, None)
                removed.append(rotation.name)
        if added or removed:
            self._changed("added" if added else "removed")
        return added, removed

    def detect_new_files(self):
        """Compares every rotation's folder with the last look. Returns {rotation_id: [new files]}."""
        result = {}
        for rotation in self.rotations:
            current = set(rotation.track_paths())
            previous = self.known_files.get(rotation.id)
            self.known_files[rotation.id] = current
            if previous is None:
                continue
            new_files = sorted(current - previous, key=str.lower)
            if new_files:
                result[rotation.id] = new_files
        return result


class RotationSchedule:
    """
    A 24-hour schedule saying which rotation is live in each hour. It builds
    itself: rotations are spread evenly round-robin across the day, and it
    regenerates whenever rotations are added or removed.
    """

    def __init__(self, settings, library):
        self.settings = settings
        self.library = library
        self.hours = [None] * 24
        self.load()
        self.ensure_valid()

    def load(self):
        try:
            data = json.loads(self.settings.value("schedule_json", "[]"))
            if isinstance(data, list) and len(data) == 24:
                self.hours = data
        except Exception:
            pass

    def save(self):
        try:
            self.settings.setValue("schedule_json", json.dumps(self.hours))
        except Exception:
            pass

    def regenerate_even(self):
        ids = [r.id for r in self.library.rotations]
        self.hours = [ids[h % len(ids)] if ids else None for h in range(24)]
        self.save()

    def ensure_valid(self):
        valid = {r.id for r in self.library.rotations}
        if any(h not in valid for h in self.hours) and valid:
            self.regenerate_even()
        elif not valid:
            self.hours = [None] * 24

    def rotation_id_for_hour(self, hour):
        return self.hours[hour % 24]

    def set_hour(self, hour, rotation_id):
        self.hours[hour % 24] = rotation_id
        self.save()

    def describe_day(self, current_hour):
        rows = []
        for hour in range(24):
            rotation = self.library.find(self.hours[hour])
            rows.append((hour_label(hour), rotation.name if rotation else "(none)", hour == current_hour))
        return rows


# ---------------------------------------------------------------------------
# Categories and spot groups (jingles, sweepers, ads) feeding the sandwich
# ---------------------------------------------------------------------------

CATEGORY_TYPES = ("jingle", "sweeper", "ad")
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

    def add_category(self, folder, name=None, category_type=None):
        base = os.path.basename(os.path.normpath(folder))
        category = {"id": uuid.uuid4().hex[:8],
                    "name": name or pretty_folder_name(base),
                    "type": category_type or guess_category_type(base),
                    "folder": folder}
        self.categories.append(category)
        return category

    def import_folder(self, folder):
        """
        One folder that holds audio becomes one category. A folder that holds only
        subfolders becomes one category per subfolder. Returns the categories added.
        """
        if not folder or not os.path.isdir(folder):
            return []
        added = []
        if scan_audio_files(folder, recursive=False):
            added.append(self.add_category(folder))
        else:
            for d in sorted(os.listdir(folder), key=str.lower):
                path = os.path.join(folder, d)
                if not d.startswith(".") and os.path.isdir(path) and scan_audio_files(path):
                    added.append(self.add_category(path))
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

    def files_for_types(self, types):
        files = []
        for category in self.categories:
            if category["type"] in types:
                files += scan_audio_files(category["folder"])
        return files

    def describe(self, category):
        return f"{category['name']} ({category['type']}) - {category['folder']}"


# ---------------------------------------------------------------------------
# M3U playlists and the Station-Playlist-style hour playlist generator
# ---------------------------------------------------------------------------

def write_m3u(path, entries):
    """Writes an extended M3U (UTF-8). Hour markers become a comment line other software ignores."""
    lines = ["#EXTM3U"]
    for entry in entries:
        if is_hour_marker(entry):
            lines.append("#VISIONSTUDIO-HOURMARKER")
            continue
        meta = get_track_metadata(entry)
        label = f"{meta['artist']} - {meta['title']}" if meta["artist"] else meta["title"]
        lines.append(f"#EXTINF:{int(get_track_duration(entry))},{label}")
        lines.append(entry)
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as handle:
        handle.write("\n".join(lines) + "\n")


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
        if line == "#VISIONSTUDIO-HOURMARKER":
            entries.append(HOUR_MARKER_TOKEN)
            continue
        if line.startswith("#"):
            continue
        full = line if os.path.isabs(line) else os.path.normpath(os.path.join(base_dir, line))
        if os.path.isfile(full):
            entries.append(full)
        else:
            missing += 1
    return entries, missing


def default_playlist_folder():
    """Documents\\VisionStudio\\Playlists, following the real Documents folder (even if OneDrive moved it)."""
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

    def build_hour_entries(self, rotation, virtual_clock, last_track, last_artist, separation=None):
        """About an hour of tracks, starting with an hour marker. virtual_clock is advanced in place."""
        separation = DEFAULT_SEPARATION_SECONDS if separation is None else separation
        pool = rotation.track_paths() if rotation else []
        entries = [HOUR_MARKER_TOKEN]
        if not pool:
            return entries
        random.shuffle(pool)
        queue_items = list(pool)
        filled = 0.0
        guard = 0
        while filled < 3600.0 and guard < 5000:
            guard += 1
            if not queue_items:
                queue_items = list(pool)
                random.shuffle(queue_items)
            chosen_index = None
            for i, candidate in enumerate(queue_items):
                last = last_track.get(candidate)
                artist = self._artist(candidate)
                a_last = last_artist.get(artist) if artist else None
                if (last is None or virtual_clock[0] - last >= separation) and \
                   (a_last is None or virtual_clock[0] - a_last >= separation):
                    chosen_index = i
                    break
            if chosen_index is None:
                chosen_index = 0  # relax the rule when the rotation is too small
            track = queue_items.pop(chosen_index)
            entries.append(track)
            duration = get_track_duration(track)
            last_track[track] = virtual_clock[0]
            artist = self._artist(track)
            if artist:
                last_artist[artist] = virtual_clock[0]
            virtual_clock[0] += duration
            filled += duration
        return entries

    def playlist_path(self, day, hour, rotation_name):
        safe = "".join(c for c in rotation_name if c.isalnum() or c in (" ", "_", "-")).strip().replace(" ", "_")
        return os.path.join(self.output_folder(), f"{day.strftime('%Y-%m-%d')}_{hour:02d}00_{safe or 'rotation'}.m3u8")

    def generate_hour(self, day, hour, virtual_clock=None, last_track=None, last_artist=None):
        rotation = self.library.find(self.schedule.rotation_id_for_hour(hour))
        if rotation is None:
            return None
        entries = self.build_hour_entries(
            rotation, virtual_clock if virtual_clock is not None else [0.0],
            last_track if last_track is not None else {}, last_artist if last_artist is not None else {})
        path = self.playlist_path(day, hour, rotation.name)
        write_m3u(path, entries)
        return path

    def generate_full_day(self, day=None):
        """Writes all 24 hourly playlists plus one combined file. Returns the list of files written."""
        day = day or datetime.now().date()
        clock = [0.0]
        last_track = {}
        last_artist = {}
        written = []
        combined = []
        for hour in range(24):
            rotation = self.library.find(self.schedule.rotation_id_for_hour(hour))
            if rotation is None:
                continue
            entries = self.build_hour_entries(rotation, clock, last_track, last_artist)
            path = self.playlist_path(day, hour, rotation.name)
            write_m3u(path, entries)
            written.append(path)
            combined += entries
        if combined:
            full_path = os.path.join(self.output_folder(), f"{day.strftime('%Y-%m-%d')}_fullday.m3u8")
            write_m3u(full_path, combined)
            written.append(full_path)
        return written

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
    ("start_rotation", "Start rotation", "Ctrl+Return", True),
    ("stop_rotation", "Stop rotation", "Ctrl+Shift+S", True),
    ("mute_all", "Mute or unmute all audio", "Ctrl+Shift+U", True),
    ("open_options", "Open Options (Settings tab)", "Ctrl+O", True),
    ("new_item", "New rotation, category or hour marker (depends on the tab)", "Ctrl+N", True),
    ("generate_now", "Generate playlists now", "Ctrl+Shift+G", True),
    ("say_elapsed", "Announce elapsed time of the current track", "Alt+Shift+T", True),
    ("say_remaining", "Announce time remaining on the current track", "Ctrl+Alt+T", True),
    ("say_current", "Announce the current track", "Ctrl+Alt+C", True),
    ("say_status", "Announce play status", "Ctrl+Alt+P", True),
    ("say_hour_remaining", "Announce time remaining in this hour", "Ctrl+Alt+H", True),
    ("say_mute", "Announce mute status", "Ctrl+Alt+M", True),
    ("say_encoders", "Announce encoder status", "Ctrl+Alt+E", True),
    ("queue_move_up", "Queue list: move the selected track up", "Ctrl+Up", False),
    ("queue_move_down", "Queue list: move the selected track down", "Ctrl+Down", False),
    ("queue_remove", "Queue list: remove the selected track", "Del", False),
    ("queue_browse", "Queue list: browse tracks", "Up / Down", False),
]


def load_shortcut_bindings(settings):
    """Default layout, with any keys the user has changed layered on top."""
    bindings = {sid: key for sid, _label, key, _rebind in DEFAULT_SHORTCUTS}
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

class Deck:
    """
    One playback deck: its own QMediaPlayer, QAudioOutput, and FadeController.
    Two of these alternate being "live" so every rotation transition is a
    real crossfade between two independent decks.
    """

    def __init__(self, name, on_fade_progress=None, output_device=None):
        self.name = name  # "A" or "B"
        self.player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        if output_device is not None:
            self.audio_output.setDevice(output_device)
        self.audio_output.setVolume(0.0)
        self.player.setAudioOutput(self.audio_output)
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
            deck.fader.mute_check = lambda: self.is_muted
            deck.player.mediaStatusChanged.connect(
                lambda status, d=deck: self.on_media_status_changed(status, d)
            )
            deck.player.positionChanged.connect(
                lambda pos, d=deck: self.on_position_changed(pos, d)
            )

        self.shuffled_queue = []
        self.is_paused_for_sequence = False
        self.is_running = False
        self.next_track_cued = False

        self.play_history = PlayHistory()
        self.separation_seconds = DEFAULT_SEPARATION_SECONDS
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

        # Break protection (never cut a song for a scheduled break)
        self.break_target = None
        self.break_slot = None
        self.break_callback = None
        self.break_started = False
        self.tail_loops = 0
        self.last_tail_seek = 0.0
        self.last_taken_slot = None
        self.last_taken_time = None

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
        if self.is_muted:
            return 0.0
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
        return list(self.shuffled_queue)

    def move_queue_item(self, index, delta):
        new_index = index + delta
        if not (0 <= index < len(self.shuffled_queue)) or not (0 <= new_index < len(self.shuffled_queue)):
            return index
        item = self.shuffled_queue.pop(index)
        self.shuffled_queue.insert(new_index, item)
        if item not in self.pinned_tracks and not is_hour_marker(item):
            self.pinned_tracks.add(item)  # a hand-moved track plays where you put it
        self._queue_changed()
        return new_index

    def remove_queue_item(self, index):
        if not (0 <= index < len(self.shuffled_queue)):
            return None
        item = self.shuffled_queue.pop(index)
        self.pinned_tracks.discard(item)
        self._queue_changed()
        return item

    def insert_queue_item(self, path, index=None):
        """Adds a track (or hour marker) to the queue. Never starts playback."""
        if index is None or index > len(self.shuffled_queue):
            index = len(self.shuffled_queue)
        index = max(0, index)
        self.shuffled_queue.insert(index, path)
        if not is_hour_marker(path):
            self.pinned_tracks.add(path)
            if self.normalizer is not None and index < 3:
                self.normalizer.start([path], priority=True)
        self._queue_changed()
        return index

    def load_queue_entries(self, entries, replace=True):
        entries = [e for e in entries if is_hour_marker(e) or os.path.isfile(e)]
        if replace:
            self.shuffled_queue = []
        for e in entries:
            self.shuffled_queue.append(e)
            if not is_hour_marker(e):
                self.pinned_tracks.add(e)
        self.prefetch_upcoming()
        self._queue_changed()
        return len(entries)

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
        self.active_rotation_id = new_id
        random.shuffle(files)
        keep = [p for p in self.shuffled_queue if p in self.pinned_tracks or is_hour_marker(p)]
        self.shuffled_queue = keep + [f for f in files if f not in keep]
        if self.is_running:
            self.prefetch_upcoming()
        self._queue_changed()
        if self.on_rotation_swapped:
            self.on_rotation_swapped(old.name if old else "", new.name)
        return True

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

    def _take_break(self):
        callback = self.break_callback
        self.last_taken_slot = self.break_slot
        self.last_taken_time = datetime.now()
        self.break_started = True
        self.disarm_break()
        self.begin_crossfade_out(callback)

    def _break_gate(self, deck, position_ms, duration_ms, ended=False):
        """
        Returns True when the break logic has taken over this moment (so the normal
        cue/crossfade must not run). Called once the live song is in its closing seconds.
        Song ends before the mark: loop its last seconds so the fade lands on the mark.
        Song still playing at the mark: let it finish, then take the break late.
        """
        if self.break_target is None or self.break_started:
            return False
        fade_s = FADE_STEPS * FADE_INTERVAL_MS / 1000.0
        seconds_to_mark = (self.break_target - datetime.now()).total_seconds()
        max_hold = float(self.settings.value("break_max_hold_seconds", 90) or 90)
        if seconds_to_mark <= fade_s + 0.5:
            self._take_break()
            return True
        if seconds_to_mark > max_hold or ended:
            return False  # too far away to hold the song: carry on and let the next song run
        now = time.monotonic()
        if now - self.last_tail_seek < 1.0:
            return True
        loop_ms = int(min(8000, max(2000, duration_ms * 0.25)))
        target_pos = max(0, duration_ms - loop_ms - 1500)
        self.last_tail_seek = now
        self.tail_loops += 1
        deck.player.setPosition(target_pos)
        if self.tail_loops == 1:
            self.on_status(f"Holding the end of this song so the break starts on the mark "
                           f"({int(seconds_to_mark)} seconds to go).")
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
        self.shuffled_queue = [p for p in self.shuffled_queue if p in self.pinned_tracks or is_hour_marker(p)]
        count = self.build_shuffled_queue()
        if count == 0:
            self.on_status("Music library folder has no audio files, including its subfolders. Rotation cannot start.")
            return
        self.is_running = True
        self.is_paused_for_sequence = False
        self.live_deck_name = "A"
        self.on_status(f"Rotation started, {count} track(s) shuffled from the library and its subfolders.")
        first_track = self.pick_next_valid_track()
        if first_track is None:
            self.on_status("Music library is empty. Rotation halted.")
            self.is_running = False
            return
        self.play_history.record_play(first_track)
        self.ending_beep_fired = False
        self.next_track_cued = False
        playback_path = normalize_file_loudness(first_track, self.on_status)
        self.deck_a.audio_output.setVolume(self._effective_level() * self.deck_a.manual_volume)
        self.deck_a.load_and_play(playback_path, first_track)
        self._notify_deck_update("A", first_track)
        self.on_now_playing(first_track)

    def stop(self):
        self.is_running = False
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
            self.shuffled_queue.pop(0)
            self.on_status("Hour marker passed.")
        if not self.shuffled_queue:
            if self.build_shuffled_queue() == 0:
                return None
        chosen = None
        for i, candidate in enumerate(self.shuffled_queue):
            if is_hour_marker(candidate):
                continue
            if candidate in self.pinned_tracks or not self.play_history.violates_separation(
                    candidate, self.separation_seconds):
                chosen = self.shuffled_queue.pop(i)
                break
        if chosen is None:
            self.on_status("Separation rule relaxed: no track available that fully satisfies it.")
            real = [c for c in self.shuffled_queue if not is_hour_marker(c)]
            if not real:
                return None
            chosen = real[0]
            self.shuffled_queue.remove(chosen)
        self.pinned_tracks.discard(chosen)
        self._queue_changed()
        return chosen

    def cue_next_track_if_needed(self):
        """Loads the next track, paused at its start, into the non-live deck."""
        if self.next_track_cued or not self.is_running or self.is_paused_for_sequence:
            return
        next_track = self.pick_next_valid_track()
        if next_track is None:
            self.on_status("Music library is empty. Rotation halted.")
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

    def crossfade_to_cued_deck(self):
        """Starts the cued deck, crossfades the live deck out and the cued deck in, then swaps roles."""
        live_deck = self.get_live_deck()
        cued_deck = self.get_cued_deck()
        if cued_deck.current_track_path is None:
            return

        target_level = self._effective_level()
        cued_deck.play()
        live_deck.fader.fade_to(0.0, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS,
                                 on_complete=lambda d=live_deck: self._retire_deck(d))
        cued_deck.fader.fade_to(target_level * cued_deck.manual_volume,
                                 steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS)

        self.live_deck_name = cued_deck.name
        self.next_track_cued = False
        self.ending_beep_fired = False
        self.play_history.record_play(cued_deck.current_track_path)
        self.on_now_playing(cued_deck.current_track_path)

    def get_upcoming_track_path(self):
        cued_deck = self.get_cued_deck()
        if cued_deck.current_track_path:
            return cued_deck.current_track_path
        real = [c for c in self.shuffled_queue if not is_hour_marker(c)]
        for candidate in real:
            if candidate in self.pinned_tracks or not self.play_history.violates_separation(
                    candidate, self.separation_seconds):
                return candidate
        return real[0] if real else None

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

        if self.is_running and not self.is_paused_for_sequence:
            crossfade_lead_ms = max(FADE_STEPS * FADE_INTERVAL_MS, 4000)
            if remaining_ms <= crossfade_lead_ms + 2000 and self._break_gate(deck, position_ms, duration_ms):
                return
            if not self.next_track_cued and 0 < remaining_ms <= crossfade_lead_ms + 2000:
                self.cue_next_track_if_needed()
            if self.next_track_cued and 0 < remaining_ms <= crossfade_lead_ms:
                self.crossfade_to_cued_deck()

    def begin_crossfade_out(self, on_complete):
        """Fades the live deck out ahead of a scheduled break."""
        if not self.is_running or self.is_paused_for_sequence:
            if on_complete:
                on_complete()
            return
        self.on_status("Fading music out for upcoming scheduled break.")

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
            self.is_paused_for_sequence = True
            live_deck.pause()
            if on_complete:
                on_complete()

        live_deck.fader.fade_to(0.0, on_complete=after_fade, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS)

    def resume_after_sequence(self):
        self.is_paused_for_sequence = False
        if self.is_running:
            self.on_status("Rotation resuming, fading music back in.")
            live_deck = self.get_live_deck()
            next_track = self.pick_next_valid_track()
            if next_track is None:
                self.on_status("Music library is empty. Rotation halted.")
                self.is_running = False
                return
            self.play_history.record_play(next_track)
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
        if self.is_muted:
            return
        self.is_ducked = True
        self.on_status("Ducking music under live microphone.")
        live_deck = self.get_live_deck()
        live_deck.fader.fade_to(MIC_DUCKING_LEVEL * live_deck.manual_volume,
                                 steps=DUCK_FADE_STEPS, interval_ms=DUCK_FADE_INTERVAL_MS)

    def unduck_after_microphone(self):
        self.is_ducked = False
        if self.is_muted:
            return
        self.on_status("Microphone off, bringing music back up.")
        live_deck = self.get_live_deck()
        live_deck.fader.fade_to(1.0 * live_deck.manual_volume,
                                 steps=DUCK_FADE_STEPS, interval_ms=DUCK_FADE_INTERVAL_MS)

    def set_muted(self, muted):
        self.is_muted = muted
        live_deck = self.get_live_deck()
        if muted:
            live_deck.audio_output.setVolume(0.0)
        else:
            live_deck.audio_output.setVolume(self._effective_level() * live_deck.manual_volume)

    def set_deck_volume(self, deck_name, level):
        deck = self.deck_a if deck_name == "A" else self.deck_b
        deck.set_manual_volume(level)
        if deck.name == self.live_deck_name and not self.is_muted:
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
            if not self.is_paused_for_sequence and self.is_running:
                if self.break_target is not None and not self.break_started:
                    self._take_break()
                    return
                if not self.next_track_cued:
                    self.cue_next_track_if_needed()
                self.crossfade_to_cued_deck()
        elif status == QMediaPlayer.MediaStatus.InvalidMedia and deck.name == self.live_deck_name:
            # A file the player can't read: skip it instead of going silent.
            if self.is_running and not self.is_paused_for_sequence:
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
        with source.lock:
            source.chunks.append(data)
            source.frames += len(data)
            limit = STREAM_SAMPLE_RATE * MAX_SOURCE_BUFFER_SECONDS
            while source.frames > limit and source.chunks:
                dropped = source.chunks.popleft()
                source.frames -= len(dropped)

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
        if self.is_muted:
            return
        if self.monitor_enabled and self.sink_io is not None and self.sink is not None:
            if self.sink.bytesFree() >= len(data):
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
            if self.armed_target != target and (target - now).total_seconds() <= BREAK_ARM_SECONDS:
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
        self.audio_output = QAudioOutput()
        if output_device is not None:
            self.audio_output.setDevice(output_device)
        self.player.setAudioOutput(self.audio_output)
        self.player.mediaStatusChanged.connect(self.on_media_status_changed)
        self.is_muted = False
        self.audio_output.setVolume(1.0)

        self.queue = []
        self.category_library = None  # set by the app: imported categories feed the sandwich

    def apply_output_device(self, device):
        if device is not None:
            self.audio_output.setDevice(device)

    def set_muted(self, muted):
        self.is_muted = muted
        self.audio_output.setVolume(0.0 if muted else 1.0)

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
            # Imported categories feed the break automatically: jingles and sweepers around the ad.
            jingles = list(dict.fromkeys(
                jingles + self.category_library.files_for_types(("jingle", "sweeper"))))
            ads_from_categories = self.category_library.files_for_types(("ad",))
        if sequence == "simple":
            if jingles:
                self.queue.append(random.choice(jingles))
            return

        ads = list(dict.fromkeys(scan_audio_files(self.settings.value("ad_break_folder", ""))
                                 + ads_from_categories))
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
            self.on_sequence_done()
            return
        self.on_status(f"Starting {slot} sequence, {len(self.queue)} item(s) queued.")
        self.play_next_in_queue()

    def play_next_in_queue(self):
        if not self.queue:
            self.on_status("Sequence finished.")
            self.on_sequence_done()
            return
        next_file = self.queue.pop(0)
        self.on_status(f"Playing: {os.path.basename(next_file)}")
        playback_path = normalize_file_loudness(next_file, self.on_status)
        self.player.setSource(QUrl.fromLocalFile(playback_path))
        self.player.play()

    def on_media_status_changed(self, status):
        if status == QMediaPlayer.MediaStatus.EndOfMedia:
            self.play_next_in_queue()
        elif status == QMediaPlayer.MediaStatus.InvalidMedia:
            self.on_status("Skipped an unreadable jingle or ad file.")
            self.play_next_in_queue()



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

        self.poll_timer = QTimer()
        self.poll_timer.setInterval(1000)
        self.poll_timer.timeout.connect(self._poll)

    # --- persistence ---
    FIELDS = ("stream_name", "protocol", "server_host", "server_port", "mount_point",
              "server_password", "source_password", "audio_format", "bitrate_kbps")

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
        url = f"icecast://source:{password}@{self.server_host.strip()}:{self.server_port.strip()}{mount}"

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

    def start(self, mixer, fallback_source):
        if self.state != "offline":
            return
        problem = self.validate()
        if problem:
            self.message.emit(f"{self.stream_name} cannot start: {problem}.")
            return
        use_pipe = mixer is not None and mixer.available
        if not use_pipe and not fallback_source:
            self.message.emit(f"{self.stream_name} cannot start: nothing is playing yet, and the live mix is "
                              f"unavailable ({mixer.unavailable_reason() if mixer else 'no mixer'}).")
            return
        try:
            self.process = subprocess.Popen(
                self.build_ffmpeg_command(use_pipe, fallback_source),
                stdin=subprocess.PIPE if use_pipe else subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                creationflags=SUBPROCESS_FLAGS)
        except FileNotFoundError:
            self.message.emit(f"{self.stream_name} cannot start: ffmpeg was not found.")
            return
        except Exception as e:
            self.message.emit(f"{self.stream_name} cannot start: {e}")
            return

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

    def _poll(self):
        if self.process is None:
            self.poll_timer.stop()
            return
        code = self.process.poll()
        if code is not None:
            reason = " ".join(list(self.stderr_tail)[-2:]) or f"ffmpeg stopped (exit code {code})"
            self._teardown()
            self.set_state("offline", reason)
        elif self.state == "connecting" and time.monotonic() - self.connect_started >= CONNECT_CONFIRM_SECONDS:
            self.set_state("live")
            if self.current_metadata:
                self.push_metadata(self.current_metadata)

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
        if self.state == "offline" and self.process is None:
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
                credentials = base64.b64encode(f"source:{self.source_password}".encode("utf-8")).decode("ascii")
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
        layout.addRow("Server Host:", self.host_edit)

        self.port_edit = QLineEdit(self.slot.server_port)
        layout.addRow("Server Port:", self.port_edit)

        self.mount_edit = QLineEdit(self.slot.mount_point)
        layout.addRow("Mount Point:", self.mount_edit)

        self.format_combo = QComboBox()
        self.format_combo.addItems(FORMAT_OPTIONS)
        self.format_combo.setCurrentText(self.slot.audio_format)
        layout.addRow("Format:", self.format_combo)

        self.bitrate_edit = QLineEdit(self.slot.bitrate_kbps)
        layout.addRow("Bitrate (kbps):", self.bitrate_edit)

        self.server_password_edit = QLineEdit(self.slot.server_password)
        self.server_password_edit.setEchoMode(QLineEdit.EchoMode.Password)
        layout.addRow("Server Password:", self.server_password_edit)

        self.source_password_edit = QLineEdit(self.slot.source_password)
        self.source_password_edit.setEchoMode(QLineEdit.EchoMode.Password)
        layout.addRow("Source Password:", self.source_password_edit)

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
        self.slot.audio_format = self.format_combo.currentText()
        self.slot.bitrate_kbps = self.bitrate_edit.text().strip() or "128"
        self.slot.server_password = self.server_password_edit.text()
        self.slot.source_password = self.source_password_edit.text()
        self.summary_label.setText(self.slot.summary_text())
        self.refresh_accessible_names()
        self.bank.save_all()
        self.bank.on_status(f"{self.slot.stream_name}: saved.")
        self.set_collapsed(True)
        self.edit_btn.setFocus()

    def on_state_changed(self, slot, state, reason):
        self.state_label.setText(STATE_TEXT.get(state, state))
        self.state_label.setStyleSheet(
            f"color: {STATE_COLOR.get(state, COLOR_TEXT_DIM)}; font-weight: bold;")
        busy = state != "offline"
        self.start_btn.setEnabled(not busy)
        self.stop_btn.setEnabled(busy)
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
        slot.start(self.mixer, self.get_fallback_source())

    def stop_slot(self, slot):
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
    """A record that spins while its deck has a playing track."""

    def __init__(self, deck_name, size=96):
        super().__init__()
        self.deck_name = deck_name
        self.angle = 0.0
        self.spinning = False
        self.setFixedSize(size, size)
        self.setAccessibleName(f"Deck {deck_name} record: stopped")

    def set_spinning(self, spinning):
        if spinning != self.spinning:
            self.spinning = spinning
            self.setAccessibleName(f"Deck {self.deck_name} record: {'spinning' if spinning else 'stopped'}")
            self.update()

    def tick(self):
        if self.spinning:
            self.angle = (self.angle + 6.0) % 360.0  # 200 degrees a second, about 33 rpm at the app's 30 ms tick
            self.update()

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        w = self.width()
        centre = QPointF(w / 2.0, w / 2.0)
        radius = w / 2.0 - 3
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QBrush(QColor("#0B0B0B")))
        painter.drawEllipse(centre, radius, radius)
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.setPen(QPen(QColor("#2A2A2A"), 1))
        for frac in (0.9, 0.78, 0.66, 0.54):
            painter.drawEllipse(centre, radius * frac, radius * frac)
        painter.translate(centre)
        painter.rotate(self.angle)
        label_radius = radius * 0.36
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QBrush(QColor(COLOR_ACTIVE_BLUE if self.spinning else "#555555")))
        painter.drawEllipse(QPointF(0, 0), label_radius, label_radius)
        painter.setBrush(QBrush(QColor("#F0F0F0")))
        painter.drawEllipse(QPointF(label_radius * 0.55, 0), 3.0, 3.0)  # marker dot shows the rotation
        painter.setBrush(QBrush(QColor("#0B0B0B")))
        painter.drawEllipse(QPointF(0, 0), 3.0, 3.0)
        painter.end()


QUEUE_DISPLAY_LIMIT = 300
_QUEUE_TEXT_CACHE = {}


class QueueList(QListWidget):
    """Browse with Up/Down. Ctrl+Up/Down moves a track, Delete removes it, Insert adds tracks."""

    move_requested = pyqtSignal(int, int)
    remove_requested = pyqtSignal(int)
    insert_requested = pyqtSignal()

    def __init__(self):
        super().__init__()
        self.setAccessibleName("Queue: upcoming tracks. Up and Down browse, Control Up and Down move the "
                               "selected track, Delete removes it, Insert adds tracks.")
        self.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

    def keyPressEvent(self, event):
        key = event.key()
        ctrl = bool(event.modifiers() & Qt.KeyboardModifier.ControlModifier)
        row = self.currentRow()
        if ctrl and key in (Qt.Key.Key_Up, Qt.Key.Key_Down):
            if row >= 0:
                self.move_requested.emit(row, -1 if key == Qt.Key.Key_Up else 1)
            event.accept()
            return
        if key == Qt.Key.Key_Delete:
            if row >= 0:
                self.remove_requested.emit(row)
            event.accept()
            return
        if key == Qt.Key.Key_Insert:
            self.insert_requested.emit()
            event.accept()
            return
        super().keyPressEvent(event)

    def event(self, e):
        # Stop application-wide shortcuts from swallowing the keys this list owns.
        if e.type() == QEvent.Type.ShortcutOverride:
            ctrl = bool(e.modifiers() & Qt.KeyboardModifier.ControlModifier)
            if e.key() in (Qt.Key.Key_Delete, Qt.Key.Key_Insert) or (
                    ctrl and e.key() in (Qt.Key.Key_Up, Qt.Key.Key_Down)):
                e.accept()
                return True
        return super().event(e)

    def show_queue(self, entries, select_row=None):
        row = self.currentRow() if select_row is None else select_row
        self.blockSignals(True)
        self.clear()
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
            self.addItem(f"{i + 1}. {text}")
        if len(entries) > len(shown):
            self.addItem(f"... and {len(entries) - len(shown)} more tracks")
        self.blockSignals(False)
        if entries:
            self.setCurrentRow(max(0, min(row, len(entries) - 1)))


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
    def __init__(self, app):
        super().__init__()
        self.app = app
        layout = QVBoxLayout()
        info = QLabel("Categories and spot groups: jingles, sweepers and ads. Import a folder and it is named and "
                      "typed from the folder name. They feed the scheduled break: jingle or sweeper, ad, "
                      "jingle or sweeper.")
        info.setWordWrap(True)
        layout.addWidget(info)
        self.list = QListWidget()
        self.list.setAccessibleName("Categories list")
        layout.addWidget(self.list)
        for text, handler in (("Import Category Folder (Ctrl+N)", self.import_folder),
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
            count = len(scan_audio_files(category["folder"]))
            self.list.addItem(f"{self.app.category_library.describe(category)}: {count} files")
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
        added = self.app.category_library.import_folder(folder)
        if not added:
            self.app.update_status("No audio files found in that folder, so no category was made.")
            return
        for category in added:
            self.app.normalizer.start(scan_audio_files(category["folder"]))
        names = ", ".join(f"{c['name']} ({c['type']})" for c in added)
        self.app.announce(f"Imported {names}.")

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
        choice, ok = QInputDialog.getItem(self, "Category type", "Type:", list(CATEGORY_TYPES),
                                          CATEGORY_TYPES.index(category["type"]), False)
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
        reset = QPushButton("Reset All Shortcuts to Station Playlist Defaults")
        reset.setStyleSheet(BUTTON_STYLE_CONSOLE)
        reset.clicked.connect(self.reset_all)
        layout.addWidget(reset)
        self.setLayout(layout)
        self.refresh()

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
        self.app.update_status("Shortcuts reset to the Station Playlist defaults.")



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


class SetupIntroPage(QWizardPage):
    def __init__(self):
        super().__init__()
        self.setTitle("Welcome to Vision Radio setup")
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
        self.setWindowTitle("Vision Radio Setup")
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
# Main application window
# ---------------------------------------------------------------------------

class BroadcastingApp(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Vision Radio: Professional Creator Suite")
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
        self.last_schedule_hour = datetime.now().hour
        self.rescan_counter = 0
        self.rotation_library = RotationLibrary(self.settings, on_changed=self.on_rotations_changed)
        self.rotation_schedule = RotationSchedule(self.settings, self.rotation_library)
        self.category_library = CategoryLibrary(self.settings, on_changed=self.on_categories_changed)
        self.playlist_generator = PlaylistGenerator(self.settings, self.rotation_library, self.rotation_schedule)
        self.shortcut_objects = []

        self.normalizer = NormalizeManager(self)
        self.normalizer.progress.connect(self.on_normalize_progress)
        self.normalizer.batch_done.connect(self.on_normalize_done)

        self.mixer = ProgramMixer(self.update_status)
        # Safety switch (Audio Settings tab): turn the live stream mix off if it ever
        # interferes with playback on a particular computer. Takes effect on restart.
        if str(self.settings.value("use_live_mix", "true")).lower() == "false":
            self.mixer.available = False

        self.rotation = RotationEngine(
            self.settings, self.update_status, self.on_now_playing,
            self.on_track_ending, self.on_crossfader_move, self.on_deck_update,
            normalizer=self.normalizer, output_device=output_device
        )
        self.rotation.rotation_library = self.rotation_library
        self.rotation.rotation_schedule = self.rotation_schedule
        self.rotation.on_queue_changed = self.refresh_queue_list
        self.rotation.on_rotation_swapped = self.on_rotation_swapped
        self.sequence_player = SequencePlayer(
            self.settings, self.update_status, self.on_sequence_done, output_device
        )
        self.sequence_player.category_library = self.category_library
        self.scheduler = SchedulerEngine(self.settings, self.on_crossfade_start, self.update_status)
        self.scheduler.on_break_upcoming = self.on_break_upcoming
        self.encoder_bank = EncoderBankWidget(
            self.settings, self.update_status, self.get_current_input_source,
            self.mixer, self.on_encoder_state_changed
        )
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
            self.mixer.add_source("mic", lambda: 0.0 if self.microphone.is_muted else 1.0)

        self.warning_beep = HostBeep(get_or_create_warning_beep_path(), output_device)
        self.connect_beep = HostBeep(get_or_create_connect_beep_path(), output_device)
        self.disconnect_beep = HostBeep(get_or_create_disconnect_beep_path(), output_device)

        self.check_ffmpeg_availability()
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
        self.setup_ui()
        self.setup_shortcuts()
        self.apply_processing_settings()
        self.refresh_queue_list()
        self.refresh_status_tree()
        if not self.setup_complete():
            QTimer.singleShot(400, self.run_setup_wizard)   # first launch: ask for every folder

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
            "start_rotation": self.rotation.start,
            "stop_rotation": self.rotation.stop,
            "mute_all": self.toggle_mute,
            "open_options": self.open_options,
            "new_item": self.new_item,
            "generate_now": self.generate_now,
            "say_elapsed": self.say_elapsed,
            "say_remaining": self.say_remaining,
            "say_current": self.say_current,
            "say_status": self.say_status,
            "say_hour_remaining": self.say_hour_remaining,
            "say_mute": self.say_mute,
            "say_encoders": self.say_encoders,
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
        for sid, handler in handlers.items():
            key = bindings.get(sid, "")
            if not key:
                continue
            shortcut = QShortcut(QKeySequence(key), self)
            shortcut.setContext(Qt.ShortcutContext.WindowShortcut)
            shortcut.activated.connect(handler)
            self.shortcut_objects.append(shortcut)

    # --- first-run setup wizard ---
    def setup_complete(self):
        return str(self.settings.value("setup_complete", "false")).lower() == "true"

    def run_setup_wizard(self):
        current = {key: self.settings.value(key, "") for key, _t, _d in WIZARD_STEPS}
        wizard = SetupWizard(self, current, self.playlist_generator.output_folder())
        if wizard.exec() == QDialog.DialogCode.Accepted:
            self.apply_setup(wizard.results())
        elif not self.setup_complete():
            self.update_status("Setup was not finished. It will ask again next time you open Vision Radio.")

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
                       + (", running" if rot.is_running else ", stopped"))
        if rot.is_paused_for_sequence:
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

    # --- shortcut actions ---
    def open_options(self):
        self.tabs.setCurrentWidget(self.tab_audio_scroll)
        self.output_combo.setFocus()
        self.announce("Options. Settings tab.")

    def new_item(self):
        """Ctrl+N: creates whatever belongs to the tab you are on."""
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
            text = "Rotation is stopped."
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
        row = self.queue_list.currentRow()
        index = row + 1 if row >= 0 and self.rotation.shuffled_queue else None
        for offset, path in enumerate(files):
            self.rotation.insert_queue_item(path, None if index is None else index + offset)
        self.normalizer.start(files, priority=True)
        self.announce(f"Inserted {len(files)} track(s) into the queue.")
        self.queue_list.setFocus()

    def insert_hour_marker(self):
        row = self.queue_list.currentRow()
        self.rotation.insert_queue_item(HOUR_MARKER_TOKEN, row + 1 if row >= 0 else None)
        self.announce("Hour marker inserted into the queue.")

    def refresh_queue_list(self):
        if hasattr(self, "queue_list"):
            self.queue_list.show_queue(self.rotation.queue_snapshot())
            self.queue_label.setText(f"Queue: {len(self.rotation.shuffled_queue)} tracks"
                                     + (f", rotation {self.rotation.active_rotation_name()}"
                                        if self.rotation.active_rotation_name() else ""))

    def on_queue_move(self, row, delta):
        new_row = self.rotation.move_queue_item(row, delta)
        self.queue_list.setCurrentRow(new_row)
        self.update_status(f"Moved to position {new_row + 1}.")

    def on_queue_remove(self, row):
        removed = self.rotation.remove_queue_item(row)
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
                if str(self.settings.value("playlist_autoload", "false")).lower() == "true" and self.rotation.is_running:
                    self.load_current_hour_playlist(announce=False)
            self.rescan_counter += 1
            if self.rescan_counter >= 60:
                self.rescan_counter = 0
                self.rescan_library()
            if (self.rotation.is_running and not self.rotation.is_paused_for_sequence
                    and self.rotation.break_target is None):
                now = datetime.now()
                mark = SchedulerEngine.next_mark(now)
                slot = {0: ":00", 15: ":15", 30: ":30", 45: ":45"}[mark.minute]
                if (mark - now).total_seconds() <= BREAK_ARM_SECONDS and not self.rotation.break_recently_taken(slot):
                    self.on_break_upcoming(slot, mark)
            job = self.playlist_generator.due_job()
            if job is not None:
                self.run_generation_job(job)
            # Safety net: a break that never got its turn (for example the deck was paused by hand).
            target = self.rotation.break_target
            if target is not None and (datetime.now() - target).total_seconds() > 600:
                slot = self.rotation.break_slot
                self.rotation.disarm_break()
                self.start_break(slot)
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)

    def on_vinyl_tick(self):
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
                files = self.playlist_generator.generate_full_day(job[1])
                self.announce(f"Playlists generated for the day: {len(files)} files.")
            else:
                path = self.playlist_generator.generate_hour(job[1], job[2])
                self.announce("Hour playlist generated." if path else "No rotation for that hour.")
        except Exception as e:
            _log_exception(type(e), e, e.__traceback__)
            self.update_status(f"Playlist generation failed: {e}")

    def generate_now(self):
        self.run_generation_job(("day", datetime.now().date()))

    def load_current_hour_playlist(self, announce=True):
        path = self.playlist_generator.current_hour_playlist()
        if not path:
            if announce:
                self.announce("No generated playlist for this hour yet. Choose Generate Now first.")
            return
        entries, _missing = read_m3u(path)
        count = self.rotation.load_queue_entries(entries, replace=True)
        self.announce(f"Loaded this hour's playlist: {count} entries.")

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

    def closeEvent(self, event):
        try:
            self.microphone.stop()
            self.encoder_bank.shutdown()
            self.normalizer.shutdown()
        except Exception:
            pass
        super().closeEvent(event)

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

        self.alert_label = QLabel("Alerts: none")
        self.alert_label.setAccessibleName("Alerts")
        self.alert_label.setWordWrap(True)
        self.alert_label.setStyleSheet(f"color: {COLOR_WARNING_AMBER}; font-weight: bold;")
        layout.addWidget(self.alert_label)

        self.tabs = QTabWidget()

        # --- Tab 1: Music Rotation ---
        self.tab_rotation = QWidget()
        layout_r = QVBoxLayout()

        lib_btn = QPushButton("Set Music Library Folder")
        lib_btn.setAccessibleName("Set music library folder")
        lib_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        lib_btn.clicked.connect(self.set_library_folder)
        layout_r.addWidget(lib_btn)

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

        player_display.addLayout(mixer_column)
        player_display.addLayout(self.build_deck_column("B"))
        layout_r.addLayout(player_display)

        rotation_btn_row = QHBoxLayout()
        start_rotation_btn = QPushButton("Start Rotation")
        start_rotation_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        start_rotation_btn.clicked.connect(self.rotation.start)
        rotation_btn_row.addWidget(start_rotation_btn)

        stop_rotation_btn = QPushButton("Stop Rotation")
        stop_rotation_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        stop_rotation_btn.clicked.connect(self.rotation.stop)
        rotation_btn_row.addWidget(stop_rotation_btn)
        layout_r.addLayout(rotation_btn_row)

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

        self.mute_btn = QPushButton("Mute All Audio (Ctrl+Shift+U)")
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
        for label, key in {":00 (Top)": ":00", ":15 (Past)": ":15",
                            ":30 (Half)": ":30", ":45 (To)": ":45"}.items():
            btn = QPushButton(f"Set Folder for {label}")
            btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
            btn.clicked.connect(lambda checked, k=key: self.set_jingle_folder(k))
            layout_j.addWidget(btn)

        ad_btn = QPushButton("Set Ad Break Folder")
        ad_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        ad_btn.clicked.connect(self.set_ad_break_folder)
        layout_j.addWidget(ad_btn)
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

        layout_a.addRow("Microphone/Line-In:", self.input_combo)
        layout_a.addRow("Speaker/Interface:", self.output_combo)

        self.live_mix_check = QCheckBox("Stream the live mix of music, jingles and microphone (restart to apply)")
        self.live_mix_check.setChecked(str(self.settings.value("use_live_mix", "true")).lower() != "false")
        layout_a.addRow(self.live_mix_check)

        # Playlist generation
        self.playlist_mode_combo = QComboBox()
        self.playlist_mode_combo.setAccessibleName("Playlist generation mode")
        for label, value in (("Whole day at midnight (default)", "midnight_full_day"),
                             ("Each hour, ahead of the hour", "hour_lead"),
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
        layout_a.addRow("Seconds early (0 = exactly on time):", self.playlist_lead_spin)

        self.playlist_times_edit = QLineEdit(str(self.settings.value("playlist_fixed_times", "00:00")))
        self.playlist_times_edit.setAccessibleName("Fixed generation times, hours and minutes separated by commas")
        layout_a.addRow("Fixed times (for example 00:00, 12:00):", self.playlist_times_edit)

        self.playlist_folder_label = QLabel(f"Playlist folder: {self.playlist_generator.output_folder()}")
        self.playlist_folder_label.setWordWrap(True)
        layout_a.addRow(self.playlist_folder_label)
        folder_btn = QPushButton("Choose Playlist Folder")
        folder_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        folder_btn.clicked.connect(self.choose_playlist_folder)
        layout_a.addRow(folder_btn)

        self.playlist_autoload_check = QCheckBox("Load each hour's playlist into the queue when the hour starts")
        self.playlist_autoload_check.setChecked(str(self.settings.value("playlist_autoload", "false")).lower() == "true")
        layout_a.addRow(self.playlist_autoload_check)

        wizard_btn = QPushButton("Run Setup Wizard Again")
        wizard_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        wizard_btn.clicked.connect(self.run_setup_wizard)
        layout_a.addRow(wizard_btn)

        generate_btn = QPushButton("Generate Playlists Now (Ctrl+Shift+G)")
        generate_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        generate_btn.clicked.connect(self.generate_now)
        layout_a.addRow(generate_btn)

        # Break protection
        self.break_hold_spin = QSpinBox()
        self.break_hold_spin.setRange(10, 300)
        self.break_hold_spin.setAccessibleName("Longest time to hold the end of a song for a break, in seconds")
        try:
            self.break_hold_spin.setValue(int(float(self.settings.value("break_max_hold_seconds", 90))))
        except Exception:
            self.break_hold_spin.setValue(90)
        layout_a.addRow("Hold the end of a song for a break up to (seconds):", self.break_hold_spin)

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

        # --- Tab order ---
        self.tabs.addTab(rotation_scroll, "Music Rotation")
        self.tabs.addTab(self.rotations_tab, "Rotations")
        self.tabs.addTab(self.schedule_tab, "Schedule")
        self.tabs.addTab(self.categories_tab, "Categories")
        self.tabs.addTab(self.tab_jingles, "Jingles && Scheduler")
        self.tabs.addTab(self.tab_audio_scroll, "Settings")
        self.tabs.addTab(self.shortcuts_tab, "Keyboard Shortcuts")
        self.tabs.addTab(self.encoder_bank, "Encoders / Simulcast")

        layout.addWidget(self.tabs)
        self.setLayout(layout)

    # --- Status / rotation callbacks ---
    def update_status(self, message):
        self.status_label.setText(f"Status: {message}")

    def announce(self, message):
        announce_accessible(self.alert_label, f"Alert: {message}")
        self.update_status(message)

    def on_now_playing(self, track_path):
        track_name = os.path.basename(track_path)
        self.now_playing_label.setText(f"Now Playing: {track_name}")
        self.onair_status_label.setText("On Air: music rotation playing.")
        self.refresh_live_indicators()

        upcoming_path = self.rotation.get_upcoming_track_path()
        if upcoming_path:
            self.up_next_label.setText(f"Up Next: {os.path.basename(upcoming_path)}")
        else:
            self.up_next_label.setText("Up Next: (reshuffling library)")

        # Tell every connected stream what is playing: artist, title and album.
        self.encoder_bank.push_metadata(get_track_metadata(track_path))

    def on_track_ending(self):
        self.warning_beep.play()
        self.update_status("Track ending in 5 seconds.")

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
        """Master mute: silences music, jingles and ads, and the microphone, on the
        speakers and in the stream."""
        self.is_muted = not self.is_muted
        self.rotation.set_muted(self.is_muted)
        self.sequence_player.set_muted(self.is_muted)
        self.microphone.set_muted(self.is_muted)
        if self.is_muted:
            self.mute_btn.setText("Unmute All Audio (Ctrl+Shift+U)")
            self.console_mute_label.setText("Mute: ON.")
            self.console_mute_label.setStyleSheet(f"color: {COLOR_LIVE_RED}; font-weight: bold;")
            self.announce("All audio muted.")
        else:
            self.mute_btn.setText("Mute All Audio (Ctrl+Shift+U)")
            self.console_mute_label.setText("Mute: off.")
            self.console_mute_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
            self.announce("Audio unmuted.")

    # --- Scheduler / sequence callbacks ---
    def start_break(self, slot):
        """Fade the music out (without cutting a song) and run the scheduled sequence."""
        self.rotation.begin_crossfade_out(lambda: self.play_break_sequence(slot))

    def play_break_sequence(self, slot):
        config = SLOT_CONFIG.get(slot, {"folder_key": slot, "sequence": "simple"})
        jingle_folder = self.settings.value(config["folder_key"], "")
        self.sequence_player.play_sequence(slot, config["sequence"], jingle_folder)

    def on_break_upcoming(self, slot, target):
        """About two minutes before a mark: the engine starts protecting the song on air."""
        if self.rotation.is_running and not self.rotation.is_paused_for_sequence:
            self.rotation.arm_break(target, slot, lambda s=slot: self.play_break_sequence(s))
            self.update_status(f"{slot} break coming up. The song on air will not be cut.")

    def on_crossfade_start(self, slot):
        """The clock reached the mark. If the engine is already managing this break, leave it to the engine."""
        if self.rotation.break_is_armed(slot) or self.rotation.break_recently_taken(slot):
            return
        self.start_break(slot)

    def on_sequence_done(self):
        self.rotation.resume_after_sequence()

    # --- Folder pickers: choosing a folder also starts loudness analysis right away ---
    def set_library_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Music Library Folder")
        if folder:
            self.settings.setValue("music_library_folder", folder)
            files = scan_audio_files(folder)
            self.update_status(f"Music library folder set: {folder} ({len(files)} tracks, including subfolders).")
            self.normalizer.start(files)

    def set_jingle_folder(self, key):
        folder = QFileDialog.getExistingDirectory(self, "Select Folder")
        if folder:
            self.settings.setValue(key, folder)
            files = scan_audio_files(folder)
            self.update_status(f"Jingle folder for {key} set ({len(files)} files).")
            self.normalizer.start(files)

    def set_ad_break_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Ad Break Folder")
        if folder:
            self.settings.setValue("ad_break_folder", folder)
            files = scan_audio_files(folder)
            self.update_status(f"Ad break folder set: {folder} ({len(files)} files).")
            self.normalizer.start(files)

    def save_audio_settings(self):
        self.settings.setValue("input_device", self.input_combo.currentText())
        self.settings.setValue("output_device", self.output_combo.currentText())
        self.settings.setValue("use_live_mix", "true" if self.live_mix_check.isChecked() else "false")
        self.settings.setValue("playlist_mode", self.playlist_mode_combo.currentData())
        self.settings.setValue("playlist_lead_seconds", self.playlist_lead_spin.value())
        self.settings.setValue("playlist_fixed_times", self.playlist_times_edit.text())
        self.settings.setValue("playlist_autoload", "true" if self.playlist_autoload_check.isChecked() else "false")
        self.settings.setValue("break_max_hold_seconds", self.break_hold_spin.value())
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
    install_crash_guard()
    app = QApplication(sys.argv)
    window = BroadcastingApp()
    window.show()
    sys.exit(app.exec())
