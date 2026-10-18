import sys
import os
import random
import subprocess
import tempfile
import math
import wave
import struct
import time
from PyQt6.QtWidgets import (QApplication, QWidget, QVBoxLayout, QPushButton,
                             QLabel, QFileDialog, QTabWidget, QFormLayout, QComboBox,
                             QHBoxLayout, QLineEdit, QScrollArea, QMessageBox, QSlider)
from PyQt6.QtCore import QSettings, QUrl, QTimer, Qt
from PyQt6.QtGui import QPixmap, QKeySequence, QShortcut
from PyQt6.QtMultimedia import (QMediaDevices, QMediaPlayer, QAudioOutput, QAudioInput,
                                 QMediaCaptureSession, QSoundEffect)

try:
    import mutagen
    from mutagen.id3 import ID3
    from mutagen.flac import FLAC
    from mutagen.mp4 import MP4
    MUTAGEN_AVAILABLE = True
except Exception:
    MUTAGEN_AVAILABLE = False


# ---------------------------------------------------------------------------
# FFmpeg bundling: looks for ffmpeg bundled next to the PyInstaller executable
# first, and falls back to a system-installed ffmpeg if not found, so the
# packaged app never depends on the end user having ffmpeg themselves.
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


SUPPORTED_AUDIO = (".mp3", ".wav", ".ogg", ".flac", ".m4a")

SLOT_CONFIG = {
    ":00": {"folder_key": ":00",         "sequence": "sandwich"},
    ":15": {"folder_key": ":15",         "sequence": "sandwich"},
    ":30": {"folder_key": ":30",         "sequence": "simple"},
    ":45": {"folder_key": ":45",         "sequence": "sandwich"},
}

CROSSFADE_LEAD_SECONDS = 10
FADE_STEPS = 20
FADE_INTERVAL_MS = (CROSSFADE_LEAD_SECONDS * 1000) // FADE_STEPS

# How far music ducks under the microphone while it's live, as a fraction
# of its normal volume (0.25 = music drops to 25% while mic is on).
MIC_DUCKING_LEVEL = 0.25
DUCK_FADE_STEPS = 10
DUCK_FADE_INTERVAL_MS = 30

MAX_ENCODER_SLOTS = 24
PROTOCOL_OPTIONS = ["Icecast", "Shoutcast", "Live365"]
FORMAT_OPTIONS = ["MP3", "AAC"]

# ---------------------------------------------------------------------------
# Broadcast console color palette. Modelled on the shared visual language of
# professional radio automation systems like WideOrbit and RCS Zetta: a dark
# charcoal console background, green for on-air/playing states, red for a
# live microphone or a deck that's live on air, amber for warnings, and blue
# for selected/active controls, all against bright high-contrast text.
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

# Target loudness for normalization, in LUFS. -16 LUFS is a common broadcast
# streaming target (matches typical online/podcast loudness standards).
LOUDNESS_TARGET_LUFS = -16.0
NORMALIZED_CACHE_DIR = os.path.join(tempfile.gettempdir(), "visionstudio_normalized")


def scan_audio_files(folder):
    if not folder or not os.path.isdir(folder):
        return []
    files = []
    for name in os.listdir(folder):
        if name.lower().endswith(SUPPORTED_AUDIO):
            files.append(os.path.join(folder, name))
    return files


def get_normalized_path_for(original_path):
    os.makedirs(NORMALIZED_CACHE_DIR, exist_ok=True)
    try:
        mtime = int(os.path.getmtime(original_path))
    except OSError:
        mtime = 0
    base = os.path.basename(original_path)
    safe_base = "".join(c for c in base if c.isalnum() or c in ("_", "-", "."))
    cache_name = f"{safe_base}.{mtime}.norm.wav"
    return os.path.join(NORMALIZED_CACHE_DIR, cache_name)


def normalize_file_loudness(original_path, on_status=None):
    """
    Runs the source file through FFmpeg's loudnorm filter so it plays back
    at a consistent target loudness (LOUDNESS_TARGET_LUFS), and caches the
    result so the same file isn't re-processed every time it is played.
    Returns the path to play: the normalized version on success, or the
    original file untouched if normalization fails for any reason.
    """
    if not original_path or not os.path.isfile(original_path):
        return original_path

    normalized_path = get_normalized_path_for(original_path)
    if os.path.isfile(normalized_path):
        return normalized_path

    ffmpeg_path = get_ffmpeg_path()
    command = [
        ffmpeg_path,
        "-y",
        "-i", original_path,
        "-af", f"loudnorm=I={LOUDNESS_TARGET_LUFS}:TP=-1.5:LRA=11",
        normalized_path,
    ]
    try:
        subprocess.run(
            command,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=120,
            check=True,
        )
        if on_status:
            on_status(f"Loudness normalized: {os.path.basename(original_path)}")
        return normalized_path
    except Exception as e:
        if on_status:
            on_status(f"Normalization skipped for {os.path.basename(original_path)}: {e}")
        return original_path


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


def get_or_create_warning_beep_path():
    """
    Synthesizes a short sine-wave warning beep into a cached WAV file using
    only Python's standard library (no ffmpeg needed for this one), so the
    "track ending" cue never depends on ffmpeg being available.
    """
    os.makedirs(NORMALIZED_CACHE_DIR, exist_ok=True)
    beep_path = os.path.join(NORMALIZED_CACHE_DIR, "warning_beep.wav")
    if os.path.isfile(beep_path):
        return beep_path

    framerate = 44100
    duration = 0.25
    frequency = 880.0
    amplitude = 16000
    n_frames = int(framerate * duration)

    with wave.open(beep_path, "w") as wav_file:
        wav_file.setnchannels(1)
        wav_file.setsampwidth(2)
        wav_file.setframerate(framerate)
        for i in range(n_frames):
            sample_value = int(amplitude * math.sin(2 * math.pi * frequency * (i / framerate)))
            wav_file.writeframesraw(struct.pack("<h", sample_value))

    return beep_path


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
        self.audio_output.setVolume(max(0.0, min(1.0, new_vol)))
        if self.on_progress:
            self.on_progress(self.start_vol, self.end_vol, progress)
        if self.current_step >= self.steps:
            self.timer.stop()
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
# Rotation engine: two alternating decks, crossfading like a DJ automation
# ---------------------------------------------------------------------------

class Deck:
    """
    One playback deck: its own QMediaPlayer, QAudioOutput, and FadeController.
    Two of these alternate being "live" so every rotation transition is a
    real crossfade between two independent decks, like a DJ mixer, instead
    of one player swapping tracks under a volume ramp.
    """

    def __init__(self, name, on_fade_progress=None):
        self.name = name  # "A" or "B"
        self.player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        self.audio_output.setVolume(0.0)
        self.player.setAudioOutput(self.audio_output)
        self.fader = FadeController(self.audio_output, on_progress=on_fade_progress)
        self.current_track_path = None
        self.manual_volume = 1.0  # the deck's own fader level, independent of ducking/mute

    def load_and_play(self, track_path):
        self.current_track_path = track_path
        self.player.setSource(QUrl.fromLocalFile(track_path))
        self.player.play()

    def pause(self):
        self.player.pause()

    def stop(self):
        self.player.stop()
        self.current_track_path = None

    def set_manual_volume(self, level):
        """Called from this deck's own volume fader in the UI."""
        self.manual_volume = max(0.0, min(1.0, level))


class RotationEngine:
    """
    Drives continuous music rotation across two alternating decks (A and B).
    Whichever deck is "live" plays the current track; shortly before it
    ends, the next track is cued into the other deck and the engine
    crossfades: the live deck fades down while the cued deck fades up, then
    the roles swap. Scheduled breaks, ducking, and muting all act on
    whichever deck is currently live, so callers outside this class don't
    need to know decks exist at all.
    """

    def __init__(self, settings, on_status, on_now_playing, on_track_ending=None,
                 on_crossfader_move=None, on_deck_update=None):
        self.settings = settings
        self.on_status = on_status
        self.on_now_playing = on_now_playing
        self.on_track_ending = on_track_ending
        self.on_crossfader_move = on_crossfader_move
        self.on_deck_update = on_deck_update  # on_deck_update(deck_name, track_path_or_None)

        self.deck_a = Deck("A", on_fade_progress=self._on_deck_a_fade_progress)
        self.deck_b = Deck("B", on_fade_progress=self._on_deck_b_fade_progress)
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
        self.is_running = False
        self.next_track_cued = False

        # Persistent play-history log, used to enforce the artist/title
        # separation rules across reshuffles rather than forgetting what
        # already played, Station-Playlist style.
        self.play_history = PlayHistory()
        self.separation_seconds = DEFAULT_SEPARATION_SECONDS

        # Tracks whether the end-of-track warning beep has already fired for
        # the track currently playing, so it only fires once per track.
        self.ending_beep_fired = False

        # Remembers ducking/mute state, applied to whichever deck is live.
        self.is_ducked = False
        self.is_muted = False

    # --- deck helpers ---
    def get_live_deck(self):
        return self.deck_a if self.live_deck_name == "A" else self.deck_b

    def get_cued_deck(self):
        return self.deck_b if self.live_deck_name == "A" else self.deck_a

    @property
    def current_track_path(self):
        return self.get_live_deck().current_track_path

    def _effective_level(self):
        """The target volume for the live deck given ducking/mute state, before its own manual fader is applied."""
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
        """
        During a deck-to-deck crossfade, the live deck's fade-down drives the
        crossfader position directly (0 = Deck A live, 100 = Deck B live).
        During a scheduled-break fade or mic duck, only one deck is moving,
        so the crossfader position just reflects that deck's own level.
        """
        if not self.on_crossfader_move:
            return
        # 0 = fully Deck A, 100 = fully Deck B.
        if deck_name == "A":
            if end_vol < start_vol:
                position = progress * 100  # A fading down -> sliding toward B
            else:
                position = (1 - progress) * 100 if self.live_deck_name == "A" else 100
        else:
            if end_vol < start_vol:
                position = (1 - progress) * 100  # B fading down -> sliding back toward A
            else:
                position = progress * 100 if self.live_deck_name == "B" else 0
        self.on_crossfader_move(position)

    def get_library_folder(self):
        return self.settings.value("music_library_folder", "")

    def build_shuffled_queue(self):
        files = scan_audio_files(self.get_library_folder())
        random.shuffle(files)
        self.shuffled_queue = files
        return len(files)

    def start(self):
        folder = self.get_library_folder()
        if not folder or not os.path.isdir(folder):
            self.on_status("No music library folder set. Rotation cannot start.")
            return
        count = self.build_shuffled_queue()
        if count == 0:
            self.on_status("Music library folder is empty. Rotation cannot start.")
            return
        self.is_running = True
        self.live_deck_name = "A"
        self.on_status(f"Rotation started, {count} track(s) shuffled.")
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
        self.deck_a.load_and_play(playback_path)
        self.deck_a.current_track_path = first_track
        self._notify_deck_update("A", first_track)
        self.on_now_playing(first_track)

    def stop(self):
        self.is_running = False
        self.deck_a.stop()
        self.deck_b.stop()
        self._notify_deck_update("A", None)
        self._notify_deck_update("B", None)
        self.on_status("Rotation stopped.")

    def pick_next_valid_track(self):
        """
        Pulls the next track from the shuffled queue, skipping over any that
        would break the artist/title separation rule, pulling from further
        ahead in the queue instead. If literally every remaining track would
        violate separation (tiny library), it falls back to the one that's
        been silent the longest rather than refusing to play anything.
        """
        if not self.shuffled_queue:
            count = self.build_shuffled_queue()
            if count == 0:
                return None

        for i, candidate in enumerate(self.shuffled_queue):
            if not self.play_history.violates_separation(candidate, self.separation_seconds):
                return self.shuffled_queue.pop(i)

        self.on_status("Separation rule relaxed: no track available that fully satisfies it.")
        return self.shuffled_queue.pop(0) if self.shuffled_queue else None

    def _notify_deck_update(self, deck_name, track_path):
        if self.on_deck_update:
            self.on_deck_update(deck_name, track_path)

    def cue_next_track_if_needed(self):
        """Loads the next track into the non-live (cued) deck, ready to crossfade in."""
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
        cued_deck.load_and_play(playback_path)
        cued_deck.current_track_path = next_track
        self.next_track_cued = True
        self._notify_deck_update(cued_deck.name, next_track)

    def crossfade_to_cued_deck(self):
        """Crossfades the live deck out and the cued deck in, then swaps which deck is live."""
        live_deck = self.get_live_deck()
        cued_deck = self.get_cued_deck()
        if cued_deck.current_track_path is None:
            return

        target_level = self._effective_level()
        live_deck.fader.fade_to(0.0, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS,
                                 on_complete=lambda: live_deck.stop())
        cued_deck.fader.fade_to(target_level * cued_deck.manual_volume,
                                 steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS)

        self.live_deck_name = cued_deck.name
        self.next_track_cued = False
        self.ending_beep_fired = False
        self.play_history.record_play(cued_deck.current_track_path)
        self.on_now_playing(cued_deck.current_track_path)

    def get_upcoming_track_path(self):
        """
        Returns the path of the track that will most likely play after the
        current one: whatever is cued on the other deck if a crossfade is
        already set up, otherwise the next qualifying candidate in the queue.
        """
        cued_deck = self.get_cued_deck()
        if cued_deck.current_track_path:
            return cued_deck.current_track_path
        for candidate in self.shuffled_queue:
            if not self.play_history.violates_separation(candidate, self.separation_seconds):
                return candidate
        return self.shuffled_queue[0] if self.shuffled_queue else None

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
            # Start cueing the next track with enough lead time to crossfade
            # smoothly before this one actually ends.
            crossfade_lead_ms = max(FADE_STEPS * FADE_INTERVAL_MS, 4000)
            if not self.next_track_cued and 0 < remaining_ms <= crossfade_lead_ms + 2000:
                self.cue_next_track_if_needed()
            if self.next_track_cued and 0 < remaining_ms <= crossfade_lead_ms:
                self.crossfade_to_cued_deck()

    def begin_crossfade_out(self, on_complete):
        """Fades the currently live deck down to silence ahead of a scheduled break."""
        if not self.is_running or self.is_paused_for_sequence:
            if on_complete:
                on_complete()
            return
        self.on_status("Fading music out for upcoming scheduled break.")
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
            live_deck.load_and_play(playback_path)
            live_deck.current_track_path = next_track
            self._notify_deck_update(live_deck.name, next_track)
            self.on_now_playing(next_track)
            target = self._effective_level() * live_deck.manual_volume
            live_deck.fader.fade_to(target, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS)

    def duck_for_microphone(self):
        """Lower music underneath a live microphone, keeping its relative level in mind."""
        if self.is_muted:
            return
        self.is_ducked = True
        self.on_status("Ducking music under live microphone.")
        live_deck = self.get_live_deck()
        live_deck.fader.fade_to(MIC_DUCKING_LEVEL * live_deck.manual_volume,
                                 steps=DUCK_FADE_STEPS, interval_ms=DUCK_FADE_INTERVAL_MS)

    def unduck_after_microphone(self):
        """Bring music back up to normal level once the microphone stops."""
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
            target = self._effective_level() * live_deck.manual_volume
            live_deck.audio_output.setVolume(target)

    def set_deck_volume(self, deck_name, level):
        """Called from a deck's own volume fader in the UI (0.0 to 1.0)."""
        deck = self.deck_a if deck_name == "A" else self.deck_b
        deck.set_manual_volume(level)
        if deck.name == self.live_deck_name and not self.is_muted:
            deck.audio_output.setVolume(self._effective_level() * deck.manual_volume)

    def play_pause_deck(self, deck_name):
        """Manual play/pause control for one deck, for the DJ-style transport buttons."""
        deck = self.deck_a if deck_name == "A" else self.deck_b
        if deck.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            deck.player.pause()
        else:
            deck.player.play()

    def cue_deck_to_start(self, deck_name):
        """Rewinds one deck's current track to the beginning, like a DJ cue button."""
        deck = self.deck_a if deck_name == "A" else self.deck_b
        deck.player.setPosition(0)

    def on_media_status_changed(self, status, deck):
        if status == QMediaPlayer.MediaStatus.EndOfMedia and deck.name == self.live_deck_name:
            if not self.is_paused_for_sequence and not self.next_track_cued:
                # Track ended before a crossfade was set up (very short track
                # or lead-time miscalculation) -- cue and cut over immediately
                # rather than leaving dead air.
                self.cue_next_track_if_needed()
                self.crossfade_to_cued_deck()


# ---------------------------------------------------------------------------
# Microphone engine (live mic on/off, feeds ducking)
# ---------------------------------------------------------------------------

class MicrophoneEngine:
    """
    Controls the live microphone input. Opening/closing the input device is
    what actually starts or stops the mic being "live" on air; on_mic_started
    and on_mic_stopped are used to trigger music ducking in sync with it.
    """

    def __init__(self, settings, on_status, on_mic_started, on_mic_stopped):
        self.settings = settings
        self.on_status = on_status
        self.on_mic_started = on_mic_started
        self.on_mic_stopped = on_mic_stopped

        self.capture_session = QMediaCaptureSession()
        self.audio_input = None
        self.is_live = False

    def get_selected_input_device(self):
        target_description = self.settings.value("input_device", "")
        for device in QMediaDevices.audioInputs():
            if device.description() == target_description:
                return device
        devices = QMediaDevices.audioInputs()
        return devices[0] if devices else None

    def start(self):
        if self.is_live:
            return
        device = self.get_selected_input_device()
        if device is None:
            self.on_status("No microphone/input device available.")
            return
        self.audio_input = QAudioInput(device)
        self.capture_session.setAudioInput(self.audio_input)
        self.is_live = True
        self.on_status(f"Microphone is live: {device.description()}")
        self.on_mic_started()

    def stop(self):
        if not self.is_live:
            return
        self.capture_session.setAudioInput(None)
        self.audio_input = None
        self.is_live = False
        self.on_status("Microphone stopped.")
        self.on_mic_stopped()


# ---------------------------------------------------------------------------
# Scheduler (quarter-hour marks, crossfade lead-in)
# ---------------------------------------------------------------------------

class SchedulerEngine:
    """
    Watches the clock and fires on_crossfade_start a little before each
    quarter-hour mark (:00, :15, :30, :45), giving the rotation engine time
    to fade music out before the scheduled jingle/ad sequence begins.
    """

    def __init__(self, settings, on_crossfade_start, on_status):
        self.settings = settings
        self.on_crossfade_start = on_crossfade_start
        self.on_status = on_status
        self.fired_this_minute = set()

        self.timer = QTimer()
        self.timer.timeout.connect(self.check_schedule)
        self.timer.start(1000)

    def check_schedule(self):
        now = time.localtime()
        minute = now.tm_min
        second = now.tm_sec
        key = f"{now.tm_hour}:{minute}"

        slot = None
        if minute == 0:
            slot = ":00"
        elif minute == 15:
            slot = ":15"
        elif minute == 30:
            slot = ":30"
        elif minute == 45:
            slot = ":45"

        if slot and second == 0 and key not in self.fired_this_minute:
            self.fired_this_minute.add(key)
            if len(self.fired_this_minute) > 50:
                self.fired_this_minute.clear()
            self.on_status(f"Scheduled {slot} break triggered.")
            self.on_crossfade_start(slot)


# ---------------------------------------------------------------------------
# Sequence player (jingle / ad-break chains for scheduled breaks)
# ---------------------------------------------------------------------------

class SequencePlayer:
    def __init__(self, settings, on_status, on_sequence_done):
        self.settings = settings
        self.on_status = on_status
        self.on_sequence_done = on_sequence_done

        self.player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        self.player.setAudioOutput(self.audio_output)
        self.player.mediaStatusChanged.connect(self.on_media_status_changed)

        self.queue = []

    def pick_random_file(self, folder):
        files = scan_audio_files(folder)
        if not files:
            return None
        return random.choice(files)

    def build_queue(self, sequence, jingle_folder):
        self.queue = []
        if sequence == "simple":
            f = self.pick_random_file(jingle_folder)
            if f:
                self.queue.append(f)
        elif sequence == "sandwich":
            ad_folder = self.settings.value("ad_break_folder", "")
            j1 = self.pick_random_file(jingle_folder)
            ad = self.pick_random_file(ad_folder)
            j2 = self.pick_random_file(jingle_folder)
            for item in (j1, ad, j2):
                if item:
                    self.queue.append(item)

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


# ---------------------------------------------------------------------------
# Encoder bank (up to 24 simulcast destinations, FFmpeg-backed, bundled)
# ---------------------------------------------------------------------------

class EncoderSlot:
    """Holds the configuration and running ffmpeg process for one simulcast destination."""

    def __init__(self, slot_number):
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
        self.process = None
        self.is_streaming = False

    def build_ffmpeg_command(self, input_source):
        ffmpeg_path = get_ffmpeg_path()
        codec = "libmp3lame" if self.audio_format == "MP3" else "aac"
        url = f"icecast://source:{self.source_password}@{self.server_host}:{self.server_port}{self.mount_point}"
        command = [
            ffmpeg_path, "-re", "-i", input_source,
            "-acodec", codec, "-b:a", f"{self.bitrate_kbps}k",
            "-content_type", "audio/mpeg" if self.audio_format == "MP3" else "audio/aac",
            url,
        ]
        return command

    def start(self, input_source, on_status):
        if self.is_streaming or not input_source:
            return
        try:
            command = self.build_ffmpeg_command(input_source)
            self.process = subprocess.Popen(
                command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
            )
            self.is_streaming = True
            on_status(f"{self.stream_name}: streaming started.")
        except Exception as e:
            on_status(f"{self.stream_name}: failed to start - {e}")

    def stop(self, on_status):
        if self.process:
            self.process.terminate()
            self.process = None
        self.is_streaming = False
        on_status(f"{self.stream_name}: streaming stopped.")


class EncoderSlotWidget(QWidget):
    def __init__(self, slot, on_status, get_input_source):
        super().__init__()
        self.slot = slot
        self.on_status = on_status
        self.get_input_source = get_input_source
        self.setup_ui()

    def setup_ui(self):
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
        save_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        save_btn.clicked.connect(self.save_settings)
        layout.addRow(save_btn)

        start_stop_row = QHBoxLayout()
        self.start_btn = QPushButton("Start Streaming")
        self.start_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.start_btn.clicked.connect(self.start_streaming)
        start_stop_row.addWidget(self.start_btn)

        self.stop_btn = QPushButton("Stop Streaming")
        self.stop_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        self.stop_btn.clicked.connect(self.stop_streaming)
        start_stop_row.addWidget(self.stop_btn)
        layout.addRow(start_stop_row)

        self.setLayout(layout)

    def save_settings(self):
        self.slot.stream_name = self.name_edit.text()
        self.slot.protocol = self.protocol_combo.currentText()
        self.slot.server_host = self.host_edit.text()
        self.slot.server_port = self.port_edit.text()
        self.slot.mount_point = self.mount_edit.text()
        self.slot.audio_format = self.format_combo.currentText()
        self.slot.bitrate_kbps = self.bitrate_edit.text()
        self.slot.server_password = self.server_password_edit.text()
        self.slot.source_password = self.source_password_edit.text()
        self.on_status(f"{self.slot.stream_name}: settings saved.")

    def start_streaming(self):
        input_source = self.get_input_source()
        self.slot.start(input_source, self.on_status)

    def stop_streaming(self):
        self.slot.stop(self.on_status)


class EncoderBankWidget(QWidget):
    def __init__(self, on_status, get_input_source):
        super().__init__()
        self.on_status = on_status
        self.get_input_source = get_input_source
        self.slots = []
        self.slot_widgets = []
        self.setup_ui()

    def setup_ui(self):
        outer_layout = QVBoxLayout()
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        container = QWidget()
        container_layout = QVBoxLayout()

        add_btn = QPushButton("Add Encoder Slot")
        add_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        add_btn.clicked.connect(self.add_slot)
        outer_layout.addWidget(add_btn)

        self.slots_layout = container_layout
        container.setLayout(container_layout)
        scroll.setWidget(container)
        outer_layout.addWidget(scroll)
        self.setLayout(outer_layout)

    def add_slot(self):
        if len(self.slots) >= MAX_ENCODER_SLOTS:
            self.on_status(f"Maximum of {MAX_ENCODER_SLOTS} encoder slots reached.")
            return
        slot = EncoderSlot(len(self.slots) + 1)
        self.slots.append(slot)
        widget = EncoderSlotWidget(slot, self.on_status, self.get_input_source)
        self.slot_widgets.append(widget)
        self.slots_layout.addWidget(widget)
        self.on_status(f"Encoder slot {slot.slot_number} added.")


# ---------------------------------------------------------------------------
# Main application window
# ---------------------------------------------------------------------------

class BroadcastingApp(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Vision Radio: Professional Creator Suite")
        self.resize(720, 680)
        self.setStyleSheet(MAIN_WINDOW_STYLE)
        self.settings = QSettings("VisionRecords", "VisionRadio")
        self.deck_widgets = {}  # populated by build_deck_column() for Deck A and Deck B

        self.rotation = RotationEngine(
            self.settings, self.update_status, self.on_now_playing,
            self.on_track_ending, self.on_crossfader_move, self.on_deck_update
        )
        self.sequence_player = SequencePlayer(self.settings, self.update_status, self.on_sequence_done)
        self.scheduler = SchedulerEngine(self.settings, self.on_crossfade_start, self.update_status)
        self.encoder_bank = EncoderBankWidget(self.update_status, self.get_current_input_source)
        self.microphone = MicrophoneEngine(
            self.settings, self.update_status, self.on_mic_started, self.on_mic_stopped
        )

        self.is_muted = False
        self.warning_beep = QSoundEffect()
        self.warning_beep.setSource(QUrl.fromLocalFile(get_or_create_warning_beep_path()))
        self.warning_beep.setVolume(0.6)

        if not MUTAGEN_AVAILABLE:
            QTimer.singleShot(500, lambda: self.update_status(
                "Note: mutagen isn't installed, so album artwork previews won't be available."
            ))

        self.check_ffmpeg_availability()
        self.setup_ui()
        self.setup_shortcuts()

    def check_ffmpeg_availability(self):
        ffmpeg_path = get_ffmpeg_path()
        try:
            subprocess.run([ffmpeg_path, "-version"], stdout=subprocess.DEVNULL,
                            stderr=subprocess.DEVNULL, timeout=5, check=True)
        except Exception:
            QTimer.singleShot(500, lambda: self.update_status(
                "Warning: ffmpeg was not found. Streaming, loudness normalization, and encoding "
                "will not work until it is bundled correctly."
            ))

    def get_current_input_source(self):
        """
        Identifies what audio should be sent to the encoders.
        For now, points at whichever file is currently loaded in the live deck.
        """
        return self.rotation.current_track_path or ""

    def setup_shortcuts(self):
        # Ctrl+Shift+U: global mute/unmute, usable from anywhere in the app
        # without needing to tab to a specific button -- key for screen
        # reader users who need a fast, memorable, always-available mute.
        self.mute_shortcut = QShortcut(QKeySequence("Ctrl+Shift+U"), self)
        self.mute_shortcut.activated.connect(self.toggle_mute)

    def build_deck_column(self, deck_name):
        """
        Builds one full deck panel: title, live-on-air indicator, artwork,
        track label, a vertical volume fader, and play/pause/cue transport
        buttons -- styled like a real broadcast console channel strip.
        """
        column = QVBoxLayout()

        title = QLabel(f"Deck {deck_name}")
        title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        title.setStyleSheet(f"color: {COLOR_TEXT_BRIGHT}; font-weight: bold; font-size: 14px;")
        column.addWidget(title)

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

        # Keep references so on_deck_update() and on_now_playing() can reach
        # each deck's own widgets by name.
        self.deck_widgets[deck_name] = {
            "live_indicator": live_indicator,
            "artwork_label": artwork_label,
            "track_label": track_label,
            "volume_slider": volume_slider,
        }

        return column

    def on_deck_update(self, deck_name, track_path):
        """Called whenever a deck loads a new track (or is cleared), independent of which deck is live."""
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
            if name == self.rotation.live_deck_name:
                widgets["live_indicator"].setText("\u25CF ON AIR")
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

    def setup_ui(self):
        layout = QVBoxLayout()
        self.tabs = QTabWidget()

        # --- Tab 1: Music Rotation ---
        self.tab_rotation = QWidget()
        layout_r = QVBoxLayout()

        lib_btn = QPushButton("Set Music Library Folder")
        lib_btn.setAccessibleName("Set music library folder")
        lib_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        lib_btn.clicked.connect(self.set_library_folder)
        layout_r.addWidget(lib_btn)

        # Player-style display: Deck A on the left, Deck B on the right, each
        # a real independent deck with its own artwork, volume fader, and
        # play/pause/cue transport -- a full DJ-style broadcast console. The
        # mixer console in the middle shows the crossfader and live status.
        player_display = QHBoxLayout()

        deck_a_column = self.build_deck_column("A")
        player_display.addLayout(deck_a_column)

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
        left_label = QLabel("Deck A")
        right_label = QLabel("Deck B")
        crossfader_labels.addWidget(left_label)
        crossfader_labels.addStretch()
        crossfader_labels.addWidget(right_label)
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
        self.console_mic_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        mixer_column.addWidget(self.console_mic_label)

        self.console_mute_label = QLabel("Mute: off.")
        self.console_mute_label.setAccessibleName("Console mute status")
        self.console_mute_label.setStyleSheet(f"color: {COLOR_TEXT_DIM};")
        mixer_column.addWidget(self.console_mute_label)

        player_display.addLayout(mixer_column)

        deck_b_column = self.build_deck_column("B")
        player_display.addLayout(deck_b_column)

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

        mic_row = QHBoxLayout()
        start_mic_btn = QPushButton("Start Microphone")
        start_mic_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        start_mic_btn.clicked.connect(self.microphone.start)
        mic_row.addWidget(start_mic_btn)

        stop_mic_btn = QPushButton("Stop Microphone")
        stop_mic_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        stop_mic_btn.clicked.connect(self.microphone.stop)
        mic_row.addWidget(stop_mic_btn)
        layout_r.addLayout(mic_row)

        self.mic_status_label = QLabel("Microphone: off air.")
        self.mic_status_label.setAccessibleName("Microphone status")
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

        self.tab_jingles.setLayout(layout_j)

        # --- Tab 3: Audio Settings ---
        self.tab_audio = QWidget()
        layout_a = QFormLayout()

        self.input_combo = QComboBox()
        self.output_combo = QComboBox()

        self.input_devices = QMediaDevices.audioInputs()
        for dev in self.input_devices:
            self.input_combo.addItem(dev.description(), dev)

        self.output_devices = QMediaDevices.audioOutputs()
        for dev in self.output_devices:
            self.output_combo.addItem(dev.description(), dev)

        self.input_combo.setCurrentText(self.settings.value("input_device", ""))
        self.output_combo.setCurrentText(self.settings.value("output_device", ""))

        layout_a.addRow("Microphone/Line-In:", self.input_combo)
        layout_a.addRow("Speaker/Interface:", self.output_combo)

        save_audio_btn = QPushButton("Save Audio Settings")
        save_audio_btn.setStyleSheet(BUTTON_STYLE_CONSOLE)
        save_audio_btn.clicked.connect(self.save_audio_settings)
        layout_a.addRow(save_audio_btn)
        self.tab_audio.setLayout(layout_a)

        # --- Tab 4: Encoders / Simulcast ---
        self.tab_encoders = self.encoder_bank

        self.tabs.addTab(self.tab_rotation, "Music Rotation")
        self.tabs.addTab(self.tab_jingles, "Jingles && Scheduler")
        self.tabs.addTab(self.tab_audio, "Audio Settings")
        self.tabs.addTab(self.tab_encoders, "Encoders / Simulcast")

        layout.addWidget(self.tabs)
        self.setLayout(layout)

    # --- Status / rotation callbacks ---
    def update_status(self, message):
        self.status_label.setText(f"Status: {message}")

    def on_now_playing(self, track_path):
        # Per-deck artwork and track-name labels are kept current by
        # on_deck_update(), fired whenever a deck loads a track. This just
        # updates the shared mixer console readout and which deck's
        # "ON AIR" indicator is lit.
        track_name = os.path.basename(track_path)
        self.now_playing_label.setText(f"Now Playing: {track_name}")
        self.onair_status_label.setText("On Air: music rotation playing.")
        self.refresh_live_indicators()

        upcoming_path = self.rotation.get_upcoming_track_path()
        if upcoming_path:
            self.up_next_label.setText(f"Up Next: {os.path.basename(upcoming_path)}")
        else:
            self.up_next_label.setText("Up Next: (reshuffling library)")

    def on_track_ending(self):
        self.warning_beep.play()
        self.update_status("Track ending in 5 seconds.")

    def on_crossfader_move(self, position_0_to_100):
        self.crossfader_slider.setValue(int(round(position_0_to_100)))

    # --- Microphone ---
    def start_microphone(self):
        self.microphone.start()

    def stop_microphone(self):
        self.microphone.stop()

    def on_mic_started(self):
        self.mic_status_label.setText("Microphone: LIVE on air.")
        self.onair_status_label.setText("On Air: microphone LIVE, music ducked.")
        self.console_mic_label.setText("Mic: LIVE.")
        self.rotation.duck_for_microphone()

    def on_mic_stopped(self):
        self.mic_status_label.setText("Microphone: off air.")
        self.onair_status_label.setText("On Air: music rotation playing.")
        self.console_mic_label.setText("Mic: off air.")
        self.rotation.unduck_after_microphone()

    def toggle_mute(self):
        self.is_muted = not self.is_muted
        self.rotation.set_muted(self.is_muted)
        if self.is_muted:
            self.mute_btn.setText("Unmute All Audio (Ctrl+Shift+U)")
            self.console_mute_label.setText("Mute: ON.")
            self.update_status("All audio muted.")
        else:
            self.mute_btn.setText("Mute All Audio (Ctrl+Shift+U)")
            self.console_mute_label.setText("Mute: off.")
            self.update_status("Audio unmuted.")

    # --- Scheduler / sequence callbacks ---
    def on_crossfade_start(self, slot):
        def after_music_faded():
            config = SLOT_CONFIG.get(slot, {"folder_key": slot, "sequence": "simple"})
            jingle_folder = self.settings.value(config["folder_key"], "")
            self.sequence_player.play_sequence(slot, config["sequence"], jingle_folder)
        self.rotation.begin_crossfade_out(after_music_faded)

    def on_sequence_done(self):
        self.rotation.resume_after_sequence()

    # --- Folder pickers ---
    def set_library_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Music Library Folder")
        if folder:
            self.settings.setValue("music_library_folder", folder)
            self.update_status(f"Music library folder set: {folder}")

    def set_jingle_folder(self, key):
        folder = QFileDialog.getExistingDirectory(self, "Select Folder")
        if folder:
            self.settings.setValue(key, folder)
            self.update_status(f"Jingle folder for {key} set.")

    def set_ad_break_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Ad Break Folder")
        if folder:
            self.settings.setValue("ad_break_folder", folder)
            self.update_status(f"Ad break folder set: {folder}")

    def save_audio_settings(self):
        self.settings.setValue("input_device", self.input_combo.currentText())
        self.settings.setValue("output_device", self.output_combo.currentText())
        self.update_status("Audio devices saved.")


if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = BroadcastingApp()
    window.show()
    sys.exit(app.exec())
