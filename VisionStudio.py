
import sys
import os
import random
import shutil
import subprocess
from PyQt6.QtWidgets import (QApplication, QWidget, QVBoxLayout, QPushButton,
                             QLabel, QFileDialog, QTabWidget, QFormLayout, QComboBox,
                             QHBoxLayout, QLineEdit, QScrollArea, QMessageBox)
from PyQt6.QtCore import QSettings, QTimer, QTime, QUrl
from PyQt6.QtMultimedia import QMediaDevices, QMediaPlayer, QAudioOutput

STYLE_SHEET = """
    QWidget { background-color: #121212; color: #E0E0E0; font-family: Arial; font-size: 14px; }
    QPushButton { background-color: #007ACC; color: white; padding: 10px; border-radius: 5px; font-weight: bold; }
    QPushButton:hover { background-color: #005A9E; }
    QComboBox, QLineEdit { background-color: #2C2C2C; color: white; padding: 5px; }
    QLabel { font-weight: bold; }
"""

SUPPORTED_AUDIO = (".mp3", ".wav", ".ogg", ".flac", ".m4a")

SLOT_CONFIG = {
    ":00": {"folder_key": "top_of_hour", "sequence": "simple"},
    ":15": {"folder_key": ":15",         "sequence": "sandwich"},
    ":30": {"folder_key": ":30",         "sequence": "simple"},
    ":45": {"folder_key": ":45",         "sequence": "sandwich"},
}

CROSSFADE_LEAD_SECONDS = 10
FADE_STEPS = 20
FADE_INTERVAL_MS = (CROSSFADE_LEAD_SECONDS * 1000) // FADE_STEPS

MAX_ENCODER_SLOTS = 24
PROTOCOL_OPTIONS = ["Icecast", "Shoutcast", "Live365"]
FORMAT_OPTIONS = ["MP3", "AAC"]


def get_ffmpeg_path():
    """
    Returns the path to FFmpeg. When the app is bundled with PyInstaller,
    FFmpeg's binary is shipped inside the same folder as the executable,
    so no separate install step is ever needed on the user's machine.
    """
    if getattr(sys, "frozen", False):
        base_path = sys._MEIPASS
    else:
        base_path = os.path.dirname(os.path.abspath(__file__))
    bundled = os.path.join(base_path, "ffmpeg", "ffmpeg.exe" if os.name == "nt" else "ffmpeg")
    if os.path.isfile(bundled):
        return bundled
    # Fall back to a system install if no bundled copy is found (e.g. during dev).
    return shutil.which("ffmpeg") or "ffmpeg"


def scan_audio_files(folder):
    if not folder or not os.path.isdir(folder):
        return []
    return [
        os.path.join(folder, f)
        for f in os.listdir(folder)
        if f.lower().endswith(SUPPORTED_AUDIO)
    ]


# ---------------------------------------------------------------------------
# Fade control
# ---------------------------------------------------------------------------

class FadeController:
    """Gradually ramps a QAudioOutput's volume up or down over time."""

    def __init__(self, audio_output, steps=FADE_STEPS, interval_ms=FADE_INTERVAL_MS):
        self.audio_output = audio_output
        self.steps = steps
        self.interval_ms = interval_ms
        self.timer = QTimer()
        self.timer.timeout.connect(self._step)
        self.current_step = 0
        self.start_vol = 1.0
        self.end_vol = 1.0
        self.on_complete = None

    def fade_to(self, target_volume, on_complete=None):
        self.timer.stop()
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
        if self.current_step >= self.steps:
            self.timer.stop()
            self.audio_output.setVolume(self.end_vol)
            if self.on_complete:
                self.on_complete()


# ---------------------------------------------------------------------------
# Rotation engine (main music library, shuffled, continuous)
# ---------------------------------------------------------------------------

class RotationEngine:
    def __init__(self, settings, on_status, on_now_playing):
        self.settings = settings
        self.on_status = on_status
        self.on_now_playing = on_now_playing

        self.player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        self.audio_output.setVolume(1.0)
        self.player.setAudioOutput(self.audio_output)
        self.player.mediaStatusChanged.connect(self.on_media_status_changed)

        self.fader = FadeController(self.audio_output)

        self.shuffled_queue = []
        self.is_paused_for_sequence = False
        self.is_running = False
        self.current_track_path = None

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
        self.audio_output.setVolume(1.0)
        self.on_status(f"Rotation started, {count} track(s) shuffled.")
        self.play_next_track()

    def stop(self):
        self.is_running = False
        self.player.stop()
        self.on_status("Rotation stopped.")

    def play_next_track(self):
        if not self.is_running or self.is_paused_for_sequence:
            return
        if not self.shuffled_queue:
            count = self.build_shuffled_queue()
            if count == 0:
                self.on_status("Music library is empty. Rotation halted.")
                self.is_running = False
                return
            self.on_status("Reshuffling library for next pass.")

        next_track = self.shuffled_queue.pop(0)
        self.current_track_path = next_track
        self.player.setSource(QUrl.fromLocalFile(next_track))
        self.audio_output.setVolume(1.0)
        self.player.play()
        self.on_now_playing(os.path.basename(next_track))

    def begin_crossfade_out(self, on_complete):
        if not self.is_running or self.is_paused_for_sequence:
            if on_complete:
                on_complete()
            return
        self.on_status("Fading music out for upcoming scheduled break.")

        def after_fade():
            self.is_paused_for_sequence = True
            self.player.pause()
            if on_complete:
                on_complete()

        self.fader.fade_to(0.0, on_complete=after_fade)

    def resume_after_sequence(self):
        self.is_paused_for_sequence = False
        if self.is_running:
            self.on_status("Rotation resuming, fading music back in.")
            self.audio_output.setVolume(0.0)
            self.play_next_track()
            self.fader.fade_to(1.0)

    def on_media_status_changed(self, status):
        if status == QMediaPlayer.MediaStatus.EndOfMedia and not self.is_paused_for_sequence:
            self.play_next_track()


# ---------------------------------------------------------------------------
# Scheduler (quarter-hour marks, crossfade lead-in)
# ---------------------------------------------------------------------------

class SchedulerEngine:
    def __init__(self, settings, on_crossfade_start, on_status):
        self.settings = settings
        self.on_crossfade_start = on_crossfade_start
        self.on_status = on_status
        self.pending_slot = None

        self.timer = QTimer()
        self.timer.setInterval(1000)
        self.timer.timeout.connect(self.check_clock)

    def start(self):
        self.timer.start()
        self.on_status("Scheduler running.")

    def stop(self):
        self.timer.stop()
        self.on_status("Scheduler stopped.")

    def check_clock(self):
        now = QTime.currentTime()
        minute = now.minute()
        second = now.second()

        if minute not in (0, 15, 30, 45):
            return

        slot = {0: ":00", 15: ":15", 30: ":30", 45: ":45"}[minute]

        if second == (60 - CROSSFADE_LEAD_SECONDS) and self.pending_slot != slot:
            self.pending_slot = slot
            self.on_status(f"{CROSSFADE_LEAD_SECONDS} seconds to {slot}, starting crossfade.")
            self.on_crossfade_start(slot)

    def get_slot_folder(self, slot):
        config = SLOT_CONFIG[slot]
        return self.settings.value(config["folder_key"], ""), config["sequence"]


# ---------------------------------------------------------------------------
# Sequence player (jingle / ad break / jingle chains)
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
        self.player.setSource(QUrl.fromLocalFile(next_file))
        self.player.play()

    def on_media_status_changed(self, status):
        if status == QMediaPlayer.MediaStatus.EndOfMedia:
            self.play_next_in_queue()


# ---------------------------------------------------------------------------
# Encoder bank (up to 24 simulcast destinations, FFmpeg-backed, bundled)
# ---------------------------------------------------------------------------

class EncoderSlot:
    def __init__(self, slot_number):
        self.slot_number = slot_number
        self.protocol = "Icecast"
        self.audio_format = "MP3"
        self.bitrate_kbps = 128
        self.server_address = ""
        self.port = ""
        self.mount_point = ""
        self.password = ""
        self.stream_name = f"Encoder {slot_number}"
        self.process = None
        self.is_streaming = False

    def build_destination_url(self):
        mount = self.mount_point if self.mount_point.startswith("/") else f"/{self.mount_point}"
        return f"icecast://source:{self.password}@{self.server_address}:{self.port}{mount}"

    def build_ffmpeg_command(self, input_source):
        codec = "libmp3lame" if self.audio_format == "MP3" else "aac"
        content_type = "audio/mpeg" if self.audio_format == "MP3" else "audio/aac"
        destination = self.build_destination_url()
        return [
            get_ffmpeg_path(),
            "-re",
            "-i", input_source,
            "-c:a", codec,
            "-b:a", f"{self.bitrate_kbps}k",
            "-content_type", content_type,
            "-f", "mp3" if self.audio_format == "MP3" else "adts",
            destination,
        ]

    def start(self, input_source, on_status):
        if not self.server_address or not self.port:
            on_status(f"{self.stream_name}: Missing server address or port.")
            return False
        try:
            command = self.build_ffmpeg_command(input_source)
            self.process = subprocess.Popen(
                command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
            )
            self.is_streaming = True
            on_status(f"{self.stream_name}: Streaming started to {self.server_address}:{self.port}.")
            return True
        except Exception as e:
            on_status(f"{self.stream_name}: Failed to start streaming. {e}")
            return False

    def stop(self, on_status):
        if self.process:
            self.process.terminate()
            self.process = None
        self.is_streaming = False
        on_status(f"{self.stream_name}: Streaming stopped.")


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
        self.protocol_combo.setAccessibleName(f"Encoder {self.slot.slot_number} protocol")
        layout.addRow("Protocol:", self.protocol_combo)

        self.format_combo = QComboBox()
        self.format_combo.addItems(FORMAT_OPTIONS)
        self.format_combo.setAccessibleName(f"Encoder {self.slot.slot_number} audio format")
        layout.addRow("Audio Format:", self.format_combo)

        self.bitrate_edit = QLineEdit(str(self.slot.bitrate_kbps))
        self.bitrate_edit.setAccessibleName(f"Encoder {self.slot.slot_number} bitrate in kilobits per second")
        layout.addRow("Bitrate (kbps):", self.bitrate_edit)

        self.server_edit = QLineEdit(self.slot.server_address)
        self.server_edit.setAccessibleName(f"Encoder {self.slot.slot_number} server address")
        layout.addRow("Server Address:", self.server_edit)

        self.port_edit = QLineEdit(self.slot.port)
        self.port_edit.setAccessibleName(f"Encoder {self.slot.slot_number} port")
        layout.addRow("Port:", self.port_edit)

        self.mount_edit = QLineEdit(self.slot.mount_point)
        self.mount_edit.setAccessibleName(f"Encoder {self.slot.slot_number} mount point")
        layout.addRow("Mount Point:", self.mount_edit)

        self.password_edit = QLineEdit(self.slot.password)
        self.password_edit.setEchoMode(QLineEdit.EchoMode.Password)
        self.password_edit.setAccessibleName(f"Encoder {self.slot.slot_number} stream password")
        layout.addRow("Stream Password:", self.password_edit)

        self.status_label = QLabel("Not streaming.")
        self.status_label.setAccessibleName(f"Encoder {self.slot.slot_number} status")
        layout.addRow("Status:", self.status_label)

        btn_row = QHBoxLayout()
        self.save_btn = QPushButton("Save Settings")
        self.save_btn.setAccessibleName(f"Save settings for encoder {self.slot.slot_number}")
        self.save_btn.clicked.connect(self.save_settings)
        btn_row.addWidget(self.save_btn)

        self.start_btn = QPushButton("Start Streaming")
        self.start_btn.setAccessibleName(f"Start streaming for encoder {self.slot.slot_number}")
        self.start_btn.clicked.connect(self.start_streaming)
        btn_row.addWidget(self.start_btn)

        self.stop_btn = QPushButton("Stop Streaming")
        self.stop_btn.setAccessibleName(f"Stop streaming for encoder {self.slot.slot_number}")
        self.stop_btn.clicked.connect(self.stop_streaming)
        btn_row.addWidget(self.stop_btn)

        layout.addRow(btn_row)
        self.setLayout(layout)

    def save_settings(self):
        self.slot.stream_name = self.name_edit.text() or f"Encoder {self.slot.slot_number}"
        self.slot.protocol = self.protocol_combo.currentText()
        self.slot.audio_format = self.format_combo.currentText()
        try:
            self.slot.bitrate_kbps = int(self.bitrate_edit.text())
        except ValueError:
            self.slot.bitrate_kbps = 128
            self.bitrate_edit.setText("128")
        self.slot.server_address = self.server_edit.text()
        self.slot.port = self.port_edit.text()
        self.slot.mount_point = self.mount_edit.text()
        self.slot.password = self.password_edit.text()
        self.on_status(f"{self.slot.stream_name}: Settings saved.")
        self.status_label.setText("Settings saved. Not streaming.")

    def start_streaming(self):
        self.save_settings()
        input_source = self.get_input_source()
        success = self.slot.start(input_source, self.on_status)
        self.status_label.setText("Streaming live." if success else "Failed to start. See status log.")

    def stop_streaming(self):
        self.slot.stop(self.on_status)
        self.status_label.setText("Not streaming.")


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

        self.add_slot_btn = QPushButton("Add Encoder")
        self.add_slot_btn.setAccessibleName("Add a new encoder slot")
        self.add_slot_btn.clicked.connect(self.add_slot)
        outer_layout.addWidget(self.add_slot_btn)

        self.count_label = QLabel(f"Encoders configured: 0 of {MAX_ENCODER_SLOTS}")
        self.count_label.setAccessibleName("Number of encoders configured")
        outer_layout.addWidget(self.count_label)

        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.slots_container = QWidget()
        self.slots_layout = QVBoxLayout()
        self.slots_container.setLayout(self.slots_layout)
        self.scroll_area.setWidget(self.slots_container)
        outer_layout.addWidget(self.scroll_area)

        self.setLayout(outer_layout)

    def add_slot(self):
        if len(self.slots) >= MAX_ENCODER_SLOTS:
            self.on_status(f"Maximum of {MAX_ENCODER_SLOTS} encoders reached.")
            return
        slot_number = len(self.slots) + 1
        slot = EncoderSlot(slot_number)
        widget = EncoderSlotWidget(slot, self.on_status, self.get_input_source)
        self.slots.append(slot)
        self.slot_widgets.append(widget)
        self.slots_layout.addWidget(widget)
        self.count_label.setText(f"Encoders configured: {len(self.slots)} of {MAX_ENCODER_SLOTS}")
        self.on_status(f"Encoder {slot_number} added.")

    def stop_all(self):
        for slot in self.slots:
            if slot.is_streaming:
                slot.stop(self.on_status)


# ---------------------------------------------------------------------------
# Main application window
# ---------------------------------------------------------------------------

class BroadcastingApp(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Vision Radio: Professional Creator Suite")
        self.resize(720, 680)
        self.setStyleSheet(STYLE_SHEET)
        self.settings = QSettings("VisionRecords", "VisionRadio")

        self.rotation = RotationEngine(self.settings, self.update_status, self.on_now_playing)
        self.sequence_player = SequencePlayer(self.settings, self.update_status, self.on_sequence_done)
        self.scheduler = SchedulerEngine(self.settings, self.on_crossfade_start, self.update_status)
        self.encoder_bank = EncoderBankWidget(self.update_status, self.get_current_input_source)

        self.check_ffmpeg_availability()
        self.setup_ui()

    def check_ffmpeg_availability(self):
        ffmpeg_path = get_ffmpeg_path()
        if not os.path.isfile(ffmpeg_path) and not shutil.which("ffmpeg"):
            QTimer.singleShot(500, lambda: self.update_status(
                "Warning: bundled FFmpeg not found. Streaming will not work until it is bundled correctly."
            ))

    def get_current_input_source(self):
        """
        Identifies what audio should be sent to the encoders.
        For now, points at whichever file is currently loaded in rotation.
        """
        return self.rotation.current_track_path or ""

    def setup_ui(self):
        layout = QVBoxLayout()
        self.tabs = QTabWidget()

        # Tab 1: Music Library & Rotation
        self.tab_rotation = QWidget()
        layout_r = QVBoxLayout()

        lib_btn = QPushButton("Set Music Library Folder")
        lib_btn.setAccessibleName("Set music library folder")
        lib_btn.clicked.connect(self.set_library_folder)
        layout_r.addWidget(lib_btn)

        self.now_playing_label = QLabel("Now Playing: (nothing yet)")
        self.now_playing_label.setAccessibleName("Now playing")
        layout_r.addWidget(self.now_playing_label)

        rotation_btns = QHBoxLayout()
        self.start_rotation_btn = QPushButton("Start Rotation")
        self.start_rotation_btn.setAccessibleName("Start music rotation")
        self.start_rotation_btn.clicked.connect(self.start_rotation)
        rotation_btns.addWidget(self.start_rotation_btn)

        self.stop_rotation_btn = QPushButton("Stop Rotation")
        self.stop_rotation_btn.setAccessibleName("Stop music rotation")
        self.stop_rotation_btn.clicked.connect(self.stop_rotation)
        rotation_btns.addWidget(self.stop_rotation_btn)
        layout_r.addLayout(rotation_btns)

        self.tab_rotation.setLayout(layout_r)

        # Tab 2: Jingle & Scheduler
        self.tab_player = QWidget()
        layout_p = QVBoxLayout()

        folder_labels = {
            "top_of_hour": "Top of Hour (:00) Jingle Folder",
            ":15": "15 Past Jingle Folder (Sandwich)",
            ":30": "30 Past Sweeper Folder",
            ":45": "45 Past Jingle Folder (Sandwich)",
            "ad_break_folder": "Ad Break Folder",
        }
        for key, label in folder_labels.items():
            btn = QPushButton(f"Set Folder: {label}")
            btn.setAccessibleName(f"Set folder for {label}")
            btn.clicked.connect(lambda checked, k=key, l=label: self.set_jingle_folder(k, l))
            layout_p.addWidget(btn)

        self.status_label = QLabel("Scheduler idle.")
        self.status_label.setAccessibleName("Scheduler status")
        layout_p.addWidget(self.status_label)

        scheduler_btns = QHBoxLayout()
        self.start_sched_btn = QPushButton("Start Scheduler")
        self.start_sched_btn.setAccessibleName("Start scheduler")
        self.start_sched_btn.clicked.connect(self.start_scheduler)
        scheduler_btns.addWidget(self.start_sched_btn)

        self.stop_sched_btn = QPushButton("Stop Scheduler")
        self.stop_sched_btn.setAccessibleName("Stop scheduler")
        self.stop_sched_btn.clicked.connect(self.stop_scheduler)
        scheduler_btns.addWidget(self.stop_sched_btn)
        layout_p.addLayout(scheduler_btns)

        self.tab_player.setLayout(layout_p)

        # Tab 3: Audio Settings (Hardware Routing)
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
        save_audio_btn.setAccessibleName("Save audio settings")
        save_audio_btn.clicked.connect(self.save_audio_settings)
        layout_a.addRow(save_audio_btn)
        self.tab_audio.setLayout(layout_a)

        # Tab 4: Encoders / Simulcast
        self.tabs.addTab(self.tab_rotation, "Music Rotation")
        self.tabs.addTab(self.tab_player, "Jingles && Scheduler")
        self.tabs.addTab(self.tab_audio, "Audio Settings")
        self.tabs.addTab(self.encoder_bank, "Encoders / Simulcast")

        layout.addWidget(self.tabs)
        self.setLayout(layout)

    # --- Music library / rotation ---
    def set_library_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Music Library Folder")
        if folder:
            self.settings.setValue("music_library_folder", folder)
            self.update_status(f"Music library set to: {folder}")

    def start_rotation(self):
        self.rotation.start()

    def stop_rotation(self):
        self.rotation.stop()

    def on_now_playing(self, track_name):
        self.now_playing_label.setText(f"Now Playing: {track_name}")

    # --- Jingles / scheduler ---
    def set_jingle_folder(self, key, label):
        folder = QFileDialog.getExistingDirectory(self, f"Select Folder for {label}")
        if folder:
            self.settings.setValue(key, folder)
            self.update_status(f"{label} set to: {folder}")

    def start_scheduler(self):
        self.scheduler.start()

    def stop_scheduler(self):
        self.scheduler.stop()

    def on_crossfade_start(self, slot):
        def after_music_faded():
            folder, sequence = self.scheduler.get_slot_folder(slot)
            if not folder or not os.path.isdir(folder):
                self.update_status(f"No folder set for {slot}, resuming music.")
                self.rotation.resume_after_sequence()
                return
            self.sequence_player.play_sequence(slot, sequence, folder)

        self.rotation.begin_crossfade_out(after_music_faded)

    def on_sequence_done(self):
        self.rotation.resume_after_sequence()

    # --- Audio settings ---
    def save_audio_settings(self):
        self.settings.setValue("input_device", self.input_combo.currentText())
        self.settings.setValue("output_device", self.output_combo.currentText())
        self.update_status("Audio devices saved.")

    def update_status(self, message):
        self.status_label.setText(message)
        print(message)

    def closeEvent(self, event):
        self.rotation.stop()
        self.scheduler.stop()
        self.encoder_bank.stop_all()
        event.accept()


if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = BroadcastingApp()
    window.show()
    sys.exit(app.exec())
