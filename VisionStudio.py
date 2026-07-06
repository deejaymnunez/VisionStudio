import sys
import os
from PyQt6.QtWidgets import (QApplication, QWidget, QVBoxLayout, QPushButton, 
                             QLabel, QFileDialog, QTabWidget, QFormLayout, QComboBox)
from PyQt6.QtCore import QSettings
from PyQt6.QtMultimedia import QMediaDevices

STYLE_SHEET = """
    QWidget { background-color: #121212; color: #E0E0E0; font-family: Arial; font-size: 14px; }
    QPushButton { background-color: #007ACC; color: white; padding: 10px; border-radius: 5px; font-weight: bold; }
    QPushButton:hover { background-color: #005A9E; }
    QComboBox { background-color: #2C2C2C; color: white; padding: 5px; }
    QLabel { font-weight: bold; }
"""

class BroadcastingApp(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Vision Radio: Professional Creator Suite")
        self.resize(600, 500)
        self.setStyleSheet(STYLE_SHEET)
        self.settings = QSettings("VisionRecords", "VisionRadio")
        
        self.setup_ui()
        
    def setup_ui(self):
        layout = QVBoxLayout()
        self.tabs = QTabWidget()
        
        # Tab 1: Jingle Player
        self.tab_player = QWidget()
        layout_p = QVBoxLayout()
        for label, key in {":00 (Top)": ":00", ":15 (Past)": ":15", ":30 (Half)": ":30", ":45 (To)": ":45"}.items():
            btn = QPushButton(f"Set Folder for {label}")
            btn.clicked.connect(lambda checked, k=key: self.set_jingle_folder(k))
            layout_p.addWidget(btn)
        self.tab_player.setLayout(layout_p)
        
        # Tab 2: Audio Settings (Hardware Routing)
        self.tab_audio = QWidget()
        layout_a = QFormLayout()
        
        self.input_combo = QComboBox()
        self.output_combo = QComboBox()
        
        # Populate devices
        self.input_devices = QMediaDevices.audioInputs()
        for dev in self.input_devices:
            self.input_combo.addItem(dev.description(), dev)
            
        self.output_devices = QMediaDevices.audioOutputs()
        for dev in self.output_devices:
            self.output_combo.addItem(dev.description(), dev)
            
        # Restore saved settings
        self.input_combo.setCurrentText(self.settings.value("input_device", ""))
        self.output_combo.setCurrentText(self.settings.value("output_device", ""))
        
        layout_a.addRow("Microphone/Line-In:", self.input_combo)
        layout_a.addRow("Speaker/Interface:", self.output_combo)
        
        save_audio_btn = QPushButton("Save Audio Settings")
        save_audio_btn.clicked.connect(self.save_audio_settings)
        layout_a.addRow(save_audio_btn)
        self.tab_audio.setLayout(layout_a)
        
        self.tabs.addTab(self.tab_player, "Jingles")
        self.tabs.addTab(self.tab_audio, "Audio Settings")
        
        layout.addWidget(self.tabs)
        self.setLayout(layout)

    def set_jingle_folder(self, key):
        folder = QFileDialog.getExistingDirectory(self, "Select Folder")
        if folder: self.settings.setValue(key, folder)

    def save_audio_settings(self):
        self.settings.setValue("input_device", self.input_combo.currentText())
        self.settings.setValue("output_device", self.output_combo.currentText())
        print("Audio devices saved.")

if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = BroadcastingApp()
window.show()
    sys.exit(app.exec())