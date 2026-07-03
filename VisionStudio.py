import sys
import json
import os
import datetime
from PyQt6.QtWidgets import (QApplication, QWidget, QVBoxLayout, QPushButton, 
                             QLabel, QFileDialog, QTabWidget, QLineEdit, QFormLayout)
from PyQt6.QtCore import Qt, QTimer, QUrl
from PyQt6.QtMultimedia import QMediaPlayer, QAudioOutput

# Accessible Color Palette
STYLE_SHEET = """
    QWidget { background-color: #121212; color: #E0E0E0; font-family: Arial; font-size: 14px; }
    QPushButton { background-color: #007ACC; color: white; padding: 10px; border-radius: 5px; font-weight: bold; }
    QPushButton:hover { background-color: #005A9E; }
    QLineEdit { background-color: #2C2C2C; border: 1px solid #555; padding: 5px; color: white; }
    QLabel { font-weight: bold; }
    QTabWidget::pane { border: 1px solid #333; }
"""

class BroadcastingApp(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Vision Radio: Professional Creator Suite")
        self.resize(600, 500)
        self.setStyleSheet(STYLE_SHEET)
        
        self.rotation_file = "rotation.json"
        self.schedule = {":00": "", ":15": "", ":30": "", ":45": ""}
        self.load_rotation()
        
        self.setup_ui()
        
    def setup_ui(self):
        layout = QVBoxLayout()
        self.tabs = QTabWidget()
        
        # Tab 1: Broadcast
        self.tab_broadcast = QWidget()
        layout_b = QVBoxLayout()
        self.status = QLabel("Status: System Ready")
        layout_b.addWidget(self.status)
        self.tab_broadcast.setLayout(layout_b)
        
        # Tab 2: Rotation Creator (Accessible Input Form)
        self.tab_creator = QWidget()
        layout_c = QFormLayout()
        self.inputs = {}
        for time_slot in [":00", ":15", ":30", ":45"]:
            edit = QLineEdit(self.schedule.get(time_slot, ""))
            layout_c.addRow(f"Jingle at {time_slot}:", edit)
            self.inputs[time_slot] = edit
            
        save_btn = QPushButton("SAVE ROTATION")
        save_btn.clicked.connect(self.save_rotation)
        layout_c.addRow(save_btn)
        self.tab_creator.setLayout(layout_c)
        
        self.tabs.addTab(self.tab_broadcast, "Broadcast")
        self.tabs.addTab(self.tab_creator, "Rotation Creator")
        layout.addWidget(self.tabs)
        self.setLayout(layout)

    def save_rotation(self):
        for time_slot, edit in self.inputs.items():
            self.schedule[time_slot] = edit.text()
        with open(self.rotation_file, 'w') as f:
            json.dump(self.schedule, f)
        self.status.setText("Rotation Saved Successfully.")

    def load_rotation(self):
        if os.path.exists(self.rotation_file):
            with open(self.rotation_file, 'r') as f:
                self.schedule = json.load(f)

if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = BroadcastingApp()
    window.show()
sys.exit(app.exec())