# 🎥 PTZ Master

Professional TUI (Terminal User Interface) in Python for Linux to control PTZ IP cameras.
Developed by Leszek Ostachowski with Gemini AI assistance.

## ✨ Key Features
* **Multi-source support:** Streams via RTSP, V4L2 (USB cameras), and local video files.
* **Integrated Player:** Uses `mpv` for high-performance video rendering.
* **PTZ Control:** Interactive movement and zoom controls directly from the terminal.
* **Linux Optimized:** Designed specifically for Linux environments utilizing `termios` and `tty`.
* **Automatic Logging:** Logs are stored in a local `logs/` directory for easy debugging.

## 🛠 Requirements
To run this tool, ensure you have the following installed:
- **Python 3.6+**
- **mpv** (video player)
- **ffprobe** (for stream analysis)
- **xdotool** (optional, for advanced window positioning)

## 🚀 Quick Start
1. Clone the repository:
   ```bash

   git clone https://github.com/laostachowski-jpg/ptz-master.git

   cd ptz-master

   ./ptz-master.py
