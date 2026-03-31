
# 🎥 PTZ Master (v9.0.6)

Professional TUI (Terminal User Interface) in Python for Linux to control PTZ IP cameras.

## ✨ Key Features
* **Multi-source support:** Streams via RTSP, V4L2 (USB cameras), and local video files.
* **Integrated Player:** Uses `mpv` for high-performance video rendering.
* **PTZ Control:** Interactive movement and zoom controls directly from the terminal.
* **Linux Optimized:** Designed specifically for Linux environments utilizing `termios` and `tty`.

## 🛠 Requirements
To run this tool, ensure you have the following installed:
- **Python 3.6+**
- **mpv** (video player)
- **ffprobe** (for stream analysis)
- **xdotool** (optional, for advanced window positioning)

## 🚀 Quick Start
1. Clone the repository or download `ptz-master-v9_0_6.py`.
2. Run the script:
   ```bash
   python3 ptz-master-v9_0_6.py
