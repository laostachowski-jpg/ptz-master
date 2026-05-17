# 🎥 PTZ Master v9.0.80

Professional TUI (Terminal User Interface) in Python for Linux — multi-source video player,
PTZ IP camera controller, V4L2/USB camera support, flatbed scanner with PDF export.

Developed by Leszek Ostachowski (with Claude, DeepSeek, Gemini AI assistance)

---

## ✨ Key Features

### 📷 Camera & Video Sources
- **RTSP / ONVIF** — full PTZ pan/tilt/zoom control, presets, imaging parameters
- **DVRIP (XM)** — Dahua/XM protocol cameras
- **RTSP-only** — cameras without PTZ (view-only)
- **V4L2 / USB** — USB webcams via `/dev/video*`
- **Local files** — video file playback (MP4, MKV, AVI, …)
- **Auto-detect** — identifies camera protocol automatically

### 🖥 TUI Interface
- Full mouse + keyboard navigation, clickable buttons and menus
- Multi-camera grid view with live stream status
- Per-camera image parameter sliders (brightness, contrast, saturation, gamma, hue)
- PTZ control panel with zoom, pan, speed, presets
- MPV player control screen (seek bar, speed, A-B loop, clip extract, screenshot)
- Playlist/directory browser for file mode
- Batch operations menu (sync, test connections, export/import config, layout save)

### 🖨 Scanner (SANE)
- Scan to JPG with configurable mode, DPI, area, compression, filename numbering
- **ImageMagick PDF export** — convert scanned JPGs to A4 PDF (6 DPI presets: 72–1200 DPI + NoScale)
- Merge via `pdfunite` (primary) or `gs` fallback
- Google Translate Images quick-launch `(T)` with target language cycle `(l)`

### 🔧 Management
- Auto MAC→IP tracking (camera moved on network → auto-reconnect)
- Player watchdog with auto-restart on crash
- Session save/restore (window positions, active cameras)
- Network scanner (nmap / arp-scan / ping sweep)
- Full debug log (`logs/ptz_master_debug.log`)

---

## 🛠 Requirements

### Python
- **Python 3.6+** — no external Python packages required (stdlib only)

### Required (critical)
| Tool | Purpose | Install |
|------|---------|---------|
| `mpv` | Video player | see below |
| `ffprobe` | Stream analysis | part of `ffmpeg` |

### Optional (enables additional features)
| Tool | Feature |
|------|---------|
| `ffmpeg` | Clip extraction `[R]EC`, audio |
| `xdotool` | mpv window positioning (X11) |
| `kdotool` | mpv window positioning (KDE/Wayland) |
| `wmctrl` | Window management (X11 alternative) |
| `v4l2-ctl` | V4L2/USB camera support |
| `scanimage` | Flatbed scanner (SANE) |
| `convert` | ImageMagick — per-page JPG→PDF conversion |
| `pdfunite` | PDF merge (poppler-tools) — recommended |
| `gs` | PDF merge fallback (ghostscript) |
| `socat` | Network diagnostics |
| `ping`, `ip` | Camera network scanning |
| `nmap` | Advanced network scanner |

### Install by distro

**Debian / Ubuntu / Mint:**
```bash
sudo apt install mpv ffmpeg xdotool wmctrl v4l-utils sane-utils imagemagick poppler-utils ghostscript socat iputils-ping iproute2
```

**openSUSE:**
```bash
sudo zypper install mpv ffmpeg xdotool wmctrl v4l2-utils sane imagemagick poppler-tools ghostscript socat iputils iproute2
```

**Fedora / RHEL:**
```bash
sudo dnf install mpv ffmpeg xdotool wmctrl v4l-utils sane-backends imagemagick poppler-utils ghostscript socat iputils iproute
```

**Arch / Manjaro:**
```bash
sudo pacman -S mpv ffmpeg xdotool wmctrl v4l-utils sane imagemagick poppler ghostscript socat iputils iproute2
```

**KDE/Wayland window positioning:**
```bash
pip install kdotool
```

---

## 🚀 Quick Start

```bash
# Clone
git clone https://github.com/laostachowski-jpg/ptz-master.git
cd ptz-master
chmod +x ptz-master.py
./ptz-master.py

# Or download single file
wget https://raw.githubusercontent.com/laostachowski-jpg/ptz-master/refs/heads/main/ptz-master.py
chmod +x ptz-master.py
./ptz-master.py
```

### Command-line options
```
./ptz-master.py                    # normal start
./ptz-master.py --config FILE      # use alternate config file
./ptz-master.py --debug            # verbose debug output
./ptz-master.py --restore          # restore last saved session
./ptz-master.py --start CAM_NAME  # start on specific camera
./ptz-master.py FILE [FILE …]     # file player mode
./ptz-master.py --help             # show help
```

---

## ⌨ Key Bindings (main TUI)

| Key | Action |
|-----|--------|
| `↑↓←→` | Navigate cameras / PTZ move |
| `Enter` | Open camera control / confirm |
| `B` | Batch operations menu |
| `S` | Scanner |
| `P` | Playlist / camera list |
| `F1` | Help |
| `ESC / Q` | Exit / back |
| Mouse | Full click support on all buttons |

---

## 📁 File Structure

```
ptz-master.py          # main script (single file)
ptz_master_config.json # camera/session config (auto-created)
logs/
  ptz_master_debug.log # full debug log
scans/                 # scanner output directory (default)
```

---

## 🐛 Known Limitations

- PTZ control requires ONVIF or DVRIP protocol (RTSP-only cameras: view only)
- ImageMagick PDF→PDF merge blocked by default `policy.xml` on some distros → use `pdfunite` instead
- Window positioning requires X11 (`xdotool`) or KDE/Wayland (`kdotool`)
- Scanner requires SANE-compatible device and `scanimage`

---

## 📄 License

Free software — GPL v2. No warranties provided.

# find_dev_on_local_net.sh

## Script for Monitoring Network Devices and Managing IP Camera Mosaic in MPV

### Version:
Test v 2.2 (with autonomous MAC management and unified configuration)
### Author:
Leszek Ostachowski (with contribution from Gemini AI)

### Purpose:
This Bash script monitors the status of network devices based on their MAC addresses in the local network. It dynamically detects the IP addresses of IP cameras and uses them to create or update a video mosaic in the MPV player. If a camera is offline, a placeholder image (or video file) will be displayed in the mosaic.

### Usage:
```bash
find_dev_on_local_net.sh
find_dev_on_local_net.sh --help
### Usage:
```
# onvif_control_ptz.sh

## Bash Script for ONVIF PTZ Camera Control

### Version:
Test v 1.0 - extended URI error debugging and IP argument handling

### Author:
Leszek Ostachowski (with contributions from Gemini AI)

### Purpose:
This Bash script allows you to interact with ONVIF PTZ (Pan-Tilt-Zoom) compatible IP cameras using Bash and `curl` to send SOAP requests. It can detect camera capabilities, control movement, and manage presets. The script provides a command-line interface for common ONVIF PTZ operations.

### Usage:
```bash
onvif_control_ptz.sh [options] [command]
onvif_control_ptz.sh -help
onvif_control_ptz.sh -ip <camera_ip_address> [command]
### Usage:
```
ONVIF (Open Network Video Interface Forum)

ONVIF stands for Open Network Video Interface Forum. It is a non-profit organization founded in 2008 by Axis Communications, Bosch, and Sony. Its primary goal is to create and promote open standards for communication between video surveillance devices (such as IP cameras, recorders, and video management software) from different manufacturers.

PTZ (Pan-Tilt-Zoom)

PTZ is an acronym for three camera functions:

Pan: The camera can rotate left and right, usually 360 degrees, allowing for monitoring a wide area.

Tilt: The camera can tilt up and down, allowing for viewing objects at different heights.

Zoom: The camera can optically zoom in or out without losing quality (unlike digital zoom, which merely "stretches" the image).
