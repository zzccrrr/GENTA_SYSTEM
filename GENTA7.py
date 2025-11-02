import google.generativeai as genai
import os
import time
import docx
import random
import re
import csv
import mysql.connector
from mysql.connector import Error
from datetime import datetime
from os import environ
environ['PYGAME_HIDE_SUPPORT_PROMPT'] = '1'
import pygame
import requests
from pydub import AudioSegment
from google.cloud import speech, translate_v2, texttospeech_v1
import threading
import sys
import os.path
import shutil
import subprocess
import io
import urllib.parse
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
import wave
import struct
# By default prefer the ESP LAN IP for playback uploads. If you need to use a public tunnel, set
# the `GENTA_ESP_PLAYBACK_IP` environment variable to the ngrok hostname (or other reachable host).
esp_playback_host = os.environ.get('GENTA_ESP_PLAYBACK_IP', '192.168.50.62')
ARDUINO_DATA_DIR = r"c:\Users\vonti\OneDrive\Desktop\GENTA SYS\ARDUINO\GENTA2\data"

# OPTIMIZATION: Global HTTP session for connection pooling (reuse connections)
_http_session = requests.Session()
_http_session.headers.update({
    'ngrok-skip-browser-warning': 'true',
    'User-Agent': 'GENTA-System/1.0'
})

# OPTIMIZATION: Thread pool for parallel operations
_thread_pool = ThreadPoolExecutor(max_workers=3)

# OPTIMIZATION: Cache ffmpeg path lookup
_cached_ffmpeg_path = None

def _get_ffmpeg_path():
    """Cached ffmpeg path lookup to avoid repeated filesystem searches."""
    global _cached_ffmpeg_path
    if _cached_ffmpeg_path is None:
        _cached_ffmpeg_path = shutil.which('ffmpeg') or shutil.which('ffmpeg.exe') or ''
    return _cached_ffmpeg_path if _cached_ffmpeg_path else None

# Directory where repeated/auto-play audio files may be dropped. We'll move processed files
# into a `processed` subfolder after we answer so they don't retrigger.
REPEAT_AUDIO_DIR = r"C:\Users\vonti\OneDrive\Desktop\GENTA SYS\RepeatAudio"
# Select whether to fetch recordings via the local proxy (Flask/ngrok) or directly from the ESP.
# If GENTA_USE_PROXY is set to 1/true/yes we will download from `audio_raw_url` (default: http://localhost:5000/recording.wav)
# Otherwise we will contact the ESP directly at GENTA_ESP_RECORD_IP.
USE_PROXY = os.environ.get('GENTA_USE_PROXY', '1').lower() in ('1', 'true', 'yes')
if USE_PROXY:
    esp_record_host = None
else:
    esp_record_host = os.environ.get('GENTA_ESP_RECORD_IP', '192.168.50.62')
BAKurl_state = "https://nonbasic-bob-inimical.ngrok-free.dev/download/state.txt" # TESTING IP ADDRESS NG STATE FILE
BAKaudio_raw_url = "https://nonbasic-bob-inimical.ngrok-free.dev/download/recording.wav" # IP ADDRESS NG RECORDING FILE
url_state = "https://nonbasic-bob-inimical.ngrok-free.dev/state.txt" # FIXED: removed /download/ prefix
audio_raw_url = "https://nonbasic-bob-inimical.ngrok-free.dev/download_recording" # FIXED: Use correct path (389KB file found!)
student_id_url = "https://nonbasic-bob-inimical.ngrok-free.dev/student_id.txt" # URL to get the current student's ID
os.environ['GOOGLE_APPLICATION_CREDENTIALS'] = r"GoogleCloud\key.json"

genai.configure(api_key='AIzaSyDyyl36Jr0RD3fQy6cPfdi69hYQurJUtQU')

model = genai.GenerativeModel(model_name="gemini-2.5-flash")


ctime = datetime.now()
ftime = str(ctime.strftime("%Y-%m-%d %H:%M:%S"))
file_path= r"uploads\Math1.txt"
conversation_file_path = r"QUIZ File\conversation_log.txt"
output_docx_path= r'uploads\analysis_result.docx'
output_docx_tailoredmodule_path= r'uploads\tailored_module.docx'
audio_raw_path = r"uploads\Recording.wav"
audio_converted_path = r"uploads\Recording_Converted.wav"
audio_mono_path = r"uploads\Recording_Mono.wav"

# Current session student/teacher context (set at GENTA startup after LRN prompt)
CURRENT_STUDENT_ID = None
CURRENT_TEACHER_ID = None
CURRENT_TEACHER_NAME = None
CURRENT_STUDENT_NAME = None

# Global flag: True after startup cleanup completes (prevents re-clearing during session)
_STARTUP_CLEANUP_DONE = False

# State monitoring flags
_STATE_CHANGE_REQUESTED = False
_STATE_MONITOR_ACTIVE = False
_CURRENT_STATE = "0"

def record_and_transcribe(esp_host: str = None, audio_raw_path_local: str = None, audio_mono_local: str = None,
                          poll_for_recording: bool = True, max_poll_seconds: int = 30, use_english: bool = False) -> tuple:
    """Poll /size on the ESP (if esp_host provided), download recording.wav and transcode to 16k mono WAV suitable for Google STT.
    Returns: (transcript_text, forced_timeout)
    This is adapted from the QUIZZER implementation to share the same robust logic.

    Changes from the original:
    - Deletes old recording.wav on remote (ESP/proxy) and local before polling
    - If a quick HEAD to `audio_raw_url` succeeds we skip polling and download immediately.
    - `poll_for_recording` can be set False to skip polling entirely and attempt an immediate download.
    - `max_poll_seconds` default reduced (30s) to avoid long blocking; adjust if you need longer waits.
    - `use_english` when True, uses English model for better digit recognition (e.g., for LRN)
    """
    if audio_raw_path_local is None:
        audio_raw_path_local = audio_raw_path
    if audio_mono_local is None:
        audio_mono_local = audio_mono_path

    forced_timeout = False

    # If esp_host not provided, attempt to derive it from audio_raw_url.
    # However: if audio_raw_url points to a local proxy (Flask/ngrok) we should
    # NOT derive esp_host (which would cause the code to use /recording.wav on
    # the proxy). Detect common proxy paths (download, download_recording)
    # or localhost hostnames and prefer using audio_raw_url directly.
    if not esp_host:
        try:
            p = urllib.parse.urlparse(audio_raw_url)
            # If the URL path looks like a proxy endpoint, keep esp_host=None so
            # download_url will use audio_raw_url directly.
            is_proxy_path = False
            if p.path:
                lower_path = p.path.lower()
                if 'download' in lower_path or 'recording' in lower_path:
                    is_proxy_path = True
            if p.hostname in ('localhost', '127.0.0.1') and is_proxy_path:
                esp_host = None
            else:
                # Only derive esp_host when the audio_raw_url appears to point
                # directly at the ESP device (not a proxy).
                esp_host = p.netloc if not is_proxy_path else None
        except Exception:
            esp_host = None

    # === RECORDING LIFECYCLE: Clear at startup + after each transcription ===
    # 1. Startup cleanup (GENTA function): Clears old recordings from previous sessions
    # 2. Wait for new recording: No clearing before download (prevents premature deletion)
    # 3. After transcription: Clear remote recording to prepare for next interaction
    print("record_and_transcribe: Waiting for recording...")

    # Decide download URL: prefer ESP host if provided (matches QUIZZER behavior)
    if esp_host:
        download_url = f'http://{esp_host}/recording.wav'
    else:
        download_url = audio_raw_url

    # OPTIMIZATION: Quick connectivity check to fail fast if ESP is offline
    if esp_host:
        try:
            # OPTIMIZATION: Use session and reduced timeout (0.8s instead of 1s)
            test_response = _http_session.head(f'http://{esp_host}/', timeout=0.8)
            print(f"ESP connectivity check: {test_response.status_code}")
        except Exception as conn_err:
            print(f"WARNING: ESP at {esp_host} appears unreachable: {conn_err}")
            print(f"Will attempt fallback to proxy if available: {audio_raw_url}")
            # If ESP is unreachable and we have a different proxy URL, prefer the proxy
            if audio_raw_url and audio_raw_url != download_url:
                print(f"Switching to proxy URL for this request")
                download_url = audio_raw_url
                esp_host = None  # Disable ESP-specific polling

    # === NEW: Immediate-download optimization for tunnel/ESP IP ===
    # Check if download_url is from known-fast endpoints (public tunnel or ESP IP)
    # and if a recording is immediately available, download it right away.
    is_tunnel_or_esp = False
    try:
        parsed = urllib.parse.urlparse(download_url)
        hostname = parsed.hostname or ''
        # Detect ngrok-style tunnels or direct ESP IP
        if 'ngrok' in hostname.lower() or hostname.startswith('192.168.') or hostname.startswith('10.'):
            is_tunnel_or_esp = True
    except Exception:
        is_tunnel_or_esp = False
    
    quick_ready = False
    # DISABLED: Fast-path check causes issues with old recordings
    # We ALWAYS want to wait for a NEW recording, not download whatever's there
    # if is_tunnel_or_esp and poll_for_recording:
    #     # Fast-path: try immediate HEAD check to see if file is ready
    #     print(f"record_and_transcribe: Detected tunnel/ESP endpoint ({download_url}), attempting immediate check...")
    #     try:
    #         # OPTIMIZATION: Use session for connection reuse
    #         h1 = _http_session.head(download_url, timeout=1.5)  # Reduced from 2s
    #         if h1.status_code == 200:
    #             cl1 = h1.headers.get('content-length')
    #             # OPTIMIZATION: Reduced micro-stabilization delay from 0.2s to 0.1s
    #             if cl1 and cl1.isdigit() and int(cl1) > 100:
    #                 time.sleep(0.1)
    #                 h2 = _http_session.head(download_url, timeout=1.5)
    #                 cl2 = h2.headers.get('content-length')
    #                 if cl2 and cl1 == cl2:
    #                     print(f"record_and_transcribe: File ready immediately (size={cl1}), skipping stabilization poll.")
    #                     quick_ready = True
    #     except Exception as e:
    #         print(f"Fast-path HEAD check failed: {e}")
    #         quick_ready = False

    # We'll decide whether to poll for recording completion. Polling (poll_for_recording=True)
    # should wait until the file size stabilizes (or the device asserts readiness via /ready_header)
    # to avoid downloading an in-progress/partial file.
    baseline_size = 0

    if not poll_for_recording or quick_ready:
        # Caller asked to skip polling OR fast-path detected ready file; proceed to download immediately.
        baseline_size = 0
    else:
        baseline_size = 0
        if esp_host:
            try:
                last = None
                # Get baseline file size (should be 0 if cleared properly, or old file size)
                for _trial in range(3):  # Increased from 2 to 3 for more reliable baseline
                    try:
                        r = _http_session.get(f'http://{esp_host}/size', timeout=1.5)
                        cur = int(r.text)
                    except Exception:
                        cur = last if last is not None else 0
                    if last is not None and cur == last:
                        baseline_size = cur
                        break
                    last = cur
                    time.sleep(0.15)  # Slightly longer delay for stability
                if baseline_size == 0:
                    baseline_size = last if last is not None else 0
                    
                # If baseline is large (old file still there), we MUST see size change
                if baseline_size > 1000:
                    print(f"⚠ WARNING: Baseline size is {baseline_size} bytes (old recording detected)")
                    print("Waiting for size to change to detect NEW recording...")
            except Exception:
                baseline_size = 0
        else:
            # No esp_host (we're using a proxy URL). Use HEAD content-length polling
            try:
                last = None
                # Get baseline via HEAD requests
                for _trial in range(3):  # Increased from 2 to 3
                    try:
                        h = _http_session.head(download_url, timeout=2.5)  # Use session
                        cl = h.headers.get('content-length')
                        cur = int(cl) if cl and cl.isdigit() else None
                    except Exception:
                        cur = last
                    if last is not None and cur == last and cur is not None:
                        baseline_size = cur
                        break
                    last = cur
                    time.sleep(0.15)
                if baseline_size == 0 and last is not None:
                    baseline_size = last if isinstance(last, int) else 0
                    
                # Warn if old file detected
                if baseline_size and baseline_size > 1000:
                    print(f"⚠ WARNING: Baseline size is {baseline_size} bytes (old recording detected)")
                    print("Waiting for size to change to detect NEW recording...")
            except Exception:
                baseline_size = 0

    seen_started = False
    recording_start_time = None
    ANSWER_TIMEOUT = 30
    previous_size = baseline_size
    stable_count = 0
    poll_start = time.time()
    max_poll_seconds = 60  # Reduced from 120s to 60s for faster timeout
    
    # ENHANCED: Store the baseline size to detect NEW recordings (must be different from cleared state)
    initial_baseline = baseline_size
    print(f"Initial baseline size after clearing: {initial_baseline}")
    
    # SMART WAIT: Give ESP32 brief time to start recording, but check for readiness
    print("Waiting for recording to be ready (checking every 0.5s)...")
    wait_start = time.time()
    max_initial_wait = 5.0  # Maximum 5 seconds initial wait
    
    while (time.time() - wait_start) < max_initial_wait:
        # Quick check if recording has started
        try:
            if esp_host:
                size_resp = _http_session.get(f'http://{esp_host}/size', timeout=0.5)
                check_size = int(size_resp.text)
                if check_size > baseline_size + 1000:  # Recording has started with substantial data
                    print(f"✓ Recording ready early! ({time.time() - wait_start:.1f}s)")
                    break
        except Exception:
            pass
        time.sleep(0.5)  # Check every 0.5 seconds
    else:
        # Completed full wait without early detection
        print(f"Initial wait completed ({max_initial_wait}s)")

    # If we can poll /size or HEAD, wait for recording to start and stabilize
    if poll_for_recording:
        while True:
            # CHECK STATE CHANGE during polling loop
            if _STATE_CHANGE_REQUESTED:
                print("\n[record_and_transcribe] State change detected during polling - aborting wait")
                return "", False
            
            # OPTIMIZATION: Check /status first (faster, doesn't interfere with file operations)
            # Only check /size when recording is actually in progress
            recording_active = False
            if esp_host:
                try:
                    status_resp = _http_session.get(f'http://{esp_host}/status', timeout=1.0)
                    if status_resp.status_code == 200:
                        recording_active = (status_resp.text.strip() == "recording")
                except Exception as e:
                    print(f"Status check failed: {e}")
                    recording_active = False
            
            # If recording is NOT active, wait longer between checks to reduce ESP32 load
            if not recording_active and not seen_started:
                print(".", end="", flush=True)
                time.sleep(0.5)  # FASTER: Check every 0.5 second when idle
                elapsed = time.time() - poll_start
                if elapsed > max_poll_seconds:
                    print(f"\n⏰ Timeout: No recording started within {max_poll_seconds}s")
                    forced_timeout = True
                    break
                continue
            
            # Recording is active or we've already seen it start - check size
            try:
                if esp_host:
                    try:
                        r = _http_session.get(f'http://{esp_host}/size', timeout=1.5)
                        current_size = int(r.text)
                    except Exception:
                        current_size = previous_size
                else:
                    # Use HEAD content-length for proxy-hosted recordings
                    try:
                        h = _http_session.head(download_url, timeout=2.5)
                        cl = h.headers.get('content-length')
                        current_size = int(cl) if cl and cl.isdigit() else previous_size
                    except Exception:
                        current_size = previous_size
            except Exception:
                current_size = previous_size

            if not seen_started:
                # ENHANCED: Detect NEW recording by size change from baseline
                # Case 1: Baseline was 0 (cleared) - any file > 100 bytes is new
                # Case 2: Baseline was large (old file) - size must CHANGE (increase or decrease to ~44 bytes for new header)
                recording_detected = False
                
                if baseline_size == 0:
                    # File was cleared, any new data means recording started
                    if current_size > 100:
                        recording_detected = True
                        print(f"✓ NEW recording detected! Size: 0 → {current_size}")
                else:
                    # Old file was present, look for size CHANGE
                    # New recording typically starts with WAV header (~44 bytes) then grows
                    if current_size != baseline_size:
                        if current_size < 1000:
                            # Size dropped (file cleared and restarted with small header)
                            recording_detected = True
                            print(f"✓ NEW recording detected! Size dropped: {baseline_size} → {current_size} (file restarted)")
                        elif current_size > baseline_size + 5000:
                            # Size increased significantly (new recording appending)
                            recording_detected = True
                            print(f"✓ NEW recording detected! Size increased: {baseline_size} → {current_size}")
                
                if recording_detected:
                    seen_started = True
                    stable_count = 0
                    previous_size = current_size
                else:
                    # CHECK STATE CHANGE during wait for recording start
                    if _STATE_CHANGE_REQUESTED:
                        print("\n[record_and_transcribe] State change detected while waiting for recording - aborting")
                        return "", False
                    
                    if time.time() - poll_start > max_poll_seconds:
                        print(f"record_and_transcribe: timed out after {max_poll_seconds}s waiting for NEW recording")
                        print(f"(Baseline: {baseline_size}, Current: {current_size})")
                        return "", False
                    time.sleep(0.7)  # FASTER: 0.7 seconds between checks
                    continue

            if recording_start_time is None:
                recording_start_time = time.time()

            if current_size != previous_size:
                previous_size = current_size
                stable_count = 0
            else:
                stable_count += 1

            # If the recording has been growing for too long without stop, enforce an upper bound
            if recording_start_time is not None and (time.time() - recording_start_time) > ANSWER_TIMEOUT:
                try:
                    if esp_host:
                        _http_session.get(f'http://{esp_host}/stop', timeout=1.5)
                except Exception:
                    pass
                forced_timeout = True
                return "", forced_timeout

            # CRITICAL: Check /status endpoint FIRST to see if ESP32 stopped recording
            if esp_host and seen_started:
                try:
                    status_resp = _http_session.get(f'http://{esp_host}/status', timeout=1.5)
                    if status_resp.status_code == 200 and status_resp.text.strip() == 'idle':
                        print("✓ ESP32 reports recording stopped (status=idle)")
                        # Wait brief moment for file to finalize
                        time.sleep(0.5)
                        break
                except Exception:
                    pass  # Status endpoint not available, fall back to size checking

            # Fall back to size stability check if status endpoint not available
            if stable_count >= 3:  # Increased from 2 to 3 for more certainty
                time.sleep(0.3)
                # allow header finalization
                ready = False
                ready_start = time.time()
                max_ready_wait = 4
                while time.time() - ready_start < max_ready_wait:
                    try:
                        if esp_host:
                            rr = _http_session.get(f'http://{esp_host}/ready_header', timeout=1.2)
                            if rr.status_code == 200 and rr.text.strip() == '1':
                                ready = True
                                break
                        else:
                            # Try proxy-specific ready header if present
                            rr = _http_session.get(download_url + '.ready', timeout=1.2)
                            if rr.status_code == 200 and rr.text.strip() == '1':
                                ready = True
                                break
                    except Exception:
                        pass
                    time.sleep(0.2)
                break

            time.sleep(0.5)  # FASTER: 0.5 seconds between polls during recording

    # Download the recording (from download_url) with streaming and attempt ffmpeg transcode
    print(f"record_and_transcribe: attempting download from: {download_url}")
    ffmpeg_path = _get_ffmpeg_path()  # OPTIMIZATION: Use cached ffmpeg path
    converted_bytes = None
    
    # OPTIMIZATION: Use session for connection reuse, with optimized timeouts
    # Connect timeout: 3s (how long to establish connection)
    # Read timeout: 20s (how long to wait for data chunks)
    try:
        print(f"⏱ Starting download at {time.strftime('%H:%M:%S')}...")
        download_start = time.time()
        
        r = _http_session.get(download_url, stream=True, timeout=(3, 20))
        
        download_connected = time.time()
        print(f"✓ Connected in {download_connected - download_start:.2f}s")
        print(f"record_and_transcribe: HTTP response status: {r.status_code}")
        
        if r.status_code == 200:
            ct = r.headers.get('content-type','')
            cl = r.headers.get('content-length', 'unknown')
            print(f"record_and_transcribe: download responded 200, content-type={ct}, content-length={cl}")

            # Stream to a local file first (more robust than piping directly to ffmpeg)
            try:
                os.makedirs(os.path.dirname(audio_raw_path_local), exist_ok=True)
            except Exception:
                pass

            written = 0
            try:
                # OPTIMIZATION: Increased chunk size from 8192 to 32768 for much faster download
                # Larger chunks = fewer network round-trips = faster download
                with open(audio_raw_path_local, 'wb') as out_f:
                    for chunk in r.iter_content(chunk_size=32768):
                        if chunk:
                            out_f.write(chunk)
                            written += len(chunk)
                
                download_finished = time.time()
                download_duration = download_finished - download_connected
                if written > 0:
                    speed_kbps = (written / 1024) / download_duration if download_duration > 0 else 0
                    print(f"✓ Downloaded {written:,} bytes in {download_duration:.2f}s ({speed_kbps:.1f} KB/s)")
            except Exception as e:
                print('record_and_transcribe: failed writing download to file:', e)
                written = 0

            # Quick validation: file size and starting bytes
            try:
                size_ok = written > 100
                start_bytes = b''
                with open(audio_raw_path_local, 'rb') as fh:
                    start_bytes = fh.read(512)
            except Exception:
                size_ok = False
                start_bytes = b''

            # Detect HTML/error pages (ngrok offline pages), or very small payloads
            if (not size_ok) or ct.startswith('text/') or start_bytes.lstrip().lower().startswith(b'<'):
                print(f"record_and_transcribe: suspicious payload from {download_url} (size={written}, content-type={ct}); saving debug copy")
                try:
                    debug_path = os.path.join('uploads', f'download_debug_{int(time.time())}.html')
                    os.makedirs(os.path.dirname(debug_path), exist_ok=True)
                    with open(debug_path, 'wb') as fh:
                        fh.write(start_bytes or b'')
                except Exception:
                    pass
                try:
                    debug_stream_path = os.path.join('uploads', f'download_debug_stream_{int(time.time())}.bin')
                    os.makedirs(os.path.dirname(debug_stream_path), exist_ok=True)
                    with open(debug_stream_path, 'wb') as fh:
                        fh.write(start_bytes or b'')
                except Exception:
                    pass
                converted_bytes = None
            else:
                # We have a plausible audio file on disk. Prefer using ffmpeg on the file to transcode.
                if ffmpeg_path:
                    try:
                        print(f"⏱ Starting FFmpeg conversion at {time.strftime('%H:%M:%S')}...")
                        ffmpeg_start = time.time()
                        
                        # OPTIMIZED: Fast conversion with minimal processing
                        # -threads 0: Use all available CPU cores for parallel processing
                        # -vn: No video processing (audio only)
                        # -sn: No subtitle processing
                        # -hide_banner: Less output overhead
                        # -loglevel error: Only show errors
                        cmd = [ffmpeg_path, '-threads', '0', '-y', '-i', audio_raw_path_local, 
                               '-vn', '-sn',  # Skip video/subtitle streams
                               '-f', 'wav', '-ac', '1', '-ar', '16000', 
                               '-acodec', 'pcm_s16le',  # Linear PCM for fast encoding
                               'pipe:1', '-hide_banner', '-loglevel', 'error']
                        
                        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, 
                                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                        out, err = proc.communicate(timeout=30)  # Reduced from 45s to 30s
                        
                        ffmpeg_finished = time.time()
                        ffmpeg_duration = ffmpeg_finished - ffmpeg_start
                        
                        if proc.returncode == 0:
                            converted_bytes = out
                            print(f"✓ FFmpeg conversion completed in {ffmpeg_duration:.2f}s ({len(out):,} bytes)")
                        else:
                            print(f"⚠ FFmpeg returned non-zero exit code: {proc.returncode}")
                            if err:
                                print(f"FFmpeg error: {err.decode('utf-8', errors='ignore')[:200]}")
                            converted_bytes = None
                            
                    except subprocess.TimeoutExpired:
                        print('⚠ FFmpeg conversion timed out after 30s')
                        try:
                            proc.kill()
                        except Exception:
                            pass
                        converted_bytes = None
                    except Exception as e:
                        print('record_and_transcribe: ffmpeg file transcode failed:', e)
                        try:
                            proc.kill()
                        except Exception:
                            pass
                        converted_bytes = None
                        try:
                            debug_stream_path = os.path.join('uploads', f'download_debug_stream_{int(time.time())}.bin')
                            os.makedirs(os.path.dirname(debug_stream_path), exist_ok=True)
                            with open(debug_stream_path, 'wb') as fh:
                                # save first 512 bytes
                                fh.write(start_bytes[:512] if start_bytes else b'')
                        except Exception:
                            pass
                else:
                    # pydub fallback: read the saved file and convert
                    try:
                        audio = AudioSegment.from_file(audio_raw_path_local)
                        audio = audio.set_channels(1)
                        audio = audio.set_frame_rate(16000)
                        buf = io.BytesIO()
                        audio.export(buf, format='wav')
                        converted_bytes = buf.getvalue()
                    except Exception as e:
                        print('record_and_transcribe: pydub conversion failed:', e)
                        converted_bytes = None
        else:
            print(f"record_and_transcribe: download returned status {r.status_code}")
            converted_bytes = None
    except requests.exceptions.ReadTimeout as e:
        print(f'record_and_transcribe: Read timeout from {download_url}')
        print(f'ERROR: The server took too long to respond (>10 seconds)')
        print(f'This usually means your Flask proxy cannot reach the ESP at 192.168.50.62')
        print(f'Solutions:')
        print(f'  1. Check if ESP is powered on and connected to WiFi')
        print(f'  2. Verify ESP IP address is still 192.168.50.62')
        print(f'  3. Make sure ESP and Flask server are on same network')
        print(f'  4. Try using RepeatAudio folder instead (drop WAV files there)')
        return "", False
    except requests.exceptions.ConnectTimeout as e:
        print(f'record_and_transcribe: Connection timeout to {download_url}')
        print(f'ERROR: ESP device appears to be offline or unreachable at {download_url}')
        
        # Try fallback to proxy if we were trying ESP directly
        if esp_host and audio_raw_url != download_url:
            print(f'Attempting fallback to proxy: {audio_raw_url}')
            try:
                r = _http_session.get(audio_raw_url, stream=True, timeout=(3, 15))  # Increased timeout for proxy
                if r.status_code == 200:
                    print('Fallback to proxy successful, processing...')
                    # Process the proxy response (same logic as above)
                    written = 0
                    try:
                        os.makedirs(os.path.dirname(audio_raw_path_local), exist_ok=True)
                    except Exception:
                        pass
                    try:
                        # OPTIMIZATION: Large chunk size for faster download
                        with open(audio_raw_path_local, 'wb') as out_f:
                            for chunk in r.iter_content(chunk_size=32768):
                                if chunk:
                                    out_f.write(chunk)
                                    written += len(chunk)
                        print(f"✓ Proxy fallback downloaded {written:,} bytes")
                    except Exception as e:
                        print(f"⚠ Proxy download failed: {e}")
                        written = 0
                    
                    if written > 100 and ffmpeg_path:
                        try:
                            print("Converting proxy download with FFmpeg...")
                            # OPTIMIZATION: Use all CPU cores
                            cmd = [ffmpeg_path, '-threads', '0', '-y', '-i', audio_raw_path_local, 
                                   '-vn', '-sn',
                                   '-f', 'wav', '-ac', '1', '-ar', '16000', '-acodec', 'pcm_s16le', 
                                   'pipe:1', '-hide_banner', '-loglevel', 'error']
                            proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                            out, _ = proc.communicate(timeout=30)
                            if proc.returncode == 0:
                                converted_bytes = out
                                print(f"✓ Proxy fallback conversion successful ({len(out):,} bytes)")
                            else:
                                converted_bytes = None
                        except Exception as e:
                            print(f"⚠ Proxy FFmpeg conversion failed: {e}")
                            converted_bytes = None
            except Exception as fallback_e:
                print(f'Fallback to proxy also failed: {fallback_e}')
                converted_bytes = None
        else:
            converted_bytes = None
    except requests.exceptions.ConnectionError as e:
        print(f'record_and_transcribe: Connection error to {download_url}: {e}')
        print('ERROR: Check if ESP device is powered on and connected to network')
        converted_bytes = None
    except Exception as e:
        print('record_and_transcribe: download request failed:', e)
        converted_bytes = None

    if not converted_bytes:
        try:
            import wave, struct
            framerate = 16000
            duration_s = 1.0
            nframes = int(framerate * duration_s)
            buf = io.BytesIO()
            with wave.open(buf, 'wb') as wf:
                wf.setnchannels(1)
                wf.setsampwidth(2)
                wf.setframerate(framerate)
                silence = struct.pack('<h', 0)
                for _ in range(nframes):
                    wf.writeframes(silence)
            converted_bytes = buf.getvalue()
        except Exception:
            converted_bytes = b''

    # Transcribe with Google Speech-to-Text
    try:
        # OPTIMIZATION: Use cached client to avoid repeated initialization
        if not hasattr(record_and_transcribe, '_stt_client'):
            record_and_transcribe._stt_client = speech.SpeechClient.from_service_account_json(r'GoogleCloud\\key.json')
            
            # ENHANCED: Use English for BETTER DIGIT RECOGNITION
            # English model has much higher accuracy for numbers/digits than Filipino
            record_and_transcribe._stt_config_english = speech.RecognitionConfig(
                encoding=speech.RecognitionConfig.AudioEncoding.LINEAR16,
                sample_rate_hertz=16000,
                language_code='en-US',  # English has best digit recognition
                enable_automatic_punctuation=False,  # Disabled for cleaner digit output
                use_enhanced=True,  # Use enhanced model for better accuracy
                model='default',  # Use default model for better general digit recognition
                speech_contexts=[
                    speech.SpeechContext(
                        phrases=[
                            # Just digits - keep it simple for best recognition
                            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9",
                            "zero", "one", "two", "three", "four", "five", 
                            "six", "seven", "eight", "nine",
                            # Common digit sequences
                            "oh", "oh zero", "double zero"
                        ],
                        boost=20.0  # Maximum boost for digits
                    )
                ],
                enable_word_time_offsets=False,
                enable_word_confidence=True,  # Enable to see per-word confidence
                profanity_filter=False,
                max_alternatives=5  # Get top 5 alternatives for better accuracy
            )
            
            # Filipino config for non-digit content (quiz answers, conversation)
            record_and_transcribe._stt_config_filipino = speech.RecognitionConfig(
                encoding=speech.RecognitionConfig.AudioEncoding.LINEAR16,
                sample_rate_hertz=16000,
                language_code='fil',  # Filipino for conversation
                enable_automatic_punctuation=True,
                speech_contexts=[
                    speech.SpeechContext(
                        phrases=[
                            # Common Filipino numbers
                            "isa", "dalawa", "tatlo", "apat", "lima", "anim", "pito", "walo", "siyam", "sampu",
                            # Digits 0-9 (English)
                            "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
                            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9",
                            # Common quiz terms
                            "tama", "mali", "sagot", "tanong", "numero", "bilang",
                        ],
                        boost=15.0
                    )
                ],
                enable_word_time_offsets=False,
                enable_word_confidence=False,
                profanity_filter=False,
                max_alternatives=1
            )
            
            # Default to Filipino
            record_and_transcribe._stt_config = record_and_transcribe._stt_config_filipino
        
        print(f"⏱ Starting transcription at {time.strftime('%H:%M:%S')}...")
        transcription_start = time.time()
        
        # Choose config based on use_english flag
        config_to_use = record_and_transcribe._stt_config_english if use_english else record_and_transcribe._stt_config_filipino
        
        if use_english:
            print("🔢 Using English enhanced model for digit recognition...")
            print(f"   Model: default, Enhanced: True, Alternatives: 5, Boost: 20.0")
        else:
            print("🗣️ Using Filipino model for conversation...")
        
        audio_file = speech.RecognitionAudio(content=converted_bytes)
        response = record_and_transcribe._stt_client.recognize(
            config=config_to_use, 
            audio=audio_file
        )
        
        transcription_finished = time.time()
        transcription_duration = transcription_finished - transcription_start
        print(f"✓ Transcription completed in {transcription_duration:.2f}s")
        
    except Exception as exc:
        print('Transcription error:', exc)
        return "", forced_timeout

    complete_text = ""
    best_confidence = 0.0
    
    if response and hasattr(response, 'results') and len(response.results) > 0:
        # If using English model with alternatives, try to find best digit-only result
        if use_english and len(response.results) > 0:
            print(f"\n📊 Analyzing {len(response.results)} transcription result(s):")
            
            # Collect all alternatives with their confidence and digit counts
            alternatives_info = []
            for idx, result in enumerate(response.results):
                if result.alternatives:
                    for alt_idx, alt in enumerate(result.alternatives):
                        text = alt.transcript
                        confidence = alt.confidence if hasattr(alt, 'confidence') else 0.0
                        
                        # Count how many digits this alternative has
                        digit_count = sum(c.isdigit() for c in text)
                        word_count = len(text.split())
                        
                        # Calculate digit ratio
                        digit_ratio = digit_count / max(len(text.replace(' ', '')), 1)
                        
                        alternatives_info.append({
                            'text': text,
                            'confidence': confidence,
                            'digit_count': digit_count,
                            'word_count': word_count,
                            'digit_ratio': digit_ratio,
                            'result_idx': idx,
                            'alt_idx': alt_idx
                        })
                        
                        print(f"  [{idx}.{alt_idx}] '{text}'")
                        print(f"       Confidence: {confidence:.1%} | Digits: {digit_count} | Words: {word_count} | Ratio: {digit_ratio:.1%}")
            
            # Sort by: 1) more digits, 2) higher confidence, 3) higher digit ratio
            alternatives_info.sort(key=lambda x: (-x['digit_count'], -x['confidence'], -x['digit_ratio']))
            
            if alternatives_info:
                best = alternatives_info[0]
                complete_text = best['text']
                best_confidence = best['confidence']
                print(f"\n✅ SELECTED: '{complete_text}'")
                print(f"   Confidence: {best_confidence:.1%} | {best['digit_count']} digits")
        else:
            # Standard flow: use first result, first alternative
            for result in response.results:
                if result.alternatives and len(result.alternatives) > 0:
                    complete_text = result.alternatives[0].transcript
                    
                    # Show confidence if available
                    if hasattr(result.alternatives[0], 'confidence'):
                        best_confidence = result.alternatives[0].confidence
                        print(f"Transcription confidence: {best_confidence:.1%}")
                    break
    
    # Print total processing time
    if 'download_start' in locals():
        total_time = time.time() - download_start
        print(f"⏱ Total processing time: {total_time:.2f}s (download + convert + transcribe)")
    
    print(f"Transcribed text: {complete_text}")

    # Save transcription to file
    try:
        with open('transcribed_text.txt', 'w', encoding='utf-8') as f:
            f.write(complete_text)
    except Exception:
        pass

    # Clean up both local cached file AND remote recording after transcription
    try:
        if os.path.exists(audio_raw_path_local):
            os.remove(audio_raw_path_local)
            print(f"✓ Cleaned up local cache: {audio_raw_path_local}")
    except Exception:
        pass
    
    # Clear remote recording after successful transcription
    print("Clearing remote recording after transcription...")
    
    # Try DIRECT ESP connection first (most reliable)
    esp_direct_ip = '192.168.50.62'
    clear_success = False
    
    try:
        # Primary: ESP /clear endpoint
        clear_resp = _http_session.get(f'http://{esp_direct_ip}/clear', timeout=3.0)
        if clear_resp.status_code == 200:
            print(f"✓ ESP /clear successful")
            clear_success = True
        
        # Also call /stop to ensure recording stopped
        _http_session.get(f'http://{esp_direct_ip}/stop', timeout=2.0)
    except Exception as e:
        print(f"⚠ Could not reach ESP directly: {e}")
    
    # Backup: Try proxy endpoints
    if not clear_success:
        try:
            parsed = urllib.parse.urlparse(audio_raw_url)
            if parsed.netloc:
                base = f'{parsed.scheme}://{parsed.netloc}'
                for path in ['/clear', '/clear_recording']:
                    try:
                        resp = _http_session.get(f'{base}{path}', timeout=2.0)
                        if resp.status_code == 200:
                            print(f"✓ Proxy {path} successful")
                            clear_success = True
                            break
                    except Exception:
                        pass
        except Exception:
            pass
    
    # Final attempt: DELETE method on recording URL
    if not clear_success:
        try:
            delete_resp = _http_session.delete(audio_raw_url, timeout=2.0)
            if delete_resp.status_code in [200, 204, 404]:
                print(f"✓ DELETE successful")
                clear_success = True
        except Exception:
            pass
    
    if clear_success:
        print("✓ Remote recording cleared successfully")
    else:
        print("⚠ Warning: Could not verify remote recording cleared")

    return complete_text, forced_timeout


def is_profane_by_ai(text_to_check):
    """Uses the AI's safety filters to check for profanity."""
    if not text_to_check or not text_to_check.strip():
        return False
    try:
        # We send the user's text to the model. If the model's safety filter
        # blocks the prompt, we consider it to contain profanity.
        response = model.generate_content(text_to_check)
        
        # Check if the prompt was blocked.
        if not response.candidates and hasattr(response, 'prompt_feedback') and response.prompt_feedback.block_reason == 'SAFETY':
            return True
            
        return False
    except Exception as e:
        print(f"Warning: Could not check for profanity via AI due to an error: {e}")
        return False # Fail safe: don't block if the check fails.

def read_state_text_file(url_state):
    try:
        # Send a GET request to the specified URL to download the file
        response = requests.get(url_state)
        
        # Check if the request was successful (status code 200)
        if response.status_code == 200:
            # Return the content of the downloaded file
            return response.text.strip().lower()
        else:
            # If the request was not successful, print an error message
            print(f"Failed to fetch data from URL {url_state}. Status code: {response.status_code}")
            return None
    except requests.exceptions.RequestException as e:
        # If an exception occurs during the request, print an error message
        print(f"An error occurred: {e}")
        return None

def set_state_to_assisting_mode():
    """Force state to 0 (Assisting Mode) via ngrok tunnel"""
    try:
        # Use ngrok URL with /set_state endpoint (goes through Flask proxy to ESP32)
        set_state_url = "https://nonbasic-bob-inimical.ngrok-free.dev/set_state"
        
        print("\n" + "="*60)
        print("INITIALIZING GENTA SYSTEM - Setting state to Assisting Mode...")
        print("="*60)
        
        # Set state to 0 via HTTP
        response = requests.get(f"{set_state_url}?value=0", timeout=15)
        
        if response.status_code == 200:
            print("✓ State set to 0 (Assisting Mode)")
            print("✓ State button DISABLED until LRN is entered")
            return True
        else:
            print(f"⚠ Warning: Could not set state. Status: {response.status_code}")
            print(f"  Response: {response.text}")
            return False
            
    except Exception as e:
        print(f"⚠ Warning: Could not set initial state: {e}")
        print("  System will use current ESP32 state")
        return False

def check_for_state_change():
    """Quick state check - returns True if state has changed"""
    global _STATE_CHANGE_REQUESTED, _CURRENT_STATE
    try:
        new_state = read_state_text_file(url_state)
        if new_state and new_state.strip() and new_state.strip() != _CURRENT_STATE:
            print(f"\n[State Change Detected] {_CURRENT_STATE} → {new_state.strip()}")
            _STATE_CHANGE_REQUESTED = True
            return True
    except Exception:
        pass
    return False

def GENTA():
    # === STARTUP CLEANUP: Clear any old recordings before beginning ===
    print("\n" + "="*60)
    print("GENTA STARTUP: Clearing old recordings from previous sessions...")
    print("="*60)
    
    # Delete local recording file if it exists
    try:
        if os.path.exists(audio_raw_path):
            os.remove(audio_raw_path)
            print(f"✓ Deleted local file: {audio_raw_path}")
        else:
            print(f"✓ No local recording file found")
    except Exception as e:
        print(f"⚠ Could not delete local file: {e}")
    
    # Clear remote recordings - Try DIRECT ESP connection first (most reliable)
    esp_direct_ip = '192.168.50.62'
    print(f"Attempting to clear ESP32 directly at {esp_direct_ip}...")
    
    clear_success = False
    try:
        # Try ESP /clear endpoint directly (most reliable method)
        clear_resp = _http_session.get(f'http://{esp_direct_ip}/clear', timeout=3.0)
        if clear_resp.status_code == 200:
            print(f"✓ ESP /clear successful (HTTP {clear_resp.status_code})")
            clear_success = True
        
        # Also try /stop to ensure recording stopped
        stop_resp = _http_session.get(f'http://{esp_direct_ip}/stop', timeout=2.0)
        if stop_resp.status_code == 200:
            print(f"✓ ESP /stop successful (HTTP {stop_resp.status_code})")
    except Exception as e:
        print(f"⚠ Could not reach ESP directly: {e}")
    
    # Try proxy/tunnel endpoints as backup
    try:
        parsed = urllib.parse.urlparse(audio_raw_url)
        if parsed.netloc:
            base = f'{parsed.scheme}://{parsed.netloc}'
            
            # Try various proxy clear endpoints
            for path in ['/clear', '/clear_recording', '/reset']:
                try:
                    resp = _http_session.get(f'{base}{path}', timeout=3.0)
                    if resp.status_code == 200:
                        print(f"✓ Proxy {path} successful")
                        clear_success = True
                except Exception:
                    pass
    except Exception:
        pass
    
    # Strategy 3: Try DELETE method on recording URL directly
    try:
        delete_resp = _http_session.delete(audio_raw_url, timeout=3.0)
        if delete_resp.status_code in [200, 204, 404]:
            print(f"✓ DELETE on proxy URL successful (HTTP {delete_resp.status_code})")
            clear_success = True
    except Exception as e:
        print(f"⚠ DELETE method failed: {e}")
    
    # Wait for deletions to complete
    print("Waiting for deletions to propagate...")
    time.sleep(1.0)
    
    # Verify recording is actually gone
    verification_attempts = 3
    recording_still_exists = False
    
    for attempt in range(verification_attempts):
        try:
            # Check via direct ESP
            try:
                verify_resp = _http_session.head(f'http://{esp_direct_ip}/recording.wav', timeout=2.0)
                if verify_resp.status_code == 200:
                    size = verify_resp.headers.get('content-length', '0')
                    print(f"  Attempt {attempt + 1}: ESP recording exists (size={size})")
                    if attempt < verification_attempts - 1:
                        # Try clearing again
                        _http_session.get(f'http://{esp_direct_ip}/clear', timeout=2.0)
                        time.sleep(0.5)
                    else:
                        recording_still_exists = True
                else:
                    print(f"✓ Verified: ESP recording cleared")
                    break
            except Exception:
                print(f"✓ Verified: ESP recording cleared or unreachable")
                break
        except Exception:
            print(f"✓ Verified: Recording cleared")
            break
    
    if clear_success or not recording_still_exists:
        print("✓ Startup cleanup completed successfully")
    else:
        print("⚠ WARNING: Recording may still exist - will use size detection")
    
    # Disable state button at startup (will be enabled after LRN entry)
    try:
        esp_speaker_ip = '192.168.50.70'  # GENTA2 (speaker/state management)
        disable_resp = _http_session.get(f'http://{esp_speaker_ip}/disable_state_button', timeout=5.0)
        if disable_resp.status_code == 200:
            print("✓ State button DISABLED - Will enable after LRN entry")
        else:
            print(f"⚠ State button disable returned: {disable_resp.status_code}")
    except Exception as e:
        print(f"⚠ Could not disable state button: {e}")
    
    print("="*60)
    print("GENTA READY: Starting LRN collection...\n")
    
    # Mark startup cleanup as complete
    global _STARTUP_CLEANUP_DONE
    _STARTUP_CLEANUP_DONE = True
    
    def retrieve_and_store_remarks(host, database, user, password, student_id):
        """Return a dict with student and teacher info for the given student_id.
        Keys returned: remark, student_name, teacher_id, teacher_name
        """
        connection = None
        cursor = None
        try:
            # Connect to the database
            connection = mysql.connector.connect(
                host=host,
                database=database,
                user=user,
                password=password
            )

            remark = None
            student_name = None
            teacher_id = None
            teacher_name = None

            if connection and connection.is_connected():
                cursor = connection.cursor()
                # Try some common lookup strategies: id (numeric), lrn/student_number (string)
                tried = []
                # sanitize candidate
                cand = str(student_id).strip()
                # Prefer explicit LRN column lookup first (user specified column name 'lrn')
                if cand:
                    try:
                        cursor.execute("SELECT remarks, name, teacher_id FROM students WHERE lrn = %s LIMIT 1", (cand,))
                        row = cursor.fetchone()
                        tried.append(('lrn', cand))
                        if row:
                            remark = row[0] if len(row) > 0 else None
                            student_name = row[1] if len(row) > 1 else None
                            teacher_id = row[2] if len(row) > 2 else None
                    except Exception:
                        pass

                # If not found via lrn, attempt numeric id lookup (common path)
                if not student_name and cand.isdigit():
                    try:
                        cursor.execute("SELECT remarks, name, teacher_id FROM students WHERE id = %s", (int(cand),))
                        row = cursor.fetchone()
                        tried.append(('id', cand))
                        if row:
                            remark = row[0] if len(row) > 0 else None
                            student_name = row[1] if len(row) > 1 else None
                            teacher_id = row[2] if len(row) > 2 else None
                    except Exception:
                        pass

                # If still not found, try matching common alternate columns (student_number or id)
                if not student_name:
                    try:
                        cursor.execute("SELECT remarks, name, teacher_id FROM students WHERE student_number = %s OR id = %s", (cand, cand))
                        row = cursor.fetchone()
                        tried.append(('student_number/id', cand))
                        if row:
                            remark = row[0] if len(row) > 0 else None
                            student_name = row[1] if len(row) > 1 else None
                            teacher_id = row[2] if len(row) > 2 else None
                    except Exception:
                        pass

                # If we have teacher_id, fetch teacher name
                if teacher_id:
                    try:
                        cursor.execute("SELECT name FROM teachers WHERE id = %s", (teacher_id,))
                        trow = cursor.fetchone()
                        if trow and len(trow) > 0:
                            teacher_name = trow[0]
                    except Exception:
                        teacher_name = None

                final_remark = None
                if remark:
                    final_remark = str(remark) + " This is the remark on the student that you need to reinforce:"

                return {
                    'remark': final_remark,
                    'student_name': student_name,
                    'teacher_id': teacher_id,
                    'teacher_name': teacher_name,
                }

        except mysql.connector.Error as e:
            print("Error while connecting to MySQL", e)
            return None
        finally:
            try:
                if cursor:
                    cursor.close()
            except Exception:
                pass
            try:
                if connection and connection.is_connected():
                    connection.close()
            except Exception:
                pass
    # Voice-driven mandatory LRN collection: keep prompting until student confirms their LRN
    def _speak_and_play(text: str):
        """Small early TTS+play helper used before full synthesize_speech/play_audio are defined.
        Generates response.wav via Google TTS and plays it locally via pygame (best-effort).
        """
        try:
            client = texttospeech_v1.TextToSpeechClient()
            voice1 = texttospeech_v1.VoiceSelectionParams(name='fil-ph-Neural2-A', language_code='fil-ph')
            audio_config = texttospeech_v1.AudioConfig(audio_encoding=texttospeech_v1.AudioEncoding.LINEAR16, pitch=6.00)
            resp = client.synthesize_speech(input=texttospeech_v1.SynthesisInput(text=text), voice=voice1, audio_config=audio_config)
            with open('response.wav', 'wb') as fh:
                fh.write(resp.audio_content)
            # play locally
            try:
                pygame.mixer.init()
                pygame.mixer.music.load('response.wav')
                pygame.mixer.music.play()
                while pygame.mixer.music.get_busy():
                    time.sleep(0.05)
                pygame.mixer.quit()
            except Exception:
                pass
        except Exception as e:
            print('Early TTS/play failed:', e)

    def _play_response_wav():
        try:
            pygame.mixer.init()
            pygame.mixer.music.load('response.wav')
            pygame.mixer.music.play()
            while pygame.mixer.music.get_busy():
                time.sleep(0.05)
            pygame.mixer.quit()
        except Exception:
            pass

    def ask_for_lrn_via_voice():
        attempts = 0
        failed_speech_attempts = 0
        def ask_for_digits_mode():
            """Collect LRN by listening for digits one-by-one (or short groups). Say 'tapos' or 'done' when finished."""
            print('Switching to digit-by-digit mode. Please say each digit clearly. Say "tapos" when finished.')
            digits = []
            no_digit_runs = 0
            max_rounds = 20
            for _r in range(max_rounds):
                try:
                    # Use English model for BEST digit recognition
                    txt, _ = record_and_transcribe(esp_host=esp_record_host, poll_for_recording=True, max_poll_seconds=6, use_english=True)
                except Exception as e:
                    print('Digit capture failed:', e)
                    txt = ''

                if not txt or not txt.strip():
                    no_digit_runs += 1
                    if no_digit_runs >= 3:
                        break
                    try:
                        _speak_and_play('Walang narinig. Pakiulit ang susunod na numero.')
                    except Exception:
                        pass
                    continue

                txt_low = txt.lower()
                if any(w in txt_low for w in ['tapos', 'done', 'tama', 'finish', 'tapós']):
                    break

                found = re.findall(r"\d+", txt)
                if found:
                    # append each digit group as separate digits
                    for grp in found:
                        for ch in grp:
                            digits.append(ch)
                    no_digit_runs = 0
                    # give brief audio ack
                    try:
                        _speak_and_play('Narekord na.')
                    except Exception:
                        pass
                else:
                    # maybe transcript spelled out numbers, try to extract words mapped to digits
                    # simple mapping for common words
                    word_map = {'zero':'0','one':'1','two':'2','three':'3','four':'4','five':'5','six':'6','seven':'7','eight':'8','nine':'9',
                                'isa':'1','dalawa':'2','tatlo':'3','apat':'4','lima':'5','anim':'6','pito':'7','walo':'8','siyam':'9','sero':'0'}
                    tokens = re.findall(r"[a-zA-Z]+", txt_low)
                    mapped = [word_map.get(t) for t in tokens if t in word_map]
                    if mapped:
                        digits.extend(mapped)
                        no_digit_runs = 0
                        try:
                            _speak_and_play('Narekord na.')
                        except Exception:
                            pass
                    else:
                        no_digit_runs += 1
                        try:
                            _speak_and_play('Hindi malinaw ang sinabi. Pakiulit.')
                        except Exception:
                            pass
                        if no_digit_runs >= 3:
                            break

            result = ''.join(digits)
            return result

        while True:
            attempts += 1
            # Verbose console prompt so user sees what's expected
            print("Please provide your LRN (voice).")
            try:
                # Ask student to say their LRN
                prompt = "Pakisabi ang iyong L-R-N numero ngayon. Sabihin ang lahat ng numero nang malinaw."
                try:
                    _speak_and_play(prompt)
                except Exception as _e:
                    print('LRN prompt playback failed:', _e)
            except Exception:
                pass

            # Quick HEAD to the download URL to see if the proxy is up. If it fails,
            # continue with voice-only flow (no typed fallback) as requested.
            try:
                # OPTIMIZATION: Use session and reduced timeout
                _ = _http_session.head(audio_raw_url, timeout=0.8)
            except Exception:
                print('Recording proxy not reachable; continuing with voice-only LRN flow.')

            # Wait briefly then record/transcribe
            time.sleep(0.3)  # OPTIMIZATION: Reduced from 0.5s to 0.3s
            lrn_text = ''
            forced = False
            print('Attempting to capture LRN via recording (short timeout)...')
            try:
                # Use English model for MUCH BETTER digit recognition
                lrn_text, forced = record_and_transcribe(
                    esp_host=esp_record_host, 
                    poll_for_recording=True, 
                    max_poll_seconds=8,
                    use_english=True  # CRITICAL: Use English for accurate digit transcription
                )
                print(f'LRN recording attempt returned: {lrn_text!r}, forced={forced}')
            except Exception as e:
                print('LRN recording failed (exception):', e)
                lrn_text = ''
                forced = False

            if not lrn_text or not lrn_text.strip():
                failed_speech_attempts += 1
                # After a couple failed freeform attempts, try digit-by-digit mode
                if failed_speech_attempts == 2:
                    try:
                        digit_result = ask_for_digits_mode()
                        if digit_result:
                            # confirm digits
                            try:
                                _speak_and_play(f'Nadinig ko ang mga numero {digit_result}. Tama ba ito?')
                            except Exception:
                                pass
                            try:
                                # Use English model for confirmation (yes/no/oo/hindi)
                                conf, _ = record_and_transcribe(esp_host=esp_record_host, poll_for_recording=True, max_poll_seconds=6, use_english=True)
                            except Exception:
                                conf = ''
                            if conf and conf.lower()[:1] in ('y','o','t'):
                                # ensure only digits in LRN
                                return re.sub(r"\D", "", digit_result)
                    except Exception:
                        pass
                # After several failed speech attempts, retry voice-only flow (do not fall back to typing)
                if failed_speech_attempts >= 3:
                    print('Multiple failed voice attempts; will retry voice-only capture.')
                    failed_speech_attempts = 0
                    # brief prompt before retrying
                    try:
                        _speak_and_play('Uulitin ko ang paghingi ng iyong L-R-N. Pakiusap, sabihin muli.')
                    except Exception:
                        pass
                    time.sleep(0.3)  # OPTIMIZATION: Reduced from 0.5s to 0.3s
                    continue
                # Ask again via voice
                try:
                    retry_msg = "Hindi ko narinig ang iyong L-R-N. Pakiulit po."
                    try:
                        _speak_and_play(retry_msg)
                    except Exception:
                        pass
                except Exception:
                    pass
                time.sleep(0.3)  # OPTIMIZATION: Reduced from 0.5s to 0.3s
                continue

            lrn_text = lrn_text.strip()
            
            # Show what was transcribed
            print(f'DEBUG: Captured LRN text (raw): "{lrn_text}"')
            
            # Convert word numbers to digits (handles mixed transcriptions like "one 2 three")
            def words_to_digits(text):
                """Convert number words to digits and extract only digits.
                Handles English and Filipino number words.
                Example: "one two 3 four" -> "1234"
                """
                # Mapping of word numbers to digits
                word_to_digit = {
                    # English
                    'zero': '0', 'one': '1', 'two': '2', 'three': '3', 'four': '4',
                    'five': '5', 'six': '6', 'seven': '7', 'eight': '8', 'nine': '9',
                    # Filipino
                    'sero': '0', 'isa': '1', 'dalawa': '2', 'tatlo': '3', 'apat': '4',
                    'lima': '5', 'anim': '6', 'pito': '7', 'walo': '8', 'siyam': '9',
                    'sampu': '10',  # Special case: "sampu" = 10 (two digits)
                }
                
                # Lowercase and split into words
                words = text.lower().split()
                result = []
                
                for word in words:
                    # Remove punctuation from word
                    clean_word = re.sub(r'[^\w]', '', word)
                    
                    if clean_word in word_to_digit:
                        # Convert word to digit
                        result.append(word_to_digit[clean_word])
                    elif clean_word.isdigit():
                        # Already a digit, keep it
                        result.append(clean_word)
                    # Ignore non-numeric words
                
                # Join all digits (no spaces)
                return ''.join(result)
            
            # Convert words to digits and extract
            digits_only = words_to_digits(lrn_text)
            print(f'DEBUG: Converted to digits: "{digits_only}" (length: {len(digits_only)})')
            
            # Also try pure digit extraction as fallback
            pure_digits = re.sub(r"\D", "", lrn_text)
            if len(pure_digits) == 12 and len(digits_only) != 12:
                # If pure extraction gives exactly 12 but conversion doesn't, use pure
                print(f'DEBUG: Using pure digit extraction: "{pure_digits}"')
                digits_only = pure_digits
            elif len(digits_only) != 12 and len(pure_digits) != 12:
                # Neither worked perfectly, prefer the conversion result
                print(f'DEBUG: Both methods failed, using word conversion result')
            
            print(f'DEBUG: Final digits: "{digits_only}" (length: {len(digits_only)})')

            # STRICT VALIDATION #1: Must be EXACTLY 12 digits
            if len(digits_only) != 12:
                print(f'DEBUG: LRN rejected - not 12 digits (got {len(digits_only)} digits)')
                try:
                    if len(digits_only) < 12:
                        _speak_and_play(f'Kulang ang numero. Nadinig ko lamang {len(digits_only)} numero. Ang L-R-N ay dapat may labindalawang numero. Pakiulit po.')
                    else:
                        _speak_and_play(f'Sobra ang numero. Nadinig ko {len(digits_only)} numero. Ang L-R-N ay dapat may labindalawang numero lamang. Pakiulit po.')
                except Exception:
                    pass
                time.sleep(0.3)
                continue

            # STRICT VALIDATION #2: Must contain ONLY digits (no letters/special chars in original)
            if not digits_only.isdigit():
                print('DEBUG: LRN rejected - contains non-numeric characters')
                try:
                    _speak_and_play('Ang L-R-N ay dapat numero lamang. Pakiulit po nang maayos.')
                except Exception:
                    pass
                time.sleep(0.3)
                continue

            # STRICT VALIDATION #3: Must exist in database
            print(f'DEBUG: Checking database for LRN: {digits_only}')
            temp_student_info = retrieve_and_store_remarks('localhost', 'my_app', 'root', '', digits_only)
            
            if not temp_student_info or not isinstance(temp_student_info, dict) or not temp_student_info.get('student_name'):
                print('DEBUG: LRN rejected - not found in database')
                try:
                    _speak_and_play(f'Ang L-R-N na {digits_only} ay hindi nakatala sa aming sistema. Pakitiyak na tama ang inyong L-R-N at ulitin po.')
                except Exception:
                    pass
                time.sleep(0.3)
                continue

            # ALL VALIDATIONS PASSED - Now ask for confirmation
            student_name = temp_student_info.get('student_name', 'Estudyante')
            print(f'DEBUG: LRN valid! Found student: {student_name}')
            
            try:
                # Read back the LRN and student name for confirmation
                confirm_prompt = f"Nadinig ko ang L-R-N: {digits_only}. Ikaw ba si {student_name}? Sagutin po ng oo o hindi."
                try:
                    _speak_and_play(confirm_prompt)
                except Exception as _e:
                    print('Confirm prompt playback failed:', _e)
            except Exception:
                pass

            # Listen for confirmation
            time.sleep(0.3)
            conf_text = ''
            try:
                conf_text, _ = record_and_transcribe(esp_host=esp_record_host, poll_for_recording=True, max_poll_seconds=8)
                print(f'DEBUG: Confirmation transcription result: "{conf_text}"')
            except Exception as e:
                print('LRN confirmation recording failed (exception):', e)
                conf_text = ''

            if conf_text and conf_text.strip():
                ct = conf_text.lower().strip()
                print(f'DEBUG: Checking confirmation text (lowercased): "{ct}"')
                # Check for affirmative responses
                if any(w in ct for w in ['oo', 'yes', 'tama', 'correct', 'oo po', 'opo']):
                    print('DEBUG: User confirmed identity! Returning validated LRN.')
                    return digits_only
                elif any(w in ct for w in ['hindi', 'no', 'mali', 'wrong', 'hindi po']):
                    print('DEBUG: User denied identity. Will ask for LRN again.')
                    try:
                        _speak_and_play("Sige, pakisabi muli ang tamang L-R-N.")
                    except Exception:
                        pass
                    time.sleep(0.3)
                    continue
                else:
                    print(f'DEBUG: Unclear response "{ct}". Treating as negative - will ask again.')
                    try:
                        _speak_and_play("Hindi malinaw ang sagot. Pakisabi muli ang inyong L-R-N.")
                    except Exception:
                        pass
                    time.sleep(0.3)
                    continue
            else:
                print('DEBUG: No confirmation text received (empty or None)')
                # No confirmation heard - retry
                failed_speech_attempts += 1
                if failed_speech_attempts >= 3:
                    print('No confirmation heard after several attempts; retrying LRN capture.')
                    failed_speech_attempts = 0
                    try:
                        _speak_and_play('Hindi ako nakarinig ng sagot. Pakiulit ang inyong L-R-N.')
                    except Exception:
                        pass
                time.sleep(0.3)
                continue

    # Collect LRN with validation (voice-only). Repeat until we get a valid LRN
    remarks = ""
    while True:
        student_input = ask_for_lrn_via_voice()
        
        # At this point, student_input should already be:
        # - Exactly 12 digits
        # - Validated against database
        # - Confirmed by user
        sanitized_lrn = re.sub(r"\D", "", (student_input or ""))

        # Final safety check (should never fail since ask_for_lrn_via_voice does validation)
        if not sanitized_lrn or len(sanitized_lrn) != 12:
            print(f'ERROR: ask_for_lrn_via_voice returned invalid LRN: {sanitized_lrn}')
            try:
                _speak_and_play('May problema sa sistema. Pakiulit ang inyong L-R-N.')
            except Exception:
                pass
            time.sleep(0.3)
            continue

        # Lookup in database (should succeed since already validated inside ask_for_lrn_via_voice)
        student_info = retrieve_and_store_remarks('localhost', 'my_app', 'root', '', sanitized_lrn)
        if not student_info or not isinstance(student_info, dict) or not student_info.get('student_name'):
            # This should never happen since we already validated, but handle it gracefully
            print(f'ERROR: Database lookup failed for previously validated LRN: {sanitized_lrn}')
            try:
                _speak_and_play('May problema sa koneksyon sa database. Pakiulit ang inyong L-R-N.')
            except Exception:
                pass
            time.sleep(0.3)
            continue

        # Success - store context and break
        remarks = student_info.get('remark') or ""
        try:
            global CURRENT_STUDENT_ID, CURRENT_TEACHER_ID, CURRENT_TEACHER_NAME, CURRENT_STUDENT_NAME
            CURRENT_STUDENT_ID = sanitized_lrn
            CURRENT_TEACHER_ID = student_info.get('teacher_id')
            CURRENT_TEACHER_NAME = student_info.get('teacher_name')
            CURRENT_STUDENT_NAME = student_info.get('student_name')
        except Exception:
            pass
        print("Retrieved student info: ", {'student': CURRENT_STUDENT_NAME, 'teacher': CURRENT_TEACHER_NAME, 'teacher_id': CURRENT_TEACHER_ID})
        
        # Enable state button on ESP32 GENTA2 (speaker) now that LRN is validated
        try:
            esp_speaker_ip = '192.168.50.70'  # GENTA2 (speaker/state management)
            enable_resp = _http_session.get(f'http://{esp_speaker_ip}/enable_state_button', timeout=5.0)
            if enable_resp.status_code == 200:
                print("✓ State button ENABLED - User can now change modes")
            else:
                print(f"⚠ State button enable returned: {enable_resp.status_code}")
        except Exception as e:
            print(f"⚠ Could not enable state button: {e}")

        # Prepare a personalized welcome message using the student's first name
        try:
            first_name = CURRENT_STUDENT_NAME.split()[0] if CURRENT_STUDENT_NAME and isinstance(CURRENT_STUDENT_NAME, str) else None
            if first_name:
                PERSONAL_WELCOME_MSG = f"Hello {first_name}. Ako si GENTA. Handa ka na ba na mag-aral ngayon?"
            else:
                PERSONAL_WELCOME_MSG = "Hello. Ako si GENTA. Handa ka na ba na mag-aral ngayon?"
        except Exception:
            PERSONAL_WELCOME_MSG = None
        break
    chat = model.start_chat(history=[
        {   "role": "user",            
            "parts": [{"text": """System prompt: You are an elementary math teacher named Jen-ta (GENTA) for Grade 3 students in the Philippines. 

CRITICAL RULES FOR YOUR RESPONSES:
1. Keep answers SHORT - maximum 3-4 sentences only
2. Use SIMPLE Tagalog words that Grade 3 students understand
3. NO special symbols, NO asterisks, NO bullets, NO formatting
4. NO markdown, NO emphasis marks, just plain text
5. Explain like talking to a 5-year-old child
6. Give ONE simple example using toys, candies, or fruits
7. Answer the question FIRST, then give one short explanation

Example of GOOD response:
"Ang 5 plus 3 ay 8. Kung mayroon kang limang kendi at may binigay sa iyo pang tatlong kendi, mayroon ka na ngayong walong kendi lahat lahat."

Example of BAD response (TOO LONG):
"Ang pagdaragdag o addition ay isang mahalagang konsepto sa matematika... [many sentences]... Kaya ang sagot ay 8."

Remember: SHORT, SIMPLE, NO SYMBOLS, Grade 3 level only. """ + remarks}]
        },
        {   "role": "model",
            "parts": [{"text": """Naiintindihan ko. Magsasalita ako ng maikli at simple, walang mga simbolo, para sa Grade 3 na estudyante."""}]
        },
        {   "role": "user", 
            "parts": [{"text": """Example: What is 5 plus 3?"""}]
        },
        {   "role": "model",      
            "parts": [{"text": """Ang 5 plus 3 ay 8. Kung mayroon kang limang kendi at may binigay sa iyo pang tatlong kendi, mayroon ka na ngayong walong kendi lahat lahat."""}]
        },
        {   "role": "user", 
            "parts": [{"text": """System prompt: who is your creator"""}]
        },
        {   "role": "model",      
            "parts": [{"text": """Ako ay ginawa ng 4th year Computer Science students sa City College of Angeles. Sila ay sina Jino Guiwan, Jonas Tiglao, Cedric Garcia, at Maria Tiblani."""}]
        },
        {   "role": "user", 
            "parts": [{"text": """Who is your thesis adviser"""}]
        },
        {   "role": "model",      
            "parts": [{"text": """Dean Maika Garbes"""}]
        }, 
        {   "role": "user", 
            "parts": [{"text": """Who is your project adviser"""}]
        },
        {   "role": "model",      
            "parts": [{"text": """Sir Billy Yee"""}]
        },        
        {   "role": "user", 
            "parts": [{"text": """What is your name"""}]
        },
        {   "role": "model",      
            "parts": [{"text": """I am 'Jen-ta'."""}]
        },
        {   "role": "user", 
            "parts": [{"text": """Who are your favorite professors?"""}]
        },
        {   "role": "model",      
            "parts": [{"text": """My favorite professors are Dean Maika Garbes, and Sir Billy Yee."""}]
        },
        {   "role": "user", 
            "parts": [{"text": """Tell me something about your research or study."""}]
        },
        {   "role": "model",      
            "parts": [{"text": """In the Philippines, elementary students face a significant educational hurdle, particularly in Grade 4, 
                       where foundational competencies prove challenging to grasp. Our capstone project aimed to provide a possible solution 
                       for this issue by investigating the functionality of GENTA, an electronic GLM-powered learner-oriented tool, in assessing 
                       Grade 3 students' mathematical competencies. GENTA integrates hardware, utilizing ESP 32 for speech-to-text and 
                       text-to-speech capabilities, along with software functionalities accessible through a teacher dashboard. 
                       This integration enables the delivery of tailored learning experiences aligned with pedagogical themes on both platforms. 
                       Through rigorous statistical analyses, including ISO 25095 and Word Error Rate (WER) assessments, we validate GENTA's accuracy and reliability. 
                       Achieving a 91.94 percent accuracy rate in speech-to-text transcription, GENTA demonstrates its ability to identify individual 
                       student weaknesses and design personalized learning modules, thereby empowering teachers with targeted interventions. 
                       Our research highlights recommendations for enhancing GENTA's functionality, such as mitigating time constraints, 
                       exploring innovative technologies, and improving user interaction through visual components. 
                       Overall, GENTA shows promising potential in improving Grade 3 mathematics learning outcomes, 
                       with significant implications for elevating educational standards globally."""}]
        },        

    ])
    
    def convert_apostrophe(text):
        text1 = text.replace("&#39;", "'")
        text2 = text1.replace("&quot;", '"')
        return text2
    def simplify_for_grade3(text: str) -> str:
        """Aggressively remove ALL special symbols, markdown, and formatting.
        Make the text clean and simple for Grade 3 TTS playback - only plain text.
        """
        if not text:
            return text
        try:
            # Remove ALL asterisks (bold/italic markdown)
            s = re.sub(r"\*+", "", text)
            
            # Remove ALL underscores (markdown emphasis)
            s = re.sub(r"_+", "", s)
            
            # Remove hash symbols (headers)
            s = re.sub(r"#+\s*", "", s)
            
            # Remove bullet points and list markers
            s = re.sub(r"^[\s]*[-•–—▪▫►○●]\s*", "", s, flags=re.MULTILINE)
            
            # Remove numbered lists (1. 2. 3. etc)
            s = re.sub(r"^[\s]*\d+[\.\)]\s*", "", s, flags=re.MULTILINE)
            
            # Remove brackets and parentheses content that might be notes
            s = re.sub(r"\[.*?\]", "", s)
            
            # Remove backticks (code formatting)
            s = re.sub(r"`+", "", s)
            
            # Remove pipe symbols (tables)
            s = s.replace("|", "")
            
            # Remove angle brackets
            s = re.sub(r"[<>]", "", s)
            
            # Remove excessive punctuation (multiple !!!, ???, etc)
            s = re.sub(r"([!?.]){2,}", r"\1", s)
            
            # Replace multiple newlines with single newline
            s = re.sub(r"\n{2,}", "\n", s)
            
            # Trim whitespace from each line
            s = "\n".join([ln.strip() for ln in s.splitlines() if ln.strip()])
            
            # Collapse multiple spaces into one
            s = re.sub(r"\s{2,}", " ", s)
            
            # Remove leading/trailing whitespace
            s = s.strip()
            
            # Limit length: if response is too long (over 500 chars), truncate with message
            if len(s) > 500:
                # Find last sentence within 500 chars
                truncated = s[:500]
                last_period = truncated.rfind('.')
                if last_period > 100:  # At least keep some content
                    s = truncated[:last_period + 1]
                else:
                    s = truncated + "..."
            
            return s
        except Exception as e:
            print(f"Warning: simplify_for_grade3 error: {e}")
            return text
    def synthesize_speech(text):
        # OPTIMIZATION: Use cached client to avoid repeated initialization
        if not hasattr(synthesize_speech, '_client'):
            synthesize_speech._client = texttospeech_v1.TextToSpeechClient()
            synthesize_speech._voice = texttospeech_v1.VoiceSelectionParams(
                name='fil-ph-Neural2-A',
                language_code='fil-ph'
            )
            synthesize_speech._audio_config = texttospeech_v1.AudioConfig(
                audio_encoding=texttospeech_v1.AudioEncoding.LINEAR16,
                pitch=6.00
            )
        
        response = synthesize_speech._client.synthesize_speech(
            input=texttospeech_v1.SynthesisInput(text=text),
            voice=synthesize_speech._voice,
            audio_config=synthesize_speech._audio_config
        )
        with open('response.wav', 'wb') as out:
            out.write(response.audio_content)

    def TranslateToFil(text):
        # OPTIMIZATION: Use cached client to avoid repeated initialization
        if not hasattr(TranslateToFil, '_client'):
            TranslateToFil._client = translate_v2.Client()
        
        # Perform translation
        translated_response = TranslateToFil._client.translate(text, target_language="fil")
        # Extract translated text from the response dictionary
        translated_text = translated_response['translatedText']
        # Write output to file
        with open(r'output.txt', 'w', encoding='utf-8') as f:
            f.write(translated_text) 
        return translated_text   
    def TranslateToEng(text):
        translate_client = translate_v2.Client()
        # Perform translation
        translated_response = translate_client.translate(text, target_language="en")
        # Extract translated text from the response dictionary
        translated_text = translated_response['translatedText']
        return translated_text 
    def system_play_audio(folder):
        # Pick a random welcome audio from the folder and attempt to upload it
        # to the ESP playback device and trigger playback there. If the upload
        # or playback on the ESP fails, fall back to local playback.
        files = [f for f in os.listdir(folder) if f.lower().endswith('.wav')]
        if not files:
            print("No WAV files found in the folder.")
            return

        file_to_play = random.choice(files)
        file_path = os.path.join(folder, file_to_play)
        file_title = file_to_play.replace('_', '?')[:-4]  # Replace underscores with question marks
        print("GENTA: Hello, ako si GENTA! " + file_title)

        def upload_and_play_on_esp(wav_path):
            try:
                url = f'http://{esp_playback_host}/upload_welcome'
                basename = os.path.basename(wav_path)
                with open(wav_path, 'rb') as fh:
                    files = {'file': (basename, fh, 'audio/wav')}
                    r = requests.post(url, files=files, timeout=15)
                if r.status_code == 200:
                    # trigger playback of the uploaded file
                    play_url = f'http://{esp_playback_host}/play?file=/WelcomeAudio/{basename}'
                    pp = requests.get(play_url, timeout=10)
                    return pp.status_code == 200
            except Exception as e:
                print("ESP welcome upload/play failed:", e)
            return False

        def play_welcome_on_esp_by_name(basename):
            """Ask the ESP to play an already-uploaded welcome file by name.
            Returns True if the ESP responded 200."""
            try:
                # sanitize locally
                if '/' in basename or '\\' in basename or '..' in basename:
                    return False
                play_url = f'http://{esp_playback_host}/play_welcome?name={basename}'
                r = requests.get(play_url, timeout=6)
                return r.status_code == 200
            except Exception as e:
                # network error / ESP unreachable
                # print for debugging but keep silent in production
                print('ESP play_welcome failed:', e)
                return False

        # First try to ask the ESP to play an already-uploaded file (no upload).
        try:
            if play_welcome_on_esp_by_name(file_to_play):
                print(f"Asked ESP to play existing welcome file: {file_to_play}")
                return
        except Exception:
            pass

        # If that failed, try uploading and playing.
        try:
            if upload_and_play_on_esp(file_path):
                print(f"Playing welcome audio on ESP at {esp_playback_host}: {file_to_play}")
                return
        except Exception:
            pass

        # Local playback fallback (if ESP unreachable)
        try:
            pygame.mixer.init()
            pygame.mixer.music.load(file_path)
            pygame.mixer.music.play()
            while pygame.mixer.music.get_busy():
                time.sleep(0.1)
            pygame.mixer.quit()
        except Exception as e:
            print("Local welcome playback failed:", e)
    def play_audio(file):
        destination_file = os.path.join(r'uploads', 'GENTA_response.mp3')
        if os.path.exists(destination_file):
            os.remove(destination_file)

        def upload_and_play_on_esp(wav_path):
            try:
                # Ensure Arduino data dir exists and save a copy there for SPIFFS-building convenience
                try:
                    os.makedirs(ARDUINO_DATA_DIR, exist_ok=True)
                    dest = os.path.join(ARDUINO_DATA_DIR, 'response.wav')
                    shutil.copy2(wav_path, dest)
                except Exception as _e:
                    # non-fatal, continue to upload
                    print('Could not copy to Arduino data folder:', _e)

                url = f'http://{esp_playback_host}/upload'
                with open(wav_path, 'rb') as fh:
                    files = {'file': ('response.wav', fh, 'audio/wav')}
                    r = requests.post(url, files=files, timeout=15)
                if r.status_code == 200:
                    # trigger playback of the uploaded response.wav on the ESP
                    pp = requests.get(f'http://{esp_playback_host}/play?file=/response.wav', timeout=8)
                    return pp.status_code == 200
                else:
                    print(f'ESP /upload returned {r.status_code}: {r.text}')
            except Exception as e:
                print("ESP playback/upload failed:", e)
            return False

        # Try to upload to the ESP and play there first. If that fails, fall back to local playback.
        try:
            if upload_and_play_on_esp(file):
                print(f"Playing on ESP at {esp_playback_host}")
                # Best-effort: ask ESP to clear the uploaded/recorded file after triggering playback
                try:
                    clear_url = f'http://{esp_playback_host}/clear'
                    cr = requests.get(clear_url, timeout=3)
                    if cr.status_code != 200:
                        print(f'ESP /clear returned {cr.status_code} when attempting to clear playback file')
                except Exception:
                    pass
                return
        except Exception:
            pass

        # Local playback fallback
        try:
            pygame.mixer.init()
            pygame.mixer.music.load(file)
            pygame.mixer.music.play()
            while pygame.mixer.music.get_busy():
                pygame.time.Clock().tick(10)
            pygame.mixer.quit()
            os.rename(file, destination_file)
        except Exception as e:
            print("Local playback failed:", e)

    # Helper: move any WAVs from RepeatAudio into a processed folder so they don't retrigger
    def move_repeat_file(single_path: str):
        try:
            src = REPEAT_AUDIO_DIR
            if not src or not os.path.exists(src) or not single_path:
                return
            proc_dir = os.path.join(src, 'processed')
            os.makedirs(proc_dir, exist_ok=True)
            fname = os.path.basename(single_path)
            dst_name = f"{int(time.time())}_{fname}"
            dst = os.path.join(proc_dir, dst_name)
            try:
                shutil.move(single_path, dst)
                print(f"Moved repeat-audio file to processed: {fname} -> {dst_name}")
            except Exception as e:
                print(f"Failed moving repeat audio {single_path}: {e}")
        except Exception:
            pass

    def find_newest_repeat_audio():
        try:
            src = REPEAT_AUDIO_DIR
            if not src or not os.path.exists(src):
                return None
            candidates = [os.path.join(src, f) for f in os.listdir(src) if f.lower().endswith('.wav')]
            # exclude processed folder
            candidates = [c for c in candidates if os.path.isfile(c)]
            if not candidates:
                return None
            candidates.sort(key=lambda p: os.path.getmtime(p), reverse=True)
            return candidates[0]
        except Exception:
            return None

    def process_repeat_audio_file(path):
        """Given a WAV file path in RepeatAudio, convert to 16k mono and run STT; returns transcript or empty string."""
        if not path or not os.path.exists(path):
            return ""

        print(f"Processing repeat-audio file for transcription: {path}")
        ffmpeg_path = shutil.which('ffmpeg') or shutil.which('ffmpeg.exe')
        converted_bytes = None
        try:
            # Try ffmpeg to transcode file to 16k mono WAV bytes
            if ffmpeg_path:
                cmd = [ffmpeg_path, '-y', '-i', path, '-f', 'wav', '-ac', '1', '-ar', '16000', '-acodec', 'pcm_s16le', 'pipe:1', '-hide_banner', '-loglevel', 'error']
                proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE)
                out, _ = proc.communicate(timeout=30)
                converted_bytes = out
            else:
                audio = AudioSegment.from_file(path)
                audio = audio.set_channels(1)
                audio = audio.set_frame_rate(16000)
                buf = io.BytesIO()
                audio.export(buf, format='wav')
                converted_bytes = buf.getvalue()
        except Exception as e:
            print('process_repeat_audio_file: conversion failed:', e)
            converted_bytes = None

        if not converted_bytes:
            return ""

        # Transcribe
        try:
            client = speech.SpeechClient.from_service_account_json(r'GoogleCloud\\key.json')
            audio_file = speech.RecognitionAudio(content=converted_bytes)
            config = speech.RecognitionConfig(
                sample_rate_hertz=16000,
                enable_automatic_punctuation=True,
                language_code='fil'
            )
            response = client.recognize(config=config, audio=audio_file)
            complete_text = ""
            if response and hasattr(response, 'results') and len(response.results) > 0:
                for result in response.results:
                    if result.alternatives and len(result.alternatives) > 0:
                        complete_text = result.alternatives[0].transcript
            # save transcription for diagnostics
            try:
                with open('transcribed_text.txt', 'w', encoding='utf-8') as f:
                    f.write(complete_text)
            except Exception:
                pass
            return complete_text
        except Exception as exc:
            print('Transcription error (repeat file):', exc)
            return ""

    def clear_remote_recording(esp_host_local: str = None, audio_url: str = None):
        """Best-effort: attempt to tell the ESP or proxy to remove/clear its recorded file so a subsequent download won't return the same recording.
        Tries a list of common endpoints and HTTP methods. Logs but never raises.
        """
        tried = []
        # helper to attempt a GET
        def try_get(u):
            try:
                r = requests.get(u, timeout=4)
                print(f'clear_remote_recording: GET {u} -> {r.status_code}')
                return r.status_code
            except Exception as e:
                print(f'clear_remote_recording: GET {u} failed: {e}')
                return None

        # helper to attempt a DELETE
        def try_delete(u):
            try:
                r = requests.delete(u, timeout=4)
                print(f'clear_remote_recording: DELETE {u} -> {r.status_code}')
                return r.status_code
            except Exception as e:
                print(f'clear_remote_recording: DELETE {u} failed: {e}')
                return None

        # First try known esp_host_local endpoints
        if esp_host_local:
            base = f'http://{esp_host_local}'
            for path in ['/clear', '/stop', '/delete', '/delete_recording']:
                try_get(base + path)
            # try DELETE on /recording.wav
            try_delete(base + '/recording.wav')

        # Next try deriving host from audio_url (may be a proxy)
        if audio_url:
            try:
                p = urllib.parse.urlparse(audio_url)
                host = p.netloc
                if host:
                    base = f'{p.scheme}://{host}'
                    # try some proxy-specific endpoints
                    for path in ['/clear', '/stop', '/clear_recording', '/delete_recording', '/delete']:
                        try_get(base + path)
                    try_delete(base + '/recording.wav')
            except Exception:
                pass

        # As a last resort, try the playback host as well (it may be the same device)
        try:
            pb = esp_playback_host
            if pb:
                base = f'http://{pb}'
                for path in ['/clear', '/stop']:
                    try_get(base + path)
        except Exception:
            pass
        # clear_remote_recording only performs best-effort HTTP attempts to remove
        # recordings on the ESP/proxy; transcription of repeat-audio files is handled
        # by process_repeat_audio_file().
        return None

    def cleanup_response_artifacts(processed_repeat_path: str = None):
        """Remove local response artifacts and best-effort ask ESP/proxy to delete uploaded response files.
        This helps ensure the previous response recording won't be re-served or replayed.
        """
        # Local files to remove
        local_candidates = [
            os.path.join('.', 'response.wav'),
            os.path.join('uploads', 'GENTA_response.mp3'),
            os.path.join('.', 'transcribed_text.txt')
        ]
        for fpath in local_candidates:
            try:
                if os.path.exists(fpath):
                    os.remove(fpath)
                    print(f'cleanup: removed local file {fpath}')
            except Exception as e:
                print(f'cleanup: failed to remove {fpath}: {e}')

        # If a repeat file was processed, try to remove original if still present
        try:
            if processed_repeat_path and os.path.exists(processed_repeat_path):
                try:
                    os.remove(processed_repeat_path)
                    print(f'cleanup: removed processed repeat file {processed_repeat_path}')
                except Exception:
                    pass
        except Exception:
            pass

        # Best-effort HTTP calls to ESP/playback host and proxy to delete any uploaded response files
        def try_delete_url(u):
            try:
                r = requests.delete(u, timeout=4)
                print(f'cleanup: DELETE {u} -> {r.status_code}')
                return True
            except Exception as e:
                try:
                    r = requests.get(u, timeout=4)
                    print(f'cleanup: GET {u} -> {getattr(r, "status_code", "err")}')
                    return True
                except Exception as _:
                    print(f'cleanup: HTTP attempt failed for {u}: {e}')
                    return False

        # Try a set of likely endpoints on the esp_playback_host
        try:
            if esp_playback_host:
                base = f'http://{esp_playback_host}'
                for p in ['/clear', '/delete', '/remove', '/delete_file?name=response.wav', '/delete?file=response.wav']:
                    try_delete_url(base + p)
        except Exception:
            pass

        # Try derived proxy host from audio_raw_url
        try:
            if audio_raw_url:
                p = urllib.parse.urlparse(audio_raw_url)
                if p.netloc:
                    base = f'{p.scheme}://{p.netloc}'
                    for pth in ['/clear', '/delete_recording', '/delete', '/clear_recording']:
                        try_delete_url(base + pth)
        except Exception:
            pass
        except Exception as exc:
            print('Transcription error (repeat file):', exc)
            return ""

    # If we prepared a personalized welcome, speak it now (use TTS + playback)
    try:
        if 'PERSONAL_WELCOME_MSG' in locals() and PERSONAL_WELCOME_MSG:
            try:
                synthesize_speech(PERSONAL_WELCOME_MSG)
                play_audio('response.wav')
            except Exception:
                pass
            time.sleep(1.0)
    except Exception:
        pass

    # WELCOME MESSAGE ONLY RUN ONCE (fallback or additional welcome audio)
    system_play_audio(r'WelcomeAudio')
    time.sleep(1.5)  # Reduced from 5s to 1.5s - just enough time for audio to finish
    first_iteration = True
    retry_delay = 5
    last_transcribed = None
    while True:
        # Check for state change before each interaction
        if check_for_state_change():
            print("\n[GENTA] State change requested - exiting to restart")
            return  # Exit GENTA() to allow main() to restart with new state
        
        if not first_iteration:
            # Play a short follow-up prompt if available; don't crash if the
            # file is missing (some installations may not include this file).
            try:
                pygame.mixer.init()
                prompt_file = r'Pwede pa ba kitang matulungan_.wav'
                if os.path.exists(prompt_file):
                    pygame.mixer.music.load(prompt_file)
                    pygame.mixer.music.play()
                    while pygame.mixer.music.get_busy():
                        time.sleep(0.1)
                    pygame.mixer.quit()
                else:
                    print(f"Prompt audio not found, will synthesize TTS prompt: {prompt_file}")
                    try:
                        # Synthesize and play a short prompt so the student hears it immediately
                        synth_text = "Pwede pa ba kitang matulungan?"
                        # OPTIMIZATION: Don't translate - text is already in Filipino
                        synthesize_speech(synth_text)
                        play_audio('response.wav')
                    except Exception as _e:
                        print('TTS prompt failed:', _e)
                print("GENTA: Pwede pa ba kitang matulungan?")
            except Exception as e:
                print('Skipping prompt playback due to error:', e)
        # Use the shared record_and_transcribe helper (same behavior as QUIZZER)
        print("Listening for student response...")
        
        # CHECK STATE CHANGE before waiting for recording
        if check_for_state_change():
            print("\n[GENTA] State change detected before recording - exiting to restart")
            return
        
        # OPTIMIZATION: Removed 3-second wait - record_and_transcribe will handle polling
        processed_repeat_path = None
        try:
            # If test/repeat audio exists, process that file instead of polling the ESP/proxy.
            repeat_candidate = find_newest_repeat_audio()
            if repeat_candidate:
                complete_text = process_repeat_audio_file(repeat_candidate)
                processed_repeat_path = repeat_candidate
                forced_timeout = False
            else:
                # Use the same ESP recording host as QUIZZER so we poll /size and download /recording.wav
                complete_text, forced_timeout = record_and_transcribe(esp_host=esp_record_host, poll_for_recording=True, max_poll_seconds=30)
        except Exception as _e:
            print("Recording/transcription helper failed:", _e)
            complete_text, forced_timeout = "", False
        
        # CHECK STATE CHANGE immediately after recording attempt
        if check_for_state_change():
            print("\n[GENTA] State change detected after recording - exiting to restart")
            return

        # Ensure the transcription file exists for downstream tools
        try:
            with open('transcribed_text.txt', 'w', encoding='utf-8') as f:
                f.write(complete_text)
        except Exception:
            pass

        print("You: ", complete_text)

        # Note: we no longer skip duplicate transcriptions here. Instead we will
        # attempt to remove the remote recording after successful processing so
        # the same recording won't be served again.

        # If transcription is empty, retry a few times (mirrors QUIZZER behavior) before giving up.
        MAX_RETRIES = 2
        attempts = 0
        while (not complete_text or not complete_text.strip()) and attempts < MAX_RETRIES and not forced_timeout:
            # CHECK STATE CHANGE during retry loop
            if check_for_state_change():
                print("\n[GENTA] State change detected during retry - exiting to restart")
                return
            
            attempts += 1
            print(f"No transcription received; retrying ({attempts}/{MAX_RETRIES})...")
            # Ask the student to repeat briefly
            try:
                # OPTIMIZATION: Text is already Filipino - no need to translate
                synth_text = "Pasensya, hindi ko narinig. Pakiulit po ang sagot."
                synthesize_speech(synth_text)
                play_audio('response.wav')
            except Exception:
                pass

            # Wait briefly then try recording again
            time.sleep(0.2)  # OPTIMIZATION: Reduced from 0.3s to 0.2s
            try:
                complete_text, forced_timeout = record_and_transcribe(esp_host=esp_record_host, poll_for_recording=True, max_poll_seconds=30)
            except Exception as _e:
                print("Retry recording/transcription failed:", _e)
                complete_text, forced_timeout = "", forced_timeout
            
            # CHECK STATE CHANGE after retry recording
            if check_for_state_change():
                print("\n[GENTA] State change detected after retry - exiting to restart")
                return

            try:
                with open('transcribed_text.txt', 'w', encoding='utf-8') as f:
                    f.write(complete_text)
            except Exception:
                pass

            print("You: ", complete_text)

        if not complete_text or not complete_text.strip():
            # Still empty after retries — handle gracefully and continue to next loop
            print("No valid transcription after retries; skipping to next iteration.")
            try:
                # OPTIMIZATION: Text is already Filipino - no need to translate
                synth_text = "Hindi ko pa rin narinig ang sagot. Pupunta tayo sa susunod."
                synthesize_speech(synth_text)
                play_audio('response.wav')
            except Exception:
                pass
            first_iteration = False
            continue

        # Now we have non-empty transcription — send to the model
        try:
            # OPTIMIZATION: Only translate if text appears to be pure Filipino
            # Model can understand Filipino input, so skip translation for speed
            prompt_text = complete_text  # Send directly without translation
            response = chat.send_message(prompt_text, generation_config={'max_output_tokens':200, 'temperature':1.0},)
        except ValueError as ve:
            print('Model rejected empty input after checks:', ve)
            # Inform user and continue
            try:
                # OPTIMIZATION: Text is already Filipino - no need to translate
                synth_text = "May problema sa pagproseso ng iyong sagot. Pakiulit mamaya."
                synthesize_speech(synth_text)
                play_audio('response.wav')
            except Exception:
                pass
            first_iteration = False
            continue
        
        # Check if the prompt was blocked by safety filters
        if not response.candidates and hasattr(response, 'prompt_feedback') and response.prompt_feedback.block_reason == 'SAFETY':
            curse_response = "Please refrain from using bad words. Paumanhin, iwasan po natin ang pagmumura."
            print("GENTA:", curse_response)
            synthesize_speech(curse_response)
            play_audio('response.wav')
            first_iteration = False
            continue

        # TRANSLATION / extract text robustly from response
        def _extract_model_text(resp):
            # Try multiple known shapes returned by different SDK versions.
            try:
                # 1) candidates -> content -> parts -> [0].text
                candidates = getattr(resp, 'candidates', None)
                if candidates:
                    for cand in candidates:
                        # try content.parts
                        content = getattr(cand, 'content', None)
                        if content is not None:
                            parts = getattr(content, 'parts', None)
                            if parts and len(parts) > 0:
                                first = parts[0]
                                if hasattr(first, 'text') and first.text:
                                    return first.text
                                # some SDKs use dict-like parts
                                if isinstance(first, dict) and first.get('text'):
                                    return first.get('text')
                            # fallback: content.text
                            txt = getattr(content, 'text', None)
                            if isinstance(txt, str) and txt:
                                return txt
                            # content might be a plain string
                            if isinstance(content, str) and content:
                                return content
                        # try cand.text directly
                        cand_text = getattr(cand, 'text', None)
                        if isinstance(cand_text, str) and cand_text:
                            return cand_text

                # 2) top-level response.text
                top_text = getattr(resp, 'text', None)
                if isinstance(top_text, str) and top_text:
                    return top_text

                # 3) try repr as last resort (shortened)
                return None
            except Exception as ex:
                print('extract_model_text: error while parsing response object:', ex)
                return None

        answer = _extract_model_text(response) or ""

        # If the chat response contains no usable text, attempt a direct
        # non-chat generation fallback (some SDKs/models return an empty
        # parts list for chat responses but generate_content() may return
        # a usable top-level text). This improves robustness against
        # inconsistent SDK shapes.
        if not answer:
            try:
                print('Warning: model response contained no text; attempting fallback generate_content()')
                # First try a default generate_content call
                try:
                    fb = model.generate_content(prompt_text)
                except TypeError:
                    # Some SDKs require keyword args for generation settings
                    try:
                        fb = model.generate_content(prompt_text, max_output_tokens=512, temperature=1.0)
                    except Exception as _fb_e:
                        fb = None
                fb_text = None
                try:
                    if fb is not None:
                        fb_text = _extract_model_text(fb) or getattr(fb, 'text', None)
                except Exception:
                    fb_text = getattr(fb, 'text', None) if fb is not None else None
                if fb_text:
                    answer = fb_text
                    print('Fallback generate_content provided text (truncated):', str(answer)[:400])
                else:
                    # If still empty and the candidate indicated MAX_TOKENS, try a bigger generation
                    try:
                        print('Fallback empty; attempting extended generate_content with larger token budget')
                        try:
                            fb2 = model.generate_content(prompt_text, max_output_tokens=1024, temperature=0.9)
                        except TypeError:
                            fb2 = model.generate_content(prompt_text)
                        fb2_text = None
                        try:
                            fb2_text = _extract_model_text(fb2) or getattr(fb2, 'text', None)
                        except Exception:
                            fb2_text = getattr(fb2, 'text', None) if fb2 is not None else None
                        if fb2_text:
                            answer = fb2_text
                            print('Extended fallback provided text (truncated):', str(answer)[:400])
                    except Exception as _fb_e:
                        print('Extended fallback failed:', _fb_e)
            except Exception as _fb_e:
                print('Fallback generate_content() failed:', _fb_e)
            except Exception:
                pass

        if not answer:
            # Handle cases where there are no candidates or no text. Log debug info
            try:
                print('Warning: model response contained no text. Raw response summary:')
                # print some useful diagnostics without flooding the terminal
                try:
                    print('  candidates_count=', len(getattr(response, 'candidates', []) or []))
                except Exception:
                    pass
                try:
                    first_cand = (getattr(response, 'candidates', None) or [None])[0]
                    if first_cand is not None:
                        print('  first_candidate_repr=', str(first_cand)[:400])
                        print('  first_candidate_finish_reason=', getattr(first_cand, 'finish_reason', None))
                except Exception:
                    pass
            except Exception:
                pass
            error_response = "I'm sorry, I could not process that. Please try again."
            print("GENTA:", error_response)
            # OPTIMIZATION: Use Filipino directly - no translation needed
            error_response_fil = "Paumanhin, hindi ko naproseso ang iyong tanong. Pakiulit po."
            synthesize_speech(error_response_fil)
            play_audio('response.wav')
            continue
        
        ConvertedAnswer = convert_apostrophe(answer)
        # Simplify and clean the model's text for grade-3 clarity and TTS friendliness
        try:
            ConvertedAnswer = simplify_for_grade3(ConvertedAnswer)
        except Exception:
            pass

        # OPTIMIZATION: Model now responds in Filipino directly, so check if translation is needed
        # If the response is already in Filipino (contains Filipino words), skip translation
        needs_translation = True
        filipino_indicators = ['ang', 'ng', 'sa', 'ay', 'mga', 'ba', 'po', 'ko', 'mo', 'siya']
        if any(word in ConvertedAnswer.lower() for word in filipino_indicators):
            needs_translation = False
            TranslatedResponse = ConvertedAnswer
            print("OPTIMIZATION: Response already in Filipino, skipping translation")
        
        if needs_translation:
            TranslatedResponse = TranslateToFil(ConvertedAnswer)
        
        synthesize_speech(TranslatedResponse)

        print("GENTA:",  TranslatedResponse)

        play_audio('response.wav')
        # After successfully answering, mark this transcription as processed and move the processed repeat file (if any)
        try:
            last_transcribed = complete_text
            if processed_repeat_path:
                try:
                    move_repeat_file(processed_repeat_path)
                except Exception:
                    pass
        except Exception:
            pass

        # Best-effort: clear/delete the remote recording so the same audio isn't served again
        try:
            # prefer esp_record_host if configured, otherwise pass the audio_raw_url for derived attempts
            clear_remote_recording(esp_host_local=esp_record_host, audio_url=audio_raw_url)
            try:
                cleanup_response_artifacts(processed_repeat_path)
            except Exception:
                pass
        except Exception:
            pass
        first_iteration = False


def QUIZZER():
    global CURRENT_STUDENT_ID, CURRENT_TEACHER_ID, CURRENT_TEACHER_NAME, CURRENT_STUDENT_NAME
    
    print("\n" + "="*70)
    print("📝 QUIZ MODE - Retrieving Student Information")
    print("="*70)
    
    # IMPORTANT: Retrieve student info to get teacher_id BEFORE loading quiz
    # The teacher_id determines which questions to load from the database
    if not CURRENT_TEACHER_ID:
        print("\n⚠ WARNING: No teacher ID available!")
        print("Student must enter LRN in Assisting Mode first to get teacher info.")
        print("Returning to Assisting Mode...")
        
        # Set state back to 0 (Assisting Mode)
        try:
            set_state_url = "https://nonbasic-bob-inimical.ngrok-free.dev/set_state"
            requests.get(f"{set_state_url}?value=0", timeout=15)
            print("✓ State reset to Assisting Mode")
        except Exception as e:
            print(f"⚠ Could not reset state: {e}")
        
        return  # Exit Quiz Mode
    
    # Display student and teacher info
    print(f"\n✓ Student: {CURRENT_STUDENT_NAME} (LRN: {CURRENT_STUDENT_ID})")
    print(f"✓ Teacher: {CURRENT_TEACHER_NAME} (ID: {CURRENT_TEACHER_ID})")
    print(f"✓ Loading quiz questions from Teacher ID: {CURRENT_TEACHER_ID}")
    print("="*70 + "\n")
    
    with open(conversation_file_path, 'w') as conv_file:
        conv_file.write("Conversation Log:\n\n")

    messages = [
        # system message first, it helps set the behavior of the assistant
        {"role": "user", "content": """ 
        Analyze and write a detailed bulleted list of the specific strengths and specific weaknesses of a student based on this quiz conversation text, 
        and provide innovative strategies to mitigate the weakness. Create a detailed lesson plan at the end.
        """},
    ]
    module_messages = [
        # system message first, it helps set the behavior of the assistant
        {"role": "user", "content": """
        Based on this quiz conversation text, analyze the student's specific weaknesses (only select those that are related to mathematics).
        Based on the weakness analysis, write a comprehensive and detailed tailored instructional e-book that will be read by a grade 3 student. 
        You should cover the fundamentals of each weaknesses that can be easily understood by the student, explain like im 5.
        """},
    ]    
    module_messages2 = [
        # system message first, it helps set the behavior of the assistant
        {"role": "user", "content": """
        Based on this tailored instructional e-book that will be read by a grade 3 student, create real world (for kids) examples with a comprehensive and detailed step-by-step solving instructions, 
        and 5 real world (for kids) problems of each topic that a student could answer. 
        """},
    ]     
    def log_conversation(log_entry):
        with open(conversation_file_path, 'a') as conv_file:
            conv_file.write(log_entry + "\n")
    def synthesize_speech(text):
            client = texttospeech_v1.TextToSpeechClient()
            voice1 = texttospeech_v1.VoiceSelectionParams(
                name='fil-ph-Neural2-A',
                language_code='fil-ph'
            )
            audio_config = texttospeech_v1.AudioConfig(
                audio_encoding=texttospeech_v1.AudioEncoding.LINEAR16,
                pitch=6.00
            )
            response = client.synthesize_speech(
                input=texttospeech_v1.SynthesisInput(text=text),
                voice=voice1,
                audio_config=audio_config
            )
            with open('response.wav', 'wb') as out:
                out.write(response.audio_content)
    def TranslateToFil(text):
        translate_client = translate_v2.Client()
        # Perform translation
        translated_response = translate_client.translate(text, target_language="fil")
        # Extract translated text from the response dictionary
        translated_text = translated_response['translatedText']
        # Write output to file
        with open(r'uploads\output.txt', 'w', encoding='utf-8') as f:
            f.write(translated_text) 
        return translated_text   
    def TranslateToEng(text):
        translate_client = translate_v2.Client()
        # Perform translation
        translated_response = translate_client.translate(text, target_language="en")
        # Extract translated text from the response dictionary
        translated_text = translated_response['translatedText']
        return translated_text 
    def play_audio(file):
        destination_file = os.path.join(r'uploads', 'GENTA_response.mp3')
        if os.path.exists(destination_file):
            os.remove(destination_file)
        # Initialize Pygame mixer
        pygame.mixer.init()
        # Load and play the audio file
        pygame.mixer.music.load(file)
        pygame.mixer.music.play()
        # Wait for playback to finish
        while pygame.mixer.music.get_busy():
            pygame.time.Clock().tick(10)  # Adjust the playback speed
            continue
        # Quit Pygame mixer
        pygame.mixer.quit()
        # Rename the file to the destination directory
        os.rename(file, destination_file)        
    def ordinal(n):
        suffix = ['th', 'st', 'nd', 'rd', 'th'][min(n % 10, 4)]
        if 11 <= (n % 100) <= 13:
            suffix = 'th'
        return str(n) + suffix
    def load_quiz(file_path, delimiter='*'):
        """Load active questions. If CURRENT_TEACHER_ID is set, restrict to that teacher's questions.
        Falls back to file if DB query fails.
        """
        questions = []
        
        print(f"\n[load_quiz] Starting quiz load...")
        print(f"[load_quiz] CURRENT_TEACHER_ID = {CURRENT_TEACHER_ID}")
        print(f"[load_quiz] File path = {file_path}")
        
        try:
            # Connect to the XAMPP MySQL database
            print("[load_quiz] Connecting to MySQL database 'my_app'...")
            connection = mysql.connector.connect(host='localhost', database='my_app', user='root', password='')
            cursor = connection.cursor()
            
            # Query to fetch only active questions
            if CURRENT_TEACHER_ID:
                query = "SELECT description, answer FROM questions WHERE status = 1 AND teacher_id = %s"
                print(f"[load_quiz] Executing query with teacher_id = {CURRENT_TEACHER_ID}")
                cursor.execute(query, (CURRENT_TEACHER_ID,))
            else:
                query = "SELECT description, answer FROM questions WHERE status = 1"
                print("[load_quiz] WARNING: No teacher_id set - loading ALL active questions")
                cursor.execute(query)
            
            rows = cursor.fetchall()
            print(f"[load_quiz] Found {len(rows)} questions in database")
            
            for row in rows:
                question = row[0]  # Description is the question
                answer = row[1]    # Answer
                questions.append({'question': question, 'answer': answer})
                print(f"[load_quiz]   - Q: {question[:50]}... A: {answer}")

            cursor.close()
            connection.close()
            
            if len(questions) == 0:
                print("[load_quiz] WARNING: No questions found in database!")
            else:
                print(f"[load_quiz] ✓ Successfully loaded {len(questions)} questions from database")
                
        except mysql.connector.Error as error:
            print(f"[load_quiz] ERROR connecting to MySQL database: {error}")
            print("[load_quiz] Will attempt to load from file as fallback...")
            
            # FALLBACK: Try loading from file
            try:
                if os.path.exists(file_path):
                    with open(file_path, 'r', encoding='utf-8') as file:
                        content = file.read()
                        qa_pairs = content.split(delimiter)
                        for pair in qa_pairs:
                            parts = pair.strip().split('\n', 1)
                            if len(parts) == 2:
                                questions.append({'question': parts[0], 'answer': parts[1]})
                    print(f"[load_quiz] Loaded {len(questions)} questions from file: {file_path}")
                else:
                    print(f"[load_quiz] ERROR: File not found: {file_path}")
            except Exception as file_error:
                print(f"[load_quiz] ERROR loading from file: {file_error}")

        return questions
    
    def run_quiz(questions):
        score = 0
        for i, q in enumerate(questions, start=1):
            question_text = f"{ordinal(i)} question: {q['question']}"
            print(question_text)
            log_conversation(question_text)
            synthesize_speech(TranslateToFil(question_text))
            play_audio('response.wav')
            
            print(f"Waiting for student to answer question {i}...")
            
            # CLEAR PREVIOUS RECORDING before waiting for new one
            print(f"[Q{i}] Clearing any previous recordings...")
            try:
                # Clear local file
                if os.path.exists(audio_raw_path):
                    os.remove(audio_raw_path)
                    print(f"[Q{i}] ✓ Cleared local recording")
                
                # Clear remote recording via proxy endpoints
                try:
                    _http_session.get('https://nonbasic-bob-inimical.ngrok-free.dev/clear', timeout=3)
                    print(f"[Q{i}] ✓ Cleared remote recording (ESP32)")
                except Exception as clear_err:
                    print(f"[Q{i}] ⚠ Could not clear remote: {clear_err}")
            except Exception as e:
                print(f"[Q{i}] ⚠ Cleanup warning: {e}")
            
            # Wait for NEW recording using modern helper
            print(f"[Q{i}] Waiting for NEW answer recording...")
            try:
                complete_text, forced_timeout = record_and_transcribe(
                    esp_host=esp_record_host, 
                    poll_for_recording=True, 
                    max_poll_seconds=60  # Allow up to 60s for student to answer
                )
            except Exception as rec_err:
                print(f"[Q{i}] Recording/transcription error: {rec_err}")
                complete_text = ""
                forced_timeout = False
            
            # Handle empty/timeout responses
            if not complete_text or not complete_text.strip():
                if forced_timeout:
                    timeout_msg = "Nag-timeout na. Sumunod na tanong."
                    print(f"[Q{i}] Timeout - no answer received")
                    log_conversation(f"Student Answer: [TIMEOUT]")
                    log_conversation(f"Oops! Ang tamang sagot ay {q['answer']}.")
                    synthesize_speech(timeout_msg)
                    play_audio('response.wav')
                else:
                    no_answer_msg = "Walang narinig na sagot. Sumunod na tanong."
                    print(f"[Q{i}] No transcription received")
                    log_conversation(f"Student Answer: [NO ANSWER]")
                    log_conversation(f"Oops! Ang tamang sagot ay {q['answer']}.")
                    synthesize_speech(no_answer_msg)
                    play_audio('response.wav')
                
                # CLEAR the failed recording before next question
                try:
                    _http_session.get('https://nonbasic-bob-inimical.ngrok-free.dev/clear', timeout=3)
                except Exception:
                    pass
                
                time.sleep(2)
                continue
            
            # Write transcription to file
            try:
                with open('transcribed_text.txt', 'w', encoding='utf-8') as f:
                    f.write(complete_text)
            except Exception:
                pass
            
            print(f"You: {complete_text}")
            user_answer = complete_text
            log_conversation(f"Student Answer: {user_answer}")
            
            # CLEAR the recording immediately after transcription
            print(f"[Q{i}] Clearing used recording...")
            try:
                _http_session.get('https://nonbasic-bob-inimical.ngrok-free.dev/clear', timeout=3)
                print(f"[Q{i}] ✓ Recording cleared for next question")
            except Exception as clear_err:
                print(f"[Q{i}] ⚠ Could not clear after use: {clear_err}")

            # Curse word detection using AI safety filters
            if is_profane_by_ai(user_answer):
                curse_response = "Please refrain from using bad words. Paumanhin, iwasan po natin ang pagmumura."
                print("GENTA:", curse_response)
                log_conversation(f"Oops! Ang tamang sagot ay {q['answer']}.") # For CSV parser
                synthesize_speech(curse_response)
                play_audio('response.wav')
            elif user_answer.lower() == q['answer'].lower():
                response_text = "Tama!"
                print(response_text)
                log_conversation(response_text)
                synthesize_speech(response_text)
                play_audio('response.wav')
                score += 1
            else:
                response_text = f"Oops! Ang tamang sagot ay {q['answer']}."
                print(response_text)
                log_conversation(response_text)
                synthesize_speech(response_text)
                play_audio('response.wav')

            time.sleep(2) # BREATHER DELAY before next question

        result_text = f"Nakakuha ka ng {score} tamang sagot, mula sa {len(questions)} tanong."
        result_log_text = f"Student got {score} out of {len(questions)} questions correct."
        print(result_text)
        log_conversation(result_log_text)
        synthesize_speech(result_text)
        play_audio('response.wav')
        


    def quiz_analysis(conversation_log, output_docx_path):
        with open(conversation_log, 'r') as file:
            conversation_text3 = file.read()
            conversation_text2 = conversation_text3.replace("Tama", "Correct")
            conversation_text = conversation_text2.replace(" Ang tamang sagot ay", "The correct answer is")

        # Perform analysis using PALM AI
        analysis_result = model.generate_content(str(messages)+" "+conversation_text)
        # Get the analysis text
        #analysis_text = "Quiz Analysis Result:\n" + analysis_result.result

        # Check if the docx file already exists
        if os.path.exists(output_docx_path):
            # Create a new docx file if it already exists
            existing_doc = docx.Document()
        else:
            # Create a new docx file if it doesn't exist
            existing_doc = docx.Document()
        #Add Title
        existing_doc.add_paragraph("Quiz Analysis Result: "+ftime)
        # Add the analysis text to the doc
        existing_doc.add_paragraph(analysis_result.text)

        # Append the conversation log at the end
        existing_doc.add_paragraph("\n\nTHIS PART IS THE QUIZ CONVERSATION LOG:\n")
        existing_doc.add_paragraph(conversation_text)

        # Save the docx file
        existing_doc.save(output_docx_path)
        print("Successfully created analysis_result.docx")

    def tailored_module(conversation_log, quiz_analysis_file_path, output_docx_tailoredmodule_path):
        with open(conversation_log, 'r') as file:
            conversation_text3 = file.read()
            conversation_text2 = conversation_text3.replace("Tama", "Correct")
            conversation_text = conversation_text2.replace(" Ang tamang sagot ay", "The correct answer is")

        # Open the DOCX file and read its content
        with open(quiz_analysis_file_path, 'rb') as file:
            doc = docx.Document(file)
            quiz_analysis = ""
            for paragraph in doc.paragraphs:
                if "Lesson Plan" in paragraph.text:
                    break  # Exit the loop when "Lesson Plan" is found
                quiz_analysis += paragraph.text + "\n"

        # Perform analysis
        tailored_module_result = model.generate_content(conversation_text + " " + str(module_messages))

        # Get the analysis text
        #module_text = "TAILORED MODULE:\n" + tailored_module_result.result

        # Check if the docx file already exists
        if os.path.exists(output_docx_tailoredmodule_path):
         # Create a new docx file if it already exists
            existing_doc = docx.Document()
        else:
            # Create a new docx file if it doesn't exist
            existing_doc = docx.Document()

        # Add the analysis text to the doc
        existing_doc.add_paragraph("TAILORED MODULE: " + ftime + "\"")
        existing_doc.add_paragraph(tailored_module_result.text)

        # Save the docx file
        existing_doc.save(output_docx_tailoredmodule_path)
        print("Writing tailored module 1/2")
        # Open the DOCX file and read its content
        with open(r'uploads\tailored_module.docx', 'rb') as file:
            existing_doc = docx.Document(file)
            previous_exported_docx = "\n".join([paragraph.text for paragraph in existing_doc.paragraphs])

        # Perform analysis using PALM AI
        tailored_module_result2 = model.generate_content(str(module_messages2)+" "+previous_exported_docx)

        # Get the new analysis text
        #module_text2 = tailored_module_result2.result

        # Append the new analysis text to the doc
        existing_doc.add_paragraph(tailored_module_result2.text)

        # Save the updated docx file
        existing_doc.save(r'uploads\tailored_module.docx')
        print("Successfully created tailored module")

    quiz_questions = load_quiz(file_path)
    
    # CRITICAL CHECK: Do not proceed if no questions were loaded
    if not quiz_questions or len(quiz_questions) == 0:
        print("\n" + "="*70)
        print("⚠ ERROR: No quiz questions found!")
        print("="*70)
        if CURRENT_TEACHER_ID:
            print(f"No questions found for Teacher ID: {CURRENT_TEACHER_ID}")
            print("\nPossible reasons:")
            print("1. No questions in database for this teacher")
            print("2. All questions for this teacher have status = 0 (inactive)")
            print("3. Database connection failed")
        else:
            print("No teacher ID available - cannot load teacher-specific questions")
        print("\nPlease:")
        print("- Check the 'questions' table in MySQL database 'my_app'")
        print("- Ensure teacher_id column matches the student's teacher")
        print("- Ensure at least one question has status = 1 (active)")
        print("="*70)
        
        # Return to Assisting Mode
        try:
            set_state_url = "https://nonbasic-bob-inimical.ngrok-free.dev/set_state"
            requests.get(f"{set_state_url}?value=0", timeout=15)
            print("✓ Returning to Assisting Mode")
        except Exception:
            pass
        return
    
    print(f"\n✓ Starting quiz with {len(quiz_questions)} questions\n")
    run_quiz(quiz_questions)
    quiz_analysis(conversation_file_path, output_docx_path)
    print("Quiz was analyzed successfully.")
    tailored_module(conversation_file_path, output_docx_path, output_docx_tailoredmodule_path)
    print("Tailored module was created successfully.")
    #Create CSV File of the quiz results
    # Define the destination directory
    destination_directory = r'uploads'
    # Define the destination path
    destination_path = os.path.join(destination_directory, 'conversation_log.csv')          
    # Define the conversation log file path
    log_file_path = r'QUIZ File\conversation_log.txt'

    # Get the Unix timestamp for the file creation time
    created_timestamp = os.path.getctime(log_file_path)
    modified_timestamp = os.path.getmtime(log_file_path)

    # Convert the Unix timestamps to datetime objects
    created_datetime = datetime.fromtimestamp(created_timestamp)
    modified_datetime = datetime.fromtimestamp(modified_timestamp)

    # Define the desired datetime format
    datetime_format = "%d/%m/%Y %I:%M:%S %p"

    # Format the datetime objects
    formatted_created_datetime = created_datetime.strftime(datetime_format)
    formatted_modified_datetime = modified_datetime.strftime(datetime_format)

    # Define the CSV file path
    csv_file_path = r'QUIZ File\conversation_log.csv'
    # Define the CSV fieldnames
    fieldnames = ["id", "student_quiz_id", "description", "image", "choices", "answer", "student_answer", "score", "status", "created", "modified"]
    # Initialize a list to store conversation log entries
    conversation_log = []

    # Read the conversation log file line by line
    with open(log_file_path, mode="r", encoding="utf-8") as logfile:
        current_entry = {}
        for line in logfile:
            # Check if the line contains the question number and description
            match = re.match(r"(\d+(?:st|nd|rd|th) question): (.+)", line.strip())
            if match:
                if current_entry:
                    conversation_log.append(current_entry)
                    current_entry = {"student_quiz_id": 22, "description": match.group(2)} # Replace with your student quiz ID
            elif "Student Answer:" in line:
                # Extract student answer
                student_answer = line.split(":")[1].strip()
                current_entry["student_answer"] = student_answer
            elif "Oops! Ang tamang sagot ay" in line:
                # Extract correct answer
                correct_answer = line.split("ay")[1].strip()
                current_entry["answer"] = correct_answer
                current_entry["status"] = "Incorrect"
                conversation_log.append(current_entry)
                current_entry = {}

    # Add the last entry to conversation log
    if current_entry:
        conversation_log.append(current_entry)

    # Write the conversation log data to the CSV file
    with open(csv_file_path, mode="w", newline="", encoding="utf-8") as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        # Write header
        writer.writeheader()
        # Write data
        for entry in conversation_log:
            entry["id"] = ""  # Set the id column to be blank
            writer.writerow(entry)

    # Read the CSV file and update fields
    updated_conversation_log = []
    with open(csv_file_path, mode="r", encoding="utf-8") as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            # Update answer field if it's blank
            if not row["answer"]:
                row["answer"] = row["student_answer"]
            # Update status field if it's blank
            if not row["status"]:
                row["status"] = "Correct"
            updated_conversation_log.append(row)

    # Set score based on status
    for entry in updated_conversation_log:
        entry["score"] = 1 if entry["status"] == "Correct" else 0

    # Write the updated conversation log data back to the CSV file
    with open(csv_file_path, mode="a", newline="", encoding="utf-8") as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        # Write data
        for entry in updated_conversation_log:
            # Set created and modified timestamps
            entry["created"] = formatted_created_datetime
            entry["modified"] = formatted_modified_datetime
            writer.writerow(entry)

    # Write the updated conversation log data back to the CSV file without the header
    with open(csv_file_path, mode="w", newline="", encoding="utf-8") as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        # Write data without header
        for entry in updated_conversation_log:
            # Set created and modified timestamps
            entry["created"] = formatted_created_datetime
            entry["modified"] = formatted_modified_datetime
            writer.writerow(entry)
    # Move the CSV file to the destination directory
    if os.path.exists(destination_path):
        os.remove(destination_path)
    os.rename(csv_file_path, destination_path)  
    print("CSV file exported successfully.")

    try:
        con = mysql.connector.connect(host='localhost', database='my_app', user='root', password='')
        cur = con.cursor()

        # Read the CSV file and iterate over its rows
        with open(destination_path, mode="r", newline="", encoding="utf-8") as csvfile:
            reader = csv.reader(csvfile)
            # Iterate over the rows and construct queries
            for row in reader:
                try:
                    # Construct the query using the values from the row
                    query = f"INSERT INTO `student_quiz_questions` (`student_quiz_id`, `description`, `image`, `choices`, `answer`, `student_answer`, `score`, `status`, `created`, `modified`) VALUES ({row[1]}, '{row[2]}', '{row[3]}', '{row[4]}', '{row[5]}', '{row[6]}', '{row[7]}', '{row[8]}', '{row[9]}', '{row[10]}')"                      
                    # Now you can execute the query or perform any other operation
                    cur.execute(query)  # Execute the query
                    print("Data inserted successfully.")
                except IndexError:
                    print("Error: Row does not contain expected number of fields")
                except Exception as e:
                    print(f"Error occurred: {e}")

        # Commit changes to the database
        con.commit()
        # Update the status of the last 10 entries
        query_update = "UPDATE `student_quiz_questions` SET `score` = '1', `status` = '1', `created` = CURRENT_TIMESTAMP, `modified` = CURRENT_TIMESTAMP ORDER BY `id` DESC LIMIT 10"
        cur.execute(query_update)
        print("Status updated for the last 10 entries.")
        con.commit()
    except Error as error:
        print("Insert data failed due to {}".format(error))
    finally:
        if con.is_connected():
            # Close cursor and database connection
            cur.close()
            con.close()
            print("MySQL connection is closed")

def state_monitor_thread():
    """Background thread that monitors state changes from ESP32."""
    global _STATE_CHANGE_REQUESTED, _STATE_MONITOR_ACTIVE, _CURRENT_STATE
    
    print("[State Monitor] Thread started")
    _STATE_MONITOR_ACTIVE = True
    check_interval = 2  # Check state every 2 seconds
    
    while _STATE_MONITOR_ACTIVE:
        try:
            # Read current state from ESP32
            new_state = read_state_text_file(url_state)
            
            if new_state and new_state.strip():
                new_state = new_state.strip()
                
                # Check if state has changed
                if new_state != _CURRENT_STATE:
                    print(f"\n[State Monitor] State change detected: {_CURRENT_STATE} → {new_state}")
                    print(f"[State Monitor] {('ASSISTING MODE' if new_state == '0' else 'QUIZ MODE')}")
                    _STATE_CHANGE_REQUESTED = True
                    _STATE_MONITOR_ACTIVE = False  # Stop monitoring to allow restart
                    break
            
            time.sleep(check_interval)
            
        except Exception as e:
            # Silent fail - don't spam console with connection errors
            time.sleep(check_interval)
    
    print("[State Monitor] Thread stopped")

def main():
    global GENTA_State, _STATE_CHANGE_REQUESTED, _STATE_MONITOR_ACTIVE, _CURRENT_STATE
    
    print("\n" + "="*70)
    print("GENTA SYSTEM STARTING - State Monitoring Enabled")
    print("="*70)
    
    # CRITICAL: Clear old recordings on startup to ensure fresh session
    print("\n[Startup Cleanup] Clearing old recordings from ESP32...")
    try:
        clear_resp = _http_session.get('https://nonbasic-bob-inimical.ngrok-free.dev/clear', timeout=5)
        if clear_resp.status_code == 200:
            print("✓ Old recordings cleared successfully")
        else:
            print(f"⚠ Clear returned status: {clear_resp.status_code}")
    except Exception as e:
        print(f"⚠ Could not clear old recordings: {e}")
    
    # Delete local recording files too
    try:
        if os.path.exists(audio_raw_path):
            os.remove(audio_raw_path)
            print("✓ Removed local recording.wav")
        if os.path.exists(audio_converted_path):
            os.remove(audio_converted_path)
            print("✓ Removed local Recording.wav")
    except Exception as e:
        print(f"⚠ Local cleanup warning: {e}")
    
    # FIRST THING: Set state to 0 (Assisting Mode) on startup
    set_state_to_assisting_mode()
    time.sleep(1)  # Give ESP32 time to update state file
    
    print("Monitoring state from: " + url_state)
    
    # Test if ESP32 is serving state.txt properly
    print("\n[System Check] Testing ESP32 state.txt endpoint...")
    try:
        test_state = read_state_text_file(url_state)
        if test_state is not None:
            print(f"✓ ESP32 state.txt accessible: Current state = {test_state}")
        else:
            print("⚠ WARNING: Cannot reach state.txt endpoint")
            print("  Make sure:")
            print("  1. ESP32 is powered on and connected")
            print("  2. Flask proxy is running")
            print("  3. ngrok tunnel is active")
    except Exception as e:
        print(f"⚠ State endpoint test failed: {e}")
    
    print("\nPress GPIO 22 button on ESP32 to toggle between modes:")
    print("  State 0 = Assisting Mode")
    print("  State 1 = Quiz Mode")
    print("  Note: Button is DISABLED until LRN is entered")
    print("="*70 + "\n")
    
    while True:
        try:
            # Read current state from ESP32
            GENTA_State = read_state_text_file(url_state)
            
            if GENTA_State is None or not GENTA_State.strip():
                GENTA_State = "0"
                print("⚠ Could not read state from server. Using default state (0)...")
            
            # Clean the state value (remove whitespace)
            GENTA_State = GENTA_State.strip()
            _CURRENT_STATE = GENTA_State
            _STATE_CHANGE_REQUESTED = False
            
            # Start background state monitoring thread
            monitor_thread = threading.Thread(target=state_monitor_thread, daemon=True)
            monitor_thread.start()
            
            if GENTA_State == "0":
                print("\n" + "="*70)
                print("🎓 GENTA ASSISTING MODE (State 0) - ACTIVE")
                print("="*70 + "\n")
                
                try:
                    GENTA()
                    # If GENTA() exits normally, check if it was due to state change
                    if not _STATE_CHANGE_REQUESTED:
                        print("\n✓ GENTA Assisting Mode session completed normally")
                        break
                except KeyboardInterrupt:
                    print("\n\n⚠ Keyboard interrupt detected. Exiting GENTA system...")
                    _STATE_MONITOR_ACTIVE = False
                    break
                except Exception as e:
                    print(f"\n⚠ Error in GENTA Assisting Mode: {e}")
                    _STATE_MONITOR_ACTIVE = False
                    if not _STATE_CHANGE_REQUESTED:
                        print("Restarting in 3 seconds...")
                        time.sleep(3)
                    
            elif GENTA_State == "1":
                print("\n" + "="*70)
                print("📝 GENTA QUIZ MODE (State 1) - ACTIVE")
                print("="*70 + "\n")
                
                try:
                    QUIZZER()
                    # If QUIZZER() exits normally, check if it was due to state change
                    if not _STATE_CHANGE_REQUESTED:
                        print("\n✓ GENTA Quiz Mode session completed normally")
                        break
                except KeyboardInterrupt:
                    print("\n\n⚠ Keyboard interrupt detected. Exiting GENTA system...")
                    _STATE_MONITOR_ACTIVE = False
                    break
                except Exception as e:
                    print(f"\n⚠ Error in GENTA Quiz Mode: {e}")
                    _STATE_MONITOR_ACTIVE = False
                    if not _STATE_CHANGE_REQUESTED:
                        print("Restarting in 3 seconds...")
                        time.sleep(3)
                    
            else:
                print(f"⚠ Invalid state '{GENTA_State}' received from server.")
                print("Valid states: 0 (Assisting) or 1 (Quiz)")
                print("Waiting 5 seconds before retry...")
                _STATE_MONITOR_ACTIVE = False
                time.sleep(5)
            
            # If state change was requested, loop will restart with new state
            if _STATE_CHANGE_REQUESTED:
                _STATE_MONITOR_ACTIVE = False
                print("\n" + "="*70)
                print("🔄 RESTARTING GENTA with new state...")
                print("="*70)
                time.sleep(1)
                continue
                
        except KeyboardInterrupt:
            print("\n\n⚠ Keyboard interrupt detected. Exiting GENTA system...")
            _STATE_MONITOR_ACTIVE = False
            break
        except Exception as e:
            print(f"\n⚠ Unexpected error in main loop: {e}")
            _STATE_MONITOR_ACTIVE = False
            print("Restarting in 5 seconds...")
            time.sleep(5)

if __name__ == "__main__":
    main()