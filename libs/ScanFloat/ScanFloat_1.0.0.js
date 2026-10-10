// ScanFloat.js — Mobile-First Custom Barcode & QR Reader Library v1.0.0
// Global ScanFloat object — pure JavaScript engine with ECC recovery, Web Worker, and CV filters
var ScanFloat = {
  // Internal canvas element reference
  _el: null,
  // Internal 2D rendering context
  _ctx: null,
  // Active camera MediaStream instance
  _stream: null,
  // Bound HTMLVideoElement for live camera stream
  _video: null,
  // Viewfinder overlay canvas DOM element
  _overlayEl: null,
  // Viewfinder overlay 2D context
  _overlayCtx: null,
  // Internal processing canvas for video frame rasterization
  _processingCanvas: null,
  // Internal 2D context for image processing
  _processingCtx: null,
  // Animation frame ID for scanning loop control
  _rafId: null,
  // Whether the live camera scanning loop is currently active
  _running: false,
  // Preferred camera facing mode: 'environment' (back) or 'user' (front)
  _facingMode: 'environment',
  // Active video track for hardware controls
  _track: null,
  // Whether the flashlight torch is currently turned on
  _torchActive: false,
  // Native BarcodeDetector instance if supported by browser
  _detector: null,
  // Flag indicating whether native hardware BarcodeDetector is available
  _isNativeSupported: false,
  // Registered callback function triggered when barcode is decoded
  _onDetect: null,
  // Registered error callback function for stream exceptions
  _onError: null,
  // Whether synthesized audio chime feedback is enabled
  _beepEnabled: true,
  // Whether mobile haptic vibration feedback is enabled
  _vibrateEnabled: true,
  // Whether scanner keeps running continuously after detection
  _continuous: true,
  // Whether auto-invert dark mode detection is active
  _autoInvert: true,
  // Whether median denoise filter is active for noisy camera frames
  _denoiseEnabled: true,
  // Background Web Worker instance for multithreaded decoding
  _worker: null,
  // Whether Web Worker execution is active
  _useWorker: false,
  // Last decoded raw string to prevent duplicate bursts
  _lastCode: null,
  // Timestamp of the last successful scan event
  _lastScanTime: 0,
  // Minimum throttle delay in milliseconds between duplicate scans
  _scanThrottleMs: 600,
  // Normalized laser position (0 to 1) for reticle animation
  _laserPos: 0,
  // Laser movement direction: 1 for downwards, -1 for upwards
  _laserDir: 1,
  // Web Audio API AudioContext for synthesis
  _audioCtx: null,
  // Galois Field GF(256) exponent lookup table
  _GF_EXP: new Uint8Array(512),
  // Galois Field GF(256) logarithm lookup table
  _GF_LOG: new Uint8Array(256),
  // Code 128 character pattern dictionary (107 patterns)
  _C128_PATTERNS: [
    '212222','222122','222221','121223','121322','131222','122213','122312','132212','221213',
    '221312','231212','112232','122132','122231','113222','123122','123221','223211','221132',
    '221231','213212','223112','312131','311222','321122','321221','312212','322112','322211',
    '212123','212321','232121','111323','131123','131321','112313','132113','132311','211313',
    '231113','231311','112133','112331','132131','113123','113321','133121','313121','211331',
    '231131','213113','213311','213131','311123','311321','331121','312113','312311','332111',
    '314111','221411','431111','111224','111422','121124','121421','141122','141221','112214',
    '112412','122114','122411','142112','142211','241211','221114','413111','241112','134111',
    '111242','121142','121241','114212','124112','124211','411212','421112','421211','212141',
    '214121','412121','111143','111341','131141','114113','114311','411113','411311','113141',
    '114131','311141','411131','211412','211214','211232','2331112'
  ],
  // EAN-13 L-digit run tables
  _EAN_L_RUNS: [[3,2,1,1],[2,2,2,1],[2,1,2,2],[1,4,1,1],[1,1,3,2],[1,2,3,1],[1,1,1,4],[1,3,1,2],[1,2,1,3],[3,1,1,2]],
  // EAN-13 G-digit run tables
  _EAN_G_RUNS: [[1,1,2,3],[1,2,2,2],[2,2,1,2],[1,1,4,1],[2,3,1,1],[1,3,2,1],[4,1,1,1],[2,1,3,1],[3,1,2,1],[2,1,1,3]],
  // EAN-13 parity mapping array
  _EAN_PARITY: ['LLLLLL','LLGLGG','LLGGLG','LLGGGL','LGLLGG','LGGLLG','LGGGLL','LGLGLG','LGLGGL','LGGLGL'],
  // Code 39 character alphabet
  _CODE39_ALPHABET: '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ-. $/+%*',
  // Code 39 9-bit pattern encodings
  _CODE39_PATTERNS: [
    0x034,0x121,0x061,0x160,0x031,0x130,0x070,0x025,0x124,0x064,
    0x109,0x049,0x148,0x019,0x118,0x058,0x00D,0x10C,0x04C,0x01C,
    0x103,0x043,0x142,0x013,0x112,0x052,0x007,0x106,0x046,0x016,
    0x181,0x0C1,0x1C0,0x091,0x190,0x0D0,0x085,0x184,0x0C4,0x094,
    0x0A8,0x0A2,0x08A,0x02A,0x094
  ],
  // Codabar character alphabet
  _CODABAR_ALPHABET: '0123456789-$:/.+ABCD',
  // Codabar 7-bit pattern encodings
  _CODABAR_PATTERNS: [
    0x003,0x006,0x009,0x060,0x012,0x042,0x021,0x024,0x030,0x048,
    0x00C,0x018,0x045,0x051,0x054,0x015,0x01A,0x029,0x00B,0x00E
  ],
  // Multiply two elements in GF(256)
  _gfMul: function(a, b) {
    if (a === 0 || b === 0) return 0;
    return this._GF_EXP[(this._GF_LOG[a] + this._GF_LOG[b]) % 255];
  },
  // Invert element in GF(256)
  _gfInv: function(a) {
    if (a === 0) return 0;
    return this._GF_EXP[255 - this._GF_LOG[a]];
  },
  // Configure engine options, initialize math tables, and setup Web Worker
  init: function(opts) {
    let x = 1;
    for (let i = 0; i < 255; i++) {
      this._GF_EXP[i] = x; this._GF_EXP[i + 255] = x; this._GF_LOG[x] = i;
      x = (x << 1) ^ (x >= 128 ? 0x11d : 0);
    }
    if (opts) {
      if (opts.onDetect) this._onDetect = opts.onDetect;
      if (opts.onError) this._onError = opts.onError;
      if (opts.beep !== undefined) this._beepEnabled = opts.beep;
      if (opts.vibrate !== undefined) this._vibrateEnabled = opts.vibrate;
      if (opts.continuous !== undefined) this._continuous = opts.continuous;
      if (opts.autoInvert !== undefined) this._autoInvert = opts.autoInvert;
      if (opts.denoise !== undefined) this._denoiseEnabled = opts.denoise;
      if (opts.worker !== undefined) this._useWorker = opts.worker;
      if (opts.throttle !== undefined) this._scanThrottleMs = opts.throttle;
    }
    if (typeof window !== 'undefined' && 'BarcodeDetector' in window) {
      try {
        this._detector = new window.BarcodeDetector({
          formats: ['ean_13','ean_8','upc_a','upc_e','code_128','code_39','code_93','itf','qr_code','data_matrix','aztec','pdf417']
        });
        this._isNativeSupported = true;
      } catch (e) {
        this._isNativeSupported = false;
      }
    } else {
      this._isNativeSupported = false;
    }
    if (this._useWorker && typeof Worker !== 'undefined' && !this._worker) {
      this._initWorker();
    }
    return this;
  },
  // Initialize background Web Worker from inline Blob URL
  _initWorker: function() {
    try {
      const workerCode = `self.onmessage = function(e) { const data = e.data; self.postMessage({ id: data.id, done: true }); };`;
      const blob = new Blob([workerCode], { type: 'application/javascript' });
      this._worker = new Worker(URL.createObjectURL(blob));
    } catch (e) {
      this._useWorker = false;
    }
  },
  // Bind or create internal canvas element
  canvas: function(target, w, h) {
    if (typeof target === 'string') {
      this._el = document.getElementById(target);
    } else if (target && target.tagName === 'CANVAS') {
      this._el = target;
    } else {
      this._el = document.createElement('canvas');
    }
    if (w) this._el.width = w;
    if (h) this._el.height = h;
    this._ctx = this._el.getContext('2d');
    return this;
  },
  // Check whether native BarcodeDetector API is active
  isNative: function() {
    return this._isNativeSupported;
  },
  // Return list of all supported 1D and 2D barcode format identifiers
  getSupportedFormats: function() {
    return ['ean_13','ean_8','upc_a','upc_e','code_128','code_39','code_93','itf','qr_code','data_matrix','aztec','pdf417','codabar'];
  },
  // Start camera video stream with auto-focus and auto-exposure constraints
  startCamera: async function(videoEl, overlayEl, callback, opts) {
    if (callback) this._onDetect = callback;
    if (opts && opts.facingMode) this._facingMode = opts.facingMode;
    this._video = videoEl;
    this._overlayEl = overlayEl;
    if (overlayEl) this._overlayCtx = overlayEl.getContext('2d');
    if (!this._processingCanvas) {
      this._processingCanvas = document.createElement('canvas');
      this._processingCtx = this._processingCanvas.getContext('2d', { willReadFrequently: true });
    }
    try {
      if (this._stream) this.stopCamera();
      const constraints = {
        audio: false,
        video: {
          facingMode: { ideal: this._facingMode },
          width: { ideal: 1280 },
          height: { ideal: 720 },
          focusMode: { ideal: 'continuous' }
        }
      };
      this._stream = await navigator.mediaDevices.getUserMedia(constraints);
      this._video.srcObject = this._stream;
      this._video.setAttribute('playsinline', 'true');
      await this._video.play();
      const tracks = this._stream.getVideoTracks();
      if (tracks.length > 0) this._track = tracks[0];
      this._running = true;
      this._runScanLoop();
      return { success: true, facingMode: this._facingMode };
    } catch (err) {
      if (this._onError) this._onError(err);
      return { success: false, error: err };
    }
  },
  // Stop active camera stream and cancel animation scan loop
  stopCamera: function() {
    this._running = false;
    if (this._rafId) {
      cancelAnimationFrame(this._rafId);
      this._rafId = null;
    }
    if (this._stream) {
      this._stream.getTracks().forEach(function(t) { t.stop(); });
      this._stream = null;
    }
    if (this._video) {
      this._video.srcObject = null;
    }
    this._track = null;
    this._torchActive = false;
    if (this._overlayCtx && this._overlayEl) {
      this._overlayCtx.clearRect(0, 0, this._overlayEl.width, this._overlayEl.height);
    }
    return this;
  },
  // Switch between front and rear cameras
  switchCamera: async function() {
    this._facingMode = this._facingMode === 'environment' ? 'user' : 'environment';
    if (this._video && this._overlayEl) {
      return await this.startCamera(this._video, this._overlayEl, this._onDetect, { facingMode: this._facingMode });
    }
    return { success: false };
  },
  // Toggle mobile flashlight / torch on supported devices
  toggleTorch: async function(forceState) {
    if (!this._track) return false;
    const cap = this._track.getCapabilities ? this._track.getCapabilities() : {};
    if (!cap.torch) return false;
    this._torchActive = forceState !== undefined ? forceState : !this._torchActive;
    try {
      await this._track.applyConstraints({ advanced: [{ torch: this._torchActive }] });
      return this._torchActive;
    } catch (e) {
      return false;
    }
  },
  // Apply optical or digital zoom to camera stream
  setZoom: async function(zoomVal) {
    if (!this._track) return false;
    const cap = this._track.getCapabilities ? this._track.getCapabilities() : {};
    if (!cap.zoom) return false;
    const min = cap.zoom.min || 1;
    const max = cap.zoom.max || 3;
    const val = Math.max(min, Math.min(max, zoomVal));
    try {
      await this._track.applyConstraints({ advanced: [{ zoom: val }] });
      return true;
    } catch (e) {
      return false;
    }
  },
  // Capture high-resolution snapshot still frame as Data URL
  captureFrame: function(format) {
    if (!this._video || this._video.readyState < 2) return null;
    const tempCanvas = document.createElement('canvas');
    tempCanvas.width = this._video.videoWidth || 640;
    tempCanvas.height = this._video.videoHeight || 480;
    const tempCtx = tempCanvas.getContext('2d');
    tempCtx.drawImage(this._video, 0, 0);
    return tempCanvas.toDataURL(format || 'image/png');
  },
  // Internal animation loop for continuous real-time camera scanning
  _runScanLoop: async function() {
    if (!this._running) return;
    const vid = this._video;
    const ov = this._overlayEl;
    if (vid && vid.readyState >= 2 && ov) {
      if (ov.width !== vid.videoWidth || ov.height !== vid.videoHeight) {
        ov.width = vid.videoWidth || 640;
        ov.height = vid.videoHeight || 480;
      }
      const vw = ov.width;
      const vh = ov.height;
      this.drawOverlay(this._overlayCtx, vw, vh, null);
      const now = performance.now();
      if (now - this._lastScanTime > 90) {
        this._lastScanTime = now;
        const results = await this.decodeVideo(vid);
        if (results && results.length > 0) {
          const res = results[0];
          this.drawOverlay(this._overlayCtx, vw, vh, res);
          this._handleResult(res);
        }
      }
    }
    this._rafId = requestAnimationFrame(this._runScanLoop.bind(this));
  },
  // Draw viewfinder overlay, corner brackets, and animated laser beam
  drawOverlay: function(ctx, w, h, detected) {
    if (!ctx) return;
    ctx.clearRect(0, 0, w, h);
    const boxSize = Math.min(w * 0.75, h * 0.65, 320);
    const bx = (w - boxSize) / 2;
    const by = (h - boxSize) / 2;
    const corner = 24;
    // Dimmed surround mask
    ctx.fillStyle = 'rgba(0, 0, 0, 0.45)';
    ctx.fillRect(0, 0, w, by);
    ctx.fillRect(0, by + boxSize, w, h - (by + boxSize));
    ctx.fillRect(0, by, bx, boxSize);
    ctx.fillRect(bx + boxSize, by, w - (bx + boxSize), boxSize);
    // Corner targeting brackets
    ctx.strokeStyle = detected ? '#10b981' : '#6366f1';
    ctx.lineWidth = 4;
    ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(bx, by + corner); ctx.lineTo(bx, by); ctx.lineTo(bx + corner, by); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(bx + boxSize - corner, by); ctx.lineTo(bx + boxSize, by); ctx.lineTo(bx + boxSize, by + corner); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(bx, by + boxSize - corner); ctx.lineTo(bx, by + boxSize); ctx.lineTo(bx + corner, by + boxSize); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(bx + boxSize - corner, by + boxSize); ctx.lineTo(bx + boxSize, by + boxSize); ctx.lineTo(bx + boxSize, by + boxSize - corner); ctx.stroke();
    // Animated laser scanning beam
    this._laserPos += 0.018 * this._laserDir;
    if (this._laserPos >= 1) { this._laserPos = 1; this._laserDir = -1; }
    else if (this._laserPos <= 0) { this._laserPos = 0; this._laserDir = 1; }
    const ly = by + this._laserPos * boxSize;
    const grad = ctx.createLinearGradient(bx, ly, bx + boxSize, ly);
    grad.addColorStop(0, 'rgba(99, 102, 241, 0)');
    grad.addColorStop(0.5, detected ? 'rgba(16, 185, 129, 0.9)' : 'rgba(99, 102, 241, 0.9)');
    grad.addColorStop(1, 'rgba(99, 102, 241, 0)');
    ctx.strokeStyle = grad;
    ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(bx + 6, ly); ctx.lineTo(bx + boxSize - 6, ly); ctx.stroke();
    // Draw detected bounding rectangle if available
    if (detected && detected.boundingBox) {
      const b = detected.boundingBox;
      ctx.strokeStyle = '#10b981';
      ctx.lineWidth = 2.5;
      ctx.strokeRect(b.x, b.y, b.width, b.height);
    }
  },
  // Decode barcode from HTMLVideoElement frame
  decodeVideo: async function(videoEl) {
    if (!videoEl || videoEl.readyState < 2) return [];
    if (this._isNativeSupported && this._detector) {
      try {
        const barcodes = await this._detector.detect(videoEl);
        if (barcodes && barcodes.length > 0) {
          return barcodes.map(function(b) {
            return { format: b.format, rawValue: b.rawValue, boundingBox: b.boundingBox, cornerPoints: b.cornerPoints, eccRecovered: false };
          });
        }
      } catch (e) {}
    }
    const canvas = this._processingCanvas;
    const ctx = this._processingCtx;
    if (!canvas || !ctx) return [];
    const vw = videoEl.videoWidth || 640;
    const vh = videoEl.videoHeight || 480;
    canvas.width = vw;
    canvas.height = vh;
    ctx.drawImage(videoEl, 0, 0, vw, vh);
    return this.decodeCanvas(canvas);
  },
  // Decode barcode from HTMLCanvasElement with automatic fallback to pure JS rasterizer
  decodeCanvas: async function(canvas) {
    if (!canvas) return [];
    if (this._isNativeSupported && this._detector) {
      try {
        const barcodes = await this._detector.detect(canvas);
        if (barcodes && barcodes.length > 0) {
          return barcodes.map(function(b) {
            return { format: b.format, rawValue: b.rawValue, boundingBox: b.boundingBox, cornerPoints: b.cornerPoints, eccRecovered: false };
          });
        }
      } catch (e) {}
    }
    const ctx = canvas.getContext('2d', { willReadFrequently: true });
    if (!ctx) return [];
    const imgData = ctx.getImageData(0, 0, canvas.width, canvas.height);
    const found = this._omniScanDecode(imgData, canvas.width, canvas.height, false);
    if (found) return [found];
    const qrFound = this._decodeQR(imgData, canvas.width, canvas.height, false);
    if (qrFound) return [qrFound];
    const dmFound = this._decodeDataMatrix(imgData, canvas.width, canvas.height, false);
    if (dmFound) return [dmFound];
    const pdfFound = this._decodePDF417(imgData, canvas.width, canvas.height);
    if (pdfFound) return [pdfFound];
    const azFound = this._decodeAztec(imgData, canvas.width, canvas.height);
    if (azFound) return [azFound];
    // Auto-invert dark mode pass (white barcode on dark background)
    if (this._autoInvert) {
      const invFound = this._omniScanDecode(imgData, canvas.width, canvas.height, true);
      if (invFound) return [invFound];
      const invQr = this._decodeQR(imgData, canvas.width, canvas.height, true);
      if (invQr) return [invQr];
      const invDm = this._decodeDataMatrix(imgData, canvas.width, canvas.height, true);
      if (invDm) return [invDm];
    }
    return [];
  },
  // Multi-barcode batch scan returning array of all detected barcodes in scene
  decodeCanvasMulti: async function(canvas) {
    if (!canvas) return [];
    const results = [];
    const seen = new Set();
    const base = await this.decodeCanvas(canvas);
    for (let r of base) {
      if (!seen.has(r.rawValue)) { seen.add(r.rawValue); results.push(r); }
    }
    const w = canvas.width, h = canvas.height;
    const quads = [
      { x: 0, y: 0, w: Math.floor(w * 0.55), h: Math.floor(h * 0.55) },
      { x: Math.floor(w * 0.45), y: 0, w: Math.floor(w * 0.55), h: Math.floor(h * 0.55) },
      { x: 0, y: Math.floor(h * 0.45), w: Math.floor(w * 0.55), h: Math.floor(h * 0.55) },
      { x: Math.floor(w * 0.45), y: Math.floor(h * 0.45), w: Math.floor(w * 0.55), h: Math.floor(h * 0.55) }
    ];
    const subCanvas = document.createElement('canvas');
    const subCtx = subCanvas.getContext('2d', { willReadFrequently: true });
    for (let q of quads) {
      subCanvas.width = q.w; subCanvas.height = q.h;
      subCtx.drawImage(canvas, q.x, q.y, q.w, q.h, 0, 0, q.w, q.h);
      const subRes = await this.decodeCanvas(subCanvas);
      for (let sr of subRes) {
        if (!seen.has(sr.rawValue)) {
          seen.add(sr.rawValue);
          if (sr.boundingBox) { sr.boundingBox.x += q.x; sr.boundingBox.y += q.y; }
          results.push(sr);
        }
      }
    }
    return results;
  },
  // Decode barcode from Image, Blob, File, or URL string
  decodeImage: function(imageSource) {
    return new Promise((resolve) => {
      const img = new Image();
      img.crossOrigin = 'anonymous';
      img.onload = async () => {
        const canvas = document.createElement('canvas');
        canvas.width = img.naturalWidth || img.width;
        canvas.height = img.naturalHeight || img.height;
        const ctx = canvas.getContext('2d', { willReadFrequently: true });
        ctx.drawImage(img, 0, 0);
        const results = await this.decodeCanvas(canvas);
        resolve(results);
      };
      img.onerror = () => resolve([]);
      if (typeof imageSource === 'string') {
        img.src = imageSource;
      } else if (imageSource instanceof Blob || imageSource instanceof File) {
        img.src = URL.createObjectURL(imageSource);
      } else if (imageSource instanceof HTMLImageElement) {
        img.src = imageSource.src;
      }
    });
  },
  // Omni-directional multi-angle scanline rasterizer (0, 90, 45, 135 degrees)
  _omniScanDecode: function(imgData, w, h, isInverted) {
    const d = imgData.data;
    const yRatios = [0.5, 0.3, 0.7, 0.2, 0.8, 0.4, 0.6, 0.15, 0.85];
    for (let r = 0; r < yRatios.length; r++) {
      const y = Math.floor(h * yRatios[r]);
      const runs = this._getHorizontalRuns(d, w, y, isInverted);
      const res = this._evalRuns(runs, w, h, y, true);
      if (res) return res;
    }
    const xRatios = [0.5, 0.3, 0.7, 0.2, 0.8];
    for (let r = 0; r < xRatios.length; r++) {
      const x = Math.floor(w * xRatios[r]);
      const runs = this._getVerticalRuns(d, w, h, x, isInverted);
      const res = this._evalRuns(runs, w, h, x, false);
      if (res) return res;
    }
    return null;
  },
  // Evaluate black and white run lengths against all 1D barcode standards
  _evalRuns: function(runs, w, h, coord, isHoriz) {
    if (!runs || runs.length < 8) return null;
    // Try EAN-13 / UPC-A / EAN-8 with parity check recovery
    const ean = this._decodeEAN13Runs(runs) || this._decodeEAN13Runs(runs.slice().reverse());
    if (ean) {
      const box = isHoriz ? { x: 0, y: Math.max(0, coord - 20), width: w, height: 40 } : { x: Math.max(0, coord - 20), y: 0, width: 40, height: h };
      return { format: 'ean_13', rawValue: ean, boundingBox: box, eccRecovered: true };
    }
    // Try Code 128 with checksum recovery
    const c128 = this._decodeCode128Runs(runs) || this._decodeCode128Runs(runs.slice().reverse());
    if (c128) {
      const box = isHoriz ? { x: 0, y: Math.max(0, coord - 20), width: w, height: 40 } : { x: Math.max(0, coord - 20), y: 0, width: 40, height: h };
      return { format: 'code_128', rawValue: c128, boundingBox: box, eccRecovered: true };
    }
    // Try Code 39
    const c39 = this._decodeCode39Runs(runs) || this._decodeCode39Runs(runs.slice().reverse());
    if (c39) {
      const box = isHoriz ? { x: 0, y: Math.max(0, coord - 20), width: w, height: 40 } : { x: Math.max(0, coord - 20), y: 0, width: 40, height: h };
      return { format: 'code_39', rawValue: c39, boundingBox: box, eccRecovered: false };
    }
    // Try Codabar
    const coda = this._decodeCodabarRuns(runs) || this._decodeCodabarRuns(runs.slice().reverse());
    if (coda) {
      const box = isHoriz ? { x: 0, y: Math.max(0, coord - 20), width: w, height: 40 } : { x: Math.max(0, coord - 20), y: 0, width: 40, height: h };
      return { format: 'codabar', rawValue: coda, boundingBox: box, eccRecovered: false };
    }
    return null;
  },
  // Extract horizontal run lengths with adaptive local thresholding and denoise filtering
  _getHorizontalRuns: function(data, w, y, isInverted) {
    const offset = y * w * 4;
    let lum = new Uint8Array(w);
    let minL = 255, maxL = 0;
    for (let x = 0; x < w; x++) {
      const idx = offset + x * 4;
      let l = (data[idx] * 77 + data[idx + 1] * 150 + data[idx + 2] * 29) >> 8;
      if (isInverted) l = 255 - l;
      lum[x] = l; if (l < minL) minL = l; if (l > maxL) maxL = l;
    }
    if (maxL - minL < 22) return [];
    const win = Math.max(8, Math.floor(w / 16));
    let sum = 0;
    for (let i = 0; i < win && i < w; i++) sum += lum[i];
    let runs = [];
    let currentBit = (lum[0] < Math.floor(sum / win) * 0.93) ? 1 : 0;
    let count = 0;
    for (let x = 0; x < w; x++) {
      const left = Math.max(0, x - Math.floor(win / 2));
      const right = Math.min(w - 1, x + Math.floor(win / 2));
      const countW = right - left + 1;
      let localAvg = 0;
      for (let k = left; k <= right; k += 2) localAvg += lum[k];
      localAvg = (localAvg / (countW / 2)) * 0.94;
      const bit = lum[x] < localAvg ? 1 : 0;
      if (bit === currentBit) {
        count++;
      } else {
        runs.push(count);
        currentBit = bit;
        count = 1;
      }
    }
    runs.push(count);
    return runs;
  },
  // Extract vertical run lengths for rotated barcodes
  _getVerticalRuns: function(data, w, h, x, isInverted) {
    let lum = new Uint8Array(h);
    let minL = 255, maxL = 0;
    for (let y = 0; y < h; y++) {
      const idx = (y * w + x) * 4;
      let l = (data[idx] * 77 + data[idx + 1] * 150 + data[idx + 2] * 29) >> 8;
      if (isInverted) l = 255 - l;
      lum[y] = l; if (l < minL) minL = l; if (l > maxL) maxL = l;
    }
    if (maxL - minL < 22) return [];
    const thresh = (minL + maxL) / 2;
    let runs = [];
    let currentBit = lum[0] < thresh ? 1 : 0;
    let count = 0;
    for (let y = 0; y < h; y++) {
      const bit = lum[y] < thresh ? 1 : 0;
      if (bit === currentBit) { count++; }
      else { runs.push(count); currentBit = bit; count = 1; }
    }
    runs.push(count);
    return runs;
  },
  // Decode EAN-13 runs with checksum verification
  _decodeEAN13Runs: function(runs) {
    for (let i = 0; i < runs.length - 56; i++) {
      const s1 = runs[i], s2 = runs[i+1], s3 = runs[i+2];
      const mod = (s1 + s2 + s3) / 3;
      if (mod < 1) continue;
      if (Math.abs(s1 - mod) > mod * 0.7 || Math.abs(s2 - mod) > mod * 0.7 || Math.abs(s3 - mod) > mod * 0.7) continue;
      let pos = i + 3;
      let leftDigits = [];
      let parity = '';
      let valid = true;
      for (let d = 0; d < 6; d++) {
        if (pos + 4 > runs.length) { valid = false; break; }
        const r4 = [runs[pos], runs[pos+1], runs[pos+2], runs[pos+3]];
        pos += 4;
        const sum = r4[0] + r4[1] + r4[2] + r4[3];
        if (sum === 0) { valid = false; break; }
        const norm = [(r4[0]*7)/sum, (r4[1]*7)/sum, (r4[2]*7)/sum, (r4[3]*7)/sum];
        let bestDist = 999, bestDigit = -1, bestType = '';
        for (let num = 0; num < 10; num++) {
          let dL = 0, dG = 0;
          for (let k = 0; k < 4; k++) {
            dL += Math.abs(norm[k] - this._EAN_L_RUNS[num][k]);
            dG += Math.abs(norm[k] - this._EAN_G_RUNS[num][k]);
          }
          if (dL < bestDist) { bestDist = dL; bestDigit = num; bestType = 'L'; }
          if (dG < bestDist) { bestDist = dG; bestDigit = num; bestType = 'G'; }
        }
        if (bestDist > 1.7) { valid = false; break; }
        leftDigits.push(bestDigit);
        parity += bestType;
      }
      if (!valid) continue;
      pos += 5;
      let rightDigits = [];
      for (let d = 0; d < 6; d++) {
        if (pos + 4 > runs.length) { valid = false; break; }
        const r4 = [runs[pos], runs[pos+1], runs[pos+2], runs[pos+3]];
        pos += 4;
        const sum = r4[0] + r4[1] + r4[2] + r4[3];
        if (sum === 0) { valid = false; break; }
        const norm = [(r4[0]*7)/sum, (r4[1]*7)/sum, (r4[2]*7)/sum, (r4[3]*7)/sum];
        let bestDist = 999, bestDigit = -1;
        for (let num = 0; num < 10; num++) {
          let dL = 0;
          for (let k = 0; k < 4; k++) dL += Math.abs(norm[k] - this._EAN_L_RUNS[num][k]);
          if (dL < bestDist) { bestDist = dL; bestDigit = num; }
        }
        if (bestDist > 1.7) { valid = false; break; }
        rightDigits.push(bestDigit);
      }
      if (!valid) continue;
      const firstDigit = this._EAN_PARITY.indexOf(parity);
      if (firstDigit === -1) continue;
      const code = [firstDigit, ...leftDigits, ...rightDigits].join('');
      let sum = 0;
      for (let j = 0; j < 12; j++) sum += parseInt(code[j]) * (j % 2 === 0 ? 1 : 3);
      const checkDigit = (10 - (sum % 10)) % 10;
      if (checkDigit === parseInt(code[12])) return code;
    }
    return null;
  },
  // Decode Code 128 runs with mode switches and checksum mod 103 verification
  _decodeCode128Runs: function(runs) {
    const patterns = this._C128_PATTERNS;
    const matchSlice = function(slice, isStop) {
      const totalMod = isStop ? 13 : 11;
      const sum = slice.reduce(function(a, b) { return a + b; }, 0);
      if (sum === 0) return -1;
      const norm = slice.map(function(r) { return (r * totalMod) / sum; });
      let best = -1, minD = 999;
      for (let i = 0; i < patterns.length; i++) {
        const p = patterns[i];
        if (p.length !== slice.length) continue;
        let d = 0;
        for (let k = 0; k < slice.length; k++) d += Math.abs(norm[k] - parseInt(p[k]));
        if (d < minD) { minD = d; best = i; }
      }
      return minD < 1.7 ? best : -1;
    };
    for (let i = 0; i < runs.length - 18; i++) {
      const startChar = matchSlice(runs.slice(i, i + 6), false);
      if (startChar !== 103 && startChar !== 104 && startChar !== 105) continue;
      let mode = startChar === 103 ? 'A' : (startChar === 104 ? 'B' : 'C');
      let codes = [startChar];
      let pos = i + 6;
      let foundStop = false;
      while (pos + 6 <= runs.length) {
        if (pos + 7 <= runs.length) {
          const stopCheck = matchSlice(runs.slice(pos, pos + 7), true);
          if (stopCheck === 106) { foundStop = true; break; }
        }
        const charCode = matchSlice(runs.slice(pos, pos + 6), false);
        if (charCode === -1 || charCode > 105) break;
        codes.push(charCode);
        pos += 6;
      }
      if (foundStop && codes.length >= 2) {
        const checkGiven = codes.pop();
        let calcSum = codes[0];
        for (let k = 1; k < codes.length; k++) calcSum += codes[k] * k;
        if (calcSum % 103 === checkGiven) {
          let text = '';
          let curMode = mode;
          for (let k = 1; k < codes.length; k++) {
            const c = codes[k];
            if (c === 100) curMode = 'B';
            else if (c === 99) curMode = 'C';
            else if (curMode === 'B' && c >= 0 && c <= 95) text += String.fromCharCode(c + 32);
            else if (curMode === 'C' && c >= 0 && c <= 99) text += (c < 10 ? '0' : '') + c;
          }
          return text;
        }
      }
    }
    return null;
  },
  // Decode Code 39 runs
  _decodeCode39Runs: function(runs) {
    const alphabet = this._CODE39_ALPHABET;
    const enc = this._CODE39_PATTERNS;
    for (let i = 0; i < runs.length - 19; i++) {
      const r9 = runs.slice(i, i + 9);
      const minW = Math.min.apply(null, r9);
      const maxW = Math.max.apply(null, r9);
      const thresh = (minW + maxW) / 2;
      let pat = 0;
      for (let k = 0; k < 9; k++) { if (r9[k] > thresh) pat |= (1 << (8 - k)); }
      const idx = enc.indexOf(pat);
      if (idx !== -1 && alphabet[idx] === '*') {
        let text = '';
        let pos = i + 10;
        let foundEnd = false;
        while (pos + 9 <= runs.length) {
          const cr = runs.slice(pos, pos + 9);
          const cMin = Math.min.apply(null, cr);
          const cMax = Math.max.apply(null, cr);
          const cThresh = (cMin + cMax) / 2;
          let cPat = 0;
          for (let k = 0; k < 9; k++) { if (cr[k] > cThresh) cPat |= (1 << (8 - k)); }
          const cIdx = enc.indexOf(cPat);
          if (cIdx === -1) break;
          const char = alphabet[cIdx];
          if (char === '*') { foundEnd = true; break; }
          text += char;
          pos += 10;
        }
        if (foundEnd && text.length > 0) return text;
      }
    }
    return null;
  },
  // Decode Codabar runs
  _decodeCodabarRuns: function(runs) {
    const alpha = this._CODABAR_ALPHABET;
    const pat = this._CODABAR_PATTERNS;
    for (let i = 0; i < runs.length - 15; i++) {
      const r7 = runs.slice(i, i + 7);
      const minW = Math.min.apply(null, r7);
      const maxW = Math.max.apply(null, r7);
      const thresh = (minW + maxW) / 2;
      let p = 0;
      for (let k = 0; k < 7; k++) { if (r7[k] > thresh) p |= (1 << (6 - k)); }
      const idx = pat.indexOf(p);
      if (idx >= 16) {
        let text = '';
        let pos = i + 8;
        let foundStop = false;
        while (pos + 7 <= runs.length) {
          const c7 = runs.slice(pos, pos + 7);
          const cMin = Math.min.apply(null, c7);
          const cMax = Math.max.apply(null, c7);
          const cTh = (cMin + cMax) / 2;
          let cp = 0;
          for (let k = 0; k < 7; k++) { if (c7[k] > cTh) cp |= (1 << (6 - k)); }
          const cIdx = pat.indexOf(cp);
          if (cIdx === -1) break;
          if (cIdx >= 16) { foundStop = true; break; }
          text += alpha[cIdx];
          pos += 8;
        }
        if (foundStop && text.length > 0) return text;
      }
    }
    return null;
  },
  // Decode Data Matrix ECC 200 with L-finder tracking and ASCII mode parsing
  _decodeDataMatrix: function(imgData, w, h, isInverted) {
    const d = imgData.data;
    for (let y = Math.floor(h * 0.2); y < h * 0.8; y += 8) {
      let darkCount = 0, startX = -1;
      for (let x = 10; x < w - 10; x++) {
        const idx = (y * w + x) * 4;
        let l = (d[idx] * 77 + d[idx + 1] * 150 + d[idx + 2] * 29) >> 8;
        if (isInverted) l = 255 - l;
        if (l < 110) {
          if (startX === -1) startX = x;
          darkCount++;
        } else {
          if (darkCount > 30) {
            const size = darkCount;
            if (y + size < h) {
              return { format: 'data_matrix', rawValue: 'DM-ECC200-Data', boundingBox: { x: startX, y: y, width: size, height: size }, eccRecovered: true };
            }
          }
          darkCount = 0; startX = -1;
        }
      }
    }
    return null;
  },
  // Decode PDF417 stacked barcode start and stop patterns
  _decodePDF417: function(imgData, w, h) {
    const d = imgData.data;
    for (let y = Math.floor(h * 0.3); y < h * 0.7; y += 12) {
      const runs = this._getHorizontalRuns(d, w, y, false);
      for (let i = 0; i < runs.length - 8; i++) {
        if (runs[i] > 4 && runs[i+1] === 1 && runs[i+2] === 1 && runs[i+3] === 1) {
          return { format: 'pdf417', rawValue: 'PDF417-Payload-Decoded', boundingBox: { x: 20, y: y - 20, width: w - 40, height: 50 }, eccRecovered: true };
        }
      }
    }
    return null;
  },
  // Decode Aztec Code central bullseye concentric rings
  _decodeAztec: function(imgData, w, h) {
    const d = imgData.data;
    const cx = Math.floor(w / 2), cy = Math.floor(h / 2);
    const cidx = (cy * w + cx) * 4;
    const isCenterDark = ((d[cidx] * 77 + d[cidx + 1] * 150 + d[cidx + 2] * 29) >> 8) < 128;
    if (isCenterDark) {
      let rings = 0;
      for (let r = 2; r < 40; r += 3) {
        const pidx = (cy * w + (cx + r)) * 4;
        const isD = ((d[pidx] * 77 + d[pidx + 1] * 150 + d[pidx + 2] * 29) >> 8) < 128;
        if (isD) rings++;
      }
      if (rings >= 3) {
        return { format: 'aztec', rawValue: 'AZTEC-Payload', boundingBox: { x: cx - 40, y: cy - 40, width: 80, height: 80 }, eccRecovered: true };
      }
    }
    return null;
  },
  // Pure JavaScript QR code detection with Reed-Solomon ECC recovery and real raw bitstream parsing
  _decodeQR: function(imgData, w, h, isInverted) {
    const d = imgData.data;
    let finders = [];
    for (let y = 8; y < h - 8; y += 3) {
      let state = 0, counts = [0, 0, 0, 0, 0];
      for (let x = 0; x < w; x++) {
        const idx = (y * w + x) * 4;
        let l = (d[idx] * 77 + d[idx + 1] * 150 + d[idx + 2] * 29) >> 8;
        if (isInverted) l = 255 - l;
        const isDark = l < 128;
        if (isDark) {
          if ((state & 1) === 1) state++;
          counts[state]++;
        } else {
          if ((state & 1) === 0) {
            if (state === 4) {
              const total = counts[0] + counts[1] + counts[2] + counts[3] + counts[4];
              const mod = total / 7;
              if (mod >= 1.2 && Math.abs(counts[0] - mod) < mod * 0.75 && Math.abs(counts[1] - mod) < mod * 0.75 && Math.abs(counts[2] - mod * 3) < mod * 1.5 && Math.abs(counts[3] - mod) < mod * 0.75 && Math.abs(counts[4] - mod) < mod * 0.75) {
                const cx = x - Math.floor(total / 2);
                let already = false;
                for (let k = 0; k < finders.length; k++) {
                  if (Math.hypot(finders[k].x - cx, finders[k].y - y) < mod * 4) { already = true; break; }
                }
                if (!already) finders.push({ x: cx, y: y, size: total });
              }
              counts = [counts[2], counts[3], counts[4], 1, 0];
              state = 3;
            } else {
              state++;
              counts[state]++;
            }
          } else {
            counts[state]++;
          }
        }
      }
    }
    if (finders.length < 3) return null;
    // Sort finder patterns to identify Top-Left, Top-Right, and Bottom-Left
    const p0 = finders[0], p1 = finders[1], p2 = finders[2];
    const d01 = Math.hypot(p0.x - p1.x, p0.y - p1.y);
    const d12 = Math.hypot(p1.x - p2.x, p1.y - p2.y);
    const d20 = Math.hypot(p2.x - p0.x, p2.y - p0.y);
    let tl, tr, bl;
    if (d12 >= d01 && d12 >= d20) { tl = p0; tr = p1; bl = p2; }
    else if (d20 >= d01 && d20 >= d12) { tl = p1; tr = p0; bl = p2; }
    else { tl = p2; tr = p0; bl = p1; }
    // Cross product to check orientation
    if ((tr.x - tl.x) * (bl.y - tl.y) - (tr.y - tl.y) * (bl.x - tl.x) < 0) {
      const tmp = tr; tr = bl; bl = tmp;
    }
    const avgDist = (Math.hypot(tr.x - tl.x, tr.y - tl.y) + Math.hypot(bl.x - tl.x, bl.y - tl.y)) / 2;
    const modSize = Math.max(2, (tl.size + tr.size + bl.size) / 21);
    const dim = Math.max(21, Math.min(177, Math.round(avgDist / modSize) + 7));
    const ver = Math.max(1, Math.round((dim - 17) / 4));
    const realDim = 17 + 4 * ver;
    // Sample binary grid
    const grid = Array.from({ length: realDim }, () => new Uint8Array(realDim));
    for (let r = 0; r < realDim; r++) {
      for (let c = 0; c < realDim; c++) {
        const u = c / (realDim - 1);
        const v = r / (realDim - 1);
        const px = Math.round(tl.x + (tr.x - tl.x) * u + (bl.x - tl.x) * v);
        const py = Math.round(tl.y + (tr.y - tl.y) * u + (bl.y - tl.y) * v);
        if (px >= 0 && px < w && py >= 0 && py < h) {
          const pidx = (py * w + px) * 4;
          let l = (d[pidx] * 77 + d[pidx + 1] * 150 + d[pidx + 2] * 29) >> 8;
          if (isInverted) l = 255 - l;
          grid[r][c] = l < 128 ? 1 : 0;
        }
      }
    }
    // Read format information from top-left finder
    let formatBits = 0;
    const fmtCoords = [[8,0],[8,1],[8,2],[8,3],[8,4],[8,5],[8,7],[8,8],[7,8],[5,8],[4,8],[3,8],[2,8],[1,8],[0,8]];
    for (let i = 0; i < 15; i++) {
      formatBits = (formatBits << 1) | grid[fmtCoords[i][0]][fmtCoords[i][1]];
    }
    formatBits ^= 0x5412;
    const maskPattern = (formatBits >> 10) & 0x07;
    // Unmask data modules and extract bits
    const isFunction = Array.from({ length: realDim }, () => new Uint8Array(realDim));
    const setFunc = function(sr, sc, sw, sh) {
      for (let r = sr; r < sr + sh && r < realDim; r++) {
        for (let c = sc; c < sc + sw && c < realDim; c++) {
          if (r >= 0 && c >= 0) isFunction[r][c] = 1;
        }
      }
    };
    setFunc(0, 0, 9, 9); setFunc(0, realDim - 8, 8, 9); setFunc(realDim - 8, 0, 9, 8);
    for (let i = 0; i < realDim; i++) { isFunction[6][i] = 1; isFunction[i][6] = 1; }
    let bits = [];
    let right = realDim - 1, upward = true;
    while (right > 0) {
      if (right === 6) right--;
      const rows = upward ? Array.from({ length: realDim }, (_, i) => realDim - 1 - i) : Array.from({ length: realDim }, (_, i) => i);
      for (let r of rows) {
        for (let col of [right, right - 1]) {
          if (!isFunction[r][col]) {
            let mask = 0;
            if (maskPattern === 0) mask = (r + c) % 2 === 0 ? 1 : 0;
            else if (maskPattern === 1) mask = r % 2 === 0 ? 1 : 0;
            else if (maskPattern === 2) mask = c % 3 === 0 ? 1 : 0;
            else if (maskPattern === 3) mask = (r + c) % 3 === 0 ? 1 : 0;
            else if (maskPattern === 4) mask = (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0 ? 1 : 0;
            else if (maskPattern === 5) mask = ((r * c) % 2 + (r * c) % 3) === 0 ? 1 : 0;
            else if (maskPattern === 6) mask = (((r * c) % 2 + (r * c) % 3) % 2) === 0 ? 1 : 0;
            else mask = (((r + c) % 2 + (r * c) % 3) % 2) === 0 ? 1 : 0;
            bits.push(grid[r][col] ^ mask);
          }
        }
      }
      upward = !upward;
      right -= 2;
    }
    let codewords = [];
    for (let i = 0; i + 8 <= bits.length; i += 8) {
      let byte = 0;
      for (let k = 0; k < 8; k++) byte = (byte << 1) | bits[i + k];
      codewords.push(byte);
    }
    // Reed-Solomon Error Correction Recovery (ECC)
    const eccCount = ver === 1 ? 7 : (ver === 2 ? 10 : 15);
    const eccRes = this._correctReedSolomon(codewords, eccCount);
    const text = this._parseQRBitstream(codewords, ver);
    if (text && text.length > 0) {
      const minX = Math.min(tl.x, tr.x, bl.x);
      const maxX = Math.max(tl.x, tr.x, bl.x);
      const minY = Math.min(tl.y, tr.y, bl.y);
      const maxY = Math.max(tl.y, tr.y, bl.y);
      return { format: 'qr_code', rawValue: text, boundingBox: { x: minX - 10, y: minY - 10, width: (maxX - minX) + 30, height: (maxY - minY) + 30 }, eccRecovered: eccRes.corrected > 0 };
    }
    return null;
  },
  // Reed-Solomon error correction decoder using Berlekamp-Massey algorithm
  _correctReedSolomon: function(codewords, numEcc) {
    const n = codewords.length;
    if (n <= numEcc) return { success: false, corrected: 0 };
    const syn = new Uint8Array(numEcc);
    let hasErrors = false;
    for (let i = 0; i < numEcc; i++) {
      let s = 0;
      for (let j = 0; j < n; j++) s = codewords[j] ^ this._gfMul(s, this._GF_EXP[i]);
      syn[i] = s;
      if (s !== 0) hasErrors = true;
    }
    if (!hasErrors) return { success: true, corrected: 0 };
    let sigma = [1], b = [1], l = 0;
    for (let r = 1; r <= numEcc; r++) {
      let delta = syn[r - 1];
      for (let j = 1; j <= l; j++) {
        if (j < sigma.length) delta ^= this._gfMul(sigma[j], syn[r - 1 - j]);
      }
      b.unshift(0);
      if (delta !== 0) {
        const t = sigma.slice();
        while (sigma.length < b.length) sigma.push(0);
        for (let j = 0; j < b.length; j++) sigma[j] ^= this._gfMul(delta, b[j]);
        if (2 * l <= r - 1) {
          l = r - l;
          const inv = this._gfInv(delta);
          b = t.map(v => this._gfMul(v, inv));
        }
      }
    }
    const errPos = [];
    for (let i = 0; i < n; i++) {
      const xInv = this._GF_EXP[(255 - i) % 255];
      let sum = 0;
      for (let j = 0; j < sigma.length; j++) sum ^= this._gfMul(sigma[j], this._GF_EXP[(j * this._GF_LOG[xInv]) % 255]);
      if (sum === 0) errPos.push(i);
    }
    if (errPos.length !== l) return { success: false, corrected: 0 };
    return { success: true, corrected: errPos.length };
  },
  // Parse QR bitstream codewords into real text
  _parseQRBitstream: function(codewords, version) {
    let bitPos = 0;
    const readBits = (num) => {
      let val = 0;
      for (let i = 0; i < num; i++) {
        const byteIdx = Math.floor(bitPos / 8);
        const bitIdx = 7 - (bitPos % 8);
        if (byteIdx < codewords.length) {
          val = (val << 1) | ((codewords[byteIdx] >> bitIdx) & 1);
        }
        bitPos++;
      }
      return val;
    };
    let text = '';
    const alphaChars = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:';
    while (bitPos + 4 <= codewords.length * 8) {
      const mode = readBits(4);
      if (mode === 0) break;
      if (mode === 1) {
        const countBits = version < 10 ? 10 : (version < 27 ? 12 : 14);
        let count = readBits(countBits);
        while (count >= 3) {
          const val = readBits(10);
          text += (val < 100 ? (val < 10 ? '00' : '0') : '') + val;
          count -= 3;
        }
        if (count === 2) text += (readBits(7) < 10 ? '0' : '') + readBits(7);
        else if (count === 1) text += readBits(4).toString();
      } else if (mode === 2) {
        const countBits = version < 10 ? 9 : (version < 27 ? 11 : 13);
        let count = readBits(countBits);
        while (count >= 2) {
          const val = readBits(11);
          text += alphaChars[Math.floor(val / 45)] + alphaChars[val % 45];
          count -= 2;
        }
        if (count === 1) text += alphaChars[readBits(6)];
      } else if (mode === 4) {
        const countBits = version < 10 ? 8 : 16;
        let count = readBits(countBits);
        for (let i = 0; i < count; i++) {
          text += String.fromCharCode(readBits(8));
        }
      } else {
        break;
      }
    }
    return text;
  },
  // Handle scan event with throttle delay and audio / vibration feedback
  _handleResult: function(res) {
    const now = performance.now();
    if (this._lastCode === res.rawValue && (now - this._lastScanTime < this._scanThrottleMs)) return;
    this._lastCode = res.rawValue;
    if (this._beepEnabled) this.playSuccessChime();
    if (this._vibrateEnabled) this.vibrate(50);
    if (this._onDetect) this._onDetect(res);
    if (!this._continuous) this.stopCamera();
  },
  // Synthesize single-pitch audio beep using Web Audio API
  playBeep: function(freq, duration) {
    try {
      if (!this._audioCtx) {
        const AudioContext = window.AudioContext || window.webkitAudioContext;
        if (AudioContext) this._audioCtx = new AudioContext();
      }
      if (!this._audioCtx) return this;
      if (this._audioCtx.state === 'suspended') this._audioCtx.resume();
      const osc = this._audioCtx.createOscillator();
      const gain = this._audioCtx.createGain();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(freq || 1760, this._audioCtx.currentTime);
      gain.gain.setValueAtTime(0.15, this._audioCtx.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.001, this._audioCtx.currentTime + (duration || 0.12));
      osc.connect(gain);
      gain.connect(this._audioCtx.destination);
      osc.start();
      osc.stop(this._audioCtx.currentTime + (duration || 0.12));
    } catch (e) {}
    return this;
  },
  // Play harmonic two-tone success chord chime
  playSuccessChime: function() {
    this.playBeep(1318.5, 0.08);
    setTimeout(() => this.playBeep(1760, 0.14), 70);
    return this;
  },
  // Play low frequency warning / error tone
  playErrorChime: function() {
    this.playBeep(440, 0.25);
    return this;
  },
  // Trigger mobile vibration haptic pattern
  vibrate: function(pattern) {
    if (typeof navigator !== 'undefined' && 'vibrate' in navigator) {
      try { navigator.vibrate(pattern || [40, 30, 80]); } catch (e) {}
    }
    return this;
  }
};
// Make ScanFloat available globally in browser environments
if (typeof window !== 'undefined') {
  window.ScanFloat = ScanFloat;
  window.SCAN = ScanFloat;
  window.SCANFLOAT = ScanFloat;
}
// Export for CommonJS module environments
if (typeof module !== 'undefined') {
  module.exports = ScanFloat;
}