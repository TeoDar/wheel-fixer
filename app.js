(function () {
  'use strict';

  /* ------------------------------------------------------------------ */
  /* локализация динамических подписей (язык берём из <html lang="...">)  */
  /* ------------------------------------------------------------------ */

  var LANG = (document.documentElement.getAttribute('lang') || 'ru').slice(0, 2).toLowerCase();

  var I18N = {
    ru: {
      empty: 'Отметьте области выпирания на схеме — и здесь появится список действий.',
      none: 'По этой разметке правки не требуется 🙂',
      counts: 'Натянуть: <b class="tight">{tight}</b> · Ослабить: <b class="loose">{loose}</b> · Всего спиц: <b>{total}</b>',
      tight: 'натянуть +',
      loose: 'ослабить −',
      turn: 'об.'
    },
    en: {
      empty: 'Mark the runout areas on the diagram — the list of actions will appear here.',
      none: 'No adjustment is needed for these marks 🙂',
      counts: 'Tighten: <b class="tight">{tight}</b> · Loosen: <b class="loose">{loose}</b> · Total spokes: <b>{total}</b>',
      tight: 'tighten +',
      loose: 'loosen −',
      turn: 'turn'
    }
  };

  var T = I18N[LANG] || I18N.ru;

  var TAU = Math.PI * 2;
  var SIG = 0.85;      // ширина влияния спицы (в шагах между спицами)
  var LAMBDA = 0.04;   // регуляризация: держит решение локальным и практичным

  var SPOKE_COUNTS = [16, 18, 20, 24, 28, 32, 36, 40, 48];

  var svg = document.getElementById('wheel');

  var state = {
    n: 32,
    firstSide: 'L',
    lateral: [],
    radial: [],
    mode: 'latR',
    strength: 2,
    maxTurn: 0.5,
    showNumbers: true
  };

  var result = null;
  var history = [];
  var painting = false;
  var lastGap = null;
  var hoverGap = -1;

  /* ------------------------------------------------------------------ */
  /* геометрия и модель                                                  */
  /* ------------------------------------------------------------------ */

  function initMarks() {
    state.lateral = new Array(state.n).fill(0);
    state.radial = new Array(state.n).fill(0);
    history = [];
  }
  initMarks();

  function spokeSide(i) { return (i % 2 === 0) ? state.firstSide : (state.firstSide === 'L' ? 'R' : 'L'); }
  function sideSign(i) { return spokeSide(i) === 'R' ? 1 : -1; }
  function polar(a, r) { return [r * Math.sin(a), -r * Math.cos(a)]; }

  function sectorPath(a0, a1, r0, r1) {
    var p0 = polar(a0, r0), p1 = polar(a0, r1), p2 = polar(a1, r1), p3 = polar(a1, r0);
    var large = (a1 - a0) > Math.PI ? 1 : 0;
    return 'M' + p0[0].toFixed(2) + ' ' + p0[1].toFixed(2) +
           'L' + p1[0].toFixed(2) + ' ' + p1[1].toFixed(2) +
           'A' + r1 + ' ' + r1 + ' 0 ' + large + ' 1 ' + p2[0].toFixed(2) + ' ' + p2[1].toFixed(2) +
           'L' + p3[0].toFixed(2) + ' ' + p3[1].toFixed(2) +
           'A' + r0 + ' ' + r0 + ' 0 ' + large + ' 0 ' + p0[0].toFixed(2) + ' ' + p0[1].toFixed(2) + 'Z';
  }

  // круговая дистанция между позицией промежутка (дробная) и спицей j (целая), в шагах
  function distSpokes(a, b) {
    var d = Math.abs(a - b) % state.n;
    return Math.min(d, state.n - d);
  }
  function kernel(d) { return Math.exp(-(d * d) / (SIG * SIG)); }

  function latFill(v) {
    var o = Math.min(0.9, 0.2 + 0.24 * Math.abs(v));
    return v > 0 ? 'rgba(239,68,68,' + o + ')' : 'rgba(59,130,246,' + o + ')';
  }
  function radFill(v) {
    var o = Math.min(0.9, 0.2 + 0.24 * Math.abs(v));
    return v > 0 ? 'rgba(245,158,11,' + o + ')' : 'rgba(139,92,246,' + o + ')';
  }

  /* Решение методом наименьших квадратов с регуляризацией (МНК + Тихонов).
     Неизвестные t[j] — изменение натяжения спицы j (t>0 — натянуть).
     Боковое смещение промежутка g:  u = Σ s_j·K·t_j , цель u = -lateral[g]
     Радиальное смещение:            w = Σ K·t_j   , цель w = radial[g]      */
  function gaussSolve(M) {
    var n = M.length;
    for (var col = 0; col < n; col++) {
      var piv = col;
      for (var r = col + 1; r < n; r++) {
        if (Math.abs(M[r][col]) > Math.abs(M[piv][col])) piv = r;
      }
      if (Math.abs(M[piv][col]) < 1e-12) continue;
      var tmp = M[col]; M[col] = M[piv]; M[piv] = tmp;
      var pv = M[col][col];
      for (var c = col; c <= n; c++) M[col][c] /= pv;
      for (var rr = 0; rr < n; rr++) {
        if (rr === col) continue;
        var f = M[rr][col];
        if (f === 0) continue;
        for (var cc = col; cc <= n; cc++) M[rr][cc] -= f * M[col][cc];
      }
    }
    return M.map(function (row) { return row[n]; });
  }

  function compute() {
    var N = state.n, g, j, row;
    var rows = [], rhs = [];

    for (g = 0; g < N; g++) {
      if (state.lateral[g] !== 0) {
        row = new Array(N);
        for (j = 0; j < N; j++) row[j] = sideSign(j) * kernel(distSpokes(g + 0.5, j));
        rows.push(row); rhs.push(-state.lateral[g]);
      }
      if (state.radial[g] !== 0) {
        row = new Array(N);
        for (j = 0; j < N; j++) row[j] = kernel(distSpokes(g + 0.5, j));
        rows.push(row); rhs.push(state.radial[g]);
      }
    }
    if (rows.length === 0) { result = null; return; }

    var ATA = [], ATb = new Array(N).fill(0), i, k;
    for (i = 0; i < N; i++) ATA.push(new Array(N).fill(0));
    for (k = 0; k < rows.length; k++) {
      var rw = rows[k];
      for (i = 0; i < N; i++) {
        var ai = rw[i];
        if (ai === 0) continue;
        ATb[i] += ai * rhs[k];
        for (j = 0; j < N; j++) ATA[i][j] += ai * rw[j];
      }
    }
    for (i = 0; i < N; i++) ATA[i][i] += LAMBDA;

    var M = ATA.map(function (r, idx) { return r.concat([ATb[idx]]); });
    var t = gaussSolve(M);

    var maxAbs = 0;
    for (i = 0; i < N; i++) maxAbs = Math.max(maxAbs, Math.abs(t[i]));
    if (maxAbs < 1e-9) { result = null; return; }

    var turns = t.map(function (x) {
      return Math.round((x / maxAbs * state.maxTurn) * 8) / 8;
    });

    var num = 0, den = 0;
    for (k = 0; k < rows.length; k++) {
      var p = 0;
      for (j = 0; j < N; j++) p += rows[k][j] * t[j];
      num = Math.max(num, Math.abs(p - rhs[k]));
      den = Math.max(den, Math.abs(rhs[k]));
    }
    result = { turns: turns, residual: den ? num / den : 0 };
  }

  /* ------------------------------------------------------------------ */
  /* отрисовка                                                           */
  /* ------------------------------------------------------------------ */

  function draw() {
    var N = state.n, da = TAU / N, g, i, s = '';

    // фон и базовые кольца
    s += '<circle cx="0" cy="0" r="100" fill="#f8fafc" stroke="#cbd5e1" stroke-width="0.7"/>';
    s += '<circle cx="0" cy="0" r="84" fill="none" stroke="#e2e8f0" stroke-width="0.6"/>';
    s += '<circle cx="0" cy="0" r="70" fill="none" stroke="#e2e8f0" stroke-width="0.6"/>';
    s += '<circle cx="0" cy="0" r="60" fill="none" stroke="#eef2f7" stroke-width="0.6"/>';

    // отметки
    for (g = 0; g < N; g++) {
      var a0 = g * da, a1 = (g + 1) * da;
      if (state.lateral[g] !== 0) s += '<path d="' + sectorPath(a0, a1, 84, 100) + '" fill="' + latFill(state.lateral[g]) + '"/>';
      if (state.radial[g] !== 0) s += '<path d="' + sectorPath(a0, a1, 60, 70) + '" fill="' + radFill(state.radial[g]) + '"/>';
    }

    // подсветка наведения
    if (hoverGap >= 0) {
      s += '<path d="' + sectorPath(hoverGap * da, (hoverGap + 1) * da, 58, 102) +
           '" fill="rgba(15,23,42,0.05)" stroke="#94a3b8" stroke-width="0.6" pointer-events="none"/>';
    }

    // спицы
    for (i = 0; i < N; i++) {
      var a = i * da;
      var sp = polar(a, 13), ep = polar(a, 84);
      var col = spokeSide(i) === 'L' ? '#9db8d6' : '#d8b79a';
      s += '<line x1="' + sp[0].toFixed(2) + '" y1="' + sp[1].toFixed(2) +
           '" x2="' + ep[0].toFixed(2) + '" y2="' + ep[1].toFixed(2) +
           '" stroke="' + col + '" stroke-width="1.1"/>';
    }

    // подсветка спиц, требующих действия
    if (result) {
      for (i = 0; i < N; i++) {
        var tv = result.turns[i];
        if (Math.abs(tv) < 0.125 - 1e-9) continue;
        var aa = i * da;
        var q1 = polar(aa, 13), q2 = polar(aa, 84);
        var c2 = tv > 0 ? '#16a34a' : '#ea580c';
        s += '<line x1="' + q1[0].toFixed(2) + '" y1="' + q1[1].toFixed(2) +
             '" x2="' + q2[0].toFixed(2) + '" y2="' + q2[1].toFixed(2) +
             '" stroke="' + c2 + '" stroke-width="2.4" stroke-linecap="round" opacity="0.85"/>';
      }
    }

    // втулка
    s += '<circle cx="0" cy="0" r="13" fill="#ffffff" stroke="#94a3b8" stroke-width="1"/>';
    s += '<circle cx="0" cy="0" r="2.5" fill="#94a3b8"/>';

    // значки «натянуть / ослабить»
    if (result) {
      for (i = 0; i < N; i++) {
        var t2 = result.turns[i];
        if (Math.abs(t2) < 0.125 - 1e-9) continue;
        var ang = i * da;
        var bp = polar(ang, 50);
        var tight = t2 > 0;
        var fill = tight ? '#dcfce7' : '#ffedd5';
        var stroke = tight ? '#16a34a' : '#ea580c';
        var glyph = tight ? '+' : '−';
        s += '<circle cx="' + bp[0].toFixed(2) + '" cy="' + bp[1].toFixed(2) + '" r="4.6" fill="' + fill + '" stroke="' + stroke + '" stroke-width="0.9"/>';
        s += '<text x="' + bp[0].toFixed(2) + '" y="' + (bp[1] + 2.1).toFixed(2) + '" text-anchor="middle" font-size="7" font-weight="700" fill="' + stroke + '">' + glyph + '</text>';
      }
    }

    // номера спиц
    if (state.showNumbers) {
      for (i = 0; i < N; i++) {
        var np = polar(i * da, 110);
        s += '<text x="' + np[0].toFixed(2) + '" y="' + (np[1] + 2.4).toFixed(2) + '" text-anchor="middle" font-size="7" fill="#475569">' + (i + 1) + '</text>';
      }
    }

    // метка старта (спица №1 сверху)
    s += '<path d="M0 -116 L-5 -125 L5 -125 Z" fill="#2563eb" opacity="0.85"/>';

    svg.innerHTML = s;
  }

  /* ------------------------------------------------------------------ */
  /* таблица результатов                                                 */
  /* ------------------------------------------------------------------ */

  function frac(v) {
    var a = Math.round(Math.abs(v) * 8) / 8;
    var map = { '0.125': '1/8', '0.25': '1/4', '0.375': '3/8', '0.5': '1/2', '0.625': '5/8', '0.75': '3/4', '0.875': '7/8', '1': '1' };
    return map[String(a)] || a.toFixed(2);
  }

  function renderResults() {
    var tbody = document.querySelector('#resTable tbody');
    var summary = document.getElementById('summary');

    if (!result) {
      summary.innerHTML = '<span class="muted">' + T.empty + '</span>';
      tbody.innerHTML = '';
      return;
    }

    var items = [];
    for (var i = 0; i < state.n; i++) {
      var tv = result.turns[i];
      if (Math.abs(tv) >= 0.125 - 1e-9) items.push({ i: i, side: spokeSide(i), tv: tv });
    }

    if (items.length === 0) {
      summary.innerHTML = '<span class="muted">' + T.none + '</span>';
      tbody.innerHTML = '';
      return;
    }

    var tight = items.filter(function (x) { return x.tv > 0; }).length;
    var loose = items.length - tight;
    summary.innerHTML = T.counts
      .replace('{tight}', tight)
      .replace('{loose}', loose)
      .replace('{total}', items.length);

    items.sort(function (a, b) { return a.i - b.i; });
    tbody.innerHTML = items.map(function (x) {
      var sideTag = x.side === 'L' ? '<span class="tag L">L</span>' : '<span class="tag R">R</span>';
      var act = x.tv > 0 ? '<span class="act tight">' + T.tight + '</span>' : '<span class="act loose">' + T.loose + '</span>';
      return '<tr><td>' + (x.i + 1) + '</td><td>' + sideTag + '</td><td>' + act + '</td><td>' + frac(x.tv) + ' ' + T.turn + '</td></tr>';
    }).join('');
  }

  function update() { compute(); draw(); renderResults(); }

  /* ------------------------------------------------------------------ */
  /* ввод: клик / перетаскивание по сегментам                            */
  /* ------------------------------------------------------------------ */

  function gapAt(evt) {
    var m = svg.getScreenCTM();
    if (!m) return -1;
    var pt = svg.createSVGPoint();
    pt.x = evt.clientX; pt.y = evt.clientY;
    var loc = pt.matrixTransform(m.inverse());
    var r = Math.hypot(loc.x, loc.y);
    if (r < 52 || r > 108) return -1;
    var a = Math.atan2(loc.x, -loc.y);
    if (a < 0) a += TAU;
    return Math.floor(a / (TAU / state.n)) % state.n;
  }

  function applyMark(g) {
    if (g < 0) return;
    var st = state.strength;
    switch (state.mode) {
      case 'latR': state.lateral[g] = st; break;
      case 'latL': state.lateral[g] = -st; break;
      case 'radO': state.radial[g] = st; break;
      case 'radI': state.radial[g] = -st; break;
      case 'erase': state.lateral[g] = 0; state.radial[g] = 0; break;
    }
  }

  function pushHistory() {
    history.push({ l: state.lateral.slice(), r: state.radial.slice() });
    if (history.length > 80) history.shift();
  }

  // закрашивает путь между двумя промежутками, чтобы перетаскивание не «пропускало» сегменты
  function paintTo(g) {
    if (g < 0) return;
    if (lastGap === null || lastGap === g) {
      applyMark(g);
    } else {
      var N = state.n;
      var d = g - lastGap;
      d = ((d % N) + N) % N;
      if (d > N / 2) d -= N;
      var step = d > 0 ? 1 : -1;
      for (var k = 1; k <= Math.abs(d); k++) {
        applyMark(((lastGap + step * k) % N + N) % N);
      }
    }
    lastGap = g;
  }

  svg.addEventListener('pointerdown', function (e) {
    if (e.pointerType === 'mouse' && e.button !== 0) return;
    e.preventDefault();
    pushHistory();
    painting = true;
    lastGap = null;
    try { svg.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    paintTo(gapAt(e));
    update();
  });

  svg.addEventListener('pointermove', function (e) {
    if (painting) {
      paintTo(gapAt(e));
      update();
    } else {
      var g = gapAt(e);
      if (g !== hoverGap) { hoverGap = g; draw(); }
    }
  });

  function endPaint() { painting = false; lastGap = null; }
  svg.addEventListener('pointerup', endPaint);
  svg.addEventListener('pointercancel', endPaint);
  svg.addEventListener('pointerleave', function () {
    if (hoverGap !== -1) { hoverGap = -1; draw(); }
  });

  /* ------------------------------------------------------------------ */
  /* элементы управления                                                 */
  /* ------------------------------------------------------------------ */

  var nSel = document.getElementById('nSel');
  SPOKE_COUNTS.forEach(function (c) {
    var o = document.createElement('option');
    o.value = c; o.textContent = c;
    if (c === 32) o.selected = true;
    nSel.appendChild(o);
  });

  nSel.addEventListener('change', function () {
    state.n = parseInt(nSel.value, 10) || 32;
    initMarks();
    result = null;
    update();
  });

  var sideSel = document.getElementById('sideSel');
  sideSel.addEventListener('change', function () {
    state.firstSide = sideSel.value;
    update();
  });

  var modeButtons = Array.prototype.slice.call(document.querySelectorAll('.mode'));
  modeButtons.forEach(function (btn) {
    btn.addEventListener('click', function () {
      state.mode = btn.getAttribute('data-mode');
      modeButtons.forEach(function (b) { b.classList.toggle('active', b === btn); });
      draw();
    });
  });

  var segStr = document.getElementById('segStr');
  segStr.addEventListener('click', function (e) {
    var b = e.target.closest ? e.target.closest('.seg-btn') : null;
    if (!b) return;
    state.strength = parseInt(b.getAttribute('data-val'), 10);
    Array.prototype.forEach.call(segStr.querySelectorAll('.seg-btn'), function (x) {
      x.classList.toggle('active', x === b);
    });
  });

  var resultsCard = document.getElementById('resultsCard');
  var resToggle = document.getElementById('resToggle');
  resToggle.addEventListener('click', function () {
    var open = resultsCard.classList.toggle('open');
    resToggle.setAttribute('aria-expanded', String(open));
  });

  var turnSel = document.getElementById('turnSel');
  turnSel.addEventListener('change', function () {
    state.maxTurn = parseFloat(turnSel.value);
    update();
  });

  var numChk = document.getElementById('numChk');
  numChk.addEventListener('change', function () {
    state.showNumbers = numChk.checked;
    draw();
  });

  document.getElementById('clearBtn').addEventListener('click', function () {
    pushHistory();
    state.lateral.fill(0);
    state.radial.fill(0);
    update();
  });

  document.getElementById('undoBtn').addEventListener('click', function () {
    if (!history.length) return;
    var st = history.pop();
    state.lateral = st.l;
    state.radial = st.r;
    update();
  });

  document.getElementById('exampleBtn').addEventListener('click', function () {
    pushHistory();
    state.lateral.fill(0);
    state.radial.fill(0);
    var c1 = Math.round(state.n * 0.14);
    var c2 = Math.round(state.n * 0.64);
    for (var d = -1; d <= 1; d++) {
      state.lateral[(c1 + d + state.n) % state.n] = 2;
      state.lateral[(c2 + d + state.n) % state.n] = -2;
    }
    update();
  });

  window.addEventListener('keydown', function (e) {
    if ((e.ctrlKey || e.metaKey) && (e.key === 'z' || e.key === 'Z')) {
      e.preventDefault();
      document.getElementById('undoBtn').click();
    }
  });

  // старт
  update();
})();