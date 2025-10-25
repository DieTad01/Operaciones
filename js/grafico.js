// ===============================
// Método gráfico (minimización) – 2 variables
// Archivo: js/grafico.js
// ===============================

const $ = (id) => document.getElementById(id);
const plot = $("plot");
const ctx = plot.getContext("2d");

// ------------ Utilidades numéricas ------------
function nearly(a, b, eps = 1e-9) { return Math.abs(a - b) <= eps; }
function isFiniteNumber(x) { return Number.isFinite(x) && !Number.isNaN(x); }

// Intersección de dos rectas: a1 x + b1 y = c1  y  a2 x + b2 y = c2
function lineIntersection(a1, b1, c1, a2, b2, c2) {
  const det = a1 * b2 - a2 * b1;
  if (nearly(det, 0)) return null; // paralelas o coincidentes
  const x = (c1 * b2 - c2 * b1) / det;
  const y = (a1 * c2 - a2 * c1) / det;
  return { x, y };
}

// Convex hull (Graham scan) para ordenar vértices y poder rellenar región
function convexHull(points) {
  const pts = points.slice().sort((p, q) => p.x === q.x ? p.y - q.y : p.x - q.x);
  if (pts.length <= 1) return pts;
  const cross = (o, a, b) => (a.x - o.x)*(b.y - o.y) - (a.y - o.y)*(b.x - o.x);
  const lower = [];
  for (const p of pts) {
    while (lower.length >= 2 && cross(lower[lower.length-2], lower[lower.length-1], p) <= 0) lower.pop();
    lower.push(p);
  }
  const upper = [];
  for (let i = pts.length - 1; i >= 0; i--) {
    const p = pts[i];
    while (upper.length >= 2 && cross(upper[upper.length-2], upper[upper.length-1], p) <= 0) upper.pop();
    upper.push(p);
  }
  upper.pop(); lower.pop();
  return lower.concat(upper);
}

// ------------ Parser de restricciones ------------
// Acepta: "2x + 3y <= 18", "-x + 2y ≥ 4", "x <= 6", "y <= 7", y también < / >
function parseConstraint(line) {
  const txt = line.replace(/·/g, "*").replace(/,/g, ".").trim();
  if (!txt) return null;

  // Normaliza símbolos
  const norm = txt
    .replace(/≤/g, "<=")
    .replace(/≥/g, ">=");

  // Detecta operador (incluye < y >)
  const opMatch = norm.match(/(<=|>=|=|<|>)/);
  if (!opMatch) return null;
  let op = opMatch[1];

  const parts = norm.split(op);
  if (parts.length !== 2) return null;
  const lhsRaw = parts[0];
  const rhs = parseFloat(parts[1]);
  if (!isFiniteNumber(rhs)) return null;

  // Normaliza estrictos a no-estrictos (pintamos solo frontera, región no cambia)
  if (op === "<") op = "<=";
  if (op === ">") op = ">=";

  // Extrae coeficientes de x e y (si falta, 0; si es solo 'x' o '+x', 1; '-x', -1)
  const coef = (expr, v) => {
    // Busca ... [+|-] [num opcional] v (evita capturar 'xy')
    const re = new RegExp(`([+-]?\\s*\\d*\\.?\\d*)\\s*${v}(?![a-zA-Z0-9_])`, "i");
    const m = expr.match(re);
    if (!m) return 0;
    const s = m[1].replace(/\s+/g, "");
    if (s === "" || s === "+" || s === "+.") return 1;
    if (s === "-" || s === "-.") return -1;
    const val = parseFloat(s);
    return Number.isFinite(val) ? val : 0;
  };

  const a = coef(lhsRaw, "x");
  const b = coef(lhsRaw, "y");

  return { a, b, op, rhs };
}

function expandEquality(c) {
  if (c.op !== "=") return [c];
  // a x + b y = rhs  ->  (<= rhs) y (>= rhs)
  return [
    { a: c.a, b: c.b, op: "<=", rhs: c.rhs },
    { a: c.a, b: c.b, op: ">=", rhs: c.rhs }
  ];
}

// ------------ Modelo y resolución ------------
function solveModel(c1, c2, constraints) {
  // Añadimos x>=0, y>=0 como restricciones: -x <= 0, -y <= 0
  const cons = [];
  for (const raw of constraints) {
    const c = parseConstraint(raw);
    if (!c) continue;
    for (const piece of expandEquality(c)) cons.push(piece);
  }
  cons.push({ a: -1, b: 0, op: "<=", rhs: 0 }); // -x <= 0  -> x >= 0
  cons.push({ a: 0, b: -1, op: "<=", rhs: 0 }); // -y <= 0  -> y >= 0

  // Generamos todas las intersecciones de fronteras (a x + b y = rhs) por pares
  const lines = cons.map(c => ({ a: c.a, b: c.b, rhs: c.rhs }));
  const vertices = [];

  for (let i = 0; i < lines.length; i++) {
    for (let j = i + 1; j < lines.length; j++) {
      const p = lineIntersection(lines[i].a, lines[i].b, lines[i].rhs,
                                 lines[j].a, lines[j].b, lines[j].rhs);
      if (!p) continue;
      if (!isFiniteNumber(p.x) || !isFiniteNumber(p.y)) continue;

      // Factibilidad: todas las desigualdades se deben cumplir
      let feasible = true;
      for (const c of cons) {
        const lhs = c.a * p.x + c.b * p.y;
        if (c.op === "<=" && lhs > c.rhs + 1e-9) { feasible = false; break; }
        if (c.op === ">=" && lhs < c.rhs - 1e-9) { feasible = false; break; }
      }
      if (feasible && p.x >= -1e-9 && p.y >= -1e-9) {
        // Redondeo suave y elimina duplicados cercanos
        const rx = Math.max(0, p.x);
        const ry = Math.max(0, p.y);
        if (!vertices.some(q => Math.hypot(q.x - rx, q.y - ry) < 1e-7)) {
          vertices.push({ x: rx, y: ry });
        }
      }
    }
  }

  if (!vertices.length) return { feasible:false, vertices:[], best:null, cons };

  // Evalúa z en cada vértice (min)
  const evals = vertices.map(v => ({ ...v, z: c1*v.x + c2*v.y }));
  evals.sort((p,q) => p.z - q.z);
  const best = evals[0];

  return { feasible:true, vertices:evals, best, cons, c1, c2 };
}

// Detecta posible no-acotado hacia abajo (heurística)
function likelyUnbounded(sol) {
  if (!sol.feasible || !sol.best) return false;
  const dir = { x: -sol.c1 || 0, y: -sol.c2 || 0 };
  const norm = Math.hypot(dir.x, dir.y);
  if (norm < 1e-12) return false; // objetivo constante
  dir.x /= norm; dir.y /= norm;

  // Prueba pasos pequeños bajando z; si seguimos factibles consistentemente, podría ser no acotado
  let test = { x: sol.best.x, y: sol.best.y };
  for (let k = 0; k < 50; k++) {
    test = { x: test.x + 0.05 * dir.x, y: test.y + 0.05 * dir.y };
    // factibilidad
    let ok = true;
    for (const c of sol.cons) {
      const lhs = c.a * test.x + c.b * test.y;
      if (c.op === "<=" && lhs > c.rhs + 1e-7) { ok = false; break; }
      if (c.op === ">=" && lhs < c.rhs - 1e-7) { ok = false; break; }
    }
    if (!ok || test.x < -1e-6 || test.y < -1e-6) return false;
  }
  return true;
}

// ------------ Dibujo ------------
function drawSolution(sol) {
  ctx.clearRect(0,0,plot.width, plot.height);

  // Margen y escalado
  const pad = 50;
  const W = plot.width, H = plot.height;
  const innerW = W - 2*pad;
  const innerH = H - 2*pad;

  // Determina límites (usa vértices factibles)
  const xs = sol.vertices.map(p => p.x), ys = sol.vertices.map(p => p.y);
  const maxX = Math.max(1, ...xs) * 1.15;
  const maxY = Math.max(1, ...ys) * 1.15;

  const sx = innerW / maxX;
  const sy = innerH / maxY;

  const X = x => pad + x * sx;
  const Y = y => H - pad - y * sy;

  // Ejes
  ctx.strokeStyle = "#000";
  ctx.lineWidth = 1.2;
  ctx.beginPath();
  ctx.moveTo(pad, Y(0)); ctx.lineTo(W-pad, Y(0)); // eje x
  ctx.moveTo(X(0), pad); ctx.lineTo(X(0), H-pad); // eje y
  ctx.stroke();
  ctx.fillStyle = "#111"; ctx.font = "12px system-ui";
  ctx.fillText("x", W - pad + 10, Y(0) + 4);
  ctx.fillText("y", X(0) - 10, pad - 8);

  // Líneas de restricciones (solo límite, como a x + b y = rhs)
  ctx.lineWidth = 1;
  for (const c of sol.cons) {
    // Puntos sobre la frontera (intersecciones con ejes)
    const pts = [];
    if (!nearly(c.b, 0)) pts.push({ x: 0, y: c.rhs / c.b });
    if (!nearly(c.a, 0)) pts.push({ x: c.rhs / c.a, y: 0 });
    // Si solo hay un punto, genera otro dentro de rango
    if (pts.length === 1) pts.push({ x: pts[0].x + 1, y: (c.rhs - c.a*(pts[0].x + 1)) / (c.b || 1e-9) });

    if (pts.length >= 2 && isFiniteNumber(pts[0].x) && isFiniteNumber(pts[0].y) && isFiniteNumber(pts[1].x) && isFiniteNumber(pts[1].y)) {
      ctx.strokeStyle = "#9ca3af";
      ctx.beginPath();
      ctx.moveTo(X(pts[0].x), Y(pts[0].y));
      ctx.lineTo(X(pts[1].x), Y(pts[1].y));
      ctx.stroke();
    }
  }

  // Región factible (hull de vértices)
  const hull = convexHull(sol.vertices);
  if (hull.length >= 3) {
    ctx.fillStyle = "rgba(16, 185, 129, 0.15)"; // verde suave
    ctx.strokeStyle = "rgba(16, 185, 129, 0.9)";
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.moveTo(X(hull[0].x), Y(hull[0].y));
    for (let i=1;i<hull.length;i++) ctx.lineTo(X(hull[i].x), Y(hull[i].y));
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
  }

  // Vértices factibles
  ctx.fillStyle = "#065f46";
  for (const p of sol.vertices) {
    ctx.beginPath();
    ctx.arc(X(p.x), Y(p.y), 3.5, 0, Math.PI*2);
    ctx.fill();
  }

  // Iso-costo óptima: c1 x + c2 y = z*
  const z = sol.best.z, c1 = sol.c1, c2 = sol.c2;
  let i1 = null, i2 = null;
  if (!nearly(c2, 0)) i1 = { x: 0, y: z / c2 };
  if (!nearly(c1, 0)) i2 = { x: z / c1, y: 0 };
  if (i1 && i2 && isFiniteNumber(i1.y) && isFiniteNumber(i2.x)) {
    ctx.strokeStyle = "#1d4ed8";
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(X(i1.x), Y(i1.y));
    ctx.lineTo(X(i2.x), Y(i2.y));
    ctx.stroke();

    ctx.fillStyle = "#1d4ed8";
    ctx.font = "12px system-ui";
    ctx.fillText(`z* = ${z.toFixed(4)}`, X((i1.x+i2.x)/2)+6, Y((i1.y+i2.y)/2)-6);
  }

  // Ejes ticks básicos
  ctx.fillStyle = "#6b7280";
  ctx.font = "11px system-ui";
  const ticks = 6;
  for (let k=0;k<=ticks;k++){
    const xv = (k/ticks)*maxX, yv=(k/ticks)*maxY;
    // x
    ctx.beginPath(); ctx.moveTo(X(xv), Y(0)-3); ctx.lineTo(X(xv), Y(0)+3); ctx.strokeStyle="#d1d5db"; ctx.stroke();
    ctx.fillText(xv.toFixed(1), X(xv)-6, Y(0)+14);
    // y
    ctx.beginPath(); ctx.moveTo(X(0)-3, Y(yv)); ctx.lineTo(X(0)+3, Y(yv)); ctx.strokeStyle="#d1d5db"; ctx.stroke();
    ctx.fillText(yv.toFixed(1), X(0)-34, Y(yv)+4);
  }
}

// ------------ UI / Integración ------------
function renderTable(sol) {
  const box = $("solutionBox");
  if (!sol.feasible) {
    box.innerHTML = `<p class="bad">No hay región factible.</p>`;
    return;
  }
  const rows = sol.vertices
    .map(v => `<tr><td>${v.x.toFixed(4)}</td><td>${v.y.toFixed(4)}</td><td>${v.z.toFixed(4)}</td></tr>`)
    .join("");

  box.innerHTML = `
    <table>
      <thead><tr><th>x</th><th>y</th><th>z = c₁x + c₂y</th></tr></thead>
      <tbody>${rows}</tbody>
    </table>
    <center><p style="margin-top:8px; font-family:Verdana">Óptimo: <span class="ok">x* = ${sol.best.x.toFixed(3)}, y* = ${sol.best.y.toFixed(3)}, Fz* = ${sol.best.z.toFixed(3)}</span></p></center>
  `;
}

function solveAndDraw() {
  const c1 = parseFloat($("c1txt").value);
  const c2 = parseFloat($("c2txt").value);
  const c1Span = $("c1txt");
  const c2Span = $("c2txt");
  if (c1Span) c1Span.textContent = isFiniteNumber(c1) ? c1 : "?";
  if (c2Span) c2Span.textContent = isFiniteNumber(c2) ? c2 : "?";

  const txt = $("constraints").value.trim();
  const lines = txt.split(/\n+/).map(s => s.trim()).filter(Boolean);

  try {
    const sol = solveModel(c1, c2, lines);
    if (!sol.feasible) {
      $("status").innerHTML = `<span class="bad">Modelo infactible.</span>`;
      $("solutionBox").innerHTML = `<p class="bad">No se encontraron vértices factibles. Revisa las restricciones.</p>`;
      ctx.clearRect(0,0,plot.width, plot.height);
      return;
    }

    // Aviso de mínimo trivial en (0,0)
    const zeroFeasible = sol.cons.every(c => {
      const lhs = c.a*0 + c.b*0;
      return (c.op === "<=" && lhs <= c.rhs + 1e-9) || (c.op === ">=" && lhs >= c.rhs - 1e-9);
    });
    if (zeroFeasible && (c1 >= 0) && (c2 >= 0)) {
      $("status").innerHTML = `<span class="ok">Listo ✓</span> <span class="mono" style="margin-left:8px;color:#6b7280">Aviso: con c₁,c₂ ≥ 0 y (0,0) factible, el mínimo es (0,0). Usa alguna restricción ≥ / = para evitarlo.</span>`;
    } else {
      $("status").innerHTML = `<span class="ok">Listo ✓</span>`;
    }

    // Posible no acotado hacia abajo
    if (sol.best && likelyUnbounded(sol)) {
      $("status").innerHTML += ` <span class="bad" style="margin-left:8px">Posible no acotado ↓z (revisa restricciones).</span>`;
    }

    renderTable(sol);
    drawSolution(sol);
  } catch (e) {
    console.error(e);
    $("status").innerHTML = `<span class="bad">Error: ${e.message}</span>`;
  }
}

// Botones
$("solveBtn").addEventListener("click", solveAndDraw);
$("exampleBtn").addEventListener("click", () => {
  $("c1text").value = 3;
  $("c2text").value = 5;
  $("constraints").value = `2x + 3y ≤ 18
x + y ≤ 10
x ≤ 6
y ≤ 7`;
  solveAndDraw();
});

// Resolver al cargar por primera vez
window.addEventListener("load", solveAndDraw);