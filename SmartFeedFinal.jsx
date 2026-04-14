import { useState, useMemo } from "react";

// ─────────────────────────────────────────────
// THEME
// ─────────────────────────────────────────────
const T = {
  bg: "#f8fafc", white: "#ffffff", text: "#0f172a",
  muted: "#64748b", border: "#e2e8f0",
  primary: "#16a34a", primaryLight: "#dcfce7", primaryDark: "#166534",
  danger: "#dc2626", dangerLight: "#fee2e2",
  warn: "#d97706",
};

const CAT = {
  energy:   { label:"Energi",   color:"#d97706", bg:"#fffbeb" },
  protein:  { label:"Protein",  color:"#059669", bg:"#ecfdf5" },
  roughage: { label:"Hijauan",  color:"#2563eb", bg:"#eff6ff" },
  additive: { label:"Aditif",   color:"#7c3aed", bg:"#f5f3ff" },
};

// ─────────────────────────────────────────────
// LP SOLVER (Big-M Simplex)
// ─────────────────────────────────────────────
function solveSimplex(cMin, rawCons, n) {
  const BIG = 1e6, EPS = 1e-8, m = rawCons.length;
  const cons = rawCons.map(function(c) {
    if (c.b < -EPS) {
      return { type: c.type === "le" ? "ge" : c.type === "ge" ? "le" : "eq", a: c.a.map(function(v){ return -v; }), b: -c.b };
    }
    return c;
  });
  var nS = 0, nA = 0;
  for (var ci = 0; ci < cons.length; ci++) {
    if (cons[ci].type === "le") nS++;
    else if (cons[ci].type === "ge") { nS++; nA++; }
    else nA++;
  }
  var N = n + nS + nA;
  var T2 = [];
  for (var r = 0; r <= m; r++) { T2.push(new Float64Array(N + 1)); }
  var basis = new Int32Array(m), isArt = new Uint8Array(N);
  var si = n, ai = n + nS;
  for (var i = 0; i < m; i++) {
    var c = cons[i];
    for (var j = 0; j < n; j++) T2[i][j] = c.a[j];
    T2[i][N] = Math.max(0, c.b);
    if (c.type === "le") { T2[i][si] = 1; basis[i] = si++; }
    else if (c.type === "ge") { T2[i][si++] = -1; T2[i][ai] = 1; isArt[ai] = 1; basis[i] = ai++; }
    else { T2[i][ai] = 1; isArt[ai] = 1; basis[i] = ai++; }
  }
  for (var j2 = 0; j2 < n; j2++) T2[m][j2] = -cMin[j2];
  for (var j3 = n + nS; j3 < N; j3++) T2[m][j3] = -BIG;
  for (var i2 = 0; i2 < m; i2++) {
    if (isArt[basis[i2]]) {
      var f = T2[m][basis[i2]];
      for (var j4 = 0; j4 <= N; j4++) T2[m][j4] -= f * T2[i2][j4];
    }
  }
  for (var iter = 0; iter < 200000; iter++) {
    var pc = -1, best = EPS;
    for (var j5 = 0; j5 < N; j5++) { if (T2[m][j5] > best) { best = T2[m][j5]; pc = j5; } }
    if (pc < 0) break;
    var pr = -1, minR = Infinity;
    for (var i3 = 0; i3 < m; i3++) {
      if (T2[i3][pc] > EPS) { var rat = T2[i3][N] / T2[i3][pc]; if (rat < minR) { minR = rat; pr = i3; } }
    }
    if (pr < 0) return { status: "unbounded" };
    basis[pr] = pc;
    var pv = T2[pr][pc];
    for (var j6 = 0; j6 <= N; j6++) T2[pr][j6] /= pv;
    for (var i4 = 0; i4 <= m; i4++) {
      if (i4 !== pr) { var ff = T2[i4][pc]; if (Math.abs(ff) > 1e-13) for (var j7 = 0; j7 <= N; j7++) T2[i4][j7] -= ff * T2[pr][j7]; }
    }
  }
  for (var i5 = 0; i5 < m; i5++) { if (isArt[basis[i5]] && T2[i5][N] > 1e-4) return { status: "infeasible" }; }
  var x = new Array(n).fill(0);
  for (var i6 = 0; i6 < m; i6++) { if (basis[i6] < n) x[basis[i6]] = Math.max(0, T2[i6][N]); }
  return { status: "optimal", x: x };
}

function runOptimize(ings, inclBounds, nutCons) {
  var n = ings.length;
  if (n < 2) return { status: "error", msg: "Pilih minimal 2 bahan pakan." };
  var lb = ings.map(function(g) { return inclBounds[g.id] ? inclBounds[g.id].min : 0; });
  var ub = ings.map(function(g) { return inclBounds[g.id] ? inclBounds[g.id].max : 100; });
  var costC = ings.map(function(g) { return g.price / (g.dm / 100); });
  var K = 100 - lb.reduce(function(s, v) { return s + v; }, 0);
  if (K < -1e-4) return { status: "infeasible", msg: "Total minimum inclusion melebihi 100%." };
  var cons = [];
  for (var i = 0; i < n; i++) {
    var a = new Array(n).fill(0); a[i] = 1;
    cons.push({ type: "le", a: a, b: ub[i] - lb[i] });
  }
  cons.push({ type: "eq", a: new Array(n).fill(1), b: K });
  for (var ni = 0; ni < nutCons.length; ni++) {
    var nc = nutCons[ni];
    if (!nc.active) continue;
    var lbAdj = 0;
    for (var ii = 0; ii < n; ii++) lbAdj += (ings[ii][nc.key] || 0) * lb[ii] / 100;
    var coeffs = ings.map(function(g) { return (g[nc.key] || 0) / 100; });
    if (nc.max != null) cons.push({ type: "le", a: coeffs, b: nc.max - lbAdj });
    if (nc.min != null) cons.push({ type: "ge", a: coeffs, b: nc.min - lbAdj });
  }
  var res = solveSimplex(costC, cons, n);
  if (res.status !== "optimal") return { status: "infeasible", msg: "Tidak ada solusi. Coba perlonggar batasan nutrisi atau inklusi bahan." };
  var xDM = res.x.map(function(q, i) { return q + lb[i]; });
  var xAFraw = xDM.map(function(v, i) { return v * (100 / ings[i].dm); });
  var sumAF = xAFraw.reduce(function(s, v) { return s + v; }, 0);
  var xAF = xAFraw.map(function(v) { return sumAF > 0 ? v / sumAF * 100 : 0; });
  var NKEYS = ["cp","ee","cf","ash","nfe","tdn","me","nem","neg","ca","p","ndf","adf"];
  var nutLvls = {};
  for (var ki = 0; ki < NKEYS.length; ki++) {
    var k = NKEYS[ki], sum = 0;
    for (var ii2 = 0; ii2 < n; ii2++) sum += (ings[ii2][k] || 0) * xDM[ii2] / 100;
    nutLvls[k] = sum;
  }
  var costDM = 0;
  for (var ii3 = 0; ii3 < n; ii3++) costDM += (ings[ii3].price / (ings[ii3].dm / 100)) * xDM[ii3] / 100;
  var inclusions = [];
  for (var ii4 = 0; ii4 < n; ii4++) {
    if (xDM[ii4] > 0.01) {
      inclusions.push(Object.assign({}, ings[ii4], {
        pctDM: xDM[ii4], pctAF: xAF[ii4],
        costContrib: (ings[ii4].price / (ings[ii4].dm / 100)) * xDM[ii4] / 100,
      }));
    }
  }
  return { status: "optimal", inclusions: inclusions, nutLvls: nutLvls, costDM: costDM };
}

// ─────────────────────────────────────────────
// NUTRIENT META
// ─────────────────────────────────────────────
var NUT_META = [
  { key:"cp",  label:"Protein Kasar (CP)", unit:"% BK",       color:"#059669", group:"Proksimat" },
  { key:"ee",  label:"Lemak Kasar (EE)",   unit:"% BK",       color:"#d97706", group:"Proksimat" },
  { key:"cf",  label:"Serat Kasar (CF)",   unit:"% BK",       color:"#7c3aed", group:"Proksimat" },
  { key:"tdn", label:"TDN",                unit:"% BK",       color:"#ea580c", group:"Energi" },
  { key:"me",  label:"ME",                 unit:"Mcal/kg BK", color:"#dc2626", group:"Energi" },
  { key:"nem", label:"NEm",                unit:"Mcal/kg BK", color:"#c2410c", group:"Energi" },
  { key:"neg", label:"NEg",                unit:"Mcal/kg BK", color:"#b45309", group:"Energi" },
  { key:"ca",  label:"Kalsium (Ca)",       unit:"% BK",       color:"#0891b2", group:"Mineral" },
  { key:"p",   label:"Fosfor (P)",         unit:"% BK",       color:"#0284c7", group:"Mineral" },
  { key:"ndf", label:"NDF",                unit:"% BK",       color:"#9333ea", group:"Serat" },
  { key:"adf", label:"ADF",                unit:"% BK",       color:"#a21caf", group:"Serat" },
];

// ─────────────────────────────────────────────
// ANIMAL DATABASE
// ─────────────────────────────────────────────
var ANIMALS = {
  sapi_potong: { label:"Sapi Potong", icon:"🐂", phases:[
    { id:"starter",  label:"Starter",  sub:"0–3 bln",   active:["cp","tdn","me","cf","ca","p"], reqs:{ cp:{min:14,max:16}, tdn:{min:66,max:72}, me:{min:2.55,max:2.79}, nem:{min:1.55,max:1.70}, neg:{min:0.85,max:1.05}, cf:{min:15,max:22}, ee:{min:2,max:7}, ca:{min:0.55,max:0.70}, p:{min:0.28,max:0.40}, ndf:{min:28,max:38}, adf:{min:18,max:28} }},
    { id:"grower",   label:"Grower",   sub:"3–6 bln",   active:["cp","tdn","me","cf","ca","p"], reqs:{ cp:{min:12,max:14}, tdn:{min:70,max:75}, me:{min:2.71,max:2.91}, nem:{min:1.60,max:1.75}, neg:{min:1.00,max:1.20}, cf:{min:13,max:20}, ee:{min:2,max:7}, ca:{min:0.50,max:0.65}, p:{min:0.25,max:0.35}, ndf:{min:26,max:35}, adf:{min:16,max:25} }},
    { id:"finisher", label:"Finisher", sub:"6+ bln",    active:["cp","tdn","me","cf","ca","p"], reqs:{ cp:{min:10,max:12}, tdn:{min:74,max:80}, me:{min:2.87,max:3.10}, nem:{min:1.65,max:1.80}, neg:{min:1.10,max:1.35}, cf:{min:12,max:18}, ee:{min:2,max:6}, ca:{min:0.40,max:0.55}, p:{min:0.22,max:0.32}, ndf:{min:24,max:32}, adf:{min:14,max:22} }},
  ]},
  sapi_perah: { label:"Sapi Perah", icon:"🐄", phases:[
    { id:"lakt_awal",  label:"Laktasi Awal",   sub:"0–3 bln",  active:["cp","tdn","me","cf","ca","p"], reqs:{ cp:{min:17,max:19}, tdn:{min:72,max:78}, me:{min:2.79,max:3.02}, nem:{min:1.68,max:1.88}, neg:{min:1.08,max:1.28}, cf:{min:14,max:20}, ee:{min:3,max:7}, ca:{min:0.65,max:0.80}, p:{min:0.40,max:0.55}, ndf:{min:28,max:38}, adf:{min:18,max:28} }},
    { id:"lakt_puncak",label:"Laktasi Puncak", sub:"3–6 bln",  active:["cp","tdn","me","cf","ca","p"], reqs:{ cp:{min:16,max:18}, tdn:{min:74,max:80}, me:{min:2.87,max:3.10}, nem:{min:1.74,max:1.94}, neg:{min:1.14,max:1.34}, cf:{min:12,max:18}, ee:{min:3,max:7}, ca:{min:0.60,max:0.75}, p:{min:0.38,max:0.50}, ndf:{min:26,max:36}, adf:{min:16,max:26} }},
    { id:"lakt_akhir", label:"Laktasi Akhir",  sub:"6+ bln",   active:["cp","tdn","me","ca","p"],      reqs:{ cp:{min:14,max:16}, tdn:{min:66,max:73}, me:{min:2.56,max:2.83}, nem:{min:1.55,max:1.72}, neg:{min:0.95,max:1.12}, cf:{min:14,max:22}, ee:{min:2,max:7}, ca:{min:0.55,max:0.70}, p:{min:0.35,max:0.45}, ndf:{min:28,max:38}, adf:{min:18,max:28} }},
    { id:"kering",     label:"Masa Kering",    sub:"Dry period",active:["cp","tdn","me","ca","p"],      reqs:{ cp:{min:12,max:14}, tdn:{min:58,max:65}, me:{min:2.25,max:2.52}, nem:{min:1.35,max:1.52}, neg:{min:0.75,max:0.92}, cf:{min:18,max:26}, ee:{min:2,max:6}, ca:{min:0.40,max:0.55}, p:{min:0.28,max:0.38}, ndf:{min:30,max:42}, adf:{min:20,max:32} }},
  ]},
  domba: { label:"Domba", icon:"🐏", phases:[
    { id:"starter",  label:"Starter",        sub:"0–2 bln",         active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:16,max:18}, tdn:{min:68,max:75}, me:{min:2.63,max:2.91}, nem:{min:1.58,max:1.76}, neg:{min:0.98,max:1.16}, cf:{min:12,max:20}, ee:{min:2,max:6}, ca:{min:0.50,max:0.65}, p:{min:0.28,max:0.40}, ndf:{min:25,max:35}, adf:{min:15,max:25} }},
    { id:"grower",   label:"Grower",         sub:"2–4 bln",         active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:14,max:16}, tdn:{min:65,max:72}, me:{min:2.52,max:2.79}, nem:{min:1.52,max:1.68}, neg:{min:0.92,max:1.08}, cf:{min:14,max:22}, ee:{min:2,max:6}, ca:{min:0.45,max:0.60}, p:{min:0.25,max:0.36}, ndf:{min:27,max:37}, adf:{min:17,max:27} }},
    { id:"finisher", label:"Finisher",       sub:"4+ bln",          active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:12,max:14}, tdn:{min:68,max:74}, me:{min:2.63,max:2.87}, nem:{min:1.58,max:1.74}, neg:{min:0.98,max:1.14}, cf:{min:12,max:20}, ee:{min:2,max:6}, ca:{min:0.40,max:0.55}, p:{min:0.22,max:0.32}, ndf:{min:24,max:34}, adf:{min:14,max:24} }},
    { id:"bunting",  label:"Induk Bunting",  sub:"Trimester akhir", active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:12,max:14}, tdn:{min:60,max:66}, me:{min:2.33,max:2.56}, nem:{min:1.40,max:1.54}, neg:{min:0.80,max:0.94}, cf:{min:15,max:25}, ee:{min:2,max:6}, ca:{min:0.45,max:0.60}, p:{min:0.25,max:0.38}, ndf:{min:28,max:40}, adf:{min:18,max:30} }},
    { id:"laktasi",  label:"Induk Laktasi",  sub:"0–3 bln",         active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:15,max:17}, tdn:{min:65,max:72}, me:{min:2.52,max:2.79}, nem:{min:1.52,max:1.68}, neg:{min:0.92,max:1.08}, cf:{min:13,max:21}, ee:{min:2,max:6}, ca:{min:0.55,max:0.70}, p:{min:0.30,max:0.42}, ndf:{min:25,max:36}, adf:{min:15,max:26} }},
  ]},
  kambing: { label:"Kambing", icon:"🐐", phases:[
    { id:"starter",  label:"Starter",      sub:"0–2 bln",   active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:16,max:18}, tdn:{min:68,max:74}, me:{min:2.63,max:2.87}, nem:{min:1.58,max:1.74}, neg:{min:0.98,max:1.14}, cf:{min:12,max:20}, ee:{min:2,max:6}, ca:{min:0.50,max:0.65}, p:{min:0.28,max:0.40}, ndf:{min:25,max:35}, adf:{min:15,max:25} }},
    { id:"grower",   label:"Grower",       sub:"2–4 bln",   active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:14,max:16}, tdn:{min:64,max:70}, me:{min:2.48,max:2.71}, nem:{min:1.49,max:1.63}, neg:{min:0.89,max:1.03}, cf:{min:14,max:22}, ee:{min:2,max:6}, ca:{min:0.45,max:0.60}, p:{min:0.25,max:0.36}, ndf:{min:27,max:37}, adf:{min:17,max:27} }},
    { id:"finisher", label:"Finisher",     sub:"4+ bln",    active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:12,max:14}, tdn:{min:66,max:72}, me:{min:2.56,max:2.79}, nem:{min:1.54,max:1.68}, neg:{min:0.94,max:1.08}, cf:{min:13,max:21}, ee:{min:2,max:6}, ca:{min:0.40,max:0.55}, p:{min:0.22,max:0.32}, ndf:{min:25,max:35}, adf:{min:15,max:25} }},
    { id:"induk",    label:"Induk/Bunting",sub:"Reproduksi", active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:13,max:15}, tdn:{min:58,max:65}, me:{min:2.25,max:2.52}, nem:{min:1.35,max:1.52}, neg:{min:0.75,max:0.92}, cf:{min:15,max:25}, ee:{min:2,max:6}, ca:{min:0.45,max:0.60}, p:{min:0.28,max:0.38}, ndf:{min:28,max:40}, adf:{min:18,max:30} }},
  ]},
  kambing_perah: { label:"Kambing Perah", icon:"🐐🥛", phases:[
    { id:"laktasi", label:"Masa Laktasi", sub:"Produksi susu", active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:16,max:18}, tdn:{min:68,max:75}, me:{min:2.63,max:2.91}, nem:{min:1.58,max:1.76}, neg:{min:0.98,max:1.16}, cf:{min:13,max:20}, ee:{min:3,max:7}, ca:{min:0.60,max:0.75}, p:{min:0.38,max:0.50}, ndf:{min:25,max:36}, adf:{min:15,max:26} }},
    { id:"kering",  label:"Masa Kering",  sub:"Dry period",    active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:12,max:14}, tdn:{min:55,max:62}, me:{min:2.13,max:2.40}, nem:{min:1.28,max:1.44}, neg:{min:0.68,max:0.84}, cf:{min:16,max:26}, ee:{min:2,max:6}, ca:{min:0.40,max:0.55}, p:{min:0.25,max:0.35}, ndf:{min:30,max:42}, adf:{min:20,max:32} }},
    { id:"dara",    label:"Dara",         sub:"Calon induk",   active:["cp","tdn","me","ca","p"], reqs:{ cp:{min:14,max:16}, tdn:{min:62,max:68}, me:{min:2.40,max:2.63}, nem:{min:1.44,max:1.58}, neg:{min:0.84,max:0.98}, cf:{min:14,max:22}, ee:{min:2,max:6}, ca:{min:0.50,max:0.65}, p:{min:0.30,max:0.42}, ndf:{min:27,max:38}, adf:{min:17,max:28} }},
  ]},
  broiler: { label:"Ayam Broiler", icon:"🐓", phases:[
    { id:"starter",  label:"Starter",  sub:"0–14 hari",  active:["cp","me","ca","p","cf"], reqs:{ cp:{min:23,max:25}, me:{min:3.10,max:3.30}, ca:{min:0.90,max:1.10}, p:{min:0.42,max:0.52}, ee:{min:4,max:8}, cf:{min:null,max:5}, tdn:{min:null,max:null}, nem:{min:null,max:null}, neg:{min:null,max:null}, ndf:{min:null,max:null}, adf:{min:null,max:null} }},
    { id:"grower",   label:"Grower",   sub:"14–28 hari", active:["cp","me","ca","p","cf"], reqs:{ cp:{min:20,max:22}, me:{min:3.15,max:3.30}, ca:{min:0.85,max:1.00}, p:{min:0.38,max:0.48}, ee:{min:4,max:8}, cf:{min:null,max:5}, tdn:{min:null,max:null}, nem:{min:null,max:null}, neg:{min:null,max:null}, ndf:{min:null,max:null}, adf:{min:null,max:null} }},
    { id:"finisher", label:"Finisher", sub:"28–42 hari", active:["cp","me","ca","p","cf"], reqs:{ cp:{min:18,max:20}, me:{min:3.20,max:3.35}, ca:{min:0.80,max:0.95}, p:{min:0.35,max:0.45}, ee:{min:5,max:9}, cf:{min:null,max:5}, tdn:{min:null,max:null}, nem:{min:null,max:null}, neg:{min:null,max:null}, ndf:{min:null,max:null}, adf:{min:null,max:null} }},
  ]},
  layer: { label:"Ayam Petelur", icon:"🥚", phases:[
    { id:"starter",  label:"Starter",   sub:"0–6 mgg",   active:["cp","me","ca","p","cf"], reqs:{ cp:{min:18,max:20}, me:{min:2.85,max:3.00}, ca:{min:0.90,max:1.05}, p:{min:0.40,max:0.50}, ee:{min:3,max:7}, cf:{min:null,max:6}, tdn:{min:null,max:null}, nem:{min:null,max:null}, neg:{min:null,max:null}, ndf:{min:null,max:null}, adf:{min:null,max:null} }},
    { id:"grower",   label:"Grower",    sub:"6–12 mgg",  active:["cp","me","ca","p"],      reqs:{ cp:{min:15,max:17}, me:{min:2.85,max:3.00}, ca:{min:0.80,max:0.95}, p:{min:0.35,max:0.45}, ee:{min:3,max:7}, cf:{min:null,max:7}, tdn:{min:null,max:null}, nem:{min:null,max:null}, neg:{min:null,max:null}, ndf:{min:null,max:null}, adf:{min:null,max:null} }},
    { id:"prelayer", label:"Pre-Layer", sub:"12–18 mgg", active:["cp","me","ca","p"],      reqs:{ cp:{min:15,max:17}, me:{min:2.80,max:3.00}, ca:{min:2.00,max:2.80}, p:{min:0.35,max:0.45}, ee:{min:3,max:7}, cf:{min:null,max:7}, tdn:{min:null,max:null}, nem:{min:null,max:null}, neg:{min:null,max:null}, ndf:{min:null,max:null}, adf:{min:null,max:null} }},
    { id:"layer",    label:"Layer",     sub:"18+ mgg",   active:["cp","me","ca","p"],      reqs:{ cp:{min:15,max:17}, me:{min:2.75,max:2.90}, ca:{min:3.50,max:4.50}, p:{min:0.30,max:0.40}, ee:{min:3,max:8}, cf:{min:null,max:8}, tdn:{min:null,max:null}, nem:{min:null,max:null}, neg:{min:null,max:null}, ndf:{min:null,max:null}, adf:{min:null,max:null} }},
  ]},
};

function buildNutReqs(animalId, phaseId) {
  var animal = ANIMALS[animalId];
  if (!animal) return NUT_META.map(function(n){ return Object.assign({}, n, { active:false, min:null, max:null }); });
  var phase = null;
  for (var i = 0; i < animal.phases.length; i++) {
    if (animal.phases[i].id === phaseId) { phase = animal.phases[i]; break; }
  }
  if (!phase) phase = animal.phases[0];
  return NUT_META.map(function(nm) {
    var rq = phase.reqs[nm.key] || {};
    return Object.assign({}, nm, {
      active: phase.active.indexOf(nm.key) >= 0,
      min: rq.min != null ? rq.min : null,
      max: rq.max != null ? rq.max : null,
    });
  });
}

// ─────────────────────────────────────────────
// FEED LIBRARY
// ─────────────────────────────────────────────
var INIT_FEEDS = [
  {id:1, name:"Jagung Kuning Giling",  code:"JKG", cat:"energy",   dm:88, cp:8.8,  ee:4.0,  cf:2.2,  ash:1.3,  nfe:83.7, tdn:86.5, me:3.35, nem:1.91, neg:1.25, ca:0.02, p:0.28,  ndf:9.5,  adf:3.5,  price:5250},
  {id:2, name:"Dedak Padi",            code:"DDP", cat:"energy",   dm:89, cp:12.8, ee:14.0, cf:11.0, ash:10.3, nfe:51.9, tdn:68.0, me:2.63, nem:1.40, neg:0.82, ca:0.08, p:1.45,  ndf:38.0, adf:25.0, price:2850},
  {id:3, name:"Pollard",               code:"PLW", cat:"energy",   dm:88, cp:16.0, ee:4.2,  cf:9.0,  ash:5.0,  nfe:65.8, tdn:72.5, me:2.81, nem:1.55, neg:0.95, ca:0.12, p:0.90,  ndf:35.0, adf:14.0, price:3850},
  {id:4, name:"Onggok Kering",         code:"OGK", cat:"energy",   dm:85, cp:2.0,  ee:0.8,  cf:10.0, ash:3.0,  nfe:84.2, tdn:74.0, me:2.87, nem:1.60, neg:1.00, ca:0.20, p:0.05,  ndf:16.0, adf:9.0,  price:2150},
  {id:5, name:"Gaplek",                code:"GPK", cat:"energy",   dm:87, cp:2.5,  ee:0.7,  cf:4.0,  ash:2.8,  nfe:90.0, tdn:76.0, me:2.95, nem:1.66, neg:1.06, ca:0.15, p:0.05,  ndf:12.0, adf:6.0,  price:2400},
  {id:6, name:"Molases Tebu",          code:"MOL", cat:"energy",   dm:75, cp:4.0,  ee:0.1,  cf:0.0,  ash:9.5,  nfe:86.4, tdn:77.0, me:2.99, nem:1.69, neg:1.09, ca:0.74, p:0.08,  ndf:0.0,  adf:0.0,  price:1900},
  {id:7, name:"Ampas Singkong Segar",  code:"ASS", cat:"energy",   dm:22, cp:2.0,  ee:0.4,  cf:10.5, ash:2.5,  nfe:84.6, tdn:70.0, me:2.71, nem:1.47, neg:0.88, ca:0.12, p:0.04,  ndf:0.0,  adf:0.0,  price:450},
  {id:8, name:"Bungkil Kedelai 44",    code:"BKK", cat:"protein",  dm:89, cp:46.0, ee:1.8,  cf:6.5,  ash:6.8,  nfe:38.9, tdn:78.0, me:3.02, nem:1.72, neg:1.12, ca:0.28, p:0.65,  ndf:15.0, adf:9.0,  price:10000},
  {id:9, name:"Bungkil Kelapa Sawit",  code:"BKS", cat:"protein",  dm:91, cp:15.3, ee:8.3,  cf:17.5, ash:4.0,  nfe:54.9, tdn:64.0, me:2.48, nem:1.27, neg:0.70, ca:0.24, p:0.55,  ndf:62.0, adf:37.0, price:3150},
  {id:10,name:"Bungkil Kelapa",        code:"BKL", cat:"protein",  dm:91, cp:21.0, ee:9.0,  cf:13.0, ash:6.5,  nfe:50.5, tdn:71.0, me:2.75, nem:1.50, neg:0.91, ca:0.18, p:0.55,  ndf:50.0, adf:28.0, price:3650},
  {id:11,name:"Ampas Tahu Segar",      code:"ATS", cat:"protein",  dm:11, cp:24.0, ee:9.8,  cf:20.0, ash:4.5,  nfe:41.7, tdn:67.5, me:2.62, nem:1.40, neg:0.82, ca:0.20, p:0.30,  ndf:0.0,  adf:0.0,  price:700},
  {id:12,name:"Ampas Tahu Kering",     code:"ATK", cat:"protein",  dm:86, cp:26.0, ee:9.8,  cf:20.0, ash:5.0,  nfe:39.2, tdn:67.5, me:2.62, nem:1.40, neg:0.82, ca:0.20, p:0.30,  ndf:0.0,  adf:0.0,  price:3000},
  {id:13,name:"Bungkil Kacang Tanah",  code:"BKT", cat:"protein",  dm:91, cp:46.0, ee:6.0,  cf:11.5, ash:6.0,  nfe:30.5, tdn:73.0, me:2.83, nem:1.56, neg:0.97, ca:0.16, p:0.57,  ndf:20.0, adf:12.0, price:7250},
  {id:14,name:"Tepung Ikan 60%",       code:"TIK", cat:"protein",  dm:92, cp:61.5, ee:9.0,  cf:0.8,  ash:20.0, nfe:8.7,  tdn:75.0, me:2.91, nem:1.63, neg:1.03, ca:4.50, p:2.80,  ndf:0.0,  adf:0.0,  price:15000},
  {id:15,name:"Rumput Gajah Segar",    code:"RGS", cat:"roughage", dm:16, cp:9.5,  ee:2.0,  cf:30.0, ash:11.0, nfe:47.5, tdn:55.0, me:2.13, nem:1.02, neg:0.51, ca:0.35, p:0.28,  ndf:65.0, adf:38.0, price:300},
  {id:16,name:"Jerami Padi Kering",    code:"JPK", cat:"roughage", dm:88, cp:3.8,  ee:1.3,  cf:33.0, ash:16.0, nfe:45.9, tdn:43.0, me:1.67, nem:0.72, neg:0.29, ca:0.18, p:0.08,  ndf:70.0, adf:46.0, price:800},
  {id:17,name:"Silase Jagung",         code:"SJG", cat:"roughage", dm:32, cp:7.8,  ee:3.0,  cf:24.0, ash:5.3,  nfe:59.9, tdn:65.0, me:2.52, nem:1.30, neg:0.74, ca:0.25, p:0.22,  ndf:50.0, adf:30.0, price:950},
  {id:18,name:"Hay Rumput",            code:"HAY", cat:"roughage", dm:87, cp:8.8,  ee:2.3,  cf:32.0, ash:9.0,  nfe:47.9, tdn:55.0, me:2.13, nem:1.02, neg:0.51, ca:0.40, p:0.22,  ndf:62.0, adf:36.0, price:2150},
  {id:19,name:"Bagas Tebu Kering",     code:"BTK", cat:"roughage", dm:90, cp:1.8,  ee:0.8,  cf:45.0, ash:3.0,  nfe:49.4, tdn:45.0, me:1.74, nem:0.77, neg:0.33, ca:0.10, p:0.04,  ndf:80.0, adf:52.0, price:500},
  {id:20,name:"Pucuk Tebu Segar",      code:"PTS", cat:"roughage", dm:22, cp:7.5,  ee:1.8,  cf:31.0, ash:8.0,  nfe:51.7, tdn:53.0, me:2.05, nem:0.96, neg:0.46, ca:0.30, p:0.18,  ndf:68.0, adf:42.0, price:200},
  {id:21,name:"Urea Feed Grade",       code:"URE", cat:"additive", dm:99, cp:0,    ee:0,    cf:0,    ash:0,    nfe:0,    tdn:0,    me:0,    nem:0,    neg:0,    ca:0,    p:0,     ndf:0,    adf:0,    price:8000},
  {id:22,name:"CaCO3 Kapur",           code:"CAC", cat:"additive", dm:100,cp:0,    ee:0,    cf:0,    ash:100,  nfe:0,    tdn:0,    me:0,    nem:0,    neg:0,    ca:39,   p:0,     ndf:0,    adf:0,    price:1050},
  {id:23,name:"Dicalcium Phosphate",   code:"DCP", cat:"additive", dm:99, cp:0,    ee:0,    cf:0,    ash:99,   nfe:0,    tdn:0,    me:0,    nem:0,    neg:0,    ca:23,   p:18.5,  ndf:0,    adf:0,    price:6750},
  {id:24,name:"Garam NaCl",            code:"GRM", cat:"additive", dm:99, cp:0,    ee:0,    cf:0,    ash:99,   nfe:0,    tdn:0,    me:0,    nem:0,    neg:0,    ca:0,    p:0,     ndf:0,    adf:0,    price:2000},
  {id:25,name:"Premix Mineral-Vit",    code:"PMX", cat:"additive", dm:99, cp:0,    ee:0,    cf:0,    ash:99,   nfe:0,    tdn:0,    me:0,    nem:0,    neg:0,    ca:0,    p:0,     ndf:0,    adf:0,    price:12500},
  {id:26,name:"Sodium Bicarbonat",     code:"SBC", cat:"additive", dm:99, cp:0,    ee:0,    cf:0,    ash:99,   nfe:0,    tdn:0,    me:0,    nem:0,    neg:0,    ca:0,    p:0,     ndf:0,    adf:0,    price:10500},
];

var DEF_SEL   = new Set([1,2,3,6,8,9,16,22,23,24,25]);
var DEF_BOUNDS = {1:{min:0,max:50},2:{min:0,max:25},3:{min:0,max:30},6:{min:0,max:10},8:{min:0,max:25},9:{min:0,max:20},16:{min:0,max:40},22:{min:0,max:1.5},23:{min:0,max:1},24:{min:0.3,max:0.8},25:{min:0.2,max:0.5}};
var BLANK_ING  = {id:null,name:"",code:"",cat:"energy",dm:88,cp:0,ee:0,cf:0,ash:0,nfe:0,tdn:0,me:0,nem:0,neg:0,ca:0,p:0,ndf:0,adf:0,price:0};

// ─────────────────────────────────────────────
// PDF PRINT
// ─────────────────────────────────────────────
function printPDF(result, nutReqs, animalId, phaseId, dmBase) {
  var animal = ANIMALS[animalId] || { label:"", icon:"", phases:[] };
  var phase = null;
  for (var i = 0; i < animal.phases.length; i++) {
    if (animal.phases[i].id === phaseId) { phase = animal.phases[i]; break; }
  }
  if (!phase && animal.phases.length) phase = animal.phases[0];
  var dateStr = new Date().toLocaleDateString("id-ID", { day:"2-digit", month:"long", year:"numeric" });
  var basisLabel = dmBase ? "Bahan Kering (BK)" : "As-Fed (Segar)";

  var rows = "";
  for (var ii = 0; ii < result.inclusions.length; ii++) {
    var ing = result.inclusions[ii];
    var pct = dmBase ? ing.pctDM : ing.pctAF;
    rows += "<tr><td><b>" + ing.name + "</b></td><td>" + CAT[ing.cat].label + "</td>" +
      "<td style='color:#16a34a;font-weight:700'>" + pct.toFixed(2) + "%</td>" +
      "<td>Rp " + ing.costContrib.toLocaleString("id",{maximumFractionDigits:0}) + "</td></tr>";
  }
  var nutRows = "";
  for (var ni = 0; ni < nutReqs.length; ni++) {
    var nr = nutReqs[ni];
    if (!nr.active || (nr.min == null && nr.max == null)) continue;
    var val = result.nutLvls[nr.key] || 0;
    var low  = nr.min != null && val < nr.min - 0.001;
    var high = nr.max != null && val > nr.max + 0.001;
    var ok   = !low && !high;
    var status = ok ? "✓ OK" : (low ? "↓ LOW" : "↑ HIGH");
    var sc = ok ? "#16a34a" : "#dc2626";
    nutRows += "<tr><td>" + nr.label + "</td><td><b>" + val.toFixed(2) + "</b></td><td>" + nr.unit + "</td>" +
      "<td>" + (nr.min != null ? nr.min : "-") + "</td><td>" + (nr.max != null ? nr.max : "-") + "</td>" +
      "<td style='color:" + sc + ";font-weight:700'>" + status + "</td></tr>";
  }

  var html = "<!DOCTYPE html><html><head><meta charset='utf-8'><title>Smart Feed - Hasil Formulasi</title>" +
    "<style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:Arial,sans-serif;font-size:12px;color:#1a1a1a;padding:28px}" +
    ".hdr{text-align:center;margin-bottom:20px;padding-bottom:14px;border-bottom:3px solid #16a34a}" +
    ".title{font-size:22px;font-weight:800;color:#16a34a}.sub{font-size:11px;color:#666;margin-top:3px}" +
    ".meta{display:flex;gap:16px;margin-bottom:16px;background:#f8fafc;padding:12px;border-radius:8px}" +
    ".ml{font-size:10px;color:#666;font-weight:700;text-transform:uppercase;margin-bottom:2px}.mv{font-size:13px;font-weight:700}" +
    ".cost{background:#16a34a;color:#fff;padding:14px 18px;border-radius:10px;display:flex;justify-content:space-between;margin-bottom:18px}" +
    ".ca{font-size:22px;font-weight:800}.cl{font-size:10px;opacity:.8;margin-bottom:2px}" +
    ".st{font-size:11px;font-weight:700;color:#64748b;letter-spacing:.5px;text-transform:uppercase;margin:14px 0 7px}" +
    "table{width:100%;border-collapse:collapse}th{background:#f1f5f9;padding:7px 10px;text-align:left;font-size:10px;font-weight:700;color:#64748b;text-transform:uppercase}" +
    "td{padding:7px 10px;border-bottom:1px solid #f1f5f9;font-size:12px}" +
    ".ft{text-align:center;font-size:9px;color:#999;margin-top:22px;padding-top:10px;border-top:1px solid #e2e8f0}</style></head><body>" +
    "<div class='hdr'><div class='title'>🌿 Smart Feed by Fajar Afandi</div><div class='sub'>Feed Formulation Report &middot; " + dateStr + "</div></div>" +
    "<div class='meta'><div><div class='ml'>Jenis Ternak</div><div class='mv'>" + animal.icon + " " + animal.label + "</div></div>" +
    "<div><div class='ml'>Fase</div><div class='mv'>" + (phase ? phase.label + " (" + phase.sub + ")" : "-") + "</div></div>" +
    "<div><div class='ml'>Basis</div><div class='mv'>" + basisLabel + "</div></div></div>" +
    "<div class='cost'><div><div class='cl'>Biaya ransum / kg BK</div><div class='ca'>Rp " + result.costDM.toLocaleString("id",{maximumFractionDigits:0}) + "</div></div>" +
    "<div style='text-align:right'><div class='cl'>Per ton BK</div><div style='font-size:16px;font-weight:800'>Rp " + (result.costDM * 1000).toLocaleString("id",{maximumFractionDigits:0}) + "</div></div></div>" +
    "<div class='st'>Komposisi Ransum (" + (dmBase ? "% BK" : "% As-Fed") + ")</div>" +
    "<table><thead><tr><th>Bahan Pakan</th><th>Kategori</th><th>Inklusi</th><th>Biaya Kontribusi</th></tr></thead><tbody>" + rows + "</tbody></table>" +
    "<div class='st'>Status Nutrisi (basis BK)</div>" +
    "<table><thead><tr><th>Nutrien</th><th>Nilai</th><th>Satuan</th><th>Min</th><th>Max</th><th>Status</th></tr></thead><tbody>" + nutRows + "</tbody></table>" +
    "<div class='ft'>Dihasilkan oleh Smart Feed by Fajar Afandi &middot; Referensi: NRC 2007&#8211;2016 &middot; " + dateStr + "</div>" +
    "</body></html>";

  var blob = new Blob([html], { type: "text/html" });
  var url  = URL.createObjectURL(blob);
  var w    = window.open(url, "_blank");
  if (w) { setTimeout(function() { w.print(); URL.revokeObjectURL(url); }, 900); }
}

// ─────────────────────────────────────────────
// SHARED SMALL COMPONENTS
// ─────────────────────────────────────────────
function Toggle({ on, color, onChange }) {
  return (
    <div onClick={onChange}
      style={{ position:"relative", width:42, height:24, borderRadius:12,
        background: on ? color : "#e2e8f0", cursor:"pointer", flexShrink:0,
        transition:"background 0.2s" }}>
      <div style={{ position:"absolute", top:4, left: on ? 22 : 4,
        width:16, height:16, borderRadius:8, background:"#fff",
        boxShadow:"0 1px 4px #0003", transition:"left 0.2s" }} />
    </div>
  );
}

function NutBar({ minV, maxV, val, color, statusColor }) {
  var lo  = minV * 0.8;
  var hi  = maxV * 1.2;
  var rng = hi - lo || 1;
  var toB = function(v) { return Math.max(0, Math.min(100, ((v - lo) / rng) * 100)); };
  return (
    <div style={{ height:6, background:T.bg, borderRadius:3, position:"relative", overflow:"hidden" }}>
      <div style={{ position:"absolute", left: toB(minV) + "%", right: (100 - toB(maxV)) + "%",
        height:"100%", background: color + "33" }} />
      <div style={{ position:"absolute", left: toB(val) + "%", top:0, width:3, height:"100%",
        background: statusColor, borderRadius:2, transform:"translateX(-50%)" }} />
    </div>
  );
}

function CardAccent({ color }) {
  return <div style={{ width:4, height:"100%", minHeight:30, background:color, borderRadius:2, flexShrink:0 }} />;
}

// ─────────────────────────────────────────────
// APP ROOT
// ─────────────────────────────────────────────
export default function App() {
  var [feedLib,   setFeedLib]   = useState(INIT_FEEDS);
  var [tab,       setTab]       = useState("library");
  var [selIds,    setSelIds]    = useState(DEF_SEL);
  var [bounds,    setBounds]    = useState(DEF_BOUNDS);
  var [animalId,  setAnimalId]  = useState("sapi_potong");
  var [phaseId,   setPhaseId]   = useState("grower");
  var [nutReqs,   setNutReqs]   = useState(function(){ return buildNutReqs("sapi_potong","grower"); });
  var [result,    setResult]    = useState(null);
  var [running,   setRunning]   = useState(false);
  var [dmBase,    setDmBase]    = useState(true);
  var [editIng,   setEditIng]   = useState(null);
  var [libCat,    setLibCat]    = useState("all");
  var [libQ,      setLibQ]      = useState("");

  var selIngs = useMemo(function() {
    return feedLib.filter(function(f){ return selIds.has(f.id); });
  }, [feedLib, selIds]);

  function toggleIng(id) {
    setSelIds(function(prev) {
      var s = new Set(prev);
      if (s.has(id)) s.delete(id); else s.add(id);
      return s;
    });
  }
  function updBound(id, type, raw) {
    var v = parseFloat(raw);
    if (isNaN(v)) return;
    v = Math.max(0, v);
    setBounds(function(prev) {
      var cur = prev[id] || { min:0, max:100 };
      return Object.assign({}, prev, { [id]: Object.assign({}, cur, { [type]: v }) });
    });
  }
  function updNut(key, field, val) {
    setNutReqs(function(prev) {
      return prev.map(function(n) {
        if (n.key !== key) return n;
        if (field === "active") return Object.assign({}, n, { active: val });
        return Object.assign({}, n, { [field]: val === "" ? null : parseFloat(val) });
      });
    });
  }
  function changeAnimal(aId) {
    setAnimalId(aId);
    var pid = ANIMALS[aId] && ANIMALS[aId].phases[0] ? ANIMALS[aId].phases[0].id : "";
    setPhaseId(pid);
    setNutReqs(buildNutReqs(aId, pid));
  }
  function changePhase(pid) {
    setPhaseId(pid);
    setNutReqs(buildNutReqs(animalId, pid));
  }
  function saveIng(ing) {
    if (ing._isNew) {
      var newId = Math.max.apply(null, feedLib.map(function(f){ return f.id; })) + 1;
      var obj = Object.assign({}, ing, { id: newId });
      delete obj._isNew;
      setFeedLib(function(prev){ return prev.concat([obj]); });
    } else {
      var obj2 = Object.assign({}, ing);
      delete obj2._isNew;
      setFeedLib(function(prev){ return prev.map(function(f){ return f.id === obj2.id ? obj2 : f; }); });
    }
    setEditIng(null);
  }
  function deleteIng(id) {
    setFeedLib(function(prev){ return prev.filter(function(f){ return f.id !== id; }); });
    setSelIds(function(prev){ var s = new Set(prev); s.delete(id); return s; });
    setEditIng(null);
  }
  function runOpt() {
    setRunning(true);
    setResult(null);
    setTimeout(function() {
      var r = runOptimize(selIngs, bounds, nutReqs);
      setResult(r);
      setRunning(false);
      setTab("hasil");
    }, 60);
  }

  var navItems = [
    { id:"library", icon:"🌾", label:"Library" },
    { id:"formula", icon:"⚗️",  label:"Formula" },
    { id:"target",  icon:"🎯",  label:"Target"  },
    { id:"hasil",   icon:"📊",  label:"Hasil"   },
  ];

  return (
    <div style={{ display:"flex", flexDirection:"column", height:"100vh", width:"100%",
      maxWidth:430, margin:"0 auto", background:T.bg,
      fontFamily:"'Segoe UI',system-ui,-apple-system,sans-serif", overflow:"hidden" }}>

      {/* ── HEADER ── */}
      <div style={{ background:T.white, borderBottom:"1px solid " + T.border,
        padding:"10px 16px", flexShrink:0 }}>
        <div style={{ display:"flex", justifyContent:"space-between", alignItems:"center" }}>
          <div>
            <div style={{ fontSize:18, fontWeight:800, color:T.primary }}>🌿 Smart Feed</div>
            <div style={{ fontSize:10, color:T.muted, marginTop:1 }}>by Fajar Afandi · Feed Optimizer</div>
          </div>
          <div style={{ display:"flex", alignItems:"center", gap:8 }}>
            {/* BK / Segar toggle */}
            <div style={{ display:"flex", background:T.bg, border:"1px solid " + T.border,
              borderRadius:20, padding:2 }}>
              {[["BK",true],["Segar",false]].map(function(item) {
                var lbl = item[0], val = item[1];
                return (
                  <button key={lbl} onClick={function(){ setDmBase(val); }}
                    style={{ padding:"3px 10px", borderRadius:16, border:"none",
                      background: dmBase === val ? T.primary : "transparent",
                      color: dmBase === val ? "#fff" : T.muted,
                      fontSize:10, fontWeight: dmBase === val ? 700 : 400,
                      cursor:"pointer", transition:"all 0.15s" }}>
                    {lbl}
                  </button>
                );
              })}
            </div>
            <div style={{ background:T.primaryLight, color:T.primary,
              fontSize:10, fontWeight:600, padding:"3px 8px", borderRadius:20 }}>
              {selIds.size} bahan
            </div>
          </div>
        </div>
      </div>

      {/* ── CONTENT ── */}
      <div style={{ flex:1, overflow:"hidden", width:"100%" }}>
        {tab === "library" && (
          <LibraryTab feedLib={feedLib} libCat={libCat} setLibCat={setLibCat}
            libQ={libQ} setLibQ={setLibQ} selIds={selIds} toggle={toggleIng}
            onEdit={function(ing){ setEditIng(Object.assign({},ing)); }}
            onAdd={function(){ setEditIng(Object.assign({},BLANK_ING,{_isNew:true})); }} />
        )}
        {tab === "formula" && (
          <FormulaTab feedLib={feedLib} selIds={selIds} bounds={bounds}
            toggle={toggleIng} updBound={updBound} />
        )}
        {tab === "target" && (
          <TargetTab nutReqs={nutReqs} animalId={animalId} phaseId={phaseId}
            changeAnimal={changeAnimal} changePhase={changePhase} updNut={updNut} />
        )}
        {tab === "hasil" && (
          <HasilTab result={result} nutReqs={nutReqs} running={running}
            onRun={runOpt} selCount={selIds.size} dmBase={dmBase}
            animalId={animalId} phaseId={phaseId} />
        )}
      </div>

      {/* ── BOTTOM NAV ── */}
      <div style={{ background:T.white, borderTop:"1px solid " + T.border,
        display:"flex", alignItems:"stretch", height:58, flexShrink:0 }}>
        {navItems.map(function(item) {
          var active = tab === item.id;
          return (
            <button key={item.id} onClick={function(){ setTab(item.id); }}
              style={{ flex:1, background:"none", border:"none", cursor:"pointer",
                display:"flex", flexDirection:"column", alignItems:"center",
                justifyContent:"center", gap:2, padding:"6px 0", position:"relative" }}>
              <span style={{ fontSize:18, lineHeight:1 }}>{item.icon}</span>
              <span style={{ fontSize:10, fontWeight: active ? 700 : 400,
                color: active ? T.primary : T.muted }}>
                {item.label}
              </span>
              {active && (
                <div style={{ position:"absolute", bottom:0, left:"25%", right:"25%",
                  height:3, background:T.primary, borderRadius:"3px 3px 0 0" }} />
              )}
            </button>
          );
        })}
        <button onClick={runOpt} disabled={running || selIds.size < 2}
          style={{ width:42, height:42, alignSelf:"center", borderRadius:21,
            background: selIds.size < 2 ? "#e2e8f0" : T.primary,
            border:"none", color:"#fff", fontSize:16, cursor: selIds.size < 2 ? "not-allowed" : "pointer",
            flexShrink:0, margin:"0 10px", display:"flex", alignItems:"center", justifyContent:"center",
            boxShadow: selIds.size >= 2 ? "0 3px 12px #16a34a44" : "none", transition:"all 0.2s" }}>
          {running ? "⏳" : "▶"}
        </button>
      </div>

      {/* ── EDIT MODAL ── */}
      {editIng && (
        <EditModal ing={editIng} onChange={setEditIng}
          onSave={saveIng} onDelete={deleteIng}
          onClose={function(){ setEditIng(null); }} />
      )}
    </div>
  );
}

// ─────────────────────────────────────────────
// LIBRARY TAB
// ─────────────────────────────────────────────
function LibraryTab({ feedLib, libCat, setLibCat, libQ, setLibQ, selIds, toggle, onEdit, onAdd }) {
  var filtered = feedLib.filter(function(f) {
    var matchCat = libCat === "all" || f.cat === libCat;
    var q = libQ.toLowerCase();
    var matchQ = f.name.toLowerCase().indexOf(q) >= 0 || f.code.toLowerCase().indexOf(q) >= 0;
    return matchCat && matchQ;
  });

  return (
    <div style={{ display:"flex", flexDirection:"column", height:"100%", width:"100%" }}>
      {/* search + add */}
      <div style={{ background:T.white, padding:"10px 14px 8px", flexShrink:0,
        borderBottom:"1px solid " + T.border }}>
        <div style={{ display:"flex", gap:8, marginBottom:8 }}>
          <input value={libQ} onChange={function(e){ setLibQ(e.target.value); }}
            placeholder="🔍  Cari bahan pakan..."
            style={{ flex:1, background:T.bg, border:"1.5px solid " + T.border,
              borderRadius:10, padding:"8px 10px", color:T.text, fontSize:13,
              outline:"none", minWidth:0 }} />
          <button onClick={onAdd}
            style={{ flexShrink:0, background:T.primary, border:"none", borderRadius:10,
              padding:"8px 14px", color:"#fff", fontSize:12, fontWeight:700,
              cursor:"pointer", whiteSpace:"nowrap" }}>
            + Tambah
          </button>
        </div>
        <div style={{ display:"flex", gap:6, overflowX:"auto", scrollbarWidth:"none", paddingBottom:2 }}>
          {[["all","Semua"],["energy","Energi"],["protein","Protein"],["roughage","Hijauan"],["additive","Aditif"]].map(function(item) {
            var k = item[0], l = item[1];
            var active = libCat === k;
            var ac = k === "all" ? T.primary : CAT[k] ? CAT[k].color : T.primary;
            var abg = k === "all" ? T.primaryLight : CAT[k] ? CAT[k].bg : T.primaryLight;
            return (
              <button key={k} onClick={function(){ setLibCat(k); }}
                style={{ flexShrink:0, padding:"4px 12px", borderRadius:20,
                  border: "1.5px solid " + (active ? ac : T.border),
                  background: active ? abg : T.white,
                  color: active ? ac : T.muted,
                  fontSize:11, fontWeight: active ? 600 : 400,
                  cursor:"pointer", whiteSpace:"nowrap" }}>
                {l}
              </button>
            );
          })}
        </div>
      </div>

      <div style={{ flex:1, overflowY:"auto", padding:"8px 12px 70px" }}>
        <div style={{ fontSize:11, color:T.muted, marginBottom:6 }}>{filtered.length} bahan pakan</div>
        {filtered.map(function(ing) {
          var cat = CAT[ing.cat];
          var sel = selIds.has(ing.id);
          return (
            <div key={ing.id}
              style={{ background:T.white, borderRadius:13,
                border: "1.5px solid " + (sel ? cat.color + "66" : T.border),
                marginBottom:7, overflow:"hidden", boxShadow:"0 1px 3px #0001" }}>
              {/* main row */}
              <div style={{ display:"flex", alignItems:"center", padding:"11px 12px",
                gap:10, cursor:"pointer" }} onClick={function(){ toggle(ing.id); }}>
                <CardAccent color={cat.color} />
                <div style={{ flex:1, minWidth:0 }}>
                  <div style={{ fontSize:13, color:T.text, fontWeight:600 }}>{ing.name}</div>
                  <div style={{ display:"flex", gap:5, marginTop:2, flexWrap:"wrap", alignItems:"center" }}>
                    <span style={{ fontSize:10, background:cat.bg, color:cat.color,
                      padding:"1px 6px", borderRadius:7, fontWeight:600 }}>{cat.label}</span>
                    <span style={{ fontSize:10, color:T.muted }}>DM {ing.dm}%</span>
                    <span style={{ fontSize:10, color:T.muted }}>Rp{ing.price.toLocaleString()}/kg</span>
                  </div>
                </div>
                <div style={{ width:24, height:24, borderRadius:7,
                  border: "2px solid " + (sel ? cat.color : T.border),
                  background: sel ? cat.color : T.white,
                  display:"flex", alignItems:"center", justifyContent:"center",
                  flexShrink:0, transition:"all 0.15s" }}>
                  {sel && <span style={{ color:"#fff", fontSize:13, fontWeight:800, lineHeight:1 }}>✓</span>}
                </div>
              </div>
              {/* expanded */}
              {sel && (
                <div style={{ display:"flex", borderTop:"1px solid " + T.border }}>
                  {[["CP",ing.cp,"%"],["TDN",ing.tdn,"%"],["ME",ing.me,"Mc"],["Ca",ing.ca,"%"]].map(function(item, i, arr) {
                    return (
                      <div key={item[0]} style={{ flex:1, textAlign:"center", padding:"6px 2px",
                        borderRight: i < arr.length - 1 ? "1px solid " + T.border : "none" }}>
                        <div style={{ fontSize:10, color:T.muted }}>{item[0]}</div>
                        <div style={{ fontSize:12, fontWeight:700, color:cat.color }}>
                          {(item[1]||0).toFixed(1)}
                        </div>
                      </div>
                    );
                  })}
                  <div style={{ width:1, background:T.border }} />
                  <button onClick={function(){ onEdit(ing); }}
                    style={{ padding:"6px 12px", background:"none", border:"none",
                      color:T.muted, cursor:"pointer", fontSize:14, flexShrink:0 }}>
                    ✏️
                  </button>
                </div>
              )}
            </div>
          );
        })}
        {filtered.length === 0 && (
          <div style={{ textAlign:"center", color:T.muted, padding:40, fontSize:13 }}>
            Tidak ada bahan pakan ditemukan.
          </div>
        )}
      </div>
    </div>
  );
}

// ─────────────────────────────────────────────
// FORMULA TAB
// ─────────────────────────────────────────────
function FormulaTab({ feedLib, selIds, bounds, toggle, updBound }) {
  var sel   = feedLib.filter(function(f){ return selIds.has(f.id); });
  var unsel = feedLib.filter(function(f){ return !selIds.has(f.id); });
  var totalMin = sel.reduce(function(s, f){ return s + (bounds[f.id] ? bounds[f.id].min : 0); }, 0);
  var over = totalMin > 100;

  return (
    <div style={{ display:"flex", flexDirection:"column", height:"100%", width:"100%" }}>
      <div style={{ background:T.white, padding:"10px 14px 8px", flexShrink:0,
        borderBottom:"1px solid " + T.border }}>
        <div style={{ display:"flex", justifyContent:"space-between", alignItems:"center",
          background: over ? "#fef2f2" : T.bg,
          border: "1.5px solid " + (over ? "#fca5a5" : T.border),
          borderRadius:10, padding:"8px 14px" }}>
          <span style={{ fontSize:13, color: over ? T.danger : T.muted }}>Total min inklusi</span>
          <span style={{ fontSize:14, fontWeight:700,
            color: over ? T.danger : totalMin > 80 ? T.warn : T.primary }}>
            {totalMin.toFixed(1)}%
          </span>
        </div>
      </div>

      <div style={{ flex:1, overflowY:"auto", padding:"8px 12px 70px" }}>
        {sel.length === 0 && (
          <div style={{ textAlign:"center", color:T.muted, padding:40, fontSize:13, lineHeight:2 }}>
            Belum ada bahan dipilih.<br/>Buka tab 🌾 Library untuk memilih.
          </div>
        )}

        {sel.map(function(ing) {
          var cat = CAT[ing.cat];
          var b   = bounds[ing.id] || { min:0, max:100 };
          var costPerKgBK = (ing.price / (ing.dm / 100)).toFixed(0);
          return (
            <div key={ing.id}
              style={{ background:T.white, borderRadius:13,
                border:"1.5px solid " + cat.color + "33",
                marginBottom:8, padding:"12px 14px",
                boxShadow:"0 1px 3px #0001", width:"100%" }}>
              {/* header */}
              <div style={{ display:"flex", alignItems:"center", gap:8, marginBottom:10 }}>
                <CardAccent color={cat.color} />
                <div style={{ flex:1, minWidth:0 }}>
                  <div style={{ fontSize:13, fontWeight:600, color:T.text,
                    overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap" }}>
                    {ing.name}
                  </div>
                  <div style={{ fontSize:11, color:T.muted }}>Rp{costPerKgBK}/kg BK</div>
                </div>
                <button onClick={function(){ toggle(ing.id); }}
                  style={{ width:28, height:28, borderRadius:8, background:"#f1f5f9",
                    border:"none", color:T.muted, cursor:"pointer", fontSize:14,
                    display:"flex", alignItems:"center", justifyContent:"center", flexShrink:0 }}>
                  ✕
                </button>
              </div>
              {/* sliders */}
              {[["Min","min",0,b.max],["Max","max",b.min,100]].map(function(row) {
                var lbl=row[0], type=row[1], lo=row[2], hi=row[3];
                return (
                  <div key={type} style={{ display:"flex", alignItems:"center",
                    gap:6, marginBottom:6, width:"100%" }}>
                    <span style={{ width:26, fontSize:11, color:T.muted,
                      fontWeight:600, flexShrink:0, textAlign:"right" }}>{lbl}</span>
                    <input type="range" min={lo} max={hi} step={0.5} value={b[type]}
                      onChange={function(e){ updBound(ing.id, type, e.target.value); }}
                      style={{ flex:1, accentColor:cat.color, cursor:"pointer",
                        minWidth:0, width:0 }} />
                    <input type="number" min={lo} max={hi} step={0.5} value={b[type]}
                      onChange={function(e){ updBound(ing.id, type, e.target.value); }}
                      style={{ width:42, flexShrink:0, background:T.bg,
                        border:"1.5px solid " + cat.color + "55", borderRadius:7,
                        padding:"4px 0", color:cat.color, fontSize:12,
                        fontWeight:700, textAlign:"center", outline:"none" }} />
                    <span style={{ fontSize:11, color:T.muted, flexShrink:0, width:12 }}>%</span>
                  </div>
                );
              })}
              {/* range bar */}
              <div style={{ height:5, background:T.bg, borderRadius:3,
                position:"relative", overflow:"hidden", marginTop:2 }}>
                <div style={{ position:"absolute", left:b.min + "%",
                  right: (100 - b.max) + "%", height:"100%",
                  background:cat.color + "44", borderRadius:3 }} />
              </div>
            </div>
          );
        })}

        {unsel.length > 0 && sel.length > 0 && (
          <div style={{ fontSize:11, color:T.muted, padding:"8px 2px 4px", fontWeight:500 }}>
            TIDAK AKTIF — ketuk untuk aktifkan
          </div>
        )}
        {unsel.map(function(ing) {
          var cat = CAT[ing.cat];
          return (
            <div key={ing.id} onClick={function(){ toggle(ing.id); }}
              style={{ background:T.white, borderRadius:11, border:"1px solid " + T.border,
                marginBottom:5, padding:"9px 12px", cursor:"pointer",
                display:"flex", alignItems:"center", gap:10, opacity:0.55 }}>
              <div style={{ width:3, height:26, background:cat.color,
                borderRadius:2, flexShrink:0 }} />
              <div style={{ flex:1, minWidth:0 }}>
                <div style={{ fontSize:12, color:T.text, fontWeight:500,
                  overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap" }}>
                  {ing.name}
                </div>
                <div style={{ fontSize:10, color:T.muted }}>{ing.code} · {cat.label}</div>
              </div>
              <span style={{ color:T.primary, fontSize:18, fontWeight:700, flexShrink:0 }}>+</span>
            </div>
          );
        })}
      </div>
    </div>
  );
}

// ─────────────────────────────────────────────
// TARGET TAB
// ─────────────────────────────────────────────
function TargetTab({ nutReqs, animalId, phaseId, changeAnimal, changePhase, updNut }) {
  var animalEntries = Object.keys(ANIMALS).map(function(k){ return [k, ANIMALS[k]]; });
  var curAnimal = ANIMALS[animalId];
  var groups = ["Proksimat","Energi","Mineral","Serat"];

  return (
    <div style={{ display:"flex", flexDirection:"column", height:"100%", width:"100%" }}>
      <div style={{ background:T.white, padding:"10px 14px 8px", flexShrink:0,
        borderBottom:"1px solid " + T.border }}>

        <div style={{ fontSize:10, color:T.muted, fontWeight:600,
          letterSpacing:0.5, marginBottom:6 }}>JENIS TERNAK</div>
        <div style={{ display:"grid", gridTemplateColumns:"repeat(4,1fr)", gap:6, marginBottom:10 }}>
          {animalEntries.map(function(entry) {
            var k = entry[0], a = entry[1];
            var active = animalId === k;
            return (
              <button key={k} onClick={function(){ changeAnimal(k); }}
                style={{ padding:"7px 4px", borderRadius:11,
                  border:"1.5px solid " + (active ? T.primary : T.border),
                  background: active ? T.primaryLight : T.white,
                  cursor:"pointer", textAlign:"center", transition:"all 0.15s" }}>
                <div style={{ fontSize:18, lineHeight:1, marginBottom:2 }}>{a.icon}</div>
                <div style={{ fontSize:9, fontWeight: active ? 700 : 400,
                  color: active ? T.primary : T.muted, lineHeight:1.2,
                  wordBreak:"break-word" }}>{a.label}</div>
              </button>
            );
          })}
        </div>

        <div style={{ fontSize:10, color:T.muted, fontWeight:600,
          letterSpacing:0.5, marginBottom:6 }}>FASE / PERIODE</div>
        <div style={{ display:"flex", gap:6, overflowX:"auto",
          scrollbarWidth:"none", paddingBottom:2 }}>
          {curAnimal && curAnimal.phases.map(function(ph) {
            var active = phaseId === ph.id;
            return (
              <button key={ph.id} onClick={function(){ changePhase(ph.id); }}
                style={{ flexShrink:0, padding:"7px 11px", borderRadius:11,
                  border:"1.5px solid " + (active ? T.primary : T.border),
                  background: active ? T.primaryLight : T.white,
                  cursor:"pointer", textAlign:"left", minWidth:80, transition:"all 0.15s" }}>
                <div style={{ fontSize:11, fontWeight: active ? 700 : 500,
                  color: active ? T.primary : T.text, whiteSpace:"nowrap" }}>
                  {ph.label}
                </div>
                <div style={{ fontSize:10, color:T.muted, whiteSpace:"nowrap" }}>{ph.sub}</div>
              </button>
            );
          })}
        </div>
      </div>

      <div style={{ flex:1, overflowY:"auto", padding:"8px 12px 70px" }}>
        <div style={{ fontSize:10, color:T.muted, marginBottom:8 }}>
          Referensi: NRC {curAnimal && curAnimal.icon === "🐓" || curAnimal && curAnimal.icon === "🥚" ? "Poultry 1994" : "Beef/Dairy/SR 2007–2016"}
        </div>

        {groups.map(function(grp) {
          var group = nutReqs.filter(function(n){ return n.group === grp; });
          if (!group.length) return null;
          return (
            <div key={grp} style={{ marginBottom:10 }}>
              <div style={{ fontSize:10, color:T.muted, fontWeight:600,
                letterSpacing:0.7, marginBottom:6 }}>{grp.toUpperCase()}</div>
              {group.map(function(nr) {
                return (
                  <div key={nr.key}
                    style={{ background:T.white, borderRadius:12,
                      border:"1.5px solid " + (nr.active ? nr.color + "33" : T.border),
                      marginBottom:6, padding:"11px 12px",
                      boxShadow:"0 1px 3px #0001" }}>
                    <div style={{ display:"flex", alignItems:"center",
                      gap:8, marginBottom: nr.active ? 9 : 0 }}>
                      <div style={{ width:4, height:30,
                        background: nr.active ? nr.color : "#e2e8f0",
                        borderRadius:2, flexShrink:0 }} />
                      <div style={{ flex:1, minWidth:0 }}>
                        <div style={{ fontSize:12, color: nr.active ? T.text : T.muted,
                          fontWeight:500 }}>{nr.label}</div>
                        <div style={{ fontSize:10, color:T.muted }}>{nr.unit}</div>
                      </div>
                      <Toggle on={nr.active} color={nr.color}
                        onChange={function(){ updNut(nr.key, "active", !nr.active); }} />
                    </div>
                    {nr.active && (
                      <div style={{ display:"flex", gap:8, paddingLeft:12 }}>
                        {[["Min","min"],["Max","max"]].map(function(row) {
                          var lbl=row[0], f=row[1];
                          return (
                            <div key={f} style={{ flex:1, display:"flex", alignItems:"center",
                              gap:5, background:T.bg, borderRadius:8, padding:"5px 8px" }}>
                              <span style={{ fontSize:10, color:T.muted,
                                fontWeight:600, width:24, flexShrink:0 }}>{lbl}</span>
                              <input type="number" step="0.1"
                                value={nr[f] != null ? nr[f] : ""}
                                placeholder="—"
                                onChange={function(e){ updNut(nr.key, f, e.target.value); }}
                                style={{ flex:1, background:"none", border:"none",
                                  color:nr.color, fontSize:13, fontWeight:700,
                                  outline:"none", textAlign:"center", minWidth:0 }} />
                            </div>
                          );
                        })}
                      </div>
                    )}
                  </div>
                );
              })}
            </div>
          );
        })}
      </div>
    </div>
  );
}

// ─────────────────────────────────────────────
// HASIL TAB
// ─────────────────────────────────────────────
function HasilTab({ result, nutReqs, running, onRun, selCount, dmBase, animalId, phaseId }) {
  if (running) {
    return (
      <div style={{ display:"flex", flexDirection:"column", alignItems:"center",
        justifyContent:"center", height:"100%", gap:12 }}>
        <div style={{ fontSize:48 }}>⚙️</div>
        <div style={{ fontSize:15, fontWeight:600, color:T.primary }}>Menjalankan optimasi...</div>
        <div style={{ fontSize:12, color:T.muted }}>Simplex Big-M Method</div>
      </div>
    );
  }

  if (!result) {
    return (
      <div style={{ display:"flex", flexDirection:"column", alignItems:"center",
        justifyContent:"center", height:"100%", padding:32, textAlign:"center", gap:10 }}>
        <div style={{ fontSize:52 }}>📊</div>
        <div style={{ fontSize:17, fontWeight:700, color:T.text }}>Siap Diformulasi</div>
        <div style={{ fontSize:13, color:T.muted, lineHeight:1.9 }}>
          {selCount < 2
            ? "Pilih minimal 2 bahan pakan\ndi tab Formula."
            : selCount + " bahan dipilih.\nTekan ▶ untuk mulai."}
        </div>
        <button onClick={onRun} disabled={selCount < 2}
          style={{ marginTop:8, padding:"13px 32px",
            background: selCount < 2 ? "#e2e8f0" : T.primary,
            border:"none", borderRadius:14,
            color: selCount < 2 ? T.muted : "#fff",
            fontSize:14, fontWeight:700,
            cursor: selCount < 2 ? "not-allowed" : "pointer",
            boxShadow: selCount >= 2 ? "0 4px 16px #16a34a33" : "none" }}>
          ▶ Hitung Formulasi
        </button>
      </div>
    );
  }

  if (result.status !== "optimal") {
    return (
      <div style={{ display:"flex", flexDirection:"column", alignItems:"center",
        justifyContent:"center", height:"100%", padding:32, textAlign:"center", gap:10 }}>
        <div style={{ fontSize:48 }}>⚠️</div>
        <div style={{ fontSize:16, fontWeight:700, color:T.danger }}>Tidak Ada Solusi</div>
        <div style={{ fontSize:13, color:T.muted, lineHeight:1.8, maxWidth:280 }}>
          {result.msg}
        </div>
        <button onClick={onRun}
          style={{ marginTop:8, padding:"12px 24px", background:T.bg,
            border:"1.5px solid " + T.border, borderRadius:12,
            color:T.text, fontSize:13, cursor:"pointer" }}>
          🔄 Coba Lagi
        </button>
      </div>
    );
  }

  var inclusions = result.inclusions;
  var nutLvls    = result.nutLvls;
  var costDM     = result.costDM;

  return (
    <div style={{ display:"flex", flexDirection:"column", height:"100%", width:"100%" }}>
      {/* cost banner */}
      <div style={{ background:T.primary, padding:"14px 16px 10px", flexShrink:0 }}>
        <div style={{ display:"flex", justifyContent:"space-between",
          alignItems:"center", marginBottom:10 }}>
          <div>
            <div style={{ fontSize:10, color:"#a7f3d0", marginBottom:1 }}>Biaya ransum / kg BK</div>
            <div style={{ fontSize:22, fontWeight:800, color:"#fff" }}>
              Rp {costDM.toLocaleString("id",{maximumFractionDigits:0})}
            </div>
          </div>
          <div style={{ textAlign:"right" }}>
            <div style={{ fontSize:10, color:"#a7f3d0", marginBottom:1 }}>Per ton BK</div>
            <div style={{ fontSize:15, fontWeight:700, color:"#d1fae5" }}>
              Rp {(costDM * 1000).toLocaleString("id",{maximumFractionDigits:0})}
            </div>
          </div>
        </div>
        {/* proportion bar */}
        <div style={{ height:8, borderRadius:4, overflow:"hidden",
          display:"flex", background:"rgba(255,255,255,0.15)" }}>
          {inclusions.map(function(ing) {
            return (
              <div key={ing.id} style={{ width:ing.pctDM + "%",
                background: CAT[ing.cat].color, opacity:0.9 }} />
            );
          })}
        </div>
        {/* PDF button */}
        <button onClick={function(){ printPDF(result, nutReqs, animalId, phaseId, dmBase); }}
          style={{ marginTop:10, width:"100%", padding:"8px",
            background:"rgba(255,255,255,0.15)",
            border:"1px solid rgba(255,255,255,0.25)",
            borderRadius:9, color:"#fff", fontSize:12, fontWeight:600,
            cursor:"pointer", display:"flex", alignItems:"center",
            justifyContent:"center", gap:6 }}>
          📄 Download PDF / Print
        </button>
      </div>

      <div style={{ flex:1, overflowY:"auto", padding:"10px 12px 70px" }}>
        {/* basis label */}
        <div style={{ display:"flex", justifyContent:"space-between",
          alignItems:"center", marginBottom:6 }}>
          <div style={{ fontSize:11, color:T.muted, fontWeight:600, letterSpacing:0.5 }}>
            KOMPOSISI RANSUM ({dmBase ? "% BK" : "% As-Fed"})
          </div>
          <div style={{ fontSize:10, color:T.muted, background:T.bg,
            padding:"2px 8px", borderRadius:8, border:"1px solid " + T.border }}>
            Basis: {dmBase ? "BK" : "Segar"}
          </div>
        </div>

        {inclusions.map(function(ing) {
          var cat = CAT[ing.cat];
          var pct = dmBase ? ing.pctDM : ing.pctAF;
          return (
            <div key={ing.id}
              style={{ background:T.white, borderRadius:12,
                border:"1.5px solid " + T.border,
                marginBottom:6, padding:"11px 12px",
                boxShadow:"0 1px 3px #0001" }}>
              <div style={{ display:"flex", alignItems:"center", gap:8, marginBottom:7 }}>
                <CardAccent color={cat.color} />
                <div style={{ flex:1, minWidth:0 }}>
                  <div style={{ fontSize:13, color:T.text, fontWeight:600,
                    overflow:"hidden", textOverflow:"ellipsis", whiteSpace:"nowrap" }}>
                    {ing.name}
                  </div>
                  <div style={{ fontSize:11, color:T.muted }}>
                    Rp{ing.costContrib.toLocaleString("id",{maximumFractionDigits:0})}/kg BK kontribusi
                  </div>
                </div>
                <div style={{ textAlign:"right", flexShrink:0 }}>
                  <div style={{ fontSize:17, fontWeight:800, color:cat.color }}>
                    {pct.toFixed(1)}<span style={{ fontSize:11 }}>%</span>
                  </div>
                  {!dmBase && (
                    <div style={{ fontSize:9, color:T.muted }}>BK: {ing.pctDM.toFixed(1)}%</div>
                  )}
                </div>
              </div>
              <div style={{ height:5, background:T.bg, borderRadius:3, overflow:"hidden" }}>
                <div style={{ width: Math.min(100, pct) + "%", height:"100%",
                  background:cat.color, borderRadius:3 }} />
              </div>
            </div>
          );
        })}

        <div style={{ fontSize:11, color:T.muted, fontWeight:600,
          letterSpacing:0.5, marginBottom:6, marginTop:8 }}>
          STATUS NUTRISI (basis BK)
        </div>

        {nutReqs.filter(function(nr){ return nr.active && (nr.min != null || nr.max != null); })
          .map(function(nr) {
            var val  = nutLvls[nr.key] || 0;
            var low  = nr.min != null && val < nr.min - 0.001;
            var high = nr.max != null && val > nr.max + 0.001;
            var ok   = !low && !high;
            var sc   = ok ? "#16a34a" : T.danger;
            return (
              <div key={nr.key}
                style={{ background:T.white, borderRadius:12,
                  border:"1.5px solid " + (ok ? "#a7f3d0" : "#fca5a5"),
                  marginBottom:6, padding:"11px 12px",
                  boxShadow:"0 1px 3px #0001" }}>
                <div style={{ display:"flex", justifyContent:"space-between",
                  alignItems:"center", marginBottom:7 }}>
                  <div style={{ display:"flex", alignItems:"center", gap:6 }}>
                    <div style={{ width:7, height:7, borderRadius:"50%",
                      background:sc, flexShrink:0 }} />
                    <span style={{ fontSize:12, color:T.text, fontWeight:500 }}>
                      {nr.label}
                    </span>
                  </div>
                  <div style={{ display:"flex", alignItems:"center", gap:5 }}>
                    <span style={{ fontSize:14, fontWeight:700, color:sc }}>
                      {val.toFixed(2)}
                    </span>
                    <span style={{ fontSize:10, color:T.muted }}>{nr.unit}</span>
                    <span style={{ fontSize:10,
                      background: ok ? T.primaryLight : T.dangerLight,
                      color:sc, padding:"1px 6px", borderRadius:8, fontWeight:600 }}>
                      {ok ? "✓ OK" : low ? "↓ LOW" : "↑ HIGH"}
                    </span>
                  </div>
                </div>
                {nr.min != null && nr.max != null && (
                  <NutBar minV={nr.min} maxV={nr.max} val={val}
                    color={nr.color} statusColor={sc} />
                )}
                <div style={{ display:"flex", justifyContent:"space-between",
                  marginTop:4, fontSize:10, color:T.muted }}>
                  <span>{nr.min != null ? "min " + nr.min : ""}</span>
                  <span>{nr.max != null ? "max " + nr.max : ""}</span>
                </div>
              </div>
            );
          })}

        <button onClick={onRun}
          style={{ width:"100%", padding:"13px", background:T.primary, border:"none",
            borderRadius:12, color:"#fff", fontSize:13, fontWeight:700,
            cursor:"pointer", marginTop:6 }}>
          🔄 Hitung Ulang
        </button>
      </div>
    </div>
  );
}

// ─────────────────────────────────────────────
// EDIT MODAL
// ─────────────────────────────────────────────
function EditModal({ ing, onChange, onSave, onDelete, onClose }) {
  var isNew = !!ing._isNew;
  var valid = ing.name.trim().length > 0 && ing.code.trim().length > 0;

  var fields = [
    { key:"dm",    label:"Dry Matter",      unit:"%" },
    { key:"cp",    label:"Protein Kasar",   unit:"% BK" },
    { key:"ee",    label:"Lemak Kasar",     unit:"% BK" },
    { key:"cf",    label:"Serat Kasar",     unit:"% BK" },
    { key:"ash",   label:"Abu",             unit:"% BK" },
    { key:"tdn",   label:"TDN",             unit:"% BK" },
    { key:"me",    label:"ME",              unit:"Mcal/kg" },
    { key:"nem",   label:"NEm",             unit:"Mcal/kg" },
    { key:"neg",   label:"NEg",             unit:"Mcal/kg" },
    { key:"ca",    label:"Kalsium (Ca)",    unit:"% BK" },
    { key:"p",     label:"Fosfor (P)",      unit:"% BK" },
    { key:"ndf",   label:"NDF",             unit:"% BK" },
    { key:"adf",   label:"ADF",             unit:"% BK" },
    { key:"price", label:"Harga Segar",     unit:"Rp/kg" },
  ];

  function upd(k, v) {
    onChange(function(prev){ return Object.assign({}, prev, { [k]: v }); });
  }

  return (
    <div style={{ position:"absolute", inset:0, background:"rgba(0,0,0,0.45)",
      zIndex:300, display:"flex", flexDirection:"column", justifyContent:"flex-end" }}>
      <div style={{ background:T.white, borderRadius:"20px 20px 0 0",
        maxHeight:"88vh", display:"flex", flexDirection:"column" }}>
        <div style={{ display:"flex", justifyContent:"center", padding:"12px 0 4px" }}>
          <div style={{ width:36, height:4, borderRadius:2, background:"#e2e8f0" }} />
        </div>
        <div style={{ display:"flex", justifyContent:"space-between", alignItems:"center",
          padding:"4px 16px 10px", borderBottom:"1px solid " + T.border }}>
          <div style={{ fontSize:15, fontWeight:700, color:T.text }}>
            {isNew ? "➕ Tambah Bahan" : "✏️ Edit Bahan Pakan"}
          </div>
          <button onClick={onClose}
            style={{ background:"#f1f5f9", border:"none", borderRadius:8,
              padding:"5px 10px", color:T.muted, cursor:"pointer", fontSize:12 }}>
            ✕ Tutup
          </button>
        </div>

        <div style={{ flex:1, overflowY:"auto", padding:"12px 16px 28px" }}>
          {/* name, code, category */}
          <div style={{ display:"grid", gridTemplateColumns:"1fr 1fr", gap:8, marginBottom:12 }}>
            <div style={{ gridColumn:"1 / -1" }}>
              <label style={{ fontSize:10, color:T.muted, fontWeight:600 }}>NAMA BAHAN *</label>
              <input value={ing.name}
                onChange={function(e){ upd("name", e.target.value); }}
                placeholder="Jagung Kuning Giling"
                style={{ width:"100%", background:T.bg, border:"1.5px solid " + T.border,
                  borderRadius:9, padding:"8px 10px", fontSize:13, color:T.text,
                  outline:"none", marginTop:3, boxSizing:"border-box" }} />
            </div>
            <div>
              <label style={{ fontSize:10, color:T.muted, fontWeight:600 }}>KODE *</label>
              <input value={ing.code}
                onChange={function(e){ upd("code", e.target.value.toUpperCase().slice(0,6)); }}
                placeholder="JKG"
                style={{ width:"100%", background:T.bg, border:"1.5px solid " + T.border,
                  borderRadius:9, padding:"8px 10px", fontSize:13, color:T.text,
                  outline:"none", marginTop:3, boxSizing:"border-box" }} />
            </div>
            <div>
              <label style={{ fontSize:10, color:T.muted, fontWeight:600 }}>KATEGORI</label>
              <select value={ing.cat}
                onChange={function(e){ upd("cat", e.target.value); }}
                style={{ width:"100%", background:T.bg, border:"1.5px solid " + T.border,
                  borderRadius:9, padding:"8px 10px", fontSize:13, color:T.text,
                  outline:"none", marginTop:3, boxSizing:"border-box" }}>
                {Object.keys(CAT).map(function(k) {
                  return <option key={k} value={k}>{CAT[k].label}</option>;
                })}
              </select>
            </div>
          </div>

          <div style={{ fontSize:10, color:T.muted, fontWeight:600,
            marginBottom:8, letterSpacing:0.4 }}>NILAI NUTRISI (basis BK)</div>
          <div style={{ display:"grid", gridTemplateColumns:"1fr 1fr", gap:7 }}>
            {fields.map(function(f) {
              return (
                <div key={f.key}>
                  <label style={{ fontSize:10, color:T.muted }}>{f.label}</label>
                  <div style={{ display:"flex", alignItems:"center", background:T.bg,
                    border:"1px solid " + T.border, borderRadius:8, marginTop:3, overflow:"hidden" }}>
                    <input type="number" step="0.01" value={ing[f.key] != null ? ing[f.key] : 0}
                      onChange={function(e){ upd(f.key, parseFloat(e.target.value) || 0); }}
                      style={{ flex:1, background:"none", border:"none",
                        padding:"6px 8px", fontSize:12, color:T.text, outline:"none", minWidth:0 }} />
                    <span style={{ fontSize:9, color:T.muted, padding:"0 6px",
                      flexShrink:0, whiteSpace:"nowrap" }}>{f.unit}</span>
                  </div>
                </div>
              );
            })}
          </div>

          <div style={{ display:"flex", gap:8, marginTop:18 }}>
            {!isNew && (
              <button onClick={function(){ onDelete(ing.id); }}
                style={{ padding:"11px 14px", background:T.dangerLight, border:"none",
                  borderRadius:11, color:T.danger, fontSize:12, fontWeight:600,
                  cursor:"pointer", whiteSpace:"nowrap" }}>
                🗑 Hapus
              </button>
            )}
            <button onClick={function(){ if (valid) onSave(ing); }} disabled={!valid}
              style={{ flex:1, padding:"12px", border:"none", borderRadius:11,
                background: valid ? T.primary : "#e2e8f0",
                color: valid ? "#fff" : T.muted,
                fontSize:13, fontWeight:700,
                cursor: valid ? "pointer" : "not-allowed" }}>
              {isNew ? "➕ Tambahkan" : "💾 Simpan"}
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}
