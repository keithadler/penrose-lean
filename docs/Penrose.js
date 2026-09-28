import * as React from 'react';
const e = React.createElement;

// Every number here is computed by Lean (Penrose.widgetProps), by evaluating the diagram drawn next to it.
const BG = '#0b0d12', PANEL = '#12151c', GRID = '#262c3a', INK = '#e8eaf0', DIM = '#8a90a2';
const WIRE = '#c9d1e6', BOX = '#5fd4b0', BOX2 = '#f2b35e', ACCENT = '#7fb2ff';
const MONO = "ui-monospace, 'SF Mono', Menlo, Consolas, monospace";
const SANS = "-apple-system, 'Segoe UI', Inter, Helvetica, Arial, sans-serif";
const SERIF = "'CMU Serif', 'Latin Modern Roman', 'STIX Two Text', Georgia, serif";

const rat = ([p, q]) => p / q;
const fmt = v => { const r = Math.round(v * 10000) / 10000; return Object.is(r, -0) ? '0' : String(r); };

const W = 210, H = 170;
const wire = (d, k) => e('path', { key: k, d, fill: 'none', stroke: WIRE, strokeWidth: 2.2, strokeLinecap: 'round' });
function Box({ x, y, label, color, flip }) {
  return e('g', null,
    e('rect', { x: x - 17, y: y - 14, width: 34, height: 28, rx: 5, fill: (color || BOX) + '26', stroke: color || BOX, strokeWidth: 2 }),
    e('text', { x, y: y + 6, textAnchor: 'middle', fontFamily: SERIF, fontStyle: 'italic', fontSize: 17, fill: INK,
      transform: flip ? `rotate(180 ${x} ${y})` : undefined }, label));
}
const svg = (...kids) => e('svg', { width: W, height: H, viewBox: `0 0 ${W} ${H}`, style: { display: 'block', flex: '0 0 auto' } }, ...kids);
const eq = (x, y, s) => e('text', { x, y, textAnchor: 'middle', fontFamily: SERIF, fontSize: 22, fill: DIM }, s);
const idx = (x, y, s) => e('text', { x, y, fontFamily: SERIF, fontStyle: 'italic', fontSize: 14, fill: DIM }, s);

// ---------- the pictures ----------

const pictures = {
  box: () => svg(wire('M105 12 V 72', 1), wire('M105 100 V 158', 2), e(Box, { x: 105, y: 86, label: 'M' }),
    idx(116, 32, 'i'), idx(116, 150, 'j')),
  square: () => svg(wire('M105 8 V 38', 1), wire('M105 66 V 104', 2), wire('M105 132 V 162', 3),
    e(Box, { x: 105, y: 52, label: 'M' }), e(Box, { x: 105, y: 118, label: 'M' }), idx(116, 90, 'k')),
  zigzag: () => svg(wire('M34 10 V 90 C 34 130, 80 130, 80 90 C 80 50, 126 50, 126 90 V 160', 1),
    eq(156, 92, '='), wire('M186 10 V 160', 2)),
  bend: () => svg(wire('M22 160 V 70 C 22 32, 70 24, 70 56 V 72', 1), e(Box, { x: 70, y: 86, label: 'M', flip: true }),
    wire('M70 100 V 116 C 70 148, 118 140, 118 100 V 10', 2), eq(146, 92, '='),
    e(Box, { x: 182, y: 86, label: 'Mᵀ' }), wire('M182 10 V 72', 3), wire('M182 100 V 160', 4)),
  trace: () => svg(wire('M80 72 C 80 18, 150 18, 150 72 V 100 C 150 154, 80 154, 80 100', 1), e(Box, { x: 80, y: 86, label: 'M' })),
  dim: () => svg(e('circle', { cx: 105, cy: 85, r: 48, fill: 'none', stroke: WIRE, strokeWidth: 2.2 })),
  slide: () => svg(
    wire('M52 48 C 52 10, 92 10, 92 48 V 122 C 92 160, 52 160, 52 122', 1), e(Box, { x: 52, y: 62, label: 'A' }),
    e(Box, { x: 52, y: 108, label: 'B', color: BOX2 }), eq(120, 92, '='),
    wire('M150 48 C 150 10, 190 10, 190 48 V 122 C 190 160, 150 160, 150 122', 2), e(Box, { x: 150, y: 62, label: 'B', color: BOX2 }),
    e(Box, { x: 150, y: 108, label: 'A' })),
};

function Ring({ k }) {
  const cx = 105, cy = 85, r = 55;
  const kids = [e('circle', { key: 'c', cx, cy, r, fill: 'none', stroke: WIRE, strokeWidth: 2.2 })];
  for (let t = 0; t < k; t++) {
    const a = -Math.PI / 2 + (2 * Math.PI * t) / k;
    kids.push(e('g', { key: t }, e(Box, { x: cx + r * Math.cos(a), y: cy + r * Math.sin(a), label: 'M' })));
  }
  return svg(...kids);
}

function Matrix({ m, hi }) {
  return e('table', { style: { borderCollapse: 'collapse', fontFamily: MONO, fontSize: 12.5, borderLeft: `1.5px solid ${DIM}`, borderRight: `1.5px solid ${DIM}` } },
    e('tbody', null, m.map((row, i) => e('tr', { key: i }, row.map((v, j) => e('td', { key: j, style: {
      padding: '2px 7px', textAlign: 'right', color: hi && hi(i, j) ? ACCENT : INK } }, fmt(rat(v))))))));
}

function Card({ title, theorem, pic, children }) {
  return e('div', { style: { background: PANEL, border: `1px solid ${GRID}`, borderRadius: 10, padding: '10px 12px', display: 'flex', flexDirection: 'column', gap: 4 } },
    e('div', { style: { fontSize: 14, fontWeight: 600, color: INK } }, title),
    e('div', { style: { display: 'flex', alignItems: 'center', gap: 12, minHeight: H } }, pic,
      e('div', { style: { display: 'flex', flexDirection: 'column', gap: 8, alignItems: 'flex-start' } }, children)),
    e('div', { style: { fontFamily: MONO, fontSize: 11.5, color: BOX } }, 'theorem ' + theorem));
}

const big = s => e('div', { style: { fontFamily: SERIF, fontSize: 28, color: INK, whiteSpace: 'nowrap' } }, s);
const note = s => e('div', { style: { fontSize: 11.5, color: DIM, maxWidth: 160 } }, s);
const sup = n => String(n).split('').map(c => '⁰¹²³⁴⁵⁶⁷⁸⁹'[+c]).join('');

export default function PenroseWidget(p) {
  const [k, setK] = React.useState(3);
  return e('div', { style: { background: BG, color: INK, borderRadius: 12, padding: 18, border: '1px solid #232838', fontFamily: SANS } },
    e('div', { style: { display: 'flex', justifyContent: 'space-between', flexWrap: 'wrap', gap: 8, borderBottom: `1px solid ${GRID}`, paddingBottom: 8 } },
      e('div', { style: { fontSize: 20, fontWeight: 700, letterSpacing: 1 } }, 'PENROSE DIAGRAMS, CHECKED BY LEAN'),
      e('div', { style: { fontSize: 12, color: DIM, alignSelf: 'flex-end' } }, 'core Lean · no Mathlib · proved for every n and every matrix')),
    e('div', { style: { fontSize: 13, color: DIM, margin: '10px 0 14px' } },
      'A box is a matrix, a wire is an index, and joining wires sums over the index they share. Each number is Lean evaluating the diagram beside it for M, the matrix from the post.'),
    e('div', { style: { display: 'grid', gridTemplateColumns: 'repeat(auto-fill, minmax(400px, 1fr))', gap: 12 } },
      e(Card, { title: 'A box is a matrix', theorem: 'eval (box M) = M', pic: pictures.box() },
        e(Matrix, { m: p.box }), note('The wire in carries the row index, the wire out the column.')),
      e(Card, { title: 'Joining two boxes is the product', theorem: 'seq_box', pic: pictures.square() },
        e(Matrix, { m: p.square }), note('M², summed over the joined wire k.')),
      e(Card, { title: 'A zig-zag pulls straight', theorem: 'snake', pic: pictures.zigzag() },
        e(Matrix, { m: p.zigzag, hi: (i, j) => i === j }), note('The identity matrix: a plain wire.')),
      e(Card, { title: 'Bent round, a box is its transpose', theorem: 'bend_transpose', pic: pictures.bend() },
        e(Matrix, { m: p.bend, hi: (i, j) => (i === 0 && j === 2) || (i === 2 && j === 0) }), note('1.8 has crossed the diagonal.')),
      e(Card, { title: 'A loop is the trace', theorem: 'loop_trace', pic: pictures.trace() },
        big('tr M = ' + fmt(rat(p.trace))), note('No loose wires, so the diagram is a number.')),
      e(Card, { title: 'A bare loop is the dimension', theorem: 'loop_dim', pic: pictures.dim() },
        big('○ = ' + fmt(rat(p.dim))), note('The trace of the identity, for n = 3.')),
      e(Card, { title: 'Boxes slide round a loop', theorem: 'trace_cyclic', pic: pictures.slide() },
        big(fmt(rat(p.slideAB)) + ' = ' + fmt(rat(p.slideBA))), note('tr(AB) = tr(BA), here with A = M and B = Mᵀ.')),
      e(Card, { title: 'A ring of k boxes is tr(Mᵏ)', theorem: 'ring_trace_pow', pic: e(Ring, { k }) },
        big('tr M' + (k === 1 ? '' : sup(k)) + ' = ' + fmt(rat(p.rings[k]))),
        e('input', { type: 'range', min: 0, max: 6, value: k, onChange: ev => setK(+ev.target.value), style: { width: 150, accentColor: BOX } }),
        note('The closed k-step walks in M\'s graph, weighed and summed.'))));
}
