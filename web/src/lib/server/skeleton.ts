// Skeleton view for the LeanNets NETWORK mode — a Node port of
// build_skeleton_view, result-compatible with the original Python
// implementation (now living in MathNetwork/Astrolabe's backend). Atoms become
// nodes, |ref|>=2 entries become directed edges; size/colour/cluster are
// computed (per source group) via the analysis library. All UI modes are
// supported — nothing is silently degraded.
import type { Store } from './store'
import { getSortFill } from '../sortColors'
import {
  perSource, degreeMetric, centralityMetric, dagMetric, stageMetric,
  communityMetric, clusterByAttr, curvatureBuckets, spectralMetric,
} from './analysis'

interface GNode { id: string; sort: string; title: string; source: string; state: string }
interface GEdge { source: string; target: string; hash: string; sort: string; hyper: boolean }
type NumMap = Record<string, number>

function parseRecord(raw: string): Record<string, any> | null {
  try { const p = JSON.parse(raw); return p && typeof p === 'object' && !Array.isArray(p) ? p : null }
  catch { return null }
}

/** Output graph (for rendering): atoms → nodes, |ref|>=2 → edges. */
function buildGraph(entries: Store): { nodes: Map<string, GNode>; edges: GEdge[] } {
  const nodes = new Map<string, GNode>()
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && e.ref[0] === h) {
      const r = parseRecord(e.record) || {}
      nodes.set(h, { id: h, sort: r.sort ?? '', title: r.title ?? '', source: r.source ?? '', state: r.state ?? '' })
    }
  }
  const edges: GEdge[] = []
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length >= 2) {
      const src = e.ref[0]
      const sort = parseRecord(e.record)?.sort ?? ''
      const hyper = e.ref.length > 2
      for (const tgt of e.ref.slice(1)) {
        if (nodes.has(src) && nodes.has(tgt)) edges.push({ source: src, target: tgt, hash: h, sort, hyper })
      }
    }
  }
  return { nodes, edges }
}

function filterBySource(entries: Store, source: string): Store {
  const keep = new Set<string>()
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && e.ref[0] === h && parseRecord(e.record)?.source === source) keep.add(h)
  }
  const out: Store = {}
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && keep.has(h)) out[h] = e
    else if (e.ref.length === 2 && keep.has(e.ref[0]) && keep.has(e.ref[1])) out[h] = e
  }
  return out
}

// ── colour helpers ──
// Sort colours come from the shared client palette (lib/sortColors, pure/
// isomorphic) so NETWORK nodes and read-view cards always agree; hslToHex
// below only serves the gradient/palette metric colourings.

function hslToHex(h: number, s: number, l: number): string {
  const sf = s / 100, lf = l / 100
  const f = (n: number) => {
    const k = (n + h / 30) % 12
    const a = sf * Math.min(lf, 1 - lf)
    return Math.round((lf - a * Math.max(-1, Math.min(k - 3, 9 - k, 1))) * 255).toString(16).padStart(2, '0')
  }
  return `#${f(0)}${f(8)}${f(4)}`
}

function blendHex(a: string, b: string): string {
  const p = (x: string, i: number) => parseInt(x.slice(i, i + 2), 16)
  const m = (x: number, y: number) => Math.floor((x + y) / 2).toString(16).padStart(2, '0')
  return `#${m(p(a, 1), p(b, 1))}${m(p(a, 3), p(b, 3))}${m(p(a, 5), p(b, 5))}`
}

function normalize(values: NumMap, lo: number, hi: number): NumMap {
  const vs = Object.values(values)
  if (!vs.length) return {}
  const min = Math.min(...vs), max = Math.max(...vs), mid = (lo + hi) / 2
  const out: NumMap = {}
  for (const [k, v] of Object.entries(values)) out[k] = max === min ? mid : lo + ((v - min) / (max - min)) * (hi - lo)
  return out
}

function gradient(values: NumMap): Record<string, string> {
  const vs = Object.values(values)
  if (!vs.length) return {}
  const min = Math.min(...vs), max = Math.max(...vs)
  const out: Record<string, string> = {}
  for (const [k, v] of Object.entries(values)) {
    const t = max === min ? 0.5 : (v - min) / (max - min)
    out[k] = hslToHex(Math.round(220 * (1 - t)), 70, 50)
  }
  return out
}

function palette(comm: NumMap, hueStep: number, sat: number, lit: number): Record<string, string> {
  const ids = [...new Set(Object.values(comm))].sort((a, b) => a - b)
  const colorById = new Map(ids.map((cid, i) => [cid, hslToHex((i * hueStep) % 360, sat, lit)]))
  const out: Record<string, string> = {}
  for (const [n, cid] of Object.entries(comm)) out[n] = colorById.get(cid) ?? '#888888'
  return out
}

export function buildSkeletonView(
  entries: Store,
  opts: { source?: string; size?: string; color?: string; cluster?: string },
) {
  const ents = opts.source && opts.source !== 'all' ? filterBySource(entries, opts.source) : entries
  const { nodes, edges } = buildGraph(ents)
  if (nodes.size === 0) return { nodes: [], edges: [] }

  // ── size → radii ──
  const size = opts.size ?? 'uniform'
  let radii: NumMap = {}
  if (['degree', 'in-degree', 'out-degree'].includes(size)) {
    const mode = size === 'degree' ? 'total' : size === 'in-degree' ? 'in' : 'out'
    radii = normalize(perSource(ents, (g) => degreeMetric(g, mode as 'total' | 'in' | 'out')), 4, 16)
  } else if (['pagerank', 'betweenness', 'katz', 'hub', 'authority'].includes(size)) {
    radii = normalize(perSource(ents, (g) => centralityMetric(g, size)), 4, 16)
  } else if (['depth', 'reachability'].includes(size)) {
    radii = normalize(perSource(ents, (g) => dagMetric(g, size as 'depth' | 'reachability')), 4, 16)
  } else {
    for (const id of nodes.keys()) radii[id] = 9.0 // uniform
  }

  // ── colour ──
  const color = opts.color ?? 'sort'
  let colors: Record<string, string> = {}
  if (color === 'sort') {
    for (const [id, n] of nodes) colors[id] = getSortFill(n.sort)
  } else if (color === 'community') {
    colors = palette(perSource(ents, communityMetric, true), 137, 65, 55)
  } else if (color === 'spectral') {
    colors = palette(perSource(ents, communityMetric, true), 97, 70, 50)
  } else if (color === 'layer') {
    colors = gradient(perSource(ents, (g) => dagMetric(g, 'depth')))
  } else if (color === 'depth') {
    colors = gradient(perSource(ents, (g) => dagMetric(g, 'depth')))
  } else if (color === 'pagerank') {
    colors = gradient(perSource(ents, (g) => centralityMetric(g, 'pagerank')))
  } else if (color === 'curvature') {
    colors = gradient(perSource(ents, (g) => centralityMetric(g, 'betweenness')))
  } else {
    for (const id of nodes.keys()) colors[id] = '#888888'
  }
  // any node missing a colour (e.g. isolated, no metric) falls back to sort
  for (const [id, n] of nodes) if (!colors[id]) colors[id] = getSortFill(n.sort)

  // ── cluster ──
  const cluster = opts.cluster ?? 'none'
  let clusters: NumMap = {}
  if (cluster === 'louvain') clusters = perSource(ents, communityMetric, true)
  else if (cluster === 'sort') clusters = perSource(ents, (g) => clusterByAttr(g, 'sort'), true)
  else if (cluster === 'source') clusters = perSource(ents, (g) => clusterByAttr(g, 'source'), true)
  else if (cluster === 'stage') clusters = perSource(ents, stageMetric, true)
  else if (cluster === 'spectral') clusters = perSource(ents, spectralMetric, true)
  else if (cluster === 'curvature') clusters = perSource(ents, curvatureBuckets, true)

  const outNodes = [...nodes.values()].map((n) => ({
    id: n.id,
    sort: n.sort,
    title: n.title,
    radius: radii[n.id] ?? 6.0,
    color: colors[n.id] ?? '#888888',
    ...(n.state ? { state: n.state } : {}),
    ...(n.id in clusters ? { cluster: clusters[n.id] } : {}),
  }))

  const outEdges = edges.map((e) => {
    const su = nodes.get(e.source)?.source ?? ''
    const sv = nodes.get(e.target)?.source ?? ''
    const cross = !!(su && sv && su !== sv)
    const col = cross ? '#333333' : blendHex(colors[e.source] ?? '#888888', colors[e.target] ?? '#888888')
    const dashed = e.sort.endsWith(', proof)') || e.hyper
    return {
      source: e.source, target: e.target, sort: e.sort, hash: e.hash,
      color: col, hyper: e.hyper, cross, ...(dashed ? { dashed: true } : {}),
    }
  })

  return { nodes: outNodes, edges: outEdges }
}
