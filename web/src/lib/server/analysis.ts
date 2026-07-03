// Graph analysis for the LeanNets skeleton — a Node port, result-compatible
// with the original Python implementation (now living in MathNetwork/
// Astrolabe's backend). Heavy algorithms use graphology (pagerank, betweenness,
// hits, louvain) and ml-matrix/ml-kmeans (spectral); the rest are direct ports.
// Metrics run independently per source group, mirroring the original.
import Graph from 'graphology'
import { pagerank, betweenness, hits } from 'graphology-metrics/centrality'
import louvain from 'graphology-communities-louvain'
import { Matrix, EigenvalueDecomposition } from 'ml-matrix'
import { kmeans } from 'ml-kmeans'
import type { Store } from './store'

type NumMap = Record<string, number>

function parseRecord(raw: string): Record<string, any> | null {
  try { const p = JSON.parse(raw); return p && typeof p === 'object' && !Array.isArray(p) ? p : null }
  catch { return null }
}

/** Directed skeleton graph: atoms → nodes (with attrs), |ref|>=2 → edges. */
export function toGraph(entries: Store): Graph {
  const g = new Graph({ type: 'directed', allowSelfLoops: true })
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && e.ref[0] === h) {
      const r = parseRecord(e.record) || {}
      g.addNode(h, { sort: r.sort ?? '', title: r.title ?? '', source: r.source ?? '', state: r.state ?? '' })
    }
  }
  for (const e of Object.values(entries)) {
    if (e.ref.length >= 2) {
      const src = e.ref[0]
      for (const tgt of e.ref.slice(1)) {
        if (g.hasNode(src) && g.hasNode(tgt) && !g.hasDirectedEdge(src, tgt)) g.addDirectedEdge(src, tgt)
      }
    }
  }
  return g
}

function splitBySource(entries: Store): Store[] {
  const atomSrc: Record<string, string> = {}
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && e.ref[0] === h) atomSrc[h] = parseRecord(e.record)?.source ?? ''
  }
  const sources = [...new Set(Object.values(atomSrc))].filter(Boolean).sort()
  return sources.map((src) => {
    const keep = new Set(Object.keys(atomSrc).filter((h) => atomSrc[h] === src))
    const group: Store = {}
    for (const [h, e] of Object.entries(entries)) {
      if (e.ref.length === 1 && keep.has(h)) group[h] = e
      else if (e.ref.length === 2 && keep.has(e.ref[0]) && keep.has(e.ref[1])) group[h] = e
    }
    return group
  })
}

/** Run a graph metric independently per source group and merge (parity with the original). */
export function perSource(entries: Store, fn: (g: Graph) => NumMap, offsetIds = false): NumMap {
  const merged: NumMap = {}
  let offset = 0
  for (const group of splitBySource(entries)) {
    let res = fn(toGraph(group))
    if (offsetIds && Object.keys(res).length) {
      const maxId = Math.max(...Object.values(res))
      res = Object.fromEntries(Object.entries(res).map(([k, v]) => [k, v + offset]))
      offset += maxId + 1
    }
    Object.assign(merged, res)
  }
  return merged
}

// ── metric primitives (on a graphology graph) ──

export function degreeMetric(g: Graph, mode: 'total' | 'in' | 'out'): NumMap {
  const r: NumMap = {}
  g.forEachNode((n) => {
    r[n] = mode === 'in' ? g.inDegree(n) : mode === 'out' ? g.outDegree(n) : g.degree(n)
  })
  return r
}

export function centralityMetric(g: Graph, metric: string): NumMap {
  if (g.order === 0) return {}
  if (metric === 'pagerank') return pagerank(g)
  if (metric === 'betweenness') return betweenness(g)
  if (metric === 'katz') return katz(g, 0.1, 1.0)
  if (metric === 'hub' || metric === 'authority') {
    const { hubs, authorities } = hits(g, { maxIterations: 200 })
    return metric === 'hub' ? hubs : authorities
  }
  throw new Error(`Unknown centrality metric: ${metric}`)
}

/** Katz centrality by power iteration (alpha=0.1, beta=1.0), L2-normalised. */
function katz(g: Graph, alpha: number, beta: number): NumMap {
  const nodes = g.nodes()
  let x: NumMap = Object.fromEntries(nodes.map((n) => [n, 0]))
  for (let it = 0; it < 1000; it++) {
    const xlast = x
    x = Object.fromEntries(nodes.map((n) => [n, beta]))
    g.forEachDirectedEdge((_e, _a, s, t) => { x[t] += alpha * xlast[s] })
    const norm = Math.hypot(...Object.values(x)) || 1
    let err = 0
    for (const n of nodes) { const v = x[n] / norm; err += Math.abs(v - xlast[n]); x[n] = v }
    if (err < nodes.length * 1e-6) break
  }
  return x
}

// ── DAG metrics: depth (longest path) and reachability (descendant count) ──

function toDag(g: Graph): Graph {
  const dag = g.copy()
  const color: Record<string, number> = {}
  const back: Array<[string, string]> = []
  const dfs = (u: string) => {
    color[u] = 1
    dag.forEachOutNeighbor(u, (v) => {
      if (color[v] === 1) back.push([u, v])
      else if (!color[v]) dfs(v)
    })
    color[u] = 2
  }
  dag.forEachNode((n) => { if (!color[n]) dfs(n) })
  for (const [u, v] of back) if (dag.hasDirectedEdge(u, v)) dag.dropDirectedEdge(u, v)
  return dag
}

function topoOrder(dag: Graph): string[] {
  const indeg: NumMap = {}
  dag.forEachNode((n) => { indeg[n] = dag.inDegree(n) })
  const queue = dag.nodes().filter((n) => indeg[n] === 0)
  const order: string[] = []
  while (queue.length) {
    const n = queue.shift()!
    order.push(n)
    dag.forEachOutNeighbor(n, (m) => { if (--indeg[m] === 0) queue.push(m) })
  }
  return order
}

export function dagMetric(g: Graph, metric: 'depth' | 'reachability'): NumMap {
  if (g.order === 0) return {}
  const dag = toDag(g)
  if (metric === 'depth') {
    const depth: NumMap = {}
    for (const n of topoOrder(dag)) {
      const preds: number[] = []
      dag.forEachInNeighbor(n, (p) => preds.push(depth[p] ?? 0))
      depth[n] = preds.length ? Math.max(...preds) + 1 : 0
    }
    return depth
  }
  // reachability: number of descendants
  const reach: NumMap = {}
  dag.forEachNode((start) => {
    const seen = new Set<string>()
    const stack = [start]
    while (stack.length) {
      const u = stack.pop()!
      dag.forEachOutNeighbor(u, (v) => { if (!seen.has(v)) { seen.add(v); stack.push(v) } })
    }
    reach[start] = seen.size
  })
  return reach
}

/** Stage = longest path from roots on the raw graph (no cycle removal). */
export function stageMetric(g: Graph): NumMap {
  const order = topoOrder(g)
  const depth: NumMap = {}
  if (order.length !== g.order) { g.forEachNode((n) => { depth[n] = 0 }); return depth } // cyclic
  for (const n of order) {
    const preds: number[] = []
    g.forEachInNeighbor(n, (p) => preds.push(depth[p] ?? 0))
    depth[n] = preds.length ? Math.max(...preds) + 1 : 0
  }
  return depth
}

// ── community / clustering ──

export function communityMetric(g: Graph): NumMap {
  if (g.order === 0) return {}
  if (g.order === 1) return { [g.nodes()[0]]: 0 }
  return louvain(g) // {node: community id}
}

export function clusterByAttr(g: Graph, field: 'sort' | 'source'): NumMap {
  const ids: Record<string, number> = {}
  const r: NumMap = {}
  g.forEachNode((n, attr) => {
    const v = (attr as any)[field] ?? ''
    if (!(v in ids)) ids[v] = Object.keys(ids).length
    r[n] = ids[v]
  })
  return r
}

/** Cluster by betweenness quartile buckets (curvature proxy). */
export function curvatureBuckets(g: Graph): NumMap {
  const bc = betweenness(g)
  const vals = Object.values(bc).sort((a, b) => a - b)
  if (!vals.length) return {}
  const n = vals.length
  const th = [vals[Math.floor(n / 4)], vals[Math.floor(n / 2)], vals[Math.floor((3 * n) / 4)]]
  const r: NumMap = {}
  for (const [node, v] of Object.entries(bc)) r[node] = v <= th[0] ? 0 : v <= th[1] ? 1 : v <= th[2] ? 2 : 3
  return r
}

/** Spectral clustering: smallest-k Laplacian eigenvectors + k-means. */
export function spectralMetric(g: Graph): NumMap {
  const nodes = g.nodes()
  const n = nodes.length
  if (n <= 2) return Object.fromEntries(nodes.map((nd) => [nd, 0]))

  const idx = Object.fromEntries(nodes.map((nd, i) => [nd, i]))
  // Undirected Laplacian L = D - A
  const L = Matrix.zeros(n, n)
  const deg = new Array(n).fill(0)
  g.forEachEdge((_e, _a, s, t) => {
    const i = idx[s], j = idx[t]
    if (i === j) return
    if (L.get(i, j) === 0) { L.set(i, j, -1); L.set(j, i, -1); deg[i]++; deg[j]++ }
  })
  for (let i = 0; i < n; i++) L.set(i, i, deg[i])

  const evd = new EigenvalueDecomposition(L)
  const evals = evd.realEigenvalues
  const V = evd.eigenvectorMatrix
  const order = evals.map((v, i) => [v, i] as [number, number]).sort((a, b) => a[0] - b[0]).map((p) => p[1])

  // auto-k from the largest eigengap among the smallest ~10 eigenvalues
  const m = Math.min(10, n - 1)
  const small = order.slice(0, m).map((i) => evals[i])
  let k = 1
  let best = -Infinity
  for (let i = 0; i < small.length - 1; i++) { const gap = small[i + 1] - small[i]; if (gap > best) { best = gap; k = i + 1 } }
  k = Math.max(2, Math.min(k, Math.floor(n / 2)))

  // embedding: smallest-k eigenvectors as columns
  const cols = order.slice(0, k)
  const data = nodes.map((_nd, row) => cols.map((c) => V.get(row, c)))
  const { clusters } = kmeans(data, k, { initialization: 'kmeans++', seed: 1 })
  return Object.fromEntries(nodes.map((nd, i) => [nd, clusters[i]]))
}
