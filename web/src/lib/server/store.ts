// Server-side reader for the Astrolabe md store (read-only) — byte-compatible
// with the original Python implementation (now living in MathNetwork/
// Astrolabe's backend), which is what keeps hashes stable. Each node is a `.md`
// file (YAML front-matter + body); the entry is reconstructed as { ref, record }
// where record is JSON of the front-matter (minus ref) plus the body as `notes`.
//
// Two layouts:
// - Legacy, self-contained: `.astrolabe/{atoms,edges,nodes}` inside the project
//   (riemannian-geometry). Having its own `atoms/` marks a project as private —
//   it reads nothing else.
// - Hypergraph-sharing: a project without its own `atoms/` reads the union of
//   the shared pool `<projectsRoot>/hypergraph/{atoms,edges}` (sibling of the
//   project folder) and its optional project layer
//   `.astrolabe/hypergraph/{atoms,edges}`. Content-addressing makes the union
//   conflict-free (same hash ⇒ same bytes); on overlap the project layer wins.
import fs from 'node:fs'
import path from 'node:path'
import { parse as parseYaml } from 'yaml'
import { resolveFs } from './paths'

export interface Entry { ref: string[]; record: string }
export type Store = Record<string, Entry>

function nodeDirs(projectDir: string): string[] {
  const root = resolveFs(projectDir)
  const base = path.join(root, '.astrolabe')
  const legacy = [path.join(base, 'atoms'), path.join(base, 'edges'), path.join(base, 'nodes')]
  if (fs.existsSync(path.join(base, 'atoms'))) return legacy // private project
  const pool = path.join(path.dirname(root), 'hypergraph')
  return [
    path.join(pool, 'atoms'),
    path.join(pool, 'edges'),
    path.join(base, 'hypergraph', 'atoms'),
    path.join(base, 'hypergraph', 'edges'),
    ...legacy,
  ]
}

/** Inverse of the original _record_to_md: md text → (ref, canonical record JSON). */
function mdToEntry(text: string): Entry {
  let front: any = {}
  let body = text
  if (text.startsWith('---\n')) {
    const idx = text.indexOf('\n---\n', 3)
    if (idx !== -1) {
      // failsafe schema: never coerce scalars — a hash like `33454896e057`
      // must stay a string, not be read as scientific notation (3.34e64).
      front = parseYaml(text.slice(4, idx + 1), { schema: 'failsafe' }) || {}
      body = text.slice(idx + 5)
    }
  }
  const ref: string[] = front.ref ?? []
  let rec: Record<string, unknown>
  if (front.record && typeof front.record === 'object') {
    // Canonical nested format: { ref, record: {...} }. Surface the prose as
    // `notes` so renderers that read `notes` keep working during migration.
    rec = { ...front.record }
    if (rec.notes == null) {
      const c = rec.content as any
      if (typeof c === 'string') rec.notes = c
      else if (c && typeof c === 'object') {
        rec.notes = (c.title
          ? `${c.author ? c.author + '. ' : ''}${c.title}.${c.year ? ' ' + c.year + '.' : ''}`
          : '').trim()
      }
    }
  } else {
    // Legacy flat format: record fields sit at top level, prose in the body.
    rec = { ...front }
    delete rec.ref
    if (body !== '') rec.notes = body
  }
  return { ref, record: JSON.stringify(rec) }
}

export function loadStore(projectDir: string): Store {
  const data: Store = {}
  for (const dir of nodeDirs(projectDir)) {
    if (!fs.existsSync(dir)) continue
    for (const f of fs.readdirSync(dir).sort()) {
      if (!f.endsWith('.md')) continue
      const hash = f.slice(0, -3)
      try {
        data[hash] = mdToEntry(fs.readFileSync(path.join(dir, f), 'utf8'))
      } catch { /* skip unreadable */ }
    }
  }
  return data
}

/** Latest mtime across the node dirs and their .md files (file-watcher polling). */
export function storeMtime(projectDir: string): number {
  let m = 0
  for (const dir of nodeDirs(projectDir)) {
    if (!fs.existsSync(dir)) continue
    try { m = Math.max(m, fs.statSync(dir).mtimeMs) } catch { /* ignore */ }
    for (const f of fs.readdirSync(dir)) {
      if (!f.endsWith('.md')) continue
      try { m = Math.max(m, fs.statSync(path.join(dir, f)).mtimeMs) } catch { /* ignore */ }
    }
  }
  return m / 1000 // seconds, matching the original st_mtime semantics
}

/** Stage decomposition: atoms = 0; an entry whose refs are all resolved gets
 *  the next stage; cyclic entries get -1. Mirrors the original algorithm. */
function stages(data: Store): Record<string, number> {
  const result: Record<string, number> = {}
  for (const [h, e] of Object.entries(data)) if (e.ref.length === 1) result[h] = 0

  let m = 0
  let changed = true
  while (changed) {
    changed = false
    const resolved = new Set(Object.keys(result))
    for (const [h, e] of Object.entries(data)) {
      if (!(h in result) && e.ref.every((r) => resolved.has(r))) {
        result[h] = m + 1
        changed = true
      }
    }
    m += 1
  }
  for (const h of Object.keys(data)) if (!(h in result)) result[h] = -1
  return result
}

/** All entries as nodes, ref entries as links — matches the original to_ref_graph. */
export function refGraph(data: Store) {
  const st = stages(data)
  const nodes: Array<{ id: string; degree: number; stage: number; record: string }> = []
  const links: Array<{ source: string; target: string; position: number }> = []
  for (const [h, e] of Object.entries(data)) {
    nodes.push({ id: h, degree: e.ref.length - 1, stage: st[h] ?? -1, record: e.record })
    if (e.ref.length > 1) {
      e.ref.forEach((target, i) => links.push({ source: h, target, position: i }))
    }
  }
  return { nodes, links }
}
