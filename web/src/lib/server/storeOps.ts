// Write-half of the Astrolabe md store — the counterpart to store.ts's reader.
//
// Content-addressed: identity = filename = hash. There is no in-place edit —
// changing a record writes a new <hash>.md, deletes the old, and repoints every
// reference to it (other node files' ref + inline hashes in record, and the
// docs). Pure per-file ops: no JSON, no load-all/save-all.
//
// The hash is the store's content-address (SHA-256 over the canonical record);
// reproducing it exactly is what lets Node-written nodes share identity with the
// existing .md store, hash-for-hash.
import fs from 'node:fs'
import path from 'node:path'
import crypto from 'node:crypto'
import { parse as parseYaml, stringify as stringifyYaml } from 'yaml'

export type Rec = Record<string, any>

// ── canonical record form: JSON with sorted keys, ", " / ": " separators, and
//    non-ASCII left as-is — the exact bytes the content-address hashes over. ──
export function canon(v: any): string {
  if (v === null) return 'null'
  if (Array.isArray(v)) return '[' + v.map(canon).join(', ') + ']'
  if (typeof v === 'object') {
    return '{' + Object.keys(v).sort().map((k) => JSON.stringify(k) + ': ' + canon(v[k])).join(', ') + '}'
  }
  if (typeof v === 'string') return JSON.stringify(v)
  return String(v) // number | boolean
}

const sha12 = (buf: Buffer) => crypto.createHash('sha256').update(buf).digest('hex').slice(0, 12)

export function atomHash(record: Rec): string {
  return sha12(Buffer.concat([Buffer.from('__self__'), Buffer.from([0]), Buffer.from(canon(record), 'utf8')]))
}
export function edgeHash(ref: string[], record: Rec): string {
  const parts: Buffer[] = []
  for (const h of ref) parts.push(Buffer.from(h, 'utf8'), Buffer.from([0]))
  parts.push(Buffer.from(canon(record), 'utf8'))
  return sha12(Buffer.concat(parts))
}
export const nodeHash = (ref: string[], record: Rec) =>
  ref.length === 1 ? atomHash(record) : edgeHash(ref, record)

// ── nested-record serialization (ref first, readable key order; format never
//    affects the hash, which is computed from canon above) ──
const KEY_ORDER = ['source', 'sort', 'from', 'rel', 'key', 'state', 'title', 'ref', 'at', 'content', 'notes']
function ordered(rec: any): any {
  if (Array.isArray(rec)) return rec.map(ordered)
  if (rec && typeof rec === 'object') {
    const rank = (k: string) => { const i = KEY_ORDER.indexOf(k); return i < 0 ? KEY_ORDER.length : i }
    const o: Rec = {}
    for (const k of Object.keys(rec).sort((a, b) => rank(a) - rank(b) || a.localeCompare(b))) o[k] = ordered(rec[k])
    return o
  }
  return rec
}
export function dumpNode(ref: string[], record: Rec): string {
  const fm = stringifyYaml({ ref, record: ordered(record) }, { sortMapEntries: false, lineWidth: 0 })
  return `---\n${fm}---\n`
}
export function parseNode(text: string): { ref: string[]; record: Rec } {
  const end = text.indexOf('\n---', 3)
  const fm = parseYaml(text.slice(4, end + 1)) || {}
  return { ref: fm.ref, record: fm.record }
}

export class StoreOps {
  readonly base: string
  constructor(projectDir: string) {
    this.base = path.basename(projectDir) === '.astrolabe' ? projectDir : path.join(projectDir, '.astrolabe')
  }
  private file(h: string): string | null {
    for (const d of ['atoms', 'edges']) {
      const f = path.join(this.base, d, `${h}.md`)
      if (fs.existsSync(f)) return f
    }
    return null
  }
  exists(h: string) { return this.file(h) !== null }
  read(h: string): { ref: string[]; record: Rec } {
    const f = this.file(h); if (!f) throw new Error(`no node ${h}`)
    return parseNode(fs.readFileSync(f, 'utf8'))
  }
  allHashes(): string[] {
    const out: string[] = []
    for (const d of ['atoms', 'edges']) {
      const dir = path.join(this.base, d)
      if (fs.existsSync(dir)) for (const f of fs.readdirSync(dir)) if (f.endsWith('.md')) out.push(f.slice(0, -3))
    }
    return out
  }
  private writeRaw(ref: string[], record: Rec): string {
    const h = nodeHash(ref, record)
    const dir = path.join(this.base, ref.length === 1 ? 'atoms' : 'edges')
    fs.mkdirSync(dir, { recursive: true })
    fs.writeFileSync(path.join(dir, `${h}.md`), dumpNode(ref, record), 'utf8')
    return h
  }
  private unlink(h: string) { const f = this.file(h); if (f) fs.unlinkSync(f) }
  private docDirs(): string[] {
    return ['docs', 'docs-src'].map((d) => path.join(this.base, d)).filter((d) => fs.existsSync(d))
  }

  // ── operations ──
  addAtom(record: Rec): string { return this.writeRaw([atomHash(record)], record) }
  addEdge(a: string, b: string, rel: string, extra: Rec = {}): string {
    return this.writeRaw([a, b], { rel, ...extra })
  }
  removeNode(h: string, dropIncidentEdges = true): string[] {
    const removed: string[] = []
    if (this.read(h).ref.length === 1 && dropIncidentEdges) {
      for (const e of this.allHashes()) {
        if (e === h) continue
        const er = this.read(e).ref
        if (er.length > 1 && er.includes(h)) { this.unlink(e); removed.push(e) }
      }
    }
    this.unlink(h); removed.push(h)
    return removed
  }
  /** Change a node's record → new hash; write new, delete old, repoint everywhere. */
  updateContent(h: string, newRecord: Rec): string {
    const { ref } = this.read(h)
    const isAtom = ref.length === 1
    const newH = isAtom ? atomHash(newRecord) : edgeHash(ref, newRecord)
    if (newH === h) { this.writeRaw(isAtom ? [h] : ref, newRecord); return h }
    this.writeRaw(isAtom ? [newH] : ref, newRecord)
    this.unlink(h)
    this.repoint(h, newH)
    return newH
  }
  setEdgeRel(h: string, rel: string, notes?: string): string {
    return this.updateContent(h, notes ? { rel, notes } : { rel })
  }

  /** Replace a literal hash old→new across docs (no rehash) and node files (which
   *  rehash, recursing). The cascade store.ts's reader never sees, made complete. */
  repoint(oldH: string, newH: string) {
    for (const dir of this.docDirs()) {
      for (const f of fs.readdirSync(dir)) {
        if (!f.endsWith('.mdx')) continue
        const p = path.join(dir, f)
        const t = fs.readFileSync(p, 'utf8')
        if (t.includes(oldH)) fs.writeFileSync(p, t.split(oldH).join(newH), 'utf8')
      }
    }
    for (const nh of this.allHashes()) {
      if (nh === newH) continue
      const { ref, record } = this.read(nh)
      const recS = canon(record)
      const inRef = ref.includes(oldH)
      const inRec = recS.includes(oldH)
      if (!inRef && !inRec) continue
      const newRef = ref.map((x) => (x === oldH ? newH : x))
      const newRec = inRec ? JSON.parse(recS.split(oldH).join(newH)) : record
      const isAtom = ref.length === 1 && ref[0] === nh
      const nh2 = isAtom ? atomHash(newRec) : edgeHash(newRef, newRec)
      this.writeRaw(isAtom ? [nh2] : newRef, newRec)
      if (nh2 !== nh) { this.unlink(nh); this.repoint(nh, nh2) }
    }
  }
}
