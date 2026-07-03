import { describe, it, expect } from 'vitest'
import fs from 'node:fs'
import os from 'node:os'
import path from 'node:path'
import { atomHash, StoreOps } from '../storeOps'

// Identity is the content hash. This record/hash pair is a known-good vector
// produced by the original store implementation — atomHash must reproduce it
// exactly so Node-written nodes share identity with any pre-existing .md store.
describe('storeOps reproduces the stored content-address', () => {
  it('atomHash(known-good bib record) === 2f407ff400c5', () => {
    const mt = {
      source: 'bib', sort: 'ref',
      content: {
        title: 'Ricci Flow and the Poincaré Conjecture',
        author: 'John W. Morgan and Gang Tian',
        year: 2007, eprint: 'math/0607607',
        archivePrefix: 'arXiv', primaryClass: 'math.DG',
        url: 'https://arxiv.org/abs/math/0607607',
      },
    }
    expect(atomHash(mt)).toBe('2f407ff400c5')
  })
})

describe('storeOps file-first cascade', () => {
  it('update → rehash incident edge → repoint docs; remove cascades', () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'ops-'))
    const proj = path.join(tmp, 'p')
    const docs = path.join(proj, '.astrolabe', 'docs')
    fs.mkdirSync(docs, { recursive: true })
    const s = new StoreOps(proj)

    const A = s.addAtom({ source: 'tex', sort: 'lemma', content: 'Lemma A.' })
    const B = s.addAtom({ source: 'tex', sort: 'lemma', content: 'Lemma B.' })
    const E = s.addEdge(A, B, 'depends', { notes: 'A needs B' })
    fs.writeFileSync(path.join(docs, '00.mdx'), `see \\entryblock{${A}} and \\entryref{${B}}`)
    expect(s.exists(A) && s.exists(B) && s.exists(E)).toBe(true)

    // change A's content → new hash; the depends-edge must re-point + rehash,
    // the doc must follow.
    const A2 = s.updateContent(A, { source: 'tex', sort: 'lemma', content: 'Lemma A, revised.' })
    expect(A2).not.toBe(A)
    expect(s.exists(A)).toBe(false)
    expect(s.exists(A2)).toBe(true)

    const edges = s.allHashes().filter((h) => s.read(h).ref.length > 1)
    expect(edges).toHaveLength(1)
    expect(edges[0]).not.toBe(E)
    expect(s.read(edges[0]).ref).toEqual([A2, B])

    const doc = fs.readFileSync(path.join(docs, '00.mdx'), 'utf8')
    expect(doc).toContain(A2)
    expect(doc).not.toContain(A)

    // referential closure holds across the whole store
    for (const h of s.allHashes()) for (const r of s.read(h).ref) expect(s.exists(r)).toBe(true)

    // removing the atom drops its incident edge too
    const removed = s.removeNode(A2)
    expect(removed).toContain(A2)
    expect(removed).toContain(edges[0])
    expect(s.allHashes().filter((h) => h !== B)).toHaveLength(0)

    fs.rmSync(tmp, { recursive: true, force: true })
  })
})
