import { describe, it, expect } from 'vitest'
import fs from 'node:fs'
import os from 'node:os'
import path from 'node:path'
import { loadStore } from '../store'

// Layered store: a project without its own atoms/ reads the shared sibling
// pool `projects/hypergraph` plus its optional `.astrolabe/hypergraph` layer;
// a legacy project with its own atoms/ stays private.
const atomMd = (h: string, content: string) =>
  `---\nref:\n- ${h}\nrecord:\n  source: tex\n  sort: lemma\n  content: ${content}\n---\n`

function makeRoot(): string {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'store-'))
  fs.mkdirSync(path.join(root, 'hypergraph', 'atoms'), { recursive: true })
  fs.writeFileSync(path.join(root, 'hypergraph', 'atoms', 'aaaaaaaaaaaa.md'), atomMd('aaaaaaaaaaaa', 'pooled'))
  return root
}

describe('hypergraph pool union', () => {
  it('a project without its own atoms/ reads the shared pool', () => {
    const root = makeRoot()
    fs.mkdirSync(path.join(root, 'p', '.astrolabe', 'docs'), { recursive: true })
    const store = loadStore(path.join(root, 'p'))
    expect(Object.keys(store)).toEqual(['aaaaaaaaaaaa'])
  })

  it('the project hypergraph layer is unioned in and wins on overlap', () => {
    const root = makeRoot()
    const layer = path.join(root, 'p', '.astrolabe', 'hypergraph', 'atoms')
    fs.mkdirSync(layer, { recursive: true })
    fs.writeFileSync(path.join(layer, 'bbbbbbbbbbbb.md'), atomMd('bbbbbbbbbbbb', 'local'))
    fs.writeFileSync(path.join(layer, 'aaaaaaaaaaaa.md'), atomMd('aaaaaaaaaaaa', 'shadowed'))
    const store = loadStore(path.join(root, 'p'))
    expect(Object.keys(store).sort()).toEqual(['aaaaaaaaaaaa', 'bbbbbbbbbbbb'])
    expect(JSON.parse(store['aaaaaaaaaaaa'].record).content).toBe('shadowed')
  })

  it('a legacy project with its own atoms/ stays private', () => {
    const root = makeRoot()
    const atoms = path.join(root, 'legacy', '.astrolabe', 'atoms')
    fs.mkdirSync(atoms, { recursive: true })
    fs.writeFileSync(path.join(atoms, 'cccccccccccc.md'), atomMd('cccccccccccc', 'private'))
    const store = loadStore(path.join(root, 'legacy'))
    expect(Object.keys(store)).toEqual(['cccccccccccc'])
  })
})
