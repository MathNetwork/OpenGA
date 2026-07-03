import { describe, it, expect } from 'vitest'
import { buildSkeletonView } from '../skeleton'
import { getSortFill } from '../../sortColors'
import type { Store } from '../store'

const atom = (hash: string, sort: string): [string, Store[string]] =>
  [hash, { ref: [hash], record: JSON.stringify({ sort, source: 'tex', title: sort }) }]

describe('skeleton sort colours', () => {
  // NETWORK nodes must use the exact same palette as the read-view cards
  // (lib/sortColors) — a drifted server-side copy once coloured them apart.
  it("color='sort' nodes match getSortFill", () => {
    const store: Store = Object.fromEntries([
      atom('aaaaaaaaaaaa', 'theorem'),
      atom('bbbbbbbbbbbb', 'definition'),
    ])
    const view = buildSkeletonView(store, { color: 'sort' })
    const colorById = new Map(view.nodes.map(n => [n.id, n.color]))
    expect(colorById.get('aaaaaaaaaaaa')).toBe(getSortFill('theorem'))
    expect(colorById.get('bbbbbbbbbbbb')).toBe(getSortFill('definition'))
    for (const c of colorById.values()) expect(c).toMatch(/^#[0-9a-f]{6}$/)
  })
})
