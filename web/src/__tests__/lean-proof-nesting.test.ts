/**
 * Lean proof nesting in EntryBlockRenderer.
 *
 * When a tex entryblock has a lean counterpart (cross-source), clicking the
 * ∀ badge expands a lean panel. That panel currently shows the lean theorem's
 * content, but NOT its proof. Since the store has (theorem, proof) edges
 * connecting lean theorems to lean proofs, the panel should also display the
 * nested lean proof (like RecordRenderer's NestedProofs does in DetailView).
 *
 * Contract:
 * 1. EntryBlockRenderer must have logic to find proofs for a lean counterpart
 * 2. The proof lookup pattern must match RecordRenderer (edge sort ends with ", proof)")
 * 3. Lean proof content must be renderable (LeanCode) in the expanded panel
 * 4. The proof section must be collapsible (not always visible)
 */
import { describe, it, expect } from 'vitest'
import * as fs from 'fs'

const entryBlockRenderer = fs.readFileSync('src/plugins/leannets/EntryBlockRenderer.tsx', 'utf-8')
const recordRenderer = fs.readFileSync('src/plugins/leannets/RecordRenderer.tsx', 'utf-8')
const leanIndex = fs.readFileSync('src/plugins/leannets/leanIndex.ts', 'utf-8')

describe('Lean proof nesting in EntryBlockRenderer', () => {
    it('has a hook or effect to find proofs for the lean counterpart', () => {
        // Must look up proofs via edges, through the shared per-project index
        expect(entryBlockRenderer).toMatch(/proof/i)
        expect(entryBlockRenderer).toContain("./leanIndex")
    })

    it('matches proof edges by sort ending with ", proof)"', () => {
        // The shared index detects proof edges the same way for every consumer
        expect(leanIndex).toContain(", proof)")
    })

    it('renders lean proof content with LeanCode component', () => {
        // LeanCode must be used for proof display (already imported)
        expect(entryBlockRenderer).toContain('LeanCode')
        // Must render proof content in the lean expanded panel area
        // Look for proof rendering near the leanExpanded section
        expect(entryBlockRenderer).toMatch(/proof.*content|proofContent|leanProof/)
    })

    it('proof section is collapsible (not always expanded)', () => {
        // Must have a toggle for showing/hiding proof
        expect(entryBlockRenderer).toMatch(/proof.*open|proof.*expand|showProof|proofOpen/i)
    })
})

describe('Consistency between RecordRenderer and EntryBlockRenderer proof lookup', () => {
    it('both use the same edge sort pattern for proof detection', () => {
        // Both route proof detection through the shared index's single pattern
        expect(recordRenderer).toContain("./leanIndex")
        expect(entryBlockRenderer).toContain("./leanIndex")
        expect(leanIndex).toContain(", proof)")
    })

    it('neither re-fetches edges per card — one store fetch in the index', () => {
        expect(recordRenderer).not.toMatch(/degree=1|degree%3D1/)
        expect(entryBlockRenderer).not.toMatch(/degree=1|degree%3D1/)
        expect(leanIndex).toContain('/api/astrolabe/entries')
    })
})
