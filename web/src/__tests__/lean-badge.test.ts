/**
 * Lean badge tests.
 *
 * LeanBadge shows formalization status on entryblocks.
 * - Lean source entries: static ∀ badge (not interactive)
 * - Tex entries with cross-source lean: interactive ∀ badge
 */
import { describe, it, expect } from 'vitest'
import * as fs from 'fs'

const entryBlockRenderer = fs.readFileSync('src/plugins/leannets/EntryBlockRenderer.tsx', 'utf-8')

describe('LeanBadge component', () => {
    it('LeanBadge file exists in leannets plugin', () => {
        expect(() => fs.readFileSync('src/plugins/leannets/LeanBadge.tsx', 'utf-8')).not.toThrow()
    })

    it('Core files do not import LeanBadge', () => {
        const coreFiles = [
            'src/components/mdx/EntryBlock.tsx',
            'src/components/mdx/EntryLink.tsx',
            'src/panels/workspace/EntryDetail.tsx',
        ]
        for (const f of coreFiles) {
            const content = fs.readFileSync(f, 'utf-8')
            expect(content).not.toContain('LeanBadge')
        }
    })
})

describe('Scenario B: lean source static badge', () => {
    it('EntryBlockRenderer imports LeanBadge', () => {
        expect(entryBlockRenderer).toContain('LeanBadge')
    })

    it('renders badge when source is lean', () => {
        expect(entryBlockRenderer).toMatch(/source\s*===?\s*['"]lean['"]/)
    })
})

describe('Scenario A: tex cross-source badge', () => {
    it('EntryBlockRenderer has cross-source query logic', () => {
        // Should fetch degree-1 entries to find cross-source lean counterpart
        expect(entryBlockRenderer).toMatch(/cross[_-]?source|lean.*counterpart|lean.*pair/i)
    })

    it('EntryBlockRenderer renders interactive badge for tex with lean', () => {
        expect(entryBlockRenderer).toContain('interactive')
    })
})
