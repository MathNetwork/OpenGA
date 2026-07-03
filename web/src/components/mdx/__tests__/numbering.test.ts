import { describe, it, expect } from 'vitest'
import { buildProjectNumbering } from '../numbering'

const rec = (sort: string) => ({ record: JSON.stringify({ sort }) })

describe('buildProjectNumbering', () => {
    it('numbers NAMED sections ordinally (Morgan–Tian-style doc → 1.1.x/1.2.x, not 1.0.x)', () => {
        const content = [
            '# Chapter 1',
            '## 3-manifolds and the geometrization conjecture',
            '\\entryblock{aaaaaaaaaaaa}',
            '\\entryblock{bbbbbbbbbbbb}',
            '## Ricci flow with surgery',
            '\\entryblock{cccccccccccc}',
        ].join('\n')
        const n = buildProjectNumbering([{ filename: '01-intro.mdx', content }])
        expect(n.get('aaaaaaaaaaaa')).toEqual({ chapter: 1, num: '1.1.1' })
        expect(n.get('bbbbbbbbbbbb')).toEqual({ chapter: 1, num: '1.1.2' })
        // '## 3-manifolds…' is the FIRST heading → section 1, never a parsed "3"
        expect(n.get('cccccccccccc')).toEqual({ chapter: 1, num: '1.2.1' })
    })

    it("numbers '## §N' docs identically to ordinal counting (riemannian-style)", () => {
        const content = [
            '# Chapter 7',
            '## §1 Preliminaries',
            '\\entryblock{aaaaaaaaaaaa}',
            '## §2 Hopf–Rinow',
            '\\entryblock{bbbbbbbbbbbb}',
            '\\entryblock{cccccccccccc}',
        ].join('\n')
        const n = buildProjectNumbering([{ filename: '07-hopf-rinow.mdx', content }])
        expect(n.get('aaaaaaaaaaaa')).toEqual({ chapter: 7, num: '7.1.1' })
        expect(n.get('bbbbbbbbbbbb')).toEqual({ chapter: 7, num: '7.2.1' })
        expect(n.get('cccccccccccc')).toEqual({ chapter: 7, num: '7.2.2' })
    })

    it('skips proofs without consuming an item number', () => {
        const content = [
            '# Chapter 2',
            '## Metrics',
            '\\entryblock{aaaaaaaaaaaa}',
            '\\entryblock{pppppppppppp}',
            '\\entryblock{bbbbbbbbbbbb}',
        ].join('\n')
        const entries = {
            aaaaaaaaaaaa: rec('theorem'),
            pppppppppppp: rec('proof'),
            bbbbbbbbbbbb: rec('definition'),
        }
        const n = buildProjectNumbering([{ filename: '02-metrics.mdx', content }], entries)
        expect(n.get('aaaaaaaaaaaa')?.num).toBe('2.1.1')
        expect(n.has('pppppppppppp')).toBe(false)
        expect(n.get('bbbbbbbbbbbb')?.num).toBe('2.1.2')
    })

    it('first occurrence wins across two docs', () => {
        const doc1 = ['# Chapter 1', '## A', '\\entryblock{aaaaaaaaaaaa}'].join('\n')
        const doc2 = ['# Chapter 2', '## B', '\\entryblock{aaaaaaaaaaaa}', '\\entryblock{bbbbbbbbbbbb}'].join('\n')
        const n = buildProjectNumbering([
            { filename: '02-later.mdx', content: doc2 },
            { filename: '01-first.mdx', content: doc1 },
        ])
        // docs are sorted by filename, so chapter 1's occurrence wins
        expect(n.get('aaaaaaaaaaaa')).toEqual({ chapter: 1, num: '1.1.1' })
        expect(n.get('bbbbbbbbbbbb')).toEqual({ chapter: 2, num: '2.1.2' })
    })

    it('content before any ## heading gets section 0', () => {
        const content = [
            '# Chapter 3',
            'Intro text.',
            '\\entryblock{aaaaaaaaaaaa}',
            '## First section',
            '\\entryblock{bbbbbbbbbbbb}',
        ].join('\n')
        const n = buildProjectNumbering([{ filename: '03-x.mdx', content }])
        expect(n.get('aaaaaaaaaaaa')?.num).toBe('3.0.1')
        expect(n.get('bbbbbbbbbbbb')?.num).toBe('3.1.1')
    })

    it('### headings do not open a new section', () => {
        const content = [
            '# Chapter 4',
            '## Only section',
            '\\entryblock{aaaaaaaaaaaa}',
            '### A subsection',
            '\\entryblock{bbbbbbbbbbbb}',
        ].join('\n')
        const n = buildProjectNumbering([{ filename: '04-x.mdx', content }])
        expect(n.get('aaaaaaaaaaaa')?.num).toBe('4.1.1')
        expect(n.get('bbbbbbbbbbbb')?.num).toBe('4.1.2')
    })
})
