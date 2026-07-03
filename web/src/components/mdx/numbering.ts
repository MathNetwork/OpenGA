/**
 * Entry numbering — DERIVED, never stored.
 *
 * A card's number is a pure POSITIONAL coordinate `chapter.section.item`:
 * the section is the ORDINAL of the `## ` heading the card sits under (first
 * `## ` heading in the doc → section 1; content before any `## ` heading →
 * section 0). Heading TEXT is irrelevant — named sections and `## §N` sections
 * number identically — and `from.at` / source labels must never influence it.
 * The item counter runs per section across all sorts (Definition 2.1,
 * Proposition 2.2, Theorem 2.8 …). First occurrence of a hash wins; later
 * `\entryref`s to the same hash resolve to that same number. Proofs are not
 * numbered.
 *
 * The map is built once across ALL chapter docs so a cross-chapter reference
 * resolves to the target's own number (+ the chapter it lives in).
 */
export interface EntryNumber {
    chapter: number
    num: string        // "chapter.section.item", e.g. "7.2.8"
}

export type Numbering = Map<string, EntryNumber>

const CHAPTER_RE = /^#\s+Chapter\s+(\d+)\b/m
const ENTRYBLOCK_RE = /\\entryblock\{([^}]+)\}/g

/** Chapter number for a doc, from its `# Chapter N` title (else filename prefix). */
export function chapterOf(content: string, filename: string): number {
    const m = content.match(CHAPTER_RE)
    if (m) return parseInt(m[1], 10)
    const fm = filename.match(/^(\d+)-/)
    return fm ? parseInt(fm[1], 10) : 0
}

function isProof(hash: string, entries?: Record<string, { record: string }>): boolean {
    if (!entries?.[hash]) return false
    try { return JSON.parse(entries[hash].record).sort === 'proof' } catch { return false }
}

/** Number every first-seen `\entryblock` in one chapter doc → hash → "§.item". */
function numberDoc(mdx: string, entries?: Record<string, { record: string }>): Map<string, string> {
    const map = new Map<string, string>()
    const counters = new Map<number, number>()   // §section → running item count
    let section = 0
    for (const line of mdx.split('\n')) {
        // Section = ordinal of `## ` headings (`###` fails ^##\s, so deeper
        // headings never open a section).
        if (/^##\s/.test(line)) { section++; continue }
        ENTRYBLOCK_RE.lastIndex = 0
        let m: RegExpExecArray | null
        while ((m = ENTRYBLOCK_RE.exec(line)) !== null) {
            const hash = m[1]
            if (map.has(hash) || isProof(hash, entries)) continue
            const c = (counters.get(section) || 0) + 1
            counters.set(section, c)
            map.set(hash, `${section}.${c}`)
        }
    }
    return map
}

/** Build the project-wide numbering from all chapter docs (sorted by filename). */
export function buildProjectNumbering(
    docs: { filename: string; content: string }[],
    entries?: Record<string, { record: string }>,
): Numbering {
    const global: Numbering = new Map()
    const sorted = [...docs].sort((a, b) => a.filename.localeCompare(b.filename))
    for (const { filename, content } of sorted) {
        const chapter = chapterOf(content, filename)
        // Full number is chapter.section.item — the chapter prefix is derived
        // from the doc's position (its `# Chapter N` / filename), so every card
        // gets a globally-unique, self-describing number (Hopf–Rinow → 7.2.8).
        for (const [hash, secItem] of numberDoc(content, entries)) {
            if (!global.has(hash)) global.set(hash, { chapter, num: `${chapter}.${secItem}` })
        }
    }
    return global
}
