import { parseSortFromRecord } from '@/lib/sortColors'

export interface EdgeInfo {
    edgeHash: string
    sort: string
    targetId: string
    targetTitle: string
    targetSource: string
    ref: string[]
}

interface GroupedEdges {
    outgoing: EdgeInfo[]  // ref[0] = selected atom
    incoming: EdgeInfo[]  // ref[1] = selected atom
}

/** Parse title from a record JSON string. */
function parseTitle(record: string): string {
    try { return JSON.parse(record).title || '' } catch { return '' }
}

/** Parse source from a record JSON string. */
function parseSource(record: string): string {
    try { return JSON.parse(record).source || '' } catch { return '' }
}

/** Group all degree-1 edges connected to a given atom, by sort. */
export function groupEdgesBySort(
    atomId: string,
    entries: Record<string, { ref: string[]; record: string }>,
): GroupedEdges {
    const outgoing: EdgeInfo[] = []
    const incoming: EdgeInfo[] = []

    for (const [hash, entry] of Object.entries(entries)) {
        if (entry.ref.length !== 2) continue

        const [ref0, ref1] = entry.ref
        const sort = parseSortFromRecord(entry.record)

        if (ref0 === atomId) {
            const target = entries[ref1]
            outgoing.push({
                edgeHash: hash,
                sort,
                targetId: ref1,
                targetTitle: target ? parseTitle(target.record) : ref1,
                targetSource: target ? parseSource(target.record) : '',
                ref: entry.ref,
            })
        } else if (ref1 === atomId) {
            const target = entries[ref0]
            incoming.push({
                edgeHash: hash,
                sort,
                targetId: ref0,
                targetTitle: target ? parseTitle(target.record) : ref0,
                targetSource: target ? parseSource(target.record) : '',
                ref: entry.ref,
            })
        }
    }

    return { outgoing, incoming }
}
