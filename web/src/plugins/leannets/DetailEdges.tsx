'use client'

import { useSelectObjStore } from '@/stores/selectObjStore'
import { usePluginStore } from '@/plugins/registry'
import { getEntryColor } from '@/lib/entryColor'
import type { EdgeInfo } from './transform'
import { useLeanIndex } from './leanIndex'

/** Skeleton plugin detail section: shows edges grouped by sort. Only visible in skeleton mode. */
export function DetailEdges({ entryId }: { entryId: string }) {
    const modeActive = usePluginStore(s => s.isModeActive('leannets'))
    const selectObj = useSelectObjStore(s => s.select)

    const projectPath = typeof window !== 'undefined'
        ? new URLSearchParams(window.location.search).get('path') || ''
        : ''

    // Edges + own source come from the shared per-project index (one store
    // fetch for the whole plugin, not one per selection).
    const index = useLeanIndex(modeActive && entryId ? projectPath : '')
    const isAtom = !!index?.atoms.has(entryId)
    const mySource = index?.atoms.get(entryId)?.source || ''
    const edges = index && isAtom
        ? { outgoing: index.edgesOut.get(entryId) ?? [], incoming: index.edgesIn.get(entryId) ?? [] }
        : null

    const isMergeOn = usePluginStore(s => (s as any).mnMergeProofs || false)

    if (!modeActive || !edges) return null
    if (edges.outgoing.length === 0 && edges.incoming.length === 0) return null

    let outgoing = edges.outgoing
    let incoming = edges.incoming

    if (isMergeOn) {
        // Hide proof edges, merge proof's dependencies into statement
        outgoing = outgoing.filter(e => !e.sort.endsWith(', proof)'))
        incoming = incoming.filter(e => !e.sort.startsWith('(proof,'))
    }

    if (outgoing.length === 0 && incoming.length === 0) return null

    const outBySort = groupBy(outgoing, e => e.sort)
    const inBySort = groupBy(incoming, e => e.sort)

    return (
        <div className="border-t border-white/5 mt-2 pt-2">
            {Object.entries(outBySort).map(([sort, items]) => (
                <EdgeGroup key={`out-${sort}`} sort={sort} items={items} direction="out" onSelect={selectObj} mySource={mySource} />
            ))}
            {Object.entries(inBySort).map(([sort, items]) => (
                <EdgeGroup key={`in-${sort}`} sort={sort} items={items} direction="in" onSelect={selectObj} mySource={mySource} />
            ))}
        </div>
    )
}

function EdgeGroup({ sort, items, direction, onSelect, mySource }: {
    sort: string; items: EdgeInfo[]; direction: 'out' | 'in'; onSelect: (id: string) => void; mySource: string
}) {
    const arrow = direction === 'out' ? '→' : '←'

    return (
        <div className="mb-2">
            <div className="text-[10px] text-white/30 flex items-center gap-1 mb-0.5">
                <span>{sort}</span>
                <span className="text-white/15">({items.length})</span>
            </div>
            {items.map(item => {
                const targetColor = getEntryColor(item.targetId)
                const isCrossSource = mySource && item.targetSource && mySource !== item.targetSource
                return (
                <button
                    key={item.edgeHash}
                    onClick={() => onSelect(item.targetId)}
                    className="w-full text-left px-2 py-0.5 text-xs hover:bg-white/5 rounded transition-colors flex items-center gap-1"
                >
                    <span className="inline-block w-1.5 h-1.5 rounded-full shrink-0" style={{ backgroundColor: isCrossSource ? '#555' : (targetColor || '#888') }} />
                    <span style={{ opacity: 0.4 }}>{arrow}</span>
                    <span className="truncate" style={{ color: isCrossSource ? '#888' : (targetColor || 'rgba(255,255,255,0.5)') }}>{item.targetTitle || item.targetId}</span>
                    {isCrossSource && <span className="text-[9px] px-1 py-0 rounded bg-white/5 text-white/20 shrink-0">{item.targetSource}</span>}
                </button>
                )
            })}
        </div>
    )
}

function groupBy<T>(items: T[], key: (item: T) => string): Record<string, T[]> {
    const result: Record<string, T[]> = {}
    for (const item of items) {
        const k = key(item)
        if (!result[k]) result[k] = []
        result[k].push(item)
    }
    return result
}
