'use client'

import { useState, useEffect } from 'react'
import { API_BASE } from '@/lib/apiBase'
import { useDataStore } from '@/stores/dataStore'
import { parseRecord } from './utils'
import type { EdgeInfo } from './transform'

export interface LeanRecord { hash: string; record: Record<string, any> }

export interface LeanIndex {
    /** atom hash → parsed record (null when the record is unparseable) */
    atoms: Map<string, Record<string, any> | null>
    /** tex atom hash → its cross-source lean counterpart */
    counterpart: Map<string, LeanRecord>
    /** statement hash → its proof atoms (via "(sort, proof)" edges) */
    proofs: Map<string, LeanRecord[]>
    /** atom hash → degree-1 edges where it is ref[0] / ref[1] */
    edgesOut: Map<string, EdgeInfo[]>
    edgesIn: Map<string, EdgeInfo[]>
}

// Per-project lean index, built ONCE from a single store fetch and shared by
// every card and detail section. Previously each card re-fetched the whole
// degree-1 edge set (megabytes) on mount — the dominant source of read-view
// lag. The promise is cached so concurrent mounts dedupe to one build; the
// entry is versioned by dataStore.refreshTrigger (bumped by useFileWatcher)
// so an external store change rebuilds it, and a failed build is evicted so
// the next mount retries.
const leanIndexCache = new Map<string, { version: number; promise: Promise<LeanIndex> }>()

async function buildLeanIndex(projectPath: string): Promise<LeanIndex> {
    const res = await fetch(`${API_BASE}/api/astrolabe/entries?path=${encodeURIComponent(projectPath)}`)
    if (!res.ok) throw new Error(res.statusText)
    const entries: Record<string, { ref: string[]; record: string }> = await res.json()

    // Parse every record once; all lookups below are in-memory.
    const recs = new Map<string, Record<string, any> | null>()
    for (const [h, e] of Object.entries(entries)) recs.set(h, parseRecord(e.record))

    const atoms = new Map<string, Record<string, any> | null>()
    for (const [h, e] of Object.entries(entries)) {
        if (e.ref.length === 1) atoms.set(h, recs.get(h) ?? null)
    }
    const isLean = (h: string) => atoms.get(h)?.source === 'lean'

    const counterpart = new Map<string, LeanRecord>()
    const proofs = new Map<string, LeanRecord[]>()
    const edgesOut = new Map<string, EdgeInfo[]>()
    const edgesIn = new Map<string, EdgeInfo[]>()

    for (const [hash, edge] of Object.entries(entries)) {
        if (edge.ref.length !== 2) continue
        const [a, b] = edge.ref
        const sort = recs.get(hash)?.sort || ''

        // Cross-source counterpart: exactly one side is lean → map tex→lean.
        const aLean = isLean(a), bLean = isLean(b)
        if (aLean !== bLean) {
            const leanH = aLean ? a : b
            const texH = aLean ? b : a
            const leanR = atoms.get(leanH)
            if (leanR && !counterpart.has(texH)) counterpart.set(texH, { hash: leanH, record: leanR })
        }

        // Proof edge: ref[0] is the statement, sort ends in ", proof)".
        if (sort.endsWith(', proof)')) {
            const proofR = atoms.get(b)
            if (proofR) {
                const list = proofs.get(a) ?? []
                list.push({ hash: b, record: proofR })
                proofs.set(a, list)
            }
        }

        // Edge grouping for the detail section (same shape as groupEdgesBySort).
        const mk = (targetId: string): EdgeInfo => ({
            edgeHash: hash,
            sort,
            targetId,
            targetTitle: targetId in entries ? recs.get(targetId)?.title || '' : targetId,
            targetSource: targetId in entries ? recs.get(targetId)?.source || '' : '',
            ref: edge.ref,
        })
        const out = edgesOut.get(a) ?? []
        out.push(mk(b))
        edgesOut.set(a, out)
        const inc = edgesIn.get(b) ?? []
        inc.push(mk(a))
        edgesIn.set(b, inc)
    }

    return { atoms, counterpart, proofs, edgesOut, edgesIn }
}

export function loadLeanIndex(projectPath: string, version: number): Promise<LeanIndex> {
    const hit = leanIndexCache.get(projectPath)
    if (hit && hit.version === version) return hit.promise
    const promise = buildLeanIndex(projectPath)
    leanIndexCache.set(projectPath, { version, promise })
    promise.catch(() => {
        if (leanIndexCache.get(projectPath)?.promise === promise) leanIndexCache.delete(projectPath)
    })
    return promise
}

/** The shared per-project index; null while loading/on failure. Pass an empty
 *  projectPath to skip loading entirely (keeps hook order stable). */
export function useLeanIndex(projectPath: string): LeanIndex | null {
    const refreshTrigger = useDataStore(s => s.refreshTrigger)
    const [index, setIndex] = useState<LeanIndex | null>(null)

    useEffect(() => {
        if (!projectPath) { setIndex(null); return }
        let alive = true
        loadLeanIndex(projectPath, refreshTrigger)
            .then(idx => { if (alive) setIndex(idx) })
            .catch(() => { if (alive) setIndex(null) })
        return () => { alive = false }
    }, [projectPath, refreshTrigger])

    return index
}
