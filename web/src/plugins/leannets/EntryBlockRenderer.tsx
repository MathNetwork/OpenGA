'use client'

import { useState, useEffect } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { API_BASE } from '@/lib/apiBase'
import { InlineMath } from '@/components/mdx/InlineMath'
import { Prose } from '@/components/mdx/Prose'
import { LeanCode } from './LeanHighlight'
import { LeanBadge } from './LeanBadge'
import { SORT_LABELS, parseRecord } from './utils'

interface LeanRecord { hash: string; record: Record<string, any> }
interface LeanIndex {
    /** tex atom hash → its cross-source lean counterpart */
    counterpart: Map<string, LeanRecord>
    /** lean theorem hash → its proof entries */
    proofs: Map<string, LeanRecord[]>
}

// Per-project lean index, built ONCE from a single atoms+edges fetch and shared
// by every card. Previously each card re-fetched the whole degree-1 edge set
// (megabytes) on mount, twice — the dominant source of read-view lag. Keyed by
// project path; the promise is cached so concurrent mounts dedupe to one build.
const leanIndexCache = new Map<string, Promise<LeanIndex>>()

async function buildLeanIndex(projectPath: string): Promise<LeanIndex> {
    const counterpart = new Map<string, LeanRecord>()
    const proofs = new Map<string, LeanRecord[]>()
    const p = encodeURIComponent(projectPath)
    try {
        const [atomsRes, edgesRes] = await Promise.all([
            fetch(`${API_BASE}/api/astrolabe/entries?path=${p}&degree=0`),
            fetch(`${API_BASE}/api/astrolabe/entries?path=${p}&degree=1`),
        ])
        const atoms: Record<string, any> = atomsRes.ok ? await atomsRes.json() : {}
        const edges: Record<string, any> = edgesRes.ok ? await edgesRes.json() : {}

        // Parse atom records once; index source + record for in-memory lookups.
        const atomRec = new Map<string, Record<string, any>>()
        for (const [h, e] of Object.entries(atoms)) {
            const rec = parseRecord((e as any).record)
            if (rec) atomRec.set(h, rec)
        }
        const isLean = (h: string) => atomRec.get(h)?.source === 'lean'

        for (const edge of Object.values(edges) as any[]) {
            const ref = edge.ref as string[]
            if (!ref || ref.length !== 2) continue
            const [a, b] = ref
            // Cross-source counterpart: exactly one side is lean → map tex→lean.
            const aLean = isLean(a), bLean = isLean(b)
            if (aLean !== bLean) {
                const leanH = aLean ? a : b
                const texH = aLean ? b : a
                const leanR = atomRec.get(leanH)
                if (leanR && !counterpart.has(texH)) counterpart.set(texH, { hash: leanH, record: leanR })
            }
            // Proof edge: ref[0] is the lean theorem, sort ends in ", proof)".
            if (isLean(ref[0])) {
                let sort = ''
                try { sort = JSON.parse(edge.record).sort || '' } catch { /* skip */ }
                const proofR = sort.endsWith(', proof)') ? atomRec.get(ref[1]) : undefined
                if (proofR) {
                    const list = proofs.get(ref[0]) ?? []
                    list.push({ hash: ref[1], record: proofR })
                    proofs.set(ref[0], list)
                }
            }
        }
    } catch { /* leave index empty on failure */ }
    return { counterpart, proofs }
}

function loadLeanIndex(projectPath: string): Promise<LeanIndex> {
    let cached = leanIndexCache.get(projectPath)
    if (!cached) { cached = buildLeanIndex(projectPath); leanIndexCache.set(projectPath, cached) }
    return cached
}

/** Find the cross-source lean counterpart for a tex atom (in-memory lookup). */
function useLeanCounterpart(hash: string, source: string | undefined, projectPath: string) {
    const [leanEntry, setLeanEntry] = useState<LeanRecord | null>(null)

    useEffect(() => {
        if (source !== 'tex' || !hash || !projectPath) { setLeanEntry(null); return }
        let alive = true
        loadLeanIndex(projectPath).then(idx => { if (alive) setLeanEntry(idx.counterpart.get(hash) ?? null) })
        return () => { alive = false }
    }, [hash, source, projectPath])

    return leanEntry
}

/** Find proof entries for a lean theorem via (theorem, proof) edges (in-memory). */
function useLeanProofs(leanHash: string | undefined, projectPath: string) {
    const [proofEntries, setProofEntries] = useState<LeanRecord[]>([])

    useEffect(() => {
        if (!leanHash || !projectPath) { setProofEntries([]); return }
        let alive = true
        loadLeanIndex(projectPath).then(idx => { if (alive) setProofEntries(idx.proofs.get(leanHash) ?? []) })
        return () => { alive = false }
    }, [leanHash, projectPath])

    return proofEntries
}

export function LeanNetsEntryBlock({ hash, record, color, number, collapsible, children }: {
    hash: string; record: string; color: string; number?: string; collapsible?: boolean; children?: React.ReactNode
}) {
    const [open, setOpen] = useState(false)
    const [leanExpanded, setLeanExpanded] = useState(false)
    const [proofOpen, setProofOpen] = useState(false)
    const selectObj = useSelectObjStore(s => s.select)

    const projectPath = typeof window !== 'undefined'
        ? new URLSearchParams(window.location.search).get('path') || ''
        : ''

    const parsed = parseRecord(record)
    if (!parsed || typeof parsed !== 'object') {
        return <div className="my-2 text-xs text-white/20 font-mono">entry: {hash}</div>
    }

    const label = SORT_LABELS[parsed.sort] || parsed.sort || ''
    const displayText = parsed.notes || parsed.content || ''
    const isLean = parsed.sort?.startsWith('lean-') || parsed.source === 'lean'
    const isTex = parsed.source === 'tex'
    const showBody = !collapsible || open
    // `number` is the DERIVED project-wide "§.item" (from where this card first
    // appears), injected by preprocess as data-number — never stored.
    const numberStr = number ? ` ${number}` : ''

    // Scenario A: tex entry — look for cross-source lean counterpart
    const leanCounterpart = useLeanCounterpart(hash, parsed.source, projectPath)
    // Find proofs for the lean counterpart (if any)
    const leanProofs = useLeanProofs(leanCounterpart?.hash, projectPath)

    return (
        <div data-entry={hash} className="my-3 pl-3 rounded-r" style={{ borderLeftColor: color, borderLeftWidth: 2, opacity: 0.9 }}>
            <div className="font-semibold flex items-center" style={{ color, fontSize: '0.85em', gap: '0.3em', marginBottom: '0.25em' }}>
                {collapsible && (
                    <button
                        onClick={(e) => { e.stopPropagation(); setOpen(!open) }}
                        className="text-white/30 hover:text-white/60"
                        style={{ width: '1em' }}
                    >
                        {open ? '▾' : '▸'}
                    </button>
                )}
                <span
                    className="cursor-pointer hover:opacity-80"
                    onClick={(e) => { e.stopPropagation(); selectObj(hash) }}
                    title={`Click to select entry ${hash}`}
                >
                    {label}{numberStr}{parsed.title ? ` (${parsed.title})` : ''}
                    {parsed.state === 'sorry' && <span className="text-red-400/70" style={{ marginLeft: '0.3em' }}>sorry</span>}
                    <span className="font-mono text-white/15 font-normal" style={{ marginLeft: '0.5em', fontSize: '0.85em' }}>{hash}</span>
                </span>
                {/* Scenario B: lean source → static badge */}
                {isLean && <LeanBadge interactive={false} state={parsed.state} />}
                {/* Scenario A: tex with lean counterpart → interactive badge */}
                {isTex && leanCounterpart && (
                    <LeanBadge
                        interactive={true}
                        state={leanCounterpart.record.state}
                        onClick={() => setLeanExpanded(!leanExpanded)}
                    />
                )}
            </div>
            {showBody && (
                <>
                    <div className="text-white/70">
                        {isLean ? (
                            <LeanCode>{displayText}</LeanCode>
                        ) : (
                            <Prose>{displayText}</Prose>
                        )}
                    </div>
                    {/* Cross-source lean panel */}
                    {leanExpanded && leanCounterpart && (
                        <div className="border-l-2 border-green-500/30" style={{ marginTop: '0.4em', paddingLeft: '0.5em' }}>
                            <div className="flex items-center" style={{ gap: '0.4em', marginBottom: '0.25em', fontSize: '0.8em' }}>
                                <span className="font-medium text-green-400/70">
                                    {SORT_LABELS[leanCounterpart.record.sort] || leanCounterpart.record.sort || 'Lean'}
                                </span>
                                {leanCounterpart.record.title && (
                                    <span className="text-white/40">{leanCounterpart.record.title}</span>
                                )}
                                {leanCounterpart.record.state && (
                                    <span className={`rounded ${leanCounterpart.record.state === 'proven' ? 'bg-green-500/10 text-green-400' : 'bg-yellow-500/10 text-yellow-400'}`} style={{ fontSize: '0.85em', padding: '0 0.3em' }}>
                                        {leanCounterpart.record.state}
                                    </span>
                                )}
                            </div>
                            {leanCounterpart.record.content && (
                                <LeanCode>{leanCounterpart.record.content}</LeanCode>
                            )}
                            {/* Nested lean proof (collapsible) */}
                            {leanProofs.length > 0 && (
                                <div className="border-l border-white/10" style={{ marginTop: '0.3em', paddingLeft: '0.5em' }}>
                                    <button
                                        onClick={(e) => { e.stopPropagation(); setProofOpen(!proofOpen) }}
                                        className="text-white/30 hover:text-white/50 flex items-center"
                                        style={{ fontSize: '0.8em', gap: '0.3em' }}
                                    >
                                        <span>{proofOpen ? '▾' : '▸'}</span>
                                        <span>Proof ({leanProofs.length})</span>
                                    </button>
                                    {proofOpen && leanProofs.map(p => (
                                        <div key={p.hash} style={{ marginTop: '0.3em' }}>
                                            {p.record.content && (
                                                <LeanCode>{p.record.content}</LeanCode>
                                            )}
                                            {p.record.notes && !p.record.content && (
                                                <div className="text-white/50 leading-relaxed" style={{ marginTop: '0.25em' }}>
                                                    <InlineMath>{p.record.notes}</InlineMath>
                                                </div>
                                            )}
                                        </div>
                                    ))}
                                </div>
                            )}
                        </div>
                    )}
                    {children}
                </>
            )}
        </div>
    )
}
