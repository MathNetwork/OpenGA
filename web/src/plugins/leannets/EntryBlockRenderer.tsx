'use client'

import { useState } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { InlineMath } from '@/components/mdx/InlineMath'
import { Prose } from '@/components/mdx/Prose'
import { LeanCode } from './LeanHighlight'
import { LeanBadge } from './LeanBadge'
import { SORT_LABELS, parseRecord } from './utils'
import { useLeanIndex, type LeanRecord } from './leanIndex'

/** Find the cross-source lean counterpart for a tex atom (in-memory lookup). */
function useLeanCounterpart(hash: string, source: string | undefined, projectPath: string): LeanRecord | null {
    const index = useLeanIndex(source === 'tex' && hash ? projectPath : '')
    return index?.counterpart.get(hash) ?? null
}

/** Find proof entries for a lean theorem via (theorem, proof) edges (in-memory). */
function useLeanProofs(leanHash: string | undefined, projectPath: string): LeanRecord[] {
    const index = useLeanIndex(leanHash ? projectPath : '')
    return (leanHash && index?.proofs.get(leanHash)) || []
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

    // Hooks must run unconditionally (before the unparseable-record return);
    // both tolerate a missing source/hash by skipping the index load.
    // Scenario A: tex entry — look for cross-source lean counterpart
    const leanCounterpart = useLeanCounterpart(hash, parsed?.source, projectPath)
    // Find proofs for the lean counterpart (if any)
    const leanProofs = useLeanProofs(leanCounterpart?.hash, projectPath)

    if (!parsed || typeof parsed !== 'object') {
        return <div className="my-2 text-xs text-white/20 font-mono">entry: {hash}</div>
    }

    const label = SORT_LABELS[parsed.sort] || parsed.sort || ''
    const displayText = parsed.notes || parsed.content || ''
    const isLean = parsed.source === 'lean'
    const isTex = parsed.source === 'tex'
    const showBody = !collapsible || open
    // `number` is the DERIVED project-wide "§.item" (from where this card first
    // appears), injected by preprocess as data-number — never stored.
    const numberStr = number ? ` ${number}` : ''

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
