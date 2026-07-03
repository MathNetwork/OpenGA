'use client'

import { useState, useEffect } from 'react'
import { API_BASE } from '@/lib/apiBase'
import { usePluginStore } from '@/plugins/registry'
import { useViewStore } from '@/stores/viewStore'
import { InlineMath } from '@/components/mdx/InlineMath'
import { Prose } from '@/components/mdx/Prose'
import { LeanCode } from './LeanHighlight'
import { SORT_LABELS, parseRecord } from './utils'

/** LeanNets record renderer — parses JSON record and renders sort/source/title/notes/content/state. */
export function RecordRenderer({ record, color, entryId, projectPath }: {
    record: string; color: string; entryId?: string; projectPath?: string
}) {
    const parsed = parseRecord(record)

    // Find proofs for this statement via edges (frontend lookup)
    const [proofHashes, setProofHashes] = useState<string[]>([])
    const isMergeOn = usePluginStore(s => (s as any).mnMergeProofs || false)
    const isAtom = parsed && parsed.sort !== 'proof'

    useEffect(() => {
        if (!isMergeOn || !isAtom || !entryId || !projectPath) { setProofHashes([]); return }
        fetch(`${API_BASE}/api/astrolabe/entries?path=${encodeURIComponent(projectPath)}&degree=1`)
            .then(r => r.ok ? r.json() : {})
            .then(edges => {
                const pHashes: string[] = []
                for (const [, edge] of Object.entries(edges) as [string, any][]) {
                    if (edge.ref[0] === entryId) {
                        try {
                            const s = JSON.parse(edge.record).sort || ''
                            if (s.endsWith(', proof)')) pHashes.push(edge.ref[1])
                        } catch {}
                    }
                }
                setProofHashes(pHashes)
            })
            .catch(() => setProofHashes([]))
    }, [isMergeOn, isAtom, entryId, projectPath])

    if (!parsed || typeof parsed !== 'object') {
        return <div className="text-white/50">{record || '—'}</div>
    }

    const { sort, source, title, notes, content, state, key } = parsed
    // Derived project-wide number ("§.item" from first occurrence) — never stored.
    const number = useViewStore(s => entryId ? s.getNumber(entryId) : undefined)
    const sortLabel = sort ? (SORT_LABELS[sort] || sort) : ''
    const numberDisplay = sortLabel && number ? `${sortLabel} ${number}` : number ? `[${number}]` : null

    return (
        <div style={{ display: 'flex', flexDirection: 'column', gap: '0.4em' }}>
            {/* number + sort + source badges */}
            <div className="flex items-center flex-wrap" style={{ gap: '0.4em' }}>
                {numberDisplay && <span className="rounded font-semibold" style={{ padding: '0.1em 0.4em', fontSize: '0.8em', backgroundColor: `${color}20`, color }}>{numberDisplay}</span>}
                {sort && !number && <span className="rounded font-medium" style={{ padding: '0.1em 0.4em', fontSize: '0.8em', backgroundColor: `${color}20`, color }}>{sort}</span>}
                {source && <span className="rounded bg-white/5 text-white/30" style={{ padding: '0.1em 0.4em', fontSize: '0.8em' }}>{source}</span>}
                {state && (
                    <span className={`rounded font-medium ${state === 'proven' ? 'bg-green-500/10 text-green-400' : 'bg-red-500/10 text-red-400'}`} style={{ padding: '0.1em 0.4em', fontSize: '0.8em' }}>
                        {state}
                    </span>
                )}
                {key && <span className="rounded bg-white/5 text-white/40 font-mono" style={{ padding: '0.1em 0.4em', fontSize: '0.8em' }}>{key}</span>}
            </div>

            {/* title */}
            {title && <div className="font-medium text-white/80" style={{ fontSize: '1.1em' }}>{title}</div>}

            {/* notes — render LaTeX + entryref, keeping paragraphs/lists */}
            {notes && (
                <div className="text-white/60 leading-relaxed">
                    <Prose>{notes}</Prose>
                </div>
            )}

            {/* content — only lean atoms carry a separate code body; for tex/bib
                `content` IS the prose, already rendered above via notes. */}
            {content && source === 'lean' && <LeanCode>{content}</LeanCode>}

            {/* Lean source — marker (file:line) + fetch the real .lean lines on demand */}
            {source === 'lean' && (parsed as any).path && (
                <LeanSource
                    path={(parsed as any).path}
                    line={(parsed as any).line ?? 1}
                    file={(parsed as any).file}
                    state={state}
                />
            )}

            {/* nested proofs (when merge is on, found via edges) */}
            {proofHashes.length > 0 && <NestedProofs proofHashes={proofHashes} />}
        </div>
    )
}

/** A Lean-backed node's source location: shows `file:line` (colored by proof
 *  state) and, on click, fetches and displays the actual `.lean` source. */
function LeanSource({ path, line, file, state }: {
    path: string; line: number; file?: string; state?: string
}) {
    const [src, setSrc] = useState<string | null>(null)
    const [start, setStart] = useState(1)
    const [open, setOpen] = useState(false)
    const color = state === 'proven' ? '#4ade80' : state === 'sorry' ? '#f59e0b' : '#669aba'

    const toggle = () => {
        if (src !== null) { setOpen(o => !o); return }
        fetch(`${API_BASE}/api/file?path=${encodeURIComponent(path)}&line=${line}&context=14`)
            .then(r => (r.ok ? r.json() : null))
            .then(d => { if (d?.content != null) { setSrc(d.content); setStart(d.startLine ?? 1); setOpen(true) } })
            .catch(() => {})
    }

    return (
        <div style={{ marginTop: '0.5em' }}>
            <button
                onClick={toggle}
                className="inline-flex items-center rounded transition-colors hover:bg-white/5"
                style={{ fontSize: '0.78em', padding: '0.15em 0.5em', gap: '0.4em', color, border: `1px solid ${color}44` }}
            >
                <span>◆ Lean</span>
                <span className="font-mono text-white/45">{(file ?? 'source')}:{line}</span>
                <span className="text-white/30">{open ? '▾' : '▸'}</span>
            </button>
            {open && src != null && (
                <div style={{ marginTop: '0.4em' }}>
                    <LeanCode>{src}</LeanCode>
                    <div className="font-mono text-white/25" style={{ fontSize: '0.7em', marginTop: '0.2em' }}>
                        lines {start}–{start + Math.max(0, src.split('\n').length - 1)} · {path.split('/').pop()}
                    </div>
                </div>
            )}
        </div>
    )
}

function NestedProofs({ proofHashes }: { proofHashes: string[] }) {
    const [proofs, setProofs] = useState<Record<string, any>>({})
    const [open, setOpen] = useState(false)

    const projectPath = typeof window !== 'undefined'
        ? new URLSearchParams(window.location.search).get('path') || ''
        : ''

    useEffect(() => {
        if (!projectPath || proofHashes.length === 0) return
        Promise.all(proofHashes.map(h =>
            fetch(`${API_BASE}/api/astrolabe/entries/${h}?path=${encodeURIComponent(projectPath)}`)
                .then(r => r.ok ? r.json() : null)
                .then(e => {
                    if (!e?.record) return null
                    try { return [h, JSON.parse(e.record)] } catch { return null }
                })
                .catch(() => null)
        )).then(results => {
            const map: Record<string, any> = {}
            for (const r of results) if (r) map[r[0]] = r[1]
            setProofs(map)
        })
    }, [proofHashes, projectPath])

    if (Object.keys(proofs).length === 0) return null

    return (
        <div className="border-l border-white/10" style={{ marginTop: '0.3em', paddingLeft: '0.5em' }}>
            <button
                onClick={() => setOpen(!open)}
                className="text-white/30 hover:text-white/50 flex items-center"
                style={{ fontSize: '0.8em', gap: '0.3em' }}
            >
                <span>{open ? '▾' : '▸'}</span>
                <span>Proof ({Object.keys(proofs).length})</span>
            </button>
            {open && Object.entries(proofs).map(([h, p]) => (
                <div key={h} style={{ marginTop: '0.3em' }}>
                    {p.source && <span className="rounded bg-white/5 text-white/25" style={{ fontSize: '0.75em', padding: '0.1em 0.3em', marginRight: '0.3em' }}>{p.source}</span>}
                    {p.notes && (
                        <div className="text-white/50 leading-relaxed" style={{ marginTop: '0.25em' }}>
                            <InlineMath>{p.notes}</InlineMath>
                        </div>
                    )}
                    {p.content && p.source === 'lean' && (
                        <div style={{ marginTop: '0.25em' }}><LeanCode>{p.content}</LeanCode></div>
                    )}
                </div>
            ))}
        </div>
    )
}
