'use client'

/**
 * EntryDetail — entry viewer
 *
 * Shows hash, ref (clickable), and record. Colors match NetworkView via sortColors.
 */
import { memo, useEffect, useMemo, useState } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { API_BASE } from '@/lib/apiBase'
import { getEntryColor, onColorsUpdated } from '@/lib/entryColor'
import { usePluginStore } from '@/plugins/registry'
import { useViewStore } from '@/stores/viewStore'
import { InlineMath } from '@/components/mdx/InlineMath'

interface Entry {
    ref: string[]
    record: string
}

export const EntryDetail = memo(function EntryDetail({ id }: { id: string }) {
    // ── All hooks at top, unconditionally ──
    const fontSize = useViewStore(s => s.fontSize)
    const number = useViewStore(s => s.getNumber(id))
    const [entry, setEntry] = useState<Entry | null>(null)
    const [refColors, setRefColors] = useState<Record<string, string>>({})
    const [error, setError] = useState(false)
    const [, rerender] = useState(0)
    const selectObj = useSelectObjStore(s => s.select)

    useEffect(() => onColorsUpdated(() => rerender(n => n + 1)), [])

    const projectPath = typeof window !== 'undefined'
        ? new URLSearchParams(window.location.search).get('path') || ''
        : ''

    useEffect(() => {
        if (!id || !projectPath) return
        setError(false)
        setRefColors({})
        fetch(`${API_BASE}/api/astrolabe/entries/${id}?path=${encodeURIComponent(projectPath)}`)
            .then(r => {
                if (!r.ok) throw new Error(r.statusText)
                return r.json()
            })
            .then(setEntry)
            .catch(() => setError(true))
    }, [id, projectPath])

    useEffect(() => {
        if (!entry || !projectPath) return
        const refs = entry.ref.filter(h => h !== id)
        if (refs.length === 0) return
        Promise.all(refs.map(h => {
            const c = getEntryColor(h)
            if (c !== '#888888') return Promise.resolve([h, c] as const)
            return fetch(`${API_BASE}/api/astrolabe/entries/${h}?path=${encodeURIComponent(projectPath)}`)
                .then(r => r.ok ? r.json() : null)
                .then(e => [h, getEntryColor(h, e?.record)] as const)
                .catch(() => [h, '#888'] as const)
        })).then(pairs => setRefColors(Object.fromEntries(pairs)))
    }, [entry, id, projectPath])

    // ── Derived values (safe after all hooks) ──
    const sortColor = entry ? getEntryColor(id, entry.record) : '#888'
    // Subscribed (not getState()) so toggling the plugin re-renders the detail.
    const PluginRecordRenderer = usePluginStore(s => s.getRecordRenderer())
    const parsed = useMemo(() => {
        if (!entry) return null
        try { return JSON.parse(entry.record) as Record<string, string> } catch { return null }
    }, [entry])
    // ── Render ──
    if (error) {
        return <div className="text-white/30 font-mono" style={{ padding: '0.75em' }}>not found: {id}</div>
    }
    if (!entry) {
        return <div className="text-white/20 animate-pulse" style={{ padding: '0.75em' }}>loading...</div>
    }

    return (
        <div style={{ padding: '0.75em', borderLeft: `2px solid ${sortColor}40` }}>
            {/* hash + number + sort color dot */}
            <div className="font-mono text-white/25 flex items-center" style={{ gap: '0.5em', marginBottom: '0.5em' }}>
                <span className="inline-block rounded-full" style={{ width: '0.5em', height: '0.5em', backgroundColor: sortColor }} />
                {number && <span className="text-white/40" style={{ fontFamily: 'inherit' }}>[{number}]</span>}
                {id}
            </div>

            {/* ref */}
            <div style={{ marginBottom: '0.5em' }}>
                <Row label="ref">
                    <span className="font-mono">
                        [{entry.ref.map((hash, i) => {
                            const isSelf = hash === id
                            return (
                                <span key={i}>
                                    {i > 0 && ', '}
                                    {isSelf ? (
                                        <span className="text-white/25">self</span>
                                    ) : (
                                        <button
                                            onClick={() => selectObj(hash)}
                                            className="hover:opacity-80 cursor-pointer"
                                            style={{ color: refColors[hash] || '#888' }}
                                        >
                                            {hash}
                                        </button>
                                    )}
                                </span>
                            )
                        })}]
                    </span>
                </Row>
            </div>

            {/* record — plugin renders by convention, otherwise raw JSON */}
            <div style={{ fontSize }}>
            {PluginRecordRenderer
                ? <PluginRecordRenderer record={entry.record} color={sortColor} entryId={id} projectPath={projectPath} />
                : <Row label="record">
                    <span className="text-white/50 whitespace-pre-wrap break-all font-mono" style={{ fontSize: '0.85em' }}>
                        {(() => { try { return JSON.stringify(JSON.parse(entry.record), null, 2) } catch { return entry.record || '—' } })()}
                    </span>
                  </Row>
            }
            </div>

            {/* Plugin detail sections */}
            <PluginSections entryId={id} />
        </div>
    )
})

function PluginSections({ entryId }: { entryId: string }) {
    const plugins = usePluginStore(s => s.plugins)
    const enabled = usePluginStore(s => s.enabled)

    return <>
        {plugins.filter(p => enabled.has(p.id) && p.DetailSection).map(p => {
            const Section = p.DetailSection!
            return <Section key={p.id} entryId={entryId} />
        })}
    </>
}

function Row({ label, children }: { label: string; children: React.ReactNode }) {
    return (
        <div>
            <span className="text-white/30" style={{ marginRight: '0.5em' }}>{label}:</span>
            {children}
        </div>
    )
}
