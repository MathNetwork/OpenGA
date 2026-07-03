'use client'

import { useState, useEffect, useContext } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { API_BASE } from '@/lib/apiBase'
import { getEntryColor, onColorsUpdated } from '@/lib/entryColor'
import { usePluginStore } from '@/plugins/registry'
import { EntriesContext } from './EntriesContext'

export function EntryBlock({ id, collapsible, number, children: nested }: { id?: string; collapsible?: string; number?: string; children?: any }) {
    const ctxEntries = useContext(EntriesContext)
    // The store's record for this hash, per the latest pre-loaded snapshot.
    // Seeding from this lets the card render fully on first paint (no async
    // placeholder → no reflow → no scroll drift).
    const ctxRecord = (id && ctxEntries?.[id]?.record) || null
    const [record, setRecord] = useState<string | null>(ctxRecord)
    const [, rerender] = useState(0)
    const selectObj = useSelectObjStore(s => s.select)
    const isCollapsible = collapsible === 'true' || collapsible === ''
    const [open, setOpen] = useState(false)

    const projectPath = typeof window !== 'undefined'
        ? new URLSearchParams(window.location.search).get('path') || ''
        : ''

    // Subscribed (not getState()) so toggling the plugin re-renders mounted cards.
    const PluginRenderer = usePluginStore(s => s.getEntryBlockRenderer())

    useEffect(() => onColorsUpdated(() => rerender(n => n + 1)), [])

    // Always track the latest context record — so a re-registration (records
    // change while the component stays mounted) never leaves a stale card.
    useEffect(() => {
        if (ctxRecord != null) setRecord(ctxRecord)
    }, [ctxRecord])

    // Fall back to a fetch only when the store wasn't pre-loaded by the host.
    useEffect(() => {
        if (record !== null || ctxRecord != null || !id || !projectPath) return
        fetch(`${API_BASE}/api/astrolabe/entries/${id}?path=${encodeURIComponent(projectPath)}`)
            .then(r => r.ok ? r.json() : null)
            .then(data => { if (data?.record != null) setRecord(data.record) })
            .catch(() => {})
    }, [id, projectPath, ctxRecord, record])

    if (record === null) {
        return <div className="my-2 text-xs text-white/20 font-mono">entry: {id || '?'}</div>
    }

    const color = getEntryColor(id || '', record)

    if (PluginRenderer) {
        return (
            <PluginRenderer
                hash={id || ''}
                record={record}
                color={color}
                number={number}
                collapsible={isCollapsible}
            >
                {nested}
            </PluginRenderer>
        )
    }

    // Raw fallback: no record parsing
    const showBody = !isCollapsible || open
    return (
        <div className="my-3 pl-3 rounded-r" style={{ borderLeftColor: color, borderLeftWidth: 2, opacity: 0.9 }}>
            <div className="text-xs font-semibold mb-1 flex items-center gap-1" style={{ color }}>
                {isCollapsible && (
                    <button onClick={(e) => { e.stopPropagation(); setOpen(!open) }} className="text-white/30 hover:text-white/60 w-3">
                        {open ? '▾' : '▸'}
                    </button>
                )}
                <span className="cursor-pointer hover:opacity-80" onClick={(e) => { e.stopPropagation(); id && selectObj(id) }}>
                    {number && <span className="text-white/40 mr-1">[{number}]</span>}
                    <span className="font-mono text-white/25">{id}</span>
                </span>
            </div>
            {showBody && (
                <>
                    <div className="text-white/50 text-xs font-mono whitespace-pre-wrap">{record}</div>
                    {nested}
                </>
            )}
        </div>
    )
}
