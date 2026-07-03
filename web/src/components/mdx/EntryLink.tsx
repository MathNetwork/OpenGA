'use client'

import { useState, useEffect, useContext } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { API_BASE } from '@/lib/apiBase'
import { getEntryColor, onColorsUpdated } from '@/lib/entryColor'
import { usePluginStore } from '@/plugins/registry'
import { EntriesContext } from './EntriesContext'

export function EntryLink({ id, number, auto, children }: { id: string; number?: string; auto?: boolean; children?: any }) {
    const ctxEntries = useContext(EntriesContext)
    const ctxRecord = (id && ctxEntries?.[id]?.record) || null
    const [color, setColor] = useState('#888')
    const [record, setRecord] = useState<string | null>(ctxRecord)
    const selectObj = useSelectObjStore(s => s.select)

    const projectPath = typeof window !== 'undefined'
        ? new URLSearchParams(window.location.search).get('path') || ''
        : ''

    // Keep record in sync with the pre-loaded store (no per-link fetch reflow).
    useEffect(() => { if (ctxRecord != null) setRecord(ctxRecord) }, [ctxRecord])

    const updateColor = () => {
        if (!id) return
        const c = getEntryColor(id, record || undefined)
        if (c !== '#888888') setColor(c)
        if (record !== null || ctxRecord != null || !projectPath) return
        fetch(`${API_BASE}/api/astrolabe/entries/${id}?path=${encodeURIComponent(projectPath)}`)
            .then(r => r.ok ? r.json() : null)
            .then(data => {
                if (!data?.record) return
                setColor(getEntryColor(id, data.record))
                setRecord(data.record)
            })
            .catch(() => {})
    }

    useEffect(updateColor, [id, projectPath, record])
    useEffect(() => onColorsUpdated(updateColor), [id, projectPath])

    // Manual mode: \entryref{hash}{text} — children contains the display text
    const displayText = !auto && children ? (typeof children === 'string' ? children : undefined) : undefined

    // Subscribed (not getState()) so toggling the plugin re-renders mounted links.
    const PluginRenderer = usePluginStore(s => s.getEntryRefRenderer())
    if (PluginRenderer && (record !== null || auto)) {
        return (
            <PluginRenderer
                hash={id}
                record={record || ''}
                color={color}
                number={number}
                displayText={displayText}
            />
        )
    }

    // Raw fallback
    let fallbackText: string
    if (!auto && children) {
        fallbackText = typeof children === 'string' ? children : id.slice(0, 8)
    } else if (number) {
        fallbackText = `[${number}]`
    } else {
        fallbackText = id.slice(0, 8)
    }

    return (
        <span
            className="cursor-pointer hover:opacity-70 underline decoration-dotted underline-offset-2"
            style={{ color }}
            onClick={(e) => { e.stopPropagation(); selectObj(id) }}
            title={`entry: ${id}`}
        >
            {fallbackText}
        </span>
    )
}
