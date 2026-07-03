'use client'

import { useSelectObjStore } from '@/stores/selectObjStore'
import { SORT_LABELS, parseRecord } from './utils'

export function LeanNetsEntryRef({ hash, record, color, number, displayText }: {
    hash: string; record: string; color: string; number?: string; displayText?: string
}) {
    const selectObj = useSelectObjStore(s => s.select)

    // Manual mode: \entryref{hash}{text} — use displayText as-is
    // Auto mode: \entryref{hash} — derived "Sort chapter.section.item" (the
    // chapter prefix makes it self-describing, so no "of Chapter C" suffix).
    let text = displayText
    if (!text) {
        const parsed = parseRecord(record)
        const label = parsed ? (SORT_LABELS[parsed.sort] || parsed.sort || '') : ''
        if (number) {
            text = label ? `${label} ${number}` : number
        } else if (parsed?.title) {
            text = parsed.title
        } else {
            text = hash.slice(0, 8)
        }
    }

    return (
        <span
            className="cursor-pointer hover:opacity-70 underline decoration-dotted underline-offset-2"
            style={{ color }}
            onClick={(e) => { e.stopPropagation(); selectObj(hash) }}
            title={`entry: ${hash}`}
        >
            {text}
        </span>
    )
}
