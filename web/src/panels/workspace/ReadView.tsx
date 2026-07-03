'use client'

/**
 * ReadView — MDX rendered viewer
 *
 * Left: chapter list; the selected chapter expands into its §section / numbered-
 * statement outline (clickable, scrolls the content).
 * Right: rendered markdown with KaTeX math.
 */
import { useState, useEffect, useRef, useMemo } from 'react'
import { API_BASE } from '@/lib/apiBase'
import { useViewStore } from '@/stores/viewStore'
import { useReadStore } from '@/stores/readStore'
import MarkdownRenderer from '@/components/MarkdownRenderer'
import type { Numbering } from '@/components/mdx/numbering'
import { ChevronDoubleLeftIcon, ChevronDoubleRightIcon } from '@heroicons/react/24/outline'

interface DocFile {
    name: string
    path: string
    title: string
}

interface Outline {
    level: number          // 2 = §section, 3 = statement
    text: string
    hash?: string          // statement → scroll to its [data-entry] card
    h2index?: number       // §section → scroll to the n-th <h2>
}

const cap = (s: string) => s ? s.charAt(0).toUpperCase() + s.slice(1) : ''

/** Build the chapter outline: `## …` §-sections plus each `\entryblock{hash}`
 *  statement (labelled "Sort N.M (title)" — number is the DERIVED one). */
function parseOutline(
    content: string,
    entries?: Record<string, { record: string }>,
    numbering?: Numbering,
): Outline[] {
    const out: Outline[] = []
    let h2i = -1
    for (const line of content.split('\n')) {
        const sec = line.match(/^##\s+(.+?)\s*$/)
        if (sec) {
            h2i++
            out.push({ level: 2, h2index: h2i, text: sec[1].replace(/\$([^$]*)\$/g, '$1').replace(/[*_`]/g, '') })
            continue
        }
        const eb = line.match(/^\\entryblock\{([0-9a-f]+)\}/)
        if (eb && entries?.[eb[1]]) {
            try {
                const r = JSON.parse(entries[eb[1]].record)
                const num = numbering?.get(eb[1])?.num || ''
                const label = `${cap(r.sort)} ${num}${r.title ? ` (${r.title})` : ''}`.trim()
                out.push({ level: 3, hash: eb[1], text: label })
            } catch { /* skip unparseable */ }
        }
    }
    return out
}

export function ReadView() {
    const [files, setFiles] = useState<DocFile[]>([])
    // Selected doc lives in a store (not local state) so switching panes/layout
    // — which unmounts ReadView — never resets which chapter is open.
    const selected = useReadStore(s => s.selectedDoc)
    const setSelected = useReadStore(s => s.setSelectedDoc)
    const sidebarOpen = useReadStore(s => s.sidebarOpen)
    const setSidebarOpen = useReadStore(s => s.setSidebarOpen)
    const [content, setContent] = useState('')
    const [entries, setEntries] = useState<Record<string, { record: string }> | undefined>(undefined)
    const fontSize = useViewStore(s => s.fontSize)
    const contentRef = useRef<HTMLDivElement>(null)

    const projectPath = typeof window !== 'undefined'
        ? new URLSearchParams(window.location.search).get('path') || ''
        : ''

    const numbering = useViewStore(s => s.numbering)
    const headings = useMemo(() => parseOutline(content, entries, numbering), [content, entries, numbering])

    // Load file list
    useEffect(() => {
        if (!projectPath) return
        fetch(`${API_BASE}/api/docs/list?path=${encodeURIComponent(projectPath)}`)
            .then(r => r.json())
            .then(data => {
                const f = data.files || []
                setFiles(f)
                if (f.length > 0 && !selected) setSelected(f[0].path)
            })
            .catch(() => {})
    }, [projectPath])

    // Load entry records (for the outline labels + each card). Re-pull on file
    // switch too, so a re-registration is picked up without a full page reload.
    useEffect(() => {
        if (!projectPath) return
        fetch(`${API_BASE}/api/astrolabe/entries?path=${encodeURIComponent(projectPath)}`)
            .then(r => r.ok ? r.json() : {})
            .then(setEntries)
            .catch(() => setEntries({}))
    }, [projectPath, selected])

    // NB: selecting a content-address (clicking a card title or \entryref) only
    // updates the card/Detail window — it deliberately does NOT scroll the main
    // document. Reading position is decoupled from selection; only the outline
    // (below) moves the document, on explicit navigation.

    // Load selected file content. `selected` is the doc's absolute path (docs
    // dir is flat), so its basename is the docs-relative name the API takes.
    useEffect(() => {
        if (!selected || !projectPath) return
        const file = selected.split('/').pop() || ''
        fetch(`${API_BASE}/api/docs/read?path=${encodeURIComponent(projectPath)}&file=${encodeURIComponent(file)}`)
            .then(r => r.json())
            .then(d => setContent(d?.content || ''))
            .catch(() => setContent('Failed to load'))
    }, [selected, projectPath])

    // Restore the saved scroll position after content renders (so a remount —
    // pane/layout switch — lands you back where you were, not at the top).
    useEffect(() => {
        if (!content) return
        const saved = useReadStore.getState().scrollTop
        const id = requestAnimationFrame(() => {
            if (contentRef.current) contentRef.current.scrollTop = saved
        })
        return () => cancelAnimationFrame(id)
    }, [content])

    // Scroll WITHIN the content pane only (never scrollIntoView, which also
    // scrolls window ancestors and pushes the top bar out of view).
    const scrollToEl = (el: Element | null | undefined, gap = 8) => {
        const root = contentRef.current
        if (!root || !el) return
        const top = el.getBoundingClientRect().top - root.getBoundingClientRect().top + root.scrollTop - gap
        root.scrollTo({ top, behavior: 'smooth' })
    }

    const scrollToOutline = (o: Outline) => {
        const root = contentRef.current
        if (!root) return
        scrollToEl(o.hash
            ? root.querySelector(`[data-entry="${o.hash}"]`)
            : root.querySelectorAll('h2')[o.h2index ?? 0])
    }

    return (
        <div className="h-full flex">
            {/* Collapsed: a thin strip to reopen the contents sidebar. */}
            {!sidebarOpen && (
                <button
                    onClick={() => setSidebarOpen(true)}
                    title="Show contents"
                    className="w-7 shrink-0 border-r border-white/5 flex items-start justify-center pt-2.5 text-white/30 hover:text-white/70 hover:bg-white/5 transition-colors"
                >
                    <ChevronDoubleRightIcon className="w-3.5 h-3.5" />
                </button>
            )}
            {/* Chapter list + per-chapter outline */}
            <div className={`${sidebarOpen ? 'w-56' : 'hidden'} shrink-0 border-r border-white/5 overflow-y-auto`}>
                <div className="flex items-center justify-between pl-3 pr-1.5 py-1.5 border-b border-white/5">
                    <span className="text-[10px] uppercase tracking-wider text-white/25">Contents</span>
                    <button
                        onClick={() => setSidebarOpen(false)}
                        title="Collapse"
                        className="p-1 text-white/30 hover:text-white/70 rounded hover:bg-white/5 transition-colors"
                    >
                        <ChevronDoubleLeftIcon className="w-3.5 h-3.5" />
                    </button>
                </div>
                {files.length === 0 ? (
                    <div className="p-3 text-xs text-white/20">No docs</div>
                ) : (
                    files.map(f => (
                        <div key={f.path}>
                            <button
                                onClick={() => setSelected(f.path)}
                                className={`w-full text-left px-3 py-2 text-xs truncate transition-colors ${
                                    selected === f.path
                                        ? 'bg-white/10 text-white/80 font-medium'
                                        : 'text-white/40 hover:text-white/60 hover:bg-white/5'
                                }`}
                            >
                                {f.name}
                            </button>
                            {selected === f.path && headings.length > 0 && (
                                <div className="pb-1">
                                    {headings.map((h, i) => (
                                        <button
                                            key={i}
                                            onClick={() => scrollToOutline(h)}
                                            className={`block w-full text-left truncate transition-colors hover:text-white/70 ${
                                                h.level === 2
                                                    ? 'pl-4 pr-2 py-0.5 text-[11px] text-white/55'
                                                    : 'pl-7 pr-2 py-0.5 text-[10px] text-white/35'
                                            }`}
                                            title={h.text}
                                        >
                                            {h.text}
                                        </button>
                                    ))}
                                </div>
                            )}
                        </div>
                    ))
                )}
            </div>
            {/* Rendered content */}
            <div
                ref={contentRef}
                className="flex-1 overflow-auto p-6"
                style={{ fontSize }}
                onScroll={(e) => useReadStore.getState().setScrollTop((e.target as HTMLDivElement).scrollTop)}
            >
                {content && entries !== undefined ? (
                    <MarkdownRenderer content={content} entries={entries} />
                ) : (
                    <div className="text-xs text-white/20">{content ? 'Loading…' : 'Select a file'}</div>
                )}
            </div>
        </div>
    )
}
