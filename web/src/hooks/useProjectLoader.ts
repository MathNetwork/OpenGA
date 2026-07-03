/**
 * useProjectLoader — 加载项目数据到 dataStore
 *
 * 从后端 API 加载 graph (nodes/links) 和文件树。
 */
import { useEffect, useRef, useState } from 'react'
import { useDataStore } from '@/stores/dataStore'
import { useViewStore } from '@/stores/viewStore'
import { useFileWatcher } from './useFileWatcher'
import { initPlugins } from '@/plugins/init'
import { buildProjectNumbering } from '@/components/mdx/numbering'

import { API_BASE } from '@/lib/apiBase'

// Register plugins once
initPlugins()

export function useProjectLoader(projectPath: string | null) {
    useFileWatcher(projectPath)
    const [loading, setLoading] = useState(false)
    const hasLoadedRef = useRef(false)
    const setObjects = useDataStore(s => s.setObjects)
    const setProjectFiles = useDataStore(s => s.setProjectFiles)
    const refreshTrigger = useDataStore(s => s.refreshTrigger)

    useEffect(() => {
        if (!projectPath) return
        let cancelled = false

        if (!hasLoadedRef.current) setLoading(true)

        const safeFetch = <T,>(url: string, fallback: T): Promise<T> =>
            fetch(url)
                .then(r => { if (!r.ok) throw new Error(r.statusText); return r.json() })
                .catch(() => fallback)

        const p = encodeURIComponent(projectPath)
        Promise.all([
            safeFetch(`${API_BASE}/api/astrolabe/ref-graph?path=${p}`, { nodes: [], links: [] }),
            safeFetch(`${API_BASE}/api/project/files?path=${p}`, []),
        ]).then(([graph, projectFiles]) => {
            if (cancelled) return
            setObjects((graph as any).nodes || [])
            if (Array.isArray(projectFiles)) {
                setProjectFiles(projectFiles)
            }
            setLoading(false)
            hasLoadedRef.current = true
        })

        return () => { cancelled = true }
    }, [projectPath, setObjects, refreshTrigger])

    // Build the project-wide DERIVED numbering: read every chapter doc and
    // assign each card a "§.item" from where it first appears. Rebuilds on any
    // store/file change so reordering a card re-numbers it everywhere.
    useEffect(() => {
        if (!projectPath) return
        let cancelled = false
        const p = encodeURIComponent(projectPath)
        const json = <T,>(url: string, fallback: T): Promise<T> =>
            fetch(url).then(r => r.ok ? r.json() : fallback).catch(() => fallback)

        Promise.all([
            json<{ files?: { path: string; name: string }[] }>(`${API_BASE}/api/docs/list?path=${p}`, {}),
            json<Record<string, { record: string }>>(`${API_BASE}/api/astrolabe/entries?path=${p}`, {}),
        ]).then(async ([list, entries]) => {
            const files = list.files || []
            const docs = await Promise.all(files.map(async f => ({
                filename: f.name,
                content: (await json<{ content?: string }>(`${API_BASE}/api/docs/read?path=${p}&file=${encodeURIComponent(f.name)}`, {})).content || '',
            })))
            if (cancelled) return
            useViewStore.getState().setNumbering(buildProjectNumbering(docs, entries))
        })

        return () => { cancelled = true }
    }, [projectPath, refreshTrigger])

    return { loading }
}
