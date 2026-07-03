'use client'

import '@/lib/errorSuppression'
import { Suspense, useCallback, useEffect, useState } from 'react'
import { Bars3BottomLeftIcon, MinusIcon, PlusIcon, HomeIcon } from '@heroicons/react/24/outline'
import { API_BASE } from '@/lib/apiBase'
import { ThemeToggle } from '@/components/site/ThemeToggle'
import { useViewStore } from '@/stores/viewStore'
import { useSearchParams, useRouter } from 'next/navigation'
import { useProjectLoader } from '@/hooks/useProjectLoader'
import { useKeyboardShortcuts } from '@/hooks/useKeyboardShortcuts'
import { ExplorerPanel } from '@/panels/explorer/ExplorerPanel'
import { WorkspacePanel } from '@/panels/workspace/WorkspacePanel'

function EditorPage() {
    const searchParams = useSearchParams()
    const router = useRouter()
    const projectPath = searchParams.get('path')

    const { loading } = useProjectLoader(projectPath)
    useKeyboardShortcuts()

    // Project display title: the index doc's top-level heading (e.g. "Riemannian
    // Geometry Challenge"), falling back to the title-cased folder name.
    const titleCase = (s: string) => s.split(/[-_]/).map(w => w.charAt(0).toUpperCase() + w.slice(1)).join(' ')
    const [title, setTitle] = useState('')
    useEffect(() => {
        if (!projectPath) return
        const p = encodeURIComponent(projectPath)
        fetch(`${API_BASE}/api/docs/list?path=${p}`)
            .then(r => r.json())
            .then(d => {
                const first = (d.files || [])[0]
                if (!first) return
                return fetch(`${API_BASE}/api/docs/read?path=${p}&file=${encodeURIComponent(first.name)}`).then(r => r.json())
            })
            .then(d => {
                const m = d?.content?.match(/^#\s+(.+?)\s*$/m)
                if (m) setTitle(m[1].trim())
            })
            .catch(() => {})
    }, [projectPath])

    // Explorer open/closed is single-sourced in viewStore (no panel-library state).
    const explorerOpen = useViewStore(s => s.explorerOpen)
    const setExplorerOpen = useViewStore(s => s.setExplorerOpen)
    const toggleExplorer = useCallback(() => setExplorerOpen(!explorerOpen), [explorerOpen, setExplorerOpen])

    if (!projectPath) {
        return <div className="h-screen flex items-center justify-center bg-black text-white/40">No project selected</div>
    }

    if (loading) {
        return (
            <div className="h-screen flex flex-col items-center justify-center bg-black text-white/40 gap-3">
                <div className="w-6 h-6 border-2 border-white/20 border-t-white/60 rounded-full animate-spin" />
                <span className="text-sm">Loading...</span>
            </div>
        )
    }

    return (
        <div className="h-screen flex flex-col bg-black text-white">
            <div className="h-10 flex items-center px-4 border-b border-white/10 shrink-0 relative">
                <div className="flex items-center gap-2">
                    <button onClick={toggleExplorer} className="p-1.5 text-white/30 hover:text-white/70 transition-colors rounded hover:bg-white/5" title="Toggle Explorer">
                        <Bars3BottomLeftIcon className="w-4 h-4" />
                    </button>
                    <button onClick={() => router.push('/')} className="p-1.5 text-white/30 hover:text-white/70 transition-colors rounded hover:bg-white/5" title="Home">
                        <HomeIcon className="w-4 h-4" />
                    </button>
                </div>
                <span className="absolute left-1/2 -translate-x-1/2 text-sm font-medium text-white/70 pointer-events-none truncate max-w-[50%]">
                    {title || titleCase(projectPath.split('/').pop() || '')}
                </span>
                <div className="flex items-center gap-1 ml-auto">
                    <button onClick={() => useViewStore.getState().decreaseFontSize()} className="p-1 text-white/30 hover:text-white/70 transition-colors rounded hover:bg-white/5" title="Decrease font size">
                        <MinusIcon className="w-3 h-3" />
                    </button>
                    <FontSizeDisplay />
                    <button onClick={() => useViewStore.getState().increaseFontSize()} className="p-1 text-white/30 hover:text-white/70 transition-colors rounded hover:bg-white/5" title="Increase font size">
                        <PlusIcon className="w-3 h-3" />
                    </button>
                    <ThemeToggle className="p-1 ml-1 text-white/30 hover:text-white/70 transition-colors rounded hover:bg-white/5" />
                </div>
            </div>

            <div className="flex-1 flex overflow-hidden">
                {explorerOpen && (
                    <div className="w-64 shrink-0 overflow-hidden border-r border-white/10">
                        <ExplorerPanel />
                    </div>
                )}
                <div className="flex-1 min-w-0">
                    <WorkspacePanel />
                </div>
            </div>
        </div>
    )
}

function FontSizeDisplay() {
    const fontSize = useViewStore(s => s.fontSize)
    return <span className="text-[10px] text-white/20 w-4 text-center">{fontSize}</span>
}

export default function Page() {
    return (
        <Suspense fallback={<div className="h-screen bg-black" />}>
            <EditorPage />
        </Suspense>
    )
}
