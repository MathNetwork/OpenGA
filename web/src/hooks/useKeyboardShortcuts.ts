/**
 * useKeyboardShortcuts — global keyboard shortcuts
 *
 *   Cmd+1/2/3      — switch Read/Network/Detail (forces single layout,
 *                    where activeTab is the visible view)
 *   Escape         — deselect
 */
import { useEffect } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { useViewStore, type ViewTab } from '@/stores/viewStore'

export function useKeyboardShortcuts() {
    useEffect(() => {
        const showTab = (tab: ViewTab) => {
            const view = useViewStore.getState()
            view.setActiveTab(tab)
            if (view.layoutMode !== 'single') view.setLayoutMode('single')
        }
        const handler = (e: KeyboardEvent) => {
            const meta = e.metaKey || e.ctrlKey

            if (meta && e.key === '1') { e.preventDefault(); showTab('read') }
            if (meta && e.key === '2') { e.preventDefault(); showTab('network') }
            if (meta && e.key === '3') { e.preventDefault(); showTab('detail') }

            if (e.key === 'Escape') {
                useSelectObjStore.getState().select(null)
            }
        }
        window.addEventListener('keydown', handler)
        return () => window.removeEventListener('keydown', handler)
    }, [])
}
