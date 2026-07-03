/**
 * useKeyboardShortcuts — global keyboard shortcuts
 *
 *   Cmd+1/2/3      — switch Read/Network/Detail
 *   Escape         — deselect
 */
import { useEffect } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { useViewStore } from '@/stores/viewStore'

export function useKeyboardShortcuts() {
    useEffect(() => {
        const handler = (e: KeyboardEvent) => {
            const meta = e.metaKey || e.ctrlKey

            if (meta && e.key === '1') { e.preventDefault(); useViewStore.getState().setActiveTab('read') }
            if (meta && e.key === '2') { e.preventDefault(); useViewStore.getState().setActiveTab('network') }
            if (meta && e.key === '3') { e.preventDefault(); useViewStore.getState().setActiveTab('detail') }

            if (e.key === 'Escape') {
                useSelectObjStore.getState().select(null)
            }
        }
        window.addEventListener('keydown', handler)
        return () => window.removeEventListener('keydown', handler)
    }, [])
}
