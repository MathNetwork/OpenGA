'use client'

/**
 * DetailView — entry 详情展示
 *
 * 订阅 selectObjStore.selectedHash，渲染对应的 EntryDetail。
 * 不区分 atom/edge/simplex，统一展示 ref + record。
 */
import { memo } from 'react'
import { useSelectObjStore } from '@/stores/selectObjStore'
import { EntryDetail } from './EntryDetail'

export const DetailView = memo(function DetailView() {
    const selectedHash = useSelectObjStore(s => s.selectedHash)

    if (!selectedHash) {
        return (
            <div className="h-full flex items-center justify-center">
                <div className="text-center text-white/20">
                    <div className="text-3xl mb-2">◇</div>
                    <div className="text-xs">Select an entry</div>
                </div>
            </div>
        )
    }

    return (
        <div className="h-full overflow-y-auto">
            <EntryDetail id={selectedHash} />
        </div>
    )
})
