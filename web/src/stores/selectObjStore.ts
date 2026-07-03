/**
 * selectObjStore — obj（节点）选中状态
 *
 * 纯选中状态，不含渲染行为（相机跳转等由 NetworkView 自行处理）。
 *
 * 写入者（调用 select）：
 *   - NetworkView:              点击 2D canvas 节点
 *   - EntryBlock / EntryLink:   文档里点击 entryblock/entryref
 *   - EntryDetail / DetailEdges: 详情面板里点击引用跳转
 *   - useKeyboardShortcuts:     Esc 清除选中
 *
 * 读取者（订阅 selectedHash）：
 *   - NetworkView:  高亮选中节点
 *   - DetailView:   渲染选中 entry 的详情（EntryDetail）
 */
import { create } from 'zustand'

interface SelectObjState {
  selectedHash: string | null
  select: (hash: string | null) => void
}

export const useSelectObjStore = create<SelectObjState>()(
    (set) => ({
        selectedHash: null,
        select: (hash) => set({ selectedHash: hash }),
    })
)
