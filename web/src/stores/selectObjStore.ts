/**
 * selectObjStore — obj（节点）选中状态
 *
 * 纯选中状态，不含渲染行为（相机跳转等由 NetworkView 自行处理）。
 *
 * 写入者（调用 select）：
 *   - NetworkView:  点击 3D 节点
 *   - CardStack:    点击卡片
 *   - ReadView:     点击 objref/objblock
 *
 * 读取者（订阅 selectedHash）：
 *   - CardStack:    滚动到选中卡片
 *   - NetworkView:  高亮节点 + 飞相机
 *   - DetailView:   显示 obj 详情
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
