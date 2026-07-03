/**
 * physicsStore — 2D 力导向图的物理参数
 *
 * 所有值都是正数，越大效果越强，符合直觉。
 *
 * 订阅者：
 *   - NetworkView: 控制节点布局的物理引擎参数
 *   - NetworkSettings: UI 滑块调整参数
 */
import { create } from 'zustand'

interface PhysicsState {
  gravity: number       // 0-100, 中心引力强度（0=自由漂浮，100=强力聚拢）
  repulsion: number     // 10-500, 节点间斥力
  linkDistance: number   // 5-100, 边的目标长度
  friction: number      // 0-100, 运动摩擦力（0=无摩擦滑冰，100=高粘度）

  setGravity: (v: number) => void
  setRepulsion: (v: number) => void
  setLinkDistance: (v: number) => void
  setFriction: (v: number) => void
}

export const usePhysicsStore = create<PhysicsState>()(
    (set) => ({
        gravity: 50,
        repulsion: 100,
        linkDistance: 30,
        friction: 40,

        setGravity: (v) => set({ gravity: v }),
        setRepulsion: (v) => set({ repulsion: v }),
        setLinkDistance: (v) => set({ linkDistance: v }),
        setFriction: (v) => set({ friction: v }),
    })
)
