import { create } from 'zustand'

/** Ref-graph node as served by /api/astrolabe/ref-graph. */
export interface GraphNode {
  id: string
  degree: number
  stage: number
  record: string
}

export interface FileEntry {
  name: string
  type: 'file' | 'directory'
  path: string
  size?: number
  children?: FileEntry[]
}

interface DataState {
  objects: GraphNode[]
  projectFiles: FileEntry[]

  refreshTrigger: number

  setObjects: (objects: GraphNode[]) => void
  setProjectFiles: (files: FileEntry[]) => void
  triggerRefresh: () => void
}

export const useDataStore = create<DataState>((set) => ({
  objects: [],
  projectFiles: [],
  refreshTrigger: 0,

  setObjects: (objects) => set({ objects }),
  setProjectFiles: (files) => set({ projectFiles: files }),
  triggerRefresh: () => set((s) => ({ refreshTrigger: s.refreshTrigger + 1 })),
}))
