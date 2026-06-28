import { create } from 'zustand'

export interface KnowledgeObject {
  id: string
  name: string
  sort: string
  status: string
  statement?: string
  proof?: string
  intuition?: string
  notes?: string
  [key: string]: unknown
}

export interface KnowledgeMorphism {
  id: string
  source: string
  target: string
  sort?: string
  notes?: string
  strict?: boolean
  [key: string]: unknown
}

export interface FileEntry {
  name: string
  type: 'file' | 'directory'
  path: string
  size?: number
  children?: FileEntry[]
}

interface DataState {
  objects: KnowledgeObject[]
  morphisms: KnowledgeMorphism[]
  objectMap: Map<string, KnowledgeObject>
  projectFiles: FileEntry[]
  /** KaTeX macro table for the project (from .astrolabe/katex-macros.json). */
  katexMacros: Record<string, string>

  refreshTrigger: number

  setObjects: (objects: KnowledgeObject[]) => void
  setMorphisms: (morphisms: KnowledgeMorphism[]) => void
  setProjectFiles: (files: FileEntry[]) => void
  setKatexMacros: (macros: Record<string, string>) => void
  triggerRefresh: () => void
  getObjectById: (id: string) => KnowledgeObject | undefined
}

export const useDataStore = create<DataState>((set, get) => ({
  objects: [],
  morphisms: [],
  objectMap: new Map(),
  projectFiles: [],
  katexMacros: {},
  refreshTrigger: 0,

  setObjects: (objects) => {
    const objectMap = new Map(objects.map(o => [o.id, o]))
    set({ objects, objectMap })
  },
  setMorphisms: (morphisms) => set({ morphisms }),
  setProjectFiles: (files) => set({ projectFiles: files }),
  setKatexMacros: (macros) => set({ katexMacros: macros }),
  triggerRefresh: () => set((s) => ({ refreshTrigger: s.refreshTrigger + 1 })),
  getObjectById: (id) => get().objectMap.get(id),
}))
