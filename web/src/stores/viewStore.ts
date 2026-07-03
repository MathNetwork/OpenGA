import { create } from 'zustand'
import type { Numbering } from '@/components/mdx/numbering'

export type LayoutMode = 'single' | 'split-right' | 'split-left' | 'split-bottom' | 'split-top' | 'three-equal'
export type ViewTab = 'read' | 'network' | 'detail'

interface ViewState {
  layoutMode: LayoutMode
  showLabels: boolean
  activeTab: ViewTab
  fontSize: number  // global font size multiplier (10-20, default 14)
  numbering: Numbering  // project-wide hash → { chapter, num }, derived from first occurrence
  explorerOpen: boolean         // Explorer: whole left panel expanded (default collapsed)
  explorerPluginsOpen: boolean  // Explorer: PLUGINS section expanded
  explorerFilesOpen: boolean    // Explorer: FILES section expanded
  setExplorerOpen: (open: boolean) => void
  setExplorerPluginsOpen: (open: boolean) => void
  setExplorerFilesOpen: (open: boolean) => void
  setLayoutMode: (mode: LayoutMode) => void
  toggleLabels: () => void
  setActiveTab: (tab: ViewTab) => void
  setFontSize: (size: number) => void
  increaseFontSize: () => void
  decreaseFontSize: () => void
  setNumbering: (map: Numbering) => void
  getNumber: (hash: string) => string | undefined
}

export const useViewStore = create<ViewState>((set, get) => ({
  layoutMode: 'split-right',
  showLabels: false,
  activeTab: 'read',
  fontSize: 14,
  numbering: new Map(),
  explorerOpen: false,
  explorerPluginsOpen: false,
  explorerFilesOpen: true,
  setExplorerOpen: (open) => set({ explorerOpen: open }),
  setExplorerPluginsOpen: (open) => set({ explorerPluginsOpen: open }),
  setExplorerFilesOpen: (open) => set({ explorerFilesOpen: open }),
  setLayoutMode: (mode) => set({ layoutMode: mode }),
  toggleLabels: () => set((s) => ({ showLabels: !s.showLabels })),
  setActiveTab: (tab) => set({ activeTab: tab }),
  setFontSize: (size) => set({ fontSize: Math.max(10, Math.min(24, size)) }),
  increaseFontSize: () => set((s) => ({ fontSize: Math.min(24, s.fontSize + 1) })),
  decreaseFontSize: () => set((s) => ({ fontSize: Math.max(10, s.fontSize - 1) })),
  setNumbering: (map) => set({ numbering: map }),
  getNumber: (hash) => get().numbering.get(hash)?.num,
}))
