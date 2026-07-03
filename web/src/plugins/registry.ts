import { create } from 'zustand'
import type { AstrolabePlugin } from './types'

interface PluginState {
    plugins: AstrolabePlugin[]
    enabled: Set<string>
    activeMode: Record<string, boolean>  // plugin id → mode active
    register: (plugin: AstrolabePlugin) => void
    toggle: (id: string) => void
    setMode: (id: string, active: boolean) => void
    isModeActive: (id: string) => boolean

    /** Returns the first enabled plugin that provides a RecordRenderer, or undefined. */
    getRecordRenderer: () => AstrolabePlugin['RecordRenderer']
    /** Returns the first enabled plugin that provides an EntryBlockRenderer, or undefined. */
    getEntryBlockRenderer: () => AstrolabePlugin['EntryBlockRenderer']
    /** Returns the first enabled plugin that provides an EntryRefRenderer, or undefined. */
    getEntryRefRenderer: () => AstrolabePlugin['EntryRefRenderer']
    /** Returns the networkMode config of the currently mode-active plugin, or undefined. */
    getActiveNetworkMode: () => (AstrolabePlugin['networkMode'] & { pluginId: string }) | undefined
    /** Returns the SettingsPanel of the currently mode-active plugin, or undefined. */
    getActiveSettingsPanel: () => AstrolabePlugin['SettingsPanel']
    /** Returns true if any plugin with networkMode is registered and enabled. */
    hasNetworkMode: () => boolean
    /** Returns true if any plugin's network mode is currently active. */
    isAnyModeActive: () => boolean
    /** Toggles the mode of the first plugin that has networkMode. */
    toggleNetworkMode: () => void
}

export const usePluginStore = create<PluginState>((set, get) => ({
    plugins: [],
    enabled: new Set(),
    activeMode: {},

    register: (plugin) => set(s => {
        if (s.plugins.some(p => p.id === plugin.id)) return s
        // Auto-enable plugins on registration
        const next = new Set(s.enabled)
        next.add(plugin.id)
        return { plugins: [...s.plugins, plugin], enabled: next }
    }),

    toggle: (id) => set(s => {
        const next = new Set(s.enabled)
        next.has(id) ? next.delete(id) : next.add(id)
        // Deactivate mode when plugin is disabled
        if (!next.has(id)) {
            const modes = { ...s.activeMode }
            delete modes[id]
            return { enabled: next, activeMode: modes }
        }
        return { enabled: next }
    }),

    setMode: (id, active) => set(s => ({
        activeMode: { ...s.activeMode, [id]: active }
    })),

    isModeActive: (id) => get().enabled.has(id) && (get().activeMode[id] ?? false),

    getRecordRenderer: () => {
        const { plugins, enabled } = get()
        const p = plugins.find(p => enabled.has(p.id) && p.RecordRenderer)
        return p?.RecordRenderer
    },

    getActiveNetworkMode: () => {
        const { plugins, enabled, activeMode } = get()
        const p = plugins.find(p => enabled.has(p.id) && p.networkMode && activeMode[p.id])
        return p?.networkMode ? { ...p.networkMode, pluginId: p.id } : undefined
    },

    getActiveSettingsPanel: () => {
        const { plugins, enabled, activeMode } = get()
        const p = plugins.find(p => enabled.has(p.id) && p.SettingsPanel && activeMode[p.id])
        return p?.SettingsPanel
    },

    hasNetworkMode: () => {
        const { plugins, enabled } = get()
        return plugins.some(p => enabled.has(p.id) && p.networkMode)
    },

    isAnyModeActive: () => {
        const { plugins, enabled, activeMode } = get()
        return plugins.some(p => enabled.has(p.id) && p.networkMode && activeMode[p.id])
    },

    toggleNetworkMode: () => {
        const { plugins, enabled, activeMode } = get()
        const p = plugins.find(p => enabled.has(p.id) && p.networkMode)
        if (p) {
            set({ activeMode: { ...activeMode, [p.id]: !activeMode[p.id] } })
        }
    },

    getEntryBlockRenderer: () => {
        const { plugins, enabled } = get()
        const p = plugins.find(p => enabled.has(p.id) && p.EntryBlockRenderer)
        return p?.EntryBlockRenderer
    },

    getEntryRefRenderer: () => {
        const { plugins, enabled } = get()
        const p = plugins.find(p => enabled.has(p.id) && p.EntryRefRenderer)
        return p?.EntryRefRenderer
    },
}))
