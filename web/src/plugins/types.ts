import type { ReactNode } from 'react'

export interface AstrolabePlugin {
    id: string
    name: string
    description: string

    /** Additional section rendered in DetailView when an entry is selected. */
    DetailSection?: React.FC<{ entryId: string }>

    /** Plugin-provided record renderer. Core uses this instead of raw JSON display. */
    RecordRenderer?: React.FC<{ record: string; color: string; entryId?: string; projectPath?: string }>

    /** Network mode configuration. When present, Core shows a mode toggle button. */
    networkMode?: {
        label: string
        /** API endpoint for skeleton/network graph data */
        endpoint: string
    }

    /** Settings panel shown when this plugin's network mode is active. */
    SettingsPanel?: React.FC<{}>

    /** Renders an \entryblock{hash} in documentation. */
    EntryBlockRenderer?: React.FC<{
        hash: string
        record: string
        color: string
        number?: string
        collapsible?: boolean
        children?: React.ReactNode
    }>

    /** Renders an \entryref{hash}{text} inline link in documentation. */
    EntryRefRenderer?: React.FC<{
        hash: string
        record: string
        color: string
        number?: string
        displayText?: string
    }>
}
