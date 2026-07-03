/** Shared sort label mapping for LeanNets plugin. */
export const SORT_LABELS: Record<string, string> = {
    definition: 'Definition', theorem: 'Theorem', lemma: 'Lemma',
    proposition: 'Proposition', corollary: 'Corollary', proof: 'Proof',
    citation: 'Citation',
}

/** Parse record JSON string. Returns parsed object or null. */
export function parseRecord(record: string): Record<string, any> | null {
    try { return JSON.parse(record) } catch { return null }
}
