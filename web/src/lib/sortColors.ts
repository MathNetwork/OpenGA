/**
 * Auto-assign colors from sort strings. Deterministic: same sort → same color.
 * Derived sorts "(a, b)" blend the two atomic colors.
 */

const _cache: Record<string, string> = {}

function hash(s: string): number {
    let h = 0
    for (let i = 0; i < s.length; i++) h = ((h << 5) - h + s.charCodeAt(i)) | 0
    return Math.abs(h)
}

function hsl2hex(h: number, s: number, l: number): string {
    const f = (n: number) => {
        const k = (n + h / 30) % 12
        const a = s * Math.min(l, 1 - l)
        return Math.round((l - a * Math.max(-1, Math.min(k - 3, 9 - k, 1))) * 255)
    }
    return '#' + [f(0), f(8), f(4)].map(v => v.toString(16).padStart(2, '0')).join('')
}

function atomicColor(sort: string): string {
    if (_cache[sort]) return _cache[sort]
    const h = hash(sort)
    // 高饱和、中等亮度 → 鲜艳不透灰。
    const color = hsl2hex(h % 360, (72 + (h >> 8) % 23) / 100, (50 + (h >> 16) % 12) / 100)
    _cache[sort] = color
    return color
}

function hexToRgb(hex: string): [number, number, number] {
    const h = hex.slice(1)
    return [parseInt(h.slice(0, 2), 16), parseInt(h.slice(2, 4), 16), parseInt(h.slice(4, 6), 16)]
}

function blendHex(a: string, b: string): string {
    const [r1, g1, b1] = hexToRgb(a), [r2, g2, b2] = hexToRgb(b)
    return '#' + [r1 + r2, g1 + g2, b1 + b2].map(v => (v >> 1).toString(16).padStart(2, '0')).join('')
}

/** Get hex fill color for any sort (atomic or derived "(a, b)"). */
export function getSortFill(sort: string): string {
    if (_cache[sort]) return _cache[sort]
    const m = sort.match(/^\((.+),\s*(.+)\)$/)
    if (m) {
        const color = blendHex(atomicColor(m[1]), atomicColor(m[2]))
        _cache[sort] = color
        return color
    }
    return atomicColor(sort)
}

/** Get inline styles for EntryBlock. */
export function getSortStyle(sort: string): { fill: string; borderStyle: Record<string, any>; textStyle: Record<string, any> } {
    const fill = getSortFill(sort)
    return { fill, borderStyle: { borderLeftColor: fill, borderLeftWidth: 2, opacity: 0.7 }, textStyle: { color: fill } }
}

/** Parse sort from a JSON record string. */
export function parseSortFromRecord(record: string): string {
    try { return JSON.parse(record).sort || '' } catch { return '' }
}
