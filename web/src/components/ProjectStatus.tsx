'use client'

import { useDataStore } from '@/stores/dataStore'

interface LeanRec { name?: string; title?: string; sort?: string; state?: string; file?: string; line?: number }

/** Live formalization status for the current project, computed from the store
 *  already loaded in memory (no extra fetch). The single source of truth is each
 *  lean node's `state` field, so the numbers never go stale. Rendered in the
 *  project reader wherever the `\status` macro appears. */
export function ProjectStatus() {
  const objects = useDataStore((s) => s.objects)

  const lean: LeanRec[] = []
  for (const o of objects) {
    let r: LeanRec & { source?: string }
    try { r = JSON.parse(o.record) } catch { continue }
    if (r?.source !== 'lean') continue
    lean.push(r)
  }
  const open = lean
    .filter((r) => r.state === 'sorry')
    .sort((a, b) => (a.name || '').localeCompare(b.name || ''))

  return (
    <div className="my-4 rounded-lg border border-white/10 bg-white/[0.02] p-4">
      <div className="flex items-baseline gap-3 mb-3">
        <span className="text-[10px] uppercase tracking-[0.2em] text-white/30">Formalization status</span>
        <span className="inline-flex items-center gap-1.5 text-[10px] text-white/35">
          <span className="w-1 h-1 rounded-full bg-white/50" /> live
        </span>
      </div>

      <div className="flex mb-1">
        <div className="pr-8">
          <div className="text-2xl text-white/90 tabular-nums leading-none">{open.length}</div>
          <div className="text-[10px] uppercase tracking-[0.15em] text-white/30 mt-1.5">Open sorries</div>
        </div>
        <div className="px-8 border-l border-white/10">
          <div className="text-2xl text-white/90 tabular-nums leading-none">{lean.length}</div>
          <div className="text-[10px] uppercase tracking-[0.15em] text-white/30 mt-1.5">Declarations</div>
        </div>
      </div>

      <p className="text-[11px] leading-relaxed text-white/30 mt-3">
        Counts only what is written in Lean so far — a live tally of open
        <code className="mx-1 bg-white/10 text-cyan-400 px-1 py-0.5 rounded text-[10px] font-mono">sorry</code>s,
        not a completion percentage.
      </p>
    </div>
  )
}
