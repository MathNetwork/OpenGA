'use client'

/** Lean formalization badge — ∀ symbol indicating formal counterpart exists. */
export function LeanBadge({ interactive, state, onClick }: {
    interactive?: boolean
    state?: 'proven' | 'sorry' | string
    onClick?: () => void
}) {
    const bg = state === 'sorry' ? 'bg-yellow-500/20' : state === 'proven' ? 'bg-green-500/20' : 'bg-green-500/15'
    const fg = state === 'sorry' ? 'text-yellow-400' : 'text-green-400'
    const hover = interactive ? 'hover:bg-green-500/30 cursor-pointer' : ''

    return (
        <span
            className={`inline-flex items-center justify-center rounded font-bold ${bg} ${fg} ${hover} select-none`}
            style={{ fontSize: '0.75em', padding: '0 0.3em' }}
            onClick={interactive ? (e) => { e.stopPropagation(); onClick?.() } : undefined}
            title={interactive ? 'Show Lean formalization' : 'Lean source'}
        >
            ∀
        </span>
    )
}
