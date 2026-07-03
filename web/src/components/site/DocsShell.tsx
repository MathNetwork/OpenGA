'use client'

import { useState, useEffect } from 'react'
import Link from 'next/link'
import type { DocMeta } from '@/lib/docs'

export interface TocItem { level: number; text: string; id: string }

/** Three-column documentation shell: left master TOC (all docs + the current
 *  doc's sections), MDX content, right on-this-page TOC. Dark project aesthetic. */
export function DocsShell({
  docs, current, toc, children,
}: {
  docs: DocMeta[]
  current: string
  toc: TocItem[]
  children: React.ReactNode
}) {
  const sections = toc.filter((t) => t.level === 2)
  const [active, setActive] = useState('')

  useEffect(() => {
    const obs = new IntersectionObserver(
      (entries) => entries.forEach((e) => { if (e.isIntersecting) setActive((e.target as HTMLElement).id) }),
      { rootMargin: '0px 0px -78% 0px', threshold: 0 },
    )
    toc.forEach((t) => { const el = document.getElementById(t.id); if (el) obs.observe(el) })
    return () => obs.disconnect()
  }, [toc])

  return (
    <div className="flex max-w-7xl mx-auto w-full">
      {/* left — master TOC: docs grouped by section, current doc's headings inline */}
      <nav className="hidden lg:block w-60 shrink-0 sticky top-0 self-start max-h-[calc(100vh-3.5rem)] overflow-y-auto px-6 py-12 border-r border-white/5">
        {[...new Set(docs.map((d) => d.section))].map((group) => (
          <div key={group} className="mb-8 last:mb-0">
            <div className="text-[10px] uppercase tracking-[0.2em] text-white/25 mb-4">{group}</div>
            <ul className="space-y-2 text-[13px]">
              {docs.filter((d) => d.section === group).map((d) => (
                <li key={d.slug}>
                  <Link
                    href={`/docs/${d.slug}`}
                    className={`block font-medium transition-colors ${d.slug === current ? 'text-white/85' : 'text-white/45 hover:text-white/70'}`}
                  >
                    {d.title}
                  </Link>
                  {d.slug === current && sections.length > 0 && (
                    <ul className="mt-1.5 ml-2 space-y-1 border-l border-white/10">
                      {sections.map((s) => (
                        <li key={s.id}>
                          <a
                            href={`#${s.id}`}
                            className={`block pl-3 -ml-px border-l transition-colors ${active === s.id ? 'border-white/60 text-white/80' : 'border-transparent text-white/35 hover:text-white/60'}`}
                          >
                            {s.text}
                          </a>
                        </li>
                      ))}
                    </ul>
                  )}
                </li>
              ))}
            </ul>
          </div>
        ))}
      </nav>

      {/* center — MDX content */}
      <article className="flex-1 min-w-0 px-8 lg:px-14 py-14 max-w-2xl">{children}</article>

      {/* right — on this page */}
      <nav className="hidden xl:block w-56 shrink-0 sticky top-0 self-start max-h-[calc(100vh-3.5rem)] overflow-y-auto px-6 py-12">
        <div className="text-[10px] uppercase tracking-[0.2em] text-white/25 mb-4">On this page</div>
        <ul className="space-y-1.5 text-[13px]">
          {toc.map((t) => (
            <li key={t.id} className={t.level === 3 ? 'pl-3' : ''}>
              <a href={`#${t.id}`} className={`block transition-colors ${active === t.id ? 'text-white/80' : 'text-white/30 hover:text-white/55'}`}>{t.text}</a>
            </li>
          ))}
        </ul>
      </nav>
    </div>
  )
}
