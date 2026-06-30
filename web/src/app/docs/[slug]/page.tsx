import fs from 'fs'
import path from 'path'
import { notFound } from 'next/navigation'
import { compileMDX } from 'next-mdx-remote/rsc'
import remarkGfm from 'remark-gfm'
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'
import 'katex/dist/katex.min.css'
import { Navbar } from '@/components/Navbar'
import { DocsShell, type TocItem } from '@/components/DocsShell'
import { StorageTree, NumberingFlow, AtomExample, EdgeExample } from '@/components/mdx/DataModelDiagrams'
import { DOCS } from '@/lib/docs'

export function generateStaticParams() {
  return DOCS.map((d) => ({ slug: d.slug }))
}

const slug = (s: string) => s.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '')
const textOf = (c: any): string =>
  Array.isArray(c) ? c.map(textOf).join('') : typeof c === 'string' ? c : c?.props?.children ? textOf(c.props.children) : ''

// MDX element overrides — the project's dark documentation style.
const components = {
  h1: ({ children }: any) => <h1 id={slug(textOf(children))} className="text-4xl font-bold tracking-[0.03em] text-white/90 mb-8 mt-1 scroll-mt-20">{children}</h1>,
  h2: ({ children }: any) => <h2 id={slug(textOf(children))} className="text-xl font-semibold text-white/85 mt-14 mb-3 scroll-mt-20">{children}</h2>,
  h3: ({ children }: any) => <h3 id={slug(textOf(children))} className="text-base font-medium text-white/80 mt-8 mb-2 scroll-mt-20">{children}</h3>,
  p: ({ children }: any) => {
    // A References entry starts with its citation key, e.g. "[Lam12] …".
    // Give it an id so inline citation marks can jump straight to it.
    const m = textOf(children).match(/^\s*\[([A-Za-z0-9+]+)\]/)
    const id = m ? `ref-${m[1].toLowerCase()}` : undefined
    return <p id={id} className={`text-[15px] leading-relaxed text-white/55 mb-4${id ? ' scroll-mt-24' : ''}`}>{children}</p>
  },
  ul: ({ children }: any) => <ul className="list-disc list-inside text-[15px] text-white/55 mb-4 space-y-1">{children}</ul>,
  ol: ({ children }: any) => <ol className="text-[15px] text-white/55 mb-4 space-y-2 list-none">{children}</ol>,
  li: ({ children }: any) => <li>{children}</li>,
  strong: ({ children }: any) => <strong className="text-white/80 font-medium">{children}</strong>,
  em: ({ children }: any) => <em className="italic text-white/45">{children}</em>,
  a: ({ href, children }: any) => {
    const h = typeof href === 'string' ? href : ''
    // Citation mark: paper-style [Key] that jumps to the References entry. No
    // underline; bracketed and muted, like a bibliography reference.
    if (h.startsWith('#ref-')) {
      return (
        <a href={h} className="text-[#e67e22] hover:text-[#ff6b35] no-underline whitespace-nowrap transition-colors">[{children}]</a>
      )
    }
    const inPage = h.startsWith('/') || h.startsWith('#')
    return (
      <a href={h} {...(inPage ? {} : { target: '_blank', rel: 'noopener noreferrer' })}
        className="text-white/70 hover:text-white underline decoration-white/20 hover:decoration-white/50 underline-offset-2 transition-colors">{children}</a>
    )
  },
  hr: () => <hr className="border-white/10 my-10" />,
  code: ({ children }: any) => <code className="text-cyan-300/80 bg-white/[0.06] px-1.5 py-0.5 rounded text-[13px] font-mono">{children}</code>,
  StorageTree,
  NumberingFlow,
  AtomExample,
  EdgeExample,
}

function parseToc(src: string): TocItem[] {
  return src.split('\n').filter((l) => /^#{2,3}\s/.test(l)).map((l) => {
    const level = (l.match(/^#+/) as RegExpMatchArray)[0].length
    const text = l.replace(/^#+\s+/, '').replace(/[*`_]/g, '')
    return { level, text, id: slug(text) }
  })
}

export default async function Page({ params }: { params: Promise<{ slug: string }> }) {
  const { slug: s } = await params
  const doc = DOCS.find((d) => d.slug === s)
  if (!doc) notFound()

  const source = fs.readFileSync(path.join(process.cwd(), `content/${doc.slug}.mdx`), 'utf8')
  const { content } = await compileMDX({
    source,
    components,
    options: { mdxOptions: { remarkPlugins: [remarkGfm, remarkMath], rehypePlugins: [rehypeKatex as any] } },
  })

  return (
    <div className="h-screen flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 overflow-y-auto">
        <DocsShell docs={DOCS} current={doc.slug} toc={parseToc(source)}>
          <p className="text-xs uppercase tracking-[0.2em] text-white/30 mb-3">{doc.eyebrow}</p>
          {content}
        </DocsShell>
      </main>
    </div>
  )
}
