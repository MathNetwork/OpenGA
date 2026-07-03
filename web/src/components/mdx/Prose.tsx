'use client'

import ReactMarkdown from 'react-markdown'
import remarkGfm from 'remark-gfm'
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'
import rehypeRaw from 'rehype-raw'
import { preprocess } from './preprocess'
import { EntryLink } from './EntryLink'
import { useViewStore } from '@/stores/viewStore'

function extractText(node: any): string {
    if (typeof node === 'string') return node
    if (Array.isArray(node)) return node.map(extractText).join('')
    if (node?.props?.children) return extractText(node.props.children)
    return ''
}

// Block-level renderer: keeps paragraphs / lists (unlike InlineMath, which
// flattens <p> for inline use). Used to render a node's `notes` — a full do
// Carmo statement with paragraphs, numbered lists and display math.
const components: any = {
    p: ({ children }: any) => <p className="mb-2 leading-relaxed last:mb-0">{children}</p>,
    ul: ({ children }: any) => <ul className="list-disc list-inside mb-2 space-y-0.5">{children}</ul>,
    ol: ({ children }: any) => <ol className="list-decimal list-inside mb-2 space-y-0.5">{children}</ol>,
    li: ({ children }: any) => <li>{children}</li>,
    strong: ({ children }: any) => <strong className="font-semibold text-white/90">{children}</strong>,
    em: ({ children }: any) => <em className="italic">{children}</em>,
    blockquote: ({ children }: any) => <blockquote className="border-l-2 border-white/20 pl-3 italic mb-2">{children}</blockquote>,
    span: ({ node, children, ...props }: any) => {
        const entryId = node?.properties?.dataEntry
        if (entryId) {
            const number = node?.properties?.dataNumber
            const auto = node?.properties?.dataAuto === 'true'
            return <EntryLink id={entryId} number={number} auto={auto}>{children}</EntryLink>
        }
        return <span {...props}>{children}</span>
    },
}

/** Render a block of text (a node's notes) with KaTeX math, lists, paragraphs
 *  and `\entryref` links. */
export function Prose({ children }: { children: any }) {
    const numbering = useViewStore(s => s.numbering)
    const text = preprocess(extractText(children), numbering)
    return (
        <ReactMarkdown
            remarkPlugins={[remarkGfm, remarkMath]}
            rehypePlugins={[rehypeRaw, rehypeKatex]}
            components={components}
        >
            {text}
        </ReactMarkdown>
    )
}
