'use client'

import ReactMarkdown from 'react-markdown'
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

const components: any = {
    p: ({ children }: any) => <>{children}</>,
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

/** Render text with KaTeX math + entrylinks. Used inside EntryBlock. */
export function InlineMath({ children }: { children: any }) {
    const numbering = useViewStore(s => s.numbering)
    const text = preprocess(extractText(children), numbering)
    return (
        <ReactMarkdown
            remarkPlugins={[remarkMath]}
            rehypePlugins={[rehypeRaw, rehypeKatex]}
            components={components}
        >
            {text}
        </ReactMarkdown>
    )
}
