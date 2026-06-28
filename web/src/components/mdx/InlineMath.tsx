'use client'

import ReactMarkdown from 'react-markdown'
import remarkMath from 'remark-math'
import rehypeRaw from 'rehype-raw'
import { preprocess } from './preprocess'
import { katexWith } from './katexOptions'
import { EntryLink } from './EntryLink'
import { useViewStore } from '@/stores/viewStore'
import { useDataStore } from '@/stores/dataStore'

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
            const chapter = node?.properties?.dataChapter
            const auto = node?.properties?.dataAuto === 'true'
            return <EntryLink id={entryId} number={number} chapter={chapter} auto={auto}>{children}</EntryLink>
        }
        return <span {...props}>{children}</span>
    },
}

/** Render text with KaTeX math + entrylinks. Used inside EntryBlock. */
export function InlineMath({ children }: { children: any }) {
    const numbering = useViewStore(s => s.numbering)
    const macros = useDataStore(s => s.katexMacros)
    const text = preprocess(extractText(children), numbering)
    return (
        <ReactMarkdown
            remarkPlugins={[remarkMath]}
            rehypePlugins={[rehypeRaw, katexWith(macros)]}
            components={components}
        >
            {text}
        </ReactMarkdown>
    )
}
