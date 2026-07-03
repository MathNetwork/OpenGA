import type { Numbering } from './numbering'

/** Convert LaTeX macros to HTML tags before Markdown rendering.
 *
 * Supported:
 *   \entryref{hash}{text (may contain $math{braces}$)}  → inline entry link
 *   \entryblock{hash}                                    → entry block
 *   \entryblock{hash}{collapsible}                       → collapsible entry block
 *   \entryblock{hash}{ ...children... }                  → nested block
 *
 * If a numbering map is provided, data-number / data-chapter attributes are
 * added so the renderer can show the derived "Sort N.M [of Chapter C]".
 */
export function preprocess(content: string, numbering?: Numbering): string {
    let result = processEntryRefs(content, numbering)
    result = processEntryBlocks(result, numbering)
    // \status → a live formalization-status block (rendered from the in-memory store)
    result = result.replace(/\\status\b/g, '<div data-status="true"></div>')
    // data-model schematic diagrams
    result = result.replace(/\\storageTree\b/g, '<div data-storage-tree="true"></div>')
    result = result.replace(/\\atomExample\b/g, '<div data-atom-example="true"></div>')
    result = result.replace(/\\edgeExample\b/g, '<div data-edge-example="true"></div>')
    result = result.replace(/\\numberingFlow\b/g, '<div data-numbering-flow="true"></div>')
    return result
}

/** ` data-number="2.8" data-chapter="7"` for a hash, or '' if unnumbered. */
function numAttrs(hash: string, numbering?: Numbering): string {
    const e = numbering?.get(hash)
    return e ? ` data-number="${e.num}" data-chapter="${e.chapter}"` : ''
}

/** Find the index of the closing } that matches the { at position pos. */
function findMatchingBrace(input: string, pos: number): number {
    if (input[pos] !== '{') return -1
    let depth = 1
    for (let i = pos + 1; i < input.length; i++) {
        if (input[i] === '{') depth++
        else if (input[i] === '}') {
            depth--
            if (depth === 0) return i
        }
    }
    return -1
}

function processEntryRefs(input: string, numbering?: Numbering): string {
    let result = ''
    let i = 0
    const tag = '\\entryref{'

    while (i < input.length) {
        const idx = input.indexOf(tag, i)
        if (idx === -1) { result += input.slice(i); break }

        result += input.slice(i, idx)

        // Parse first arg: hash
        const hashStart = idx + tag.length
        const hashEnd = findMatchingBrace(input, hashStart - 1)
        if (hashEnd === -1) { result += input.slice(idx); break }
        const hash = input.slice(hashStart, hashEnd)

        // Check for optional second arg: text (with brace matching)
        const textBrace = hashEnd + 1
        const numAttr = numAttrs(hash, numbering)

        if (textBrace >= input.length || input[textBrace] !== '{') {
            // Single-arg: \entryref{hash} → auto mode (no display text)
            result += `<span data-entry="${hash}" data-auto="true"${numAttr}></span>`
            i = hashEnd + 1
            continue
        }
        const textEnd = findMatchingBrace(input, textBrace)
        if (textEnd === -1) { result += input.slice(idx); break }
        const text = input.slice(textBrace + 1, textEnd)

        // Two-arg: \entryref{hash}{text} → manual mode
        result += `<span data-entry="${hash}"${numAttr}>${text}</span>`
        i = textEnd + 1
    }

    return result
}

function processEntryBlocks(input: string, numbering?: Numbering): string {
    let result = ''
    let i = 0
    const tag = '\\entryblock{'

    while (i < input.length) {
        const idx = input.indexOf(tag, i)
        if (idx === -1) { result += input.slice(i); break }

        result += input.slice(i, idx)

        // Parse first arg: hash
        const hashStart = idx + tag.length
        const hashEnd = findMatchingBrace(input, hashStart - 1)
        if (hashEnd === -1) { result += input.slice(idx); break }
        const hash = input.slice(hashStart, hashEnd)

        const numAttr = numAttrs(hash, numbering)

        // Check for second arg
        let afterHash = hashEnd + 1
        while (afterHash < input.length && ' \n\r'.includes(input[afterHash])) afterHash++

        if (afterHash >= input.length || input[afterHash] !== '{') {
            result += `<div data-entry="${hash}"${numAttr}></div>`
            i = hashEnd + 1
        } else {
            const bodyEnd = findMatchingBrace(input, afterHash)
            if (bodyEnd === -1) { result += input.slice(idx); break }
            const body = input.slice(afterHash + 1, bodyEnd).trim()

            if (body === 'collapsible') {
                result += `<div data-entry="${hash}" data-collapsible="true"${numAttr}></div>`
            } else {
                result += `<div data-entry="${hash}"${numAttr}>\n${processEntryBlocks(body, numbering)}\n</div>`
            }
            i = bodyEnd + 1
        }
    }

    return result
}
