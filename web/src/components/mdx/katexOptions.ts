import rehypeKatex from 'rehype-katex'
import type { Pluggable } from 'unified'

/**
 * Build the rehype-katex plugin entry with a project's custom macro table.
 *
 * The macros come from `.astrolabe/katex-macros.json` (produced by
 * tools/tex2mdx.py) so MDX can keep source macros like `\Ar`, `\eps` verbatim
 * and KaTeX resolves them at render time. We hand KaTeX a *copy* of the table
 * because it mutates `macros` in place (e.g. caching `\gdef`s), and the table
 * lives in a shared store.
 */
export function katexWith(macros: Record<string, string>): Pluggable {
  return [rehypeKatex, { macros: { ...macros }, strict: false, throwOnError: false }]
}
