// The documentation registry — one entry per MDX file in `web/content/<section>/`.
// Drives the dynamic /docs/[slug] route and the left "Documentation" nav,
// which groups entries by `section`.
export interface DocMeta {
  slug: string // file is content/<section>/<slug>.mdx (section lowercased)
  title: string
  eyebrow: string
  section: 'About' | 'Docs'
}

export const DOCS: DocMeta[] = [
  {
    slug: 'challenge',
    title: 'Open Questions',
    eyebrow: 'Open Questions',
    section: 'About',
  },
  {
    slug: 'data-model',
    title: 'Astrolabe: Data Model',
    eyebrow: 'How the knowledge is stored',
    section: 'Docs',
  },
  {
    slug: 'authoring',
    title: 'Writing with Cards',
    eyebrow: 'Documents, entryblock & entryref',
    section: 'Docs',
  },
  {
    slug: 'numbering',
    title: 'Derived Numbering',
    eyebrow: 'Positional coordinates, never stored',
    section: 'Docs',
  },
]
