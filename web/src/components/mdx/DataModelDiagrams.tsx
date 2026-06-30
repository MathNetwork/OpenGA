// Hand-authored schematic diagrams for the docs — pure presentational, no deps.
// Styled to the site: monochrome + hairlines, mono cyan for hashes, the Astrolabe
// orange for assigned numbers. Used from MDX via the route's components map.

const Hash = ({ children }: { children: React.ReactNode }) => (
  <span className="text-cyan-300/80">{children}</span>
)
const Num = ({ children }: { children: React.ReactNode }) => (
  <span className="text-[#e67e22]">{children}</span>
)
const Dim = ({ children }: { children: React.ReactNode }) => (
  <span className="text-white/30">{children}</span>
)

/** The one-file-per-node storage layout. */
export function StorageTree() {
  return (
    <figure className="my-8">
      <pre className="rounded-lg border border-white/10 bg-white/[0.02] p-5 text-[13px] leading-relaxed font-mono text-white/55 overflow-x-auto">
        <div><Dim>.astrolabe/</Dim></div>
        <div>├─ atoms/</div>
        <div>│  ├─ <Hash>38c99016b279</Hash>.md{'   '}<Dim>← one file per node</Dim></div>
        <div>│  └─ <Hash>097d60abf481</Hash>.md</div>
        <div>├─ edges/</div>
        <div>│  └─ <Hash>014c1e2a49fe</Hash>.md{'   '}<Dim>← a (lean, tex) bridge</Dim></div>
        <div>└─ docs/</div>
        <div>{'   '}├─ 00-index.mdx</div>
        <div>{'   '}└─ 03-geodesics.mdx{'  '}<Dim>composes nodes by hash</Dim></div>
      </pre>
      <figcaption className="mt-2 text-[13px] text-white/35">
        Every node is a single file named by its hash; documents only reference them.
      </figcaption>
    </figure>
  )
}

/** One row of an entry: a fixed-width key and its value, at an indent depth. */
function Field({ k, v, depth = 0 }: { k: string; v: React.ReactNode; depth?: number }) {
  const pad = depth >= 2 ? 'pl-10' : depth === 1 ? 'pl-5' : ''
  return (
    <div className={`flex gap-2 ${pad}`}>
      <span className="w-14 shrink-0 text-white/35">{k}</span>
      <span className="text-white/65 min-w-0 break-words">{v}</span>
    </div>
  )
}

/** Render record fields, descending into a nested group when the value is an array. */
function renderFields(entries: any[], depth: number): React.ReactNode {
  return entries.map(([k, v]) =>
    Array.isArray(v) ? (
      <div key={k}>
        <div className={`${depth >= 2 ? 'pl-10' : 'pl-5'} text-white/35`}>{k}</div>
        {renderFields(v, depth + 1)}
      </div>
    ) : (
      <Field key={k} k={k} v={v} depth={depth} />
    ),
  )
}

/** An entry in the canonical (hash, ref, record) shape — everything but ref and
 *  hash lives, layered, inside record. */
function NodeEntry({ hash, refs, record }: { hash: string; refs: string[]; record: any[] }) {
  const badge = refs.length === 1 ? 'self-reference → atom' : refs.length === 2 ? 'two atoms → edge' : ''
  return (
    <figure className="my-5">
      <div className="rounded-lg border border-white/10 bg-white/[0.02] p-4 text-[12px] font-mono leading-relaxed">
        <Field k="hash" v={<Hash>{hash}</Hash>} />
        <Field k="ref" v={<>[ <Hash>{refs.join(', ')}</Hash> ]{badge && <Dim>{'  ← '}{badge}</Dim>}</>} />
        <div className="text-white/35 mt-0.5">record</div>
        {renderFields(record, 1)}
      </div>
    </figure>
  )
}

/** A real atom from the Riemannian Geometry project. */
export function AtomExample() {
  return (
    <NodeEntry
      hash="38c99016b279"
      refs={['38c99016b279']}
      record={[
        ['sort', <>(ref[0].source)<Dim>{'  = (tex)'}</Dim></>],
        ['source', 'tex'],
        ['content', [
          ['title', 'Geodesic sphere'],
          ['notes', String.raw`$S_\delta = \exp_p(\{v : \lVert v\rVert = \delta\})$`],
        ]],
      ]}
    />
  )
}

/** A real (lean, tex) cross-source edge. */
export function EdgeExample() {
  return (
    <NodeEntry
      hash="014c1e2a49fe"
      refs={['264fbf8cb406', '6e6c552589c3']}
      record={[
        ['sort', <>(ref[0].source, ref[1].source)<Dim>{'  = (lean, tex)'}</Dim></>],
        ['rel', 'formalizes'],
      ]}
    />
  )
}

/** How a hash gets its derived number from its first appearance in a document. */
export function NumberingFlow() {
  const rows: [string, string, string][] = [
    ['a1f3c9e2', 'Definition', '3.2.1'],
    ['9c2e0f81', 'Theorem', '3.2.2'],
    ['4e7d22b0', 'Corollary', '3.2.3'],
  ]
  return (
    <figure className="my-8">
      <div className="rounded-lg border border-white/10 bg-white/[0.02] p-5 text-[13px] font-mono">
        <div className="flex items-center gap-2 mb-4 text-white/45">
          03-geodesics.mdx <Dim>→ chapter 3</Dim>
        </div>
        <div className="space-y-2.5">
          {rows.map(([h, kind, n]) => (
            <div key={h} className="flex items-center gap-3 whitespace-nowrap">
              <Hash>{h}…</Hash>
              <Dim>{kind} · first appears</Dim>
              <span className="text-white/25">→</span>
              <Num>{n}</Num>
            </div>
          ))}
          <div className="flex items-center gap-3 whitespace-nowrap pt-1.5 border-t border-white/[0.07]">
            <Hash>a1f3c9e2…</Hash>
            <Dim>appears again</Dim>
            <span className="text-white/25">→</span>
            <Num>3.2.1</Num>
            <Dim>(same hash, same number)</Dim>
          </div>
        </div>
      </div>
      <figcaption className="mt-2 text-[13px] text-white/35">
        The number is assigned on first occurrence and follows the hash — never stored,
        always consistent within the project.
      </figcaption>
    </figure>
  )
}
