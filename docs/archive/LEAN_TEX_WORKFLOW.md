# Lean ↔ tex formalization loop

The repeatable workflow for advancing the formal (Lean) side using the informal
(do Carmo tex) hypergraph as the blueprint, and using the formal side to repair
the informal one. One iteration closes the loop; repeat until Hopf–Rinow (and
beyond) is `sorry`-free.

```
            tools/lean_tex_audit.py
 ┌──────────────────┴───────────────────┐
 │  1. sorries   2. fruit   3. holes  4. under-linked │
 └──────────────────┬───────────────────┘
        pick the most-upstream gap
                    │
   ┌──── Lean side ─┴──── tex side ────┐
   │ formalize + lake build            │ repair holes (3) / link under-linked (4)
   │ wire import → extract → register  │   — see tools/tex_extract.py, edit edges
   │ → bridge → re-audit               │
   └───────────────────────────────────┘
```

## The loop, step by step

### 0. Audit — where are we?
```bash
python3 tools/lean_tex_audit.py
```
Prints four signals (see the script): **(1) Lean sorries** = open formal gaps,
**(2) low-hanging fruit** = tex statements whose prerequisites Lean already
covers, **(3) lean→tex holes** = dependencies Lean proves but tex omits,
**(4) under-linked tex** = long-but-sparsely-connected nodes (missed concepts).

Pick the **most upstream** item — the one nothing else depends on yet. The tex
hypergraph's dependency order (`Definition → Lemma → Theorem`, `Ch3 §3 → Ch7`)
is the build order.

### 1. Formalize (Lean side)
Write the proof in `OpenGALib/Riemannian/...`. Lean blocks already exist for most
of it — search Mathlib (`grep -rn ... .lake/packages/mathlib/Mathlib`) and the
repo before building from scratch; many lemmas are one `rw` away (e.g.
`SymmetryLemma` = Mathlib `second_derivative_symmetric` + repo
`chartChristoffelContraction_symm`). Verify incrementally with the LSP, then:
```bash
lake build OpenGALib.Riemannian.<Module>      # must be 0 errors, 0 sorry warnings
```

### 2. Wire into the import tree (only for a NEW file)
The extractor only sees `import`ed modules. Add the new module to **both**:
- `OpenGALib.lean`            (puts it in the closed-loop slice)
- `tools/ExtractLeanGraph.lean` import header

```bash
lake build OpenGALib                          # confirm the root still builds
```

### 3. Extract + register (Lean → store)
```bash
lake env lean tools/ExtractLeanGraph.lean     # → /tmp/lean_graph.json (all OpenGALib.* decls)
python3 tools/lean_register.py                 # update-only; identity hash H({source,name})
```
`lean_register.py` is idempotent: a fixed `sorry → proven` updates the same
node (hash unchanged), and Lean→Lean dependency edges are rebuilt. Tex nodes and
(lean, tex) bridges are untouched.

> The store is plain `.md` files; the tools read/write them via
> `tools/astrolabe_store.py` (system `python3`, no backend). The Next.js app only
> *reads* the store, so there are no concurrent writers to worry about.

### 4. Bridge (Lean ↔ tex)
Connect the new Lean node(s) to the do Carmo concept they formalize, as a binary
edge typed `(lean, tex)` with `rel: formalizes`. Definitions map by concept
cluster (geodesic/metric/manifold/Christoffel); a specific theorem maps by name
to its `dcref` (e.g. `covariant_sndFDeriv_symm ↔ ch3:3.4`). The shared `ref`
makes the tex card light its Lean badge. This is currently a short scripted
`s.create_entry([lean, tex], …)`; promote to `tools/lean_bridge.py` when the
mapping stabilises.

### 5. Re-audit
```bash
python tools/lean_tex_audit.py
```
A new lemma usually surfaces **new holes** (its dependencies the tex graph
omitted) and unlocks **new fruit** (statements now fully covered). Repair the
holes (`rel: uses`, `via: lean`) on the tex side, then go to step 0.

## Toolbox

| Tool | Side | Job |
|------|------|-----|
| `tools/ExtractLeanGraph.lean` | Lean | walk `OpenGALib.*` env → `/tmp/lean_graph.json` |
| `tools/lean_register.py` | Lean→store | register/update Lean atoms + Lean→Lean edges |
| `tools/tex_extract.py` | tex→store | do Carmo MDX → tex atoms + dependency/`\entryref` edges |
| `tools/lean_tex_audit.py` | both | sorries / fruit / holes / under-linked |
| `tools/graph.py` | read | stats / diff / sorry / node from the live API |

## Identity & types (so re-runs stay clean)
- **Lean node** identity = `H({source: "lean", name})` — stable across re-extraction.
- **Tex node** identity = `H({source: "tex", src: "docarmo", dcref})`.
- **Cross-source edge** type = `(lean, tex)`, inherited from both ends; `rel: formalizes`.
- **Tex repair edge** (a hole the Lean side exposed): `rel: uses`, `via: lean`.
