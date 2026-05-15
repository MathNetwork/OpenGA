# Sorry Catalog

Each `sorry` carries its closure plan in its docstring. This file lists the open count by classification + module; the strict baseline is enforced by `.github/workflows/ci.yml` (`EXPECTED` constant).

## Classification

- **PRE-PAPER** — Mathlib API gap or framework primitive missing; closure path is self-build or Mathlib upstream.
- **CITED-BLACK-BOX** — theorem quoted from a paper as given; body never proven in the framework. The named theorem is the value.

## Open sorries (current)

| Module | PRE-PAPER | CITED-BLACK-BOX | Total |
|--------|-----------|------------------|-------|
| Algebraic | 5 | 0 | 5 |
| Tensor | 9 | 0 | 9 |
| MetricGeometry | 0 | 0 | 0 |
| Riemannian | varies | 0 | — |
| Bridges | 1 | 0 | 1 |
| Comparison | 1 | 0 | 1 |
| GeometricMeasureTheory | 5 | 10 | 15 |

The Riemannian count drifts as feature branches add statement-only sorries. CI `EXPECTED` is the authoritative current value. For per-file location and repair plans, `grep -rn "sorry" OpenGALib/` and read each docstring.

## Discipline

- Substantive chain proofs stay 0-sorry, non-circular.
- Never silently weaken a statement to remove a sorry.
- When adding a new `sorry`: write the repair plan in its docstring and bump `EXPECTED` in `ci.yml`.
- When closing a `sorry`: remove it and decrement `EXPECTED`.
