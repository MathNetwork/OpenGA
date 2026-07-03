# Sorry Catalog

Each `sorry` carries its closure plan in its docstring. This file lists the open count by classification + module; the strict baseline is enforced by `.github/workflows/ci.yml` (`EXPECTED` constant).

## Classification

- **PRE-PAPER** — Mathlib API gap or framework primitive missing; closure path is self-build or Mathlib upstream.
- **CITED-BLACK-BOX** — theorem quoted from a paper as given; body never proven in the framework. The named theorem is the value.

## Open sorries (current: 3)

All three live in `OpenGALib/Riemannian/Geodesic/HopfRinow.lean` — the statement-only
Hopf–Rinow file (theorem + two corollaries, each with its do Carmo Ch. 7 proof plan
inline). Classification: PRE-PAPER (the classical proofs are scoped upstream work).

| Location | Statement |
|----------|-----------|
| HopfRinow.lean `hopfRinow` | complete ↔ geodesically complete |
| HopfRinow.lean `complete_of_geodesicallyComplete_at` | `exp_p` total at one point ⟹ complete |
| HopfRinow.lean `exists_minimizing_geodesic` | minimizing geodesic between any two points |

The old per-module table (35 sorries across Algebraic/Tensor/GMT/…) described the
pre-restructure tree and was retired with it. CI `EXPECTED` is the authoritative
current value; for repair plans read the docstrings in place.

## Discipline

- Substantive chain proofs stay 0-sorry, non-circular.
- Never silently weaken a statement to remove a sorry.
- When adding a new `sorry`: write the repair plan in its docstring and bump `EXPECTED` in `ci.yml`.
- When closing a `sorry`: remove it and decrement `EXPECTED`.
