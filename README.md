# OpenGA

A Lean 4 library for geometric analysis.

Built on [Mathlib](https://github.com/leanprover-community/mathlib4), layered into four sub-namespaces:

- **`Riemannian`** — `RiemannianMetric` typeclass, Levi-Civita connection, Riemann / Ricci / scalar curvature, codim-1 second fundamental form, manifold gradient, bump functions.
- **`GeometricMeasureTheory`** — finite-perimeter sets, varifolds, stationary varifolds, tangent cones, rectifiability, isoperimetric tools (BV / coarea / Sobolev–Poincaré / Federer–Fleming), first / second variation operators.
- **`MinMax`** — sweepout-based min-max theory.
- **`Regularity`** — Wickramasekera 𝒮_α regularity class + smooth regularity theorem.

## Build

```
lake exe cache get
lake build
```

Requires Mathlib at the SHA pinned in `lake-manifest.json`.

## Status

Pre-`v0.1.0`, experimental. PRE-PAPER `sorry`'d statements and narrow structural axioms are tracked with explicit repair plans in module docstrings (search for `**Sorry status**:` / `axiom`).

## Contributing

The library is designed for downstream research consumption, teaching use, and Mathlib upstream candidacy. Issues and PRs welcome.
