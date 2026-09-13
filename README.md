# OpenGALib

[![Prove2Me](https://img.shields.io/badge/Prove2Me-Poincar%C3%A9_Conjecture-2b7489)](https://prove2.me/missions/Formalization%20of%20the%20Poincar%C3%A9%20Conjecture)

Geometric analysis and geometric measure theory, formalized in Lean 4 on top
of Mathlib. OpenGA develops reusable definitions and proofs, and reviews and
adapts results from other formalization projects with their attribution and
mathematical hypotheses preserved.

## Library contents

| Area | Available foundations |
| --- | --- |
| [Geometric measure theory](OpenGALib/GeometricMeasureTheory) | Compact unoriented Grassmannians; Euclidean varifolds as Radon measures; weight measures, mass and support; weak-* convergence; weighted and atomic constructions; varifolds of finite-area `C¹` parametrizations. |
| [Area and energy](OpenGALib/Analysis/AreaEnergy.lean) | The area–energy inequality and its equality criterion; orthonormal-frame invariance; bounds on parametrized varifold mass by energy. |
| [Riemannian surfaces](OpenGALib/Riemannian/Surface) | Induced metrics, global area and coordinate compatibility; tangent and normal projections; geometric Dirichlet energy; smooth sweepouts and their homotopy width. |
| [Comparison geometry](OpenGALib/ComparisonGeometry) | Metric balls, local Ricci bounds, volume measures and surgery volume budgets; [Bishop–Gromov comparison](OpenGALib/Interoperability/BishopGromov.lean) for complete manifolds with nonpositive model curvature, reused from DifferentialGeometry. |
| [Ricci flow and extinction](OpenGALib/Interoperability/RicciFlow) | Scalar lower bounds; local and closed-surface area variation; [width comparison](OpenGALib/Analysis/WidthComparison.lean) and [finite-time extinction](OpenGALib/Analysis/WidthExtinction.lean) under explicit analytic hypotheses. |
| [Geometry](OpenGALib/Riemannian) and [topology](OpenGALib/Topology) | Riemannian metrics, geodesic and exponential-map foundations; covering spaces, connected sums and the topological extinction endgame under explicit reconstruction hypotheses. |

The library is under active development. The smooth-sweepout width is a
precursor to the Colding–Minicozzi Sobolev width; identifying the two and
constructing the required uniform area-evolution data remain open work.
These foundations do not yet constitute a proof of the Poincaré conjecture.

## Collaborative formalization

Open tasks are coordinated in the [Prove2Me Poincaré mission](https://prove2.me/missions/Formalization%20of%20the%20Poincar%C3%A9%20Conjecture).
The [PoincareConjecture workspace](PoincareConjecture) prepares submissions,
mirrors platform definitions and proofs, and records source reviews and
verification receipts. Its open problems and proof sketches are separate
from the reusable library in `OpenGALib/`.

We thank the authors and contributors of
[DifferentialGeometry](https://github.com/qinz1yang/differential-geometry),
[Poincare-Conjecture](https://github.com/frenzymath/Poincare-Conjecture),
Mathlib and Lean, and the Prove2Me team. Source-specific attribution and
dependency revisions are recorded alongside the reused results.

## Use

Add to your `lakefile.lean`:

```lean
require OpenGALib from git "https://github.com/MathNetwork/OpenGA.git" @ "main"
```

Then:

```sh
lake exe cache get
lake build
```

Pins Lean v4.33.1 and Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474`, matching Prove2Me's
Lean v4.33.1 verification environment. Dependency revisions are recorded
in `lake-manifest.json`.

OpenGA also pins DifferentialGeometry v0.1.2. Public interfaces to the
reviewed upstream results live in `OpenGALib/Interoperability`.

Import the whole library or a focused entry point:

```lean
import OpenGALib
-- Or:
import OpenGALib.GeometricMeasureTheory
import OpenGALib.Riemannian.Surface
```

## Contributing and verification

See [CONTRIBUTING.md](CONTRIBUTING.md) and the [review guide](.github/REVIEW.md).
The `main` branch requires a successful build and no `sorry` in `OpenGALib/`.
CI also checks source-review receipts and the axioms of curated declarations.

```sh
lake build
python3 -m unittest discover -s PoincareConjecture -p 'test_*.py'
python3 PoincareConjecture/check_curation.py
```

## License

Apache 2.0 — see LICENSE.
