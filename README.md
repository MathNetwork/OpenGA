# OpenGALib

[![Prove2Me](https://img.shields.io/badge/Prove2Me-Poincar%C3%A9_Conjecture-2b7489)](https://prove2.me/missions/Formalization%20of%20the%20Poincar%C3%A9%20Conjecture)

Riemannian geometry, formalized in Lean 4 on top of Mathlib.

Open tasks live in the Prove2Me mission above — that is where contributions
are coordinated.

## Use

Add to your `lakefile.lean`:

```
require OpenGALib from git "https://github.com/MathNetwork/OpenGA.git" @ "main"
```

Then:

```
lake exe cache get
lake build
```

Pins Lean v4.33.1 and Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474`, matching Prove2Me's
Lean v4.33.1 verification environment. Dependency revisions are recorded
in `lake-manifest.json`.

OpenGA also pins [DifferentialGeometry](https://github.com/qinz1yang/differential-geometry)
v0.1.2. Reviewed reuse currently includes Riemannian volume and complete-manifold
Bishop–Gromov comparison for nonpositive model curvature, with public interfaces
in `OpenGALib/Interoperability`.

## License

Apache 2.0 — see LICENSE.
