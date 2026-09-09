# OpenGALib

Riemannian geometry, formalized in Lean 4 on top of Mathlib.

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
