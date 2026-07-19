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

Requires Mathlib at the SHA pinned in `lake-manifest.json`.

## License

Apache 2.0 — see LICENSE.
