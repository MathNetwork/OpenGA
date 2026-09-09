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

Requires Mathlib at the SHA pinned in `lake-manifest.json`.

## License

Apache 2.0 — see LICENSE.
