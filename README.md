<h1 align="center">Riemannian Geometry Challenge</h1>

<p align="center"><em>In progress.</em></p>

<p align="center">
A public, open initiative to build Riemannian geometry into a living,<br/>
machine-verified textbook — a shared foundation anyone can learn from,<br/>
contribute to, reuse, and build on. Made for everyone.
</p>

## Use the Lean library

Add the dependency to your `lakefile.lean`:

```
require OpenGALib from git "https://github.com/MathNetwork/OpenGA.git" @ "main"
```

Build:

```
lake exe cache get
lake build
```

Requires Mathlib at the SHA pinned in `lake-manifest.json`.

## Status

Pre-`v0.1.0`, experimental. PRE-PAPER `sorry`'d statements and narrow structural
axioms are tracked with explicit repair plans in module docstrings (search for
`**Sorry status**:` / `axiom`).

## Contributing

Issues and PRs welcome.

## License

Released under the Apache 2.0 License. See the LICENSE file for details.

---
