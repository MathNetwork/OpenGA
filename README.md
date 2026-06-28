<h1 align="center">Riemannian Geometry Challenge</h1>

<p align="center"><em>In progress.</em></p>

<p align="center">
A public, open initiative to build Riemannian geometry into a living,<br/>
machine-verified textbook — a shared foundation anyone can learn from,<br/>
contribute to, reuse, and build on. Made for everyone.
</p>

<p align="center">
  <a href="https://github.com/MathNetwork/Astrolabe"><img src="https://img.shields.io/badge/Powered_by-Astrolabe-669aba?style=for-the-badge&labelColor=11111b&logoColor=white" alt="Powered by Astrolabe"></a>
  &nbsp;
  <a href="https://events.astrolabe.network/"><img src="https://img.shields.io/badge/Website-events.astrolabe.network-be1420?style=for-the-badge&labelColor=11111b" alt="Website"></a>
  &nbsp;
  <a href="https://discord.com/invite/CvfrT34ra"><img src="https://img.shields.io/badge/Discord-Join-5865F2?style=for-the-badge&logo=discord&logoColor=white&labelColor=11111b" alt="Join our Discord"></a>
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
