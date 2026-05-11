# OpenGA

A Lean 4 library for geometric analysis.

## Quick Start

Add the following dependency to your Lean project's `lakefile.lean`:

```
require OpenGALib from git "https://github.com/MathNetwork/OpenGA.git" @ "main"
```

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

## License

OpenGA is released under the Apache 2.0 License.
See the LICENSE file for details.
