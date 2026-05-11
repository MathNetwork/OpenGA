# OpenGA

A Lean 4 library for geometric analysis. 



## About

OpenGA is a library for formalizing geometric analysis built on top of the Lean 4 theorem prover.

Lean 4 is an interactive theorem prover based on dependent type theory, designed to bridge the gap between interactive and automated reasoning, and between proof assistants and programming languages.



## Quick Start

### Using OpenGA in Your Project
Add the following dependency to your Lean project's `lakefile.lean`:
```
require OpenGA from git "https://github.com/MathNetwork/OpenGA.git" @ "main"
```

### Building Locally (For Developers)

```
# Clone the repository
git clone https://github.com/MathNetwork/OpenGA.git
cd OpenGA
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
