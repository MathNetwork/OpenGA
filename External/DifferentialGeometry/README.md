# External: differential-geometry

Third-party library vendored into this project.

- **Source**: https://github.com/qinz1yang/differential-geometry
- **Commit**: `59aedca44bc62a7ba68ce8bfc6200a50e4c52e02` (2026-07-21)
- **Author**: qinz1yang and contributors
- **License**: Apache-2.0 (`LICENSE`, preserved unmodified)
- **Upstream README**: `UPSTREAM_README.md` (preserved unmodified)
- **Toolchain at vendoring time**: upstream `leanprover/lean4:v4.29.0`
  (`lean-toolchain`, preserved for reference); OpenGALib is on
  `v4.30.0-rc2` — the vendored tree does not build under the root
  lakefile yet and is not imported by any OpenGALib module.

A Lean 4 library for differential geometry and geometric analysis
focused on Ricci flow: short-time existence via DeTurck's trick,
scalar-curvature evolution, parabolic maximum principle, and the
supporting Sobolev / elliptic-regularity / spectral / heat-semigroup
stack on manifolds. Vendored as the PDE foundation candidate for the
finite-time-extinction (Colding–Minicozzi) track.

Note: upstream itself vendors De Giorgi–Nash–Moser regularity under
`DifferentialGeometry/External/DeGiorgi/` (Scott Armstrong and Julia
Kempe, Apache-2.0, license preserved there).

Provenance is reciprocal: upstream states that part of its Riemannian
geometry infrastructure was originally derived from OpenGA and has
since been substantially extended and rewritten.

Any modifications we make are tracked in `MODIFICATIONS.md` per
Apache-2.0 §4(b).
