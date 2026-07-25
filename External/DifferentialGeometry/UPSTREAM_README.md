# Differential Geometry in Lean 4

An ongoing Lean 4 library for differential geometry and geometric analysis, currently focused on Ricci flow.

## Formalized theorems

Each is `sorry`-free (axioms: `propext, Classical.choice, Quot.sound`).

> These three are the standard axioms of Lean's core library — propositional extensionality, the axiom of choice, and quotient soundness — on which all of classical mathematics in Mathlib rests. `#print axioms` lists everything a theorem transitively assumes: a `sorry` would surface as `sorryAx`, and any ad-hoc axiom would be named. An output of exactly these three therefore certifies that the proof is fully kernel-checked, with no `sorry` and no assumptions beyond the classical foundations.

- [Ricci flow short-time existence](DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTimeExistence.lean#L34) — on every closed Riemannian manifold $(M, g_0)$ the Ricci flow $\partial_t g = -2\,\mathrm{Ric}_{g(t)}$ has a solution on some $[0, T)$ with $g(0) = g_0$, jointly smooth in $(t, x)$ up to and including the initial time. Proved via the DeTurck's trick and a conjugating flow of the DeTurck vector field.
- [Ricci–DeTurck flow short-time existence](DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/DeTurckInitialDataExistence.lean#L142) — the gauge-fixed, strictly parabolic flow behind the reduction: a solution whose chart-Gram entries are jointly smooth on the closed time slab, together with joint smoothness of the DeTurck vector field.
- [Ricci-tensor naturality under diffeomorphisms](DifferentialGeometry/Geometry/Flow/RicciFlow/Pullback/Naturality/RicciTensor.lean#L24) — $\mathrm{Ric}_{\Phi^* g}(v, w) = \mathrm{Ric}_g(d\Phi\, v, d\Phi\, w)$, the equivariance that transports the DeTurck solution back to a Ricci flow.
- [Scalar-curvature evolution under Ricci flow](DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/Scalar/Basic.lean#L96).
- [Bonnet–Myers diameter bound](DifferentialGeometry/Geometry/Comparison/BonnetMyers/Headlines.lean#L570) — a positive Ricci lower bound forces a bounded diameter.
- [Bochner formula](DifferentialGeometry/Analysis/Elliptic/Regularity/Bochner/Polarised.lean#L244) — the polarised, pointwise form.
- [Weitzenböck identity](DifferentialGeometry/Analysis/Elliptic/ConnectionLaplacian/GreenIdentityAndIBP/IntegratedOrder2Weitzenbock.lean#L103) — the integrated $L^2$ form.
- [Lichnerowicz inequality](DifferentialGeometry/Analysis/Elliptic/Lichnerowicz.lean#L59), with the [eigenvalue bound on closed manifolds](DifferentialGeometry/Analysis/Elliptic/Lichnerowicz.lean#L586).
- [Reilly identity](DifferentialGeometry/Analysis/Elliptic/WithBoundary/Neumann/Reilly.lean#L43) — an integral identity on a manifold with boundary.
- [Voss–Weyl divergence formula](DifferentialGeometry/Analysis/Integration/DivergenceTheorem/ChartInvariance.lean#L576) — the chart-invariant divergence.
- [Perelman's $\mathcal{W}$-entropy invariances](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/Defs.lean#L141) — scale and diffeomorphism invariance.
- [Perelman's $\mathcal{F}$-functional first variation](DifferentialGeometry/Geometry/Flow/RicciFlow/Entropy/F/Producer.lean#L411) — Perelman's formula 5.10.

## PDE infrastructure

Underlying these results is a substantial geometric-analysis backbone — the [`Analysis/`](DifferentialGeometry/Analysis) pillar, roughly 770,000 lines of Lean:

- [**Integration & the divergence theorem**](DifferentialGeometry/Analysis/Integration) — Riemannian measures, integration by parts and surface measures, with and without boundary.
- [**Elliptic regularity**](DifferentialGeometry/Analysis/Elliptic) — the connection (rough) Laplacian, Green identities, Gårding / Caccioppoli estimates, and interior bootstrap.
- [**Spectral theory**](DifferentialGeometry/Analysis/Spectral) — the scalar theory on closed manifolds (discrete Laplacian spectrum, compact resolvent, eigenbasis); an iterated covariant-gradient jet calculus for tensor fields with fibre-norm towers and Sobolev-scale spectral estimates; and the intrinsic heat-semigroup / Galerkin machinery driving the DeTurck flow.
- [**Sobolev spaces**](DifferentialGeometry/Analysis/Sobolev) — chart-based and intrinsic $H^k$ / $W^{k,p}$ spaces with completeness, embedding and compactness results; tensor-valued Hilbert–Sobolev towers; Moser-type tame product estimates; and Gagliardo–Nirenberg interpolation down to fibre-norm level.
- [**Parabolic & heat equations**](DifferentialGeometry/Analysis/Parabolic) — heat semigroups, Duhamel mild solutions, Lions–Magenes time-Sobolev theory, strict parabolicity and principal symbols, and the complete quasilinear existence engine behind the DeTurck–Ricci reduction: maximal-regularity Galerkin solutions with all-order Sobolev-scale jet control, tame estimates for the DeTurck nonlinearity, and joint $(t,x)$-smoothness of the solution down to the initial time. A parabolic [maximum principle and heat smoothing](DifferentialGeometry/Analysis/Heat) sit alongside.
- [**ODE flows**](DifferentialGeometry/Analysis/ODE) — $C^\infty$ dependence of flows on their initial data, and time-dependent flows on closed manifolds jointly smooth up to the initial time (via Seeley-type time extension of the vector field).

The classical De Giorgi–Nash–Moser regularity machinery is vendored under [`External/`](DifferentialGeometry/External) from [scottnarmstrong/DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi) (Scott Armstrong and Julia Kempe, Apache-2.0).

## Work in progress

- [**Hamilton's theorem (1982)**](DifferentialGeometry/Geometry/Flow/RicciFlow/DimensionThree/HamiltonPositiveRicci.lean#L3258) — the three-dimensional positive-Ricci program. Curvature evolution, tensor maximum principles, pinching, Hamilton–Cheeger–Gromov compactness, volume comparison, and universal-cover infrastructure are present. The headline remains incomplete.

## AI Disclaimer

Generative AI (ChatGPT, Claude, Deepseek, Gemini, GLM, etc.) was used in the development of this codebase. The high-level architecture is human-designed; AI agents assisted with formalizing individual proofs and writing boilerplate. All definitions and core theorem statements were human-verified for correctness. Since all proofs are verified by Lean's type checker, AI-generated and human-written code are held to the same standard of correctness.
