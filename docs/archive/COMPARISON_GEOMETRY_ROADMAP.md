# Comparison-geometry roadmap — overlap with Morgan–Tian, and OpenGALib infrastructure assessment

## Context

The full Poincaré conjecture is proved via Ricci flow with surgery
(Hamilton–Perelman). Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*
(arXiv:math/0607607, kept under `references/arXiv-math0607607v2/`), gives a
complete book-length proof. Its first chapters are **not** Ricci flow — they are
a condensed comparison-geometry foundation (Riemannian preliminaries, non-negative
curvature, Busemann/soul/splitting, Gromov–Hausdorff convergence) that the flow
machinery is then built on top of.

A detailed lecture-note treatment of exactly that foundation lives under
`references/arXiv-2404.09792v2/` (comparison-geometry notes). Those notes are, in
effect, **an expanded reference for Morgan–Tian's comparison-geometry chapters**:
where MT states a comparison/soul/splitting result in one section, the notes
develop it over a full chapter with proofs.

This document maps that overlap to **concrete formalization targets** and assesses
**how far OpenGALib's current infrastructure reaches each one**. The overlap is
the reachable layer; the Ricci-flow-specific machinery beyond it (L-length,
κ-noncollapsing, ε-necks, surgery) is out of current reach and is the territory
the upstream `external/differential-geometry` project is attacking.

## The overlap, as a target list

Status legend: ✅ done · 🟡 partial (stated / sorries / shallow) · 🔴 absent.

| # | Topic | Notes (arXiv-2404.09792v2) | Morgan–Tian | OpenGALib | Status |
|---|---|---|---|---|---|
| 1 | Riemannian foundations (metric, Levi-Civita, Riemann/Ricci curvature) | "Review on Riemannian Geometry" | `prelim` §1–2 | `Riemannian/Connection/LeviCivita`, `Curvature/{RiemannCurvature,RicciTensorBundle}` | ✅ |
| 2 | Bochner–Weitzenböck identity | — | — | `Riemannian/Operators/Bochner` (`bochner_weitzenboeck`) | 🟡 (1 sorry in `Bochner/BochnerExpansion`) |
| 3 | Exponential map, Gaussian normal coordinates | "Geodesics, Length, Distances" | `prelim` §3–4 | `Riemannian/Volume/Exponential` | 🟡 (2 sorries) |
| 4 | Geodesics (as solutions of the geodesic equation) | "Geodesics, Length, Distances" | `prelim` §3 | — (synthetic geodesic spaces only, see #9) | 🔴 |
| 5 | Volume form + integration over a manifold | — | `prelim` "local volume" | `Riemannian/Volume/{VolumeForm,Util/ChartLocalIntegral}` | 🟡 (1 sorry in `VolumeForm`) |
| 6 | **Divergence theorem / integration by parts** (`∫_M Δ_g u dV = 0`) | — | used throughout | `Riemannian/Operators/Divergence` (divergence operator only) | 🔴 **keystone** |
| 7 | Bishop–Gromov volume comparison | "Bishop-Gromov Volume Comparison" ch. | `prelim` "Basic curvature comparison" | `Comparison/BishopGromov/VolumeComparison` (`bishopGromov_volume_comparison`) | 🟡 (1 sorry) |
| 8 | Space forms / model spaces | — | `prelim` | `Comparison/Util/SpaceForm` | ✅ |
| 9 | Length / geodesic metric spaces (synthetic) | "Gromov-Hausdorff" ch. context | `converge2` | `MetricGeometry/{GeodesicSpace,LengthSpace}` | ✅ |
| 10 | Injectivity radius | (notes) | `prelim` "injectivity radius" | scattered (6 files reference) | 🟡 (shallow) |
| 11 | Gromov–Hausdorff convergence + precompactness | "Gromov-Hausdorff Convergence" ch. | `converge2` "GH convergence" | — | 🔴 |
| 12 | Busemann functions | Soul chapters | `prelim` "Busemann functions" | — | 🔴 |
| 13 | Cheeger–Gromoll soul theorem | "Soul Theorem" chapters | `prelim` "The soul theorem" | — | 🔴 |
| 14 | Cheeger–Gromoll splitting theorem | "Splitting Theorem" ch. | `prelim` "The splitting theorem" + `converge2` | — | 🔴 |
| 15 | Metric tangent cones / blow-up limits | "Tangent Spaces and Cones" | `converge2` "Blow-up limits" | GMT `TangentCone` is varifold-tangent, a different object | 🔴 |
| 16 | Critical-point theory of the distance function | Grove–Shiohama / Grove–Petersen | `canonnbhd` "Shortening curves" | — | 🔴 |
| 17 | Maximum principle (scalar / tensor) | — | `maxprin` | — | 🔴 |

Notes-only (no MT counterpart, not formalization targets here): Riemannian
submersions, Grove–Shiohama sphere theorem, Sharafutdinov retraction,
semi-concave functions / Petrunin gradient flows, Cheeger–Gromoll covering
theorem.

## Infrastructure assessment

**Strong (✅) — the tensor-analytic core is real.** Levi-Civita connection,
Riemann/Ricci curvature, the Bochner stack, model spaces, and the synthetic
metric-space layer (length/geodesic spaces) are in place and mostly sorry-free.
This is a genuine foundation, not a skeleton.

**Partial (🟡) — close, with isolated gaps.** Bishop–Gromov volume comparison is
*stated and substantially proved* with one sorry; the exponential map and volume
form carry a few sorries; injectivity radius is referenced but shallow. These are
finishable with focused effort, not new theory.

**Absent (🔴) — the global comparison-geometry theorems.** Busemann functions,
soul, splitting, Gromov–Hausdorff convergence/precompactness, metric tangent
cones, critical-point theory, and the maximum principle are not formalized. These
are the substantive content of the notes and of MT's foundation chapters; they
are the bulk of the work ahead.

**The keystone (#6).** The single highest-leverage missing piece is the
**divergence theorem on closed manifolds** (`∫_M Δ_g u dV_g = 0`). We already have
the divergence operator and the chart-local integration machinery
(`Volume/Util/ChartLocalIntegral`, partition-of-unity glue); the theorem is an
assembly job, not new theory. It unlocks the analytic payoff of the
already-proved Bochner identity — most immediately the **Lichnerowicz eigenvalue
estimate** (`Ric ≥ (n-1)k g, k>0` on closed `M^n` ⟹ `λ₁(Δ_g) ≥ nk`), the first
genuine "positive Ricci ⟹ spectral rigidity" theorem on the road toward sphere
theorems.

## Suggested ordering

1. **Finish the partials (🟡)** that gate everything else: close the
   `BochnerExpansion` sorry (verify whether `bochner_weitzenboeck` transitively
   depends on it), the `VolumeForm` sorry, and the Bishop–Gromov sorry.
2. **Build the keystone (#6)**: divergence theorem on closed manifolds.
3. **First headline theorem**: Lichnerowicz eigenvalue estimate (Bochner +
   divergence theorem + Cauchy–Schwarz + Ricci lower bound).
4. **Then the global comparison theorems** (🔴), in dependency order: maximum
   principle → Busemann → splitting; Gromov–Hausdorff convergence → precompactness
   → metric tangent cones. These are where the comparison-geometry notes become
   the working reference.

Ricci flow itself (evolution equations, L-length, κ-noncollapsing, surgery) stays
out of scope until this foundation is complete; it is the upstream
`external/differential-geometry` program's territory.
