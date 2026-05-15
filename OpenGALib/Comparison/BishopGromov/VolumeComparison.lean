import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import OpenGALib.Riemannian.Curvature.RicciTensorBundle

/-!
# Bishop–Gromov volume comparison

The north-star theorem of OpenGA Layer 3b (Comparison Geometry). For a
complete Riemannian manifold whose Ricci curvature is bounded below by
`(n - 1) K g`, the ratio of the volume of a metric ball at any point to
the volume of the corresponding ball in the simply-connected space form of
constant sectional curvature `K` is a non-increasing function of the radius.

This file records the **statement**; the proof is the multi-stage goal that
drives the Layer 1 ⟶ Layer 3a ⟶ Layer 3b development pipeline (see the
PRE-PAPER block on the headline theorem for the full repair plan).

## Ground truth

* do Carmo, *Riemannian Geometry*, Ch. 10 §2 (Theorem 2.2).
* Petersen, *Riemannian Geometry*, Ch. 9 §1 (Theorem 27).
* Cheeger–Ebin, *Comparison Theorems in Riemannian Geometry*, Theorem 1.93.
* Burago–Burago–Ivanov, *A Course in Metric Geometry*, §6.5.

## North-star role

Statement-level dependencies this theorem forces to be load-bearing:

* **Layer 1** — `Metric.ball p r` and the `IsRiemannianManifold I M` instance
  combine to identify the metric ball with the path-length ball
  (`Bridges/RiemannianToLength`). The `≤` direction of the bridge currently
  carries a PRE-PAPER sorry; this theorem's hypothesis stack makes that
  sorry load-bearing.
* **Layer 1** — `IsRiemannianVolume μ` constrains `μ : Measure M` to be the
  canonical Riemannian volume. The class is a placeholder here; its body
  is the responsibility of Layer 3a `Util/RiemannianVolume.lean` (pending).
* **Layer 3a** — `ricciTensor x` (`Curvature/RicciTensorBundle`) provides
  the Ricci `(0,2)`-tensor at each point; the lower bound `(n - 1) K g`
  is stated against it via the `RicciLowerBound` predicate.
* **Layer 3b** — the actual proof requires Jacobi-field / Riccati comparison
  (Petersen Ch. 6 §2), Hessian comparison, Laplacian comparison
  (`Δ_g r ≤ (n - 1) s_K'(r) / s_K(r)`), and the coarea identity. These are
  the future content of `Comparison/BishopGromov/*` sibling files.

## Auxiliary definitions
* `snakeFunction K r` — the snake function `s_K(r)` of the space form `M_K^n`
  (`sin / sinh / id` according to the sign of `K`).
* `spaceFormBallVolume n K r` — the volume of a radius-`r` geodesic ball in
  the simply-connected `n`-dimensional space form of constant sectional
  curvature `K`, given by `n · ω_n · ∫_0^r s_K(t)^(n-1) dt` where `ω_n` is
  the volume of the unit ball in `ℝⁿ`.
* `spaceFormAdmissibleRadii K` — the set `𝒟_K` of admissible radii on which
  the comparison holds: `(0, π/√K)` when `K > 0`, and `(0, +∞)` otherwise.

## Paper-style notation

Scoped to `OpenGA.Comparison.BishopGromov` (cross-file):
* `B(p, r)` — open metric ball (wraps Mathlib `Metric.ball`).

Local to the headline's `section` (only valid where `K` is a
section variable):
* `V_K^n(r)` — space-form ball volume (wraps `spaceFormBallVolume n K r`).
* `𝒟_K` — admissible radii (wraps `spaceFormAdmissibleRadii K`).

Inherited from Mathlib / OpenGA scopes:
* `μ.real s` — `Measure.real`, gives `(μ s).toReal`.
* `⟪v, w⟫_g`, `Ric_g(v, w) x` — OpenGA Riemannian.
-/

open scoped Real Manifold InnerProductSpace ENNReal ContDiff Riemannian
open Bundle MeasureTheory Riemannian Set

namespace OpenGA.Comparison.BishopGromov

/-! ## Space-form auxiliary functions -/

/-- **Math.** The *snake function* `s_K(r)` of the simply-connected space
form `M_K^n`:

* `s_K(r) = sin(√K · r) / √K`   if `K > 0`;
* `s_K(r) = r`                    if `K = 0`;
* `s_K(r) = sinh(√(-K) · r) / √(-K)`   if `K < 0`.

This is the radial scaling factor of Jacobi fields in the space form, and
the building block of the space-form ball volume `V_K^n(r)` and of the
Laplacian comparison `Δ_g r ≤ (n - 1) · s_K'(r) / s_K(r)`.

Ground truth: Petersen, *Riemannian Geometry*, Ch. 6 §2 (Definition of
`sn_K`); do Carmo, Ch. 10 §1. -/
noncomputable def snakeFunction (K r : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * r) / Real.sqrt K
  else if K < 0 then Real.sinh (Real.sqrt (-K) * r) / Real.sqrt (-K)
  else r

/-- **Math.** The volume `V_K^n(r)` of a geodesic ball of radius `r` in the
simply-connected `n`-dimensional space form `M_K^n` of constant sectional
curvature `K`:

$$V_K^n(r) \;=\; n\,\omega_n \int_0^r s_K(t)^{\,n-1}\, dt$$

where `ω_n` is the Lebesgue measure of the unit ball in `ℝⁿ`. The
integrand is the Jacobian of polar coordinates in the space form.

Ground truth: do Carmo, Ch. 10 §2 (formula (5)); Petersen, Ch. 9 §1. -/
noncomputable def spaceFormBallVolume (n : ℕ) (K r : ℝ) : ℝ :=
  let unitBallVolume : ℝ :=
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
  (n : ℝ) * unitBallVolume * ∫ t in (0 : ℝ)..r, (snakeFunction K t) ^ (n - 1)

/-- **Math.** The set of *admissible radii* `𝒟_K` for Bishop–Gromov
comparison in the space form `M_K^n`: the open interval `(0, D_K^n)`
where `D_K^n = π/√K` for `K > 0` and `D_K^n = +∞` otherwise. Concretely

* `𝒟_K = (0, π/√K)`   if `K > 0`  (sphere, comparison fails past
  the antipode);
* `𝒟_K = (0, +∞)`     if `K ≤ 0`  (Euclidean / hyperbolic, no cut). -/
noncomputable def spaceFormAdmissibleRadii (K : ℝ) : Set ℝ :=
  if 0 < K then Set.Ioo 0 (Real.pi / Real.sqrt K) else Set.Ioi 0

/-! ## Paper-style notation -/

/-- **Math.** `B(p, r)` — open metric ball of radius `r` around `p` in the
ambient Riemannian manifold (Mathlib `Metric.ball`). -/
scoped notation:max "B(" p ", " r ")" => Metric.ball p r

end OpenGA.Comparison.BishopGromov

/-! ## Riemannian setup for the headline theorem

A single file-level variable block fixes the Riemannian-manifold setup so
that the headline `bishopGromov_volume_comparison` reads as the
textbook sentence with no engineering tax exposed (mirrors the discipline
of `bochner_weitzenboeck` in `Riemannian/Operators/Bochner.lean`). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [HasMetric I M]
  [PseudoMetricSpace M] [IsRiemannianManifold I M] [MeasurableSpace M]

/-- Dimension of the Riemannian manifold `M` (the finrank of the model
space `E`); used in the textbook `(n - 1) K g` form of the Ricci lower
bound and as the `n` argument of `spaceFormBallVolume` / `spaceFormCutDiameter`. -/
local notation:max "n_M" => Module.finrank ℝ E

/-! ## Riemannian volume — placeholder typeclass

`IsRiemannianVolume μ` asserts that `μ : Measure M` is the canonical
Riemannian volume on `(M, g)` (in any chart it pulls back to
`√det(g_ij) · Lebesgue`; equivalently it is the `n`-dimensional Hausdorff
measure of the Riemannian distance, normalized so the unit tangent ball has
the Euclidean unit-ball volume).

Ground truth: do Carmo, Ch. 1 (volume form on an oriented Riemannian
manifold); Petersen, Ch. 7 §1.

**PRE-PAPER placeholder.** For Stage 0 the class is declared with no
fields — every measure on a Riemannian manifold trivially satisfies the
predicate. The actual characterizing content is the responsibility of
Layer 3a `Util/RiemannianVolume.lean` (pending); when that file lands,
populate this class with the real field and register the canonical
instance on every `[HasMetric I M]`. The Bishop–Gromov hypothesis list
does not change. -/
class IsRiemannianVolume (μ : Measure M) : Prop where

/-! ## The Bishop–Gromov volume comparison theorem -/

open OpenGA.Comparison.BishopGromov

/-! Section-scoped paper notation: `K` becomes an implicit section
variable, so the local notation expansion captures it cleanly (the
hygiene barrier that blocks `macro`-based capture is bypassed because
`K` is parsed as a section variable, not as a free identifier in the
notation RHS). -/
section BishopGromovStatement

variable {K : ℝ}

/-- **Math.** `V_K^n(r)` — volume of a radius-`r` geodesic ball in the
`n`-dimensional space form of constant sectional curvature `K`. -/
local notation:max "V_K^" n:max "(" r:max ")" =>
  spaceFormBallVolume n K r

/-- **Math.** `𝒟_K` — the open interval of admissible radii for
Bishop–Gromov comparison at curvature lower bound `K`. -/
local notation:max "𝒟_K" => spaceFormAdmissibleRadii K

/-- **Math.** **Bishop–Gromov volume comparison.**

For a complete `n`-dimensional Riemannian manifold `M` whose Ricci curvature
satisfies `Ric_g ≥ (n - 1) K · g`, the ratio of the volume of a metric ball
at any base point to the volume of the corresponding ball in the
simply-connected `n`-dimensional space form `M_K^n` is non-increasing in the
radius, on the maximal interval `(0, D_K^n)`.

Ground truth: do Carmo, Ch. 10 §2 Theorem 2.2; Petersen, Ch. 9 §1 Theorem 27;
Cheeger–Ebin, Theorem 1.93; Burago–Burago–Ivanov, §6.5.

**NORTH-STAR (PRE-PAPER).** This is the headline target driving Stage II of
OpenGA Layer 1 + Layer 3a + Layer 3b development. The statement is landed
at the correct signature so that downstream consumers can already invoke it;
the proof is the multi-stage goal.

**Repair plan** (sketch of the classical proof, do Carmo Ch. 10 §1–2):

1. *Riccati comparison* (Petersen Lemma 27.1). For `u(t) = Δ_g r(γ(t))`
   along a unit-speed geodesic `γ`, the Bochner / shape-operator identity
   gives `u'(t) + u(t)^2 / (n - 1) ≤ -Ric_g(γ'(t), γ'(t)) / (n - 1) ≤ -K`,
   so by Riccati comparison `u(t) ≤ (n - 1) · s_K'(t) / s_K(t)` on the
   maximal interval of definition.
2. *Laplacian comparison* (do Carmo Ch. 10 §1 Theorem 1.4):
   `Δ_g r(x) ≤ (n - 1) · s_K'(d_g(p, x)) / s_K(d_g(p, x))` pointwise on
   `M ∖ {p, Cut(p)}`.
3. *Volume comparison* (do Carmo Ch. 10 §2 Theorem 2.2 / Petersen Theorem 27).
   Polar coordinates around `p` and the Laplacian-comparison upper bound on
   the radial Jacobian give `∂_r vol(B_g(p, r)) ≤ n · ω_n · s_K(r)^{n-1}`,
   which integrates (via the coarea identity) to the antitone ratio.

Each step in this chain depends on Layer 3a infrastructure that is not yet
present (smooth radial distance function on `M ∖ Cut(p)`, Hessian comparison,
polar-coordinates change-of-variables on Riemannian manifolds). The chain
closes the Layer 1 bridge sorry as a side effect — Bishop–Gromov cannot be
invoked without `Metric.ball` being the path-infimum ball, which forces
`IsRiemannianManifold.toLengthSpace` to be 0-sorry. -/
theorem bishopGromov_volume_comparison
    (μ : Measure M) [IsRiemannianVolume μ]
    (hRic : ∀ x : M, ∀ v : TangentSpace I x,
      (n_M - 1 : ℝ) * K * ⟪v, v⟫_g ≤ Ric_g(v, v) x)
    (p : M) {r R : ℝ} (hr : r ∈ 𝒟_K) (hR : R ∈ 𝒟_K) (hrR : r ≤ R) :
    μ.real B(p, R) / V_K^n_M(R) ≤ μ.real B(p, r) / V_K^n_M(r) := by
  sorry

end BishopGromovStatement
