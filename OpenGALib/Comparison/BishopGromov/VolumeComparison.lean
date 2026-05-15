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
* **Layer 3a** — `ricciTensor p` (`Curvature/RicciTensorBundle`) provides
  the Ricci `(0,2)`-tensor at each point; the lower bound `(n - 1) K g`
  is stated against it.
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
* `spaceFormCutDiameter K` — the maximal radius `D_K^n` on which the
  volume-ratio comparison holds: `π / √K` when `K > 0`, and `+∞` otherwise.
-/

open scoped Real Manifold InnerProductSpace ENNReal ContDiff Riemannian
open Bundle MeasureTheory Set

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

/-- **Math.** The *cut diameter* `D_K^n` of the space form `M_K^n`: the
radius at which the geodesic ball closes up. The volume-ratio comparison
of Bishop–Gromov is stated on the open interval `(0, D_K^n)`.

* `D_K^n = π / √K`   if `K > 0` (positive curvature, `M_K^n` is a sphere);
* `D_K^n = +∞`       if `K ≤ 0` (flat or negative curvature, `M_K^n` is
  Euclidean or hyperbolic). -/
noncomputable def spaceFormCutDiameter (K : ℝ) : ℝ≥0∞ :=
  if 0 < K then ENNReal.ofReal (Real.pi / Real.sqrt K) else ⊤

end OpenGA.Comparison.BishopGromov

/-! ## Riemannian-volume placeholder typeclass -/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [HasMetric I M]

/-- **Math.** The predicate `IsRiemannianVolume μ`: the measure `μ` on the
Riemannian manifold `(M, g)` is the canonical *Riemannian volume measure*,
i.e. it agrees in any chart with `√det(g_ij) · Lebesgue`, equivalently with
the `n`-dimensional Hausdorff measure of the Riemannian distance normalized
so that the unit ball in any tangent space has the usual Euclidean unit-ball
volume.

Ground truth: do Carmo, Ch. 1 (volume form on an oriented Riemannian
manifold); Petersen, Ch. 7 §1.

**PRE-PAPER placeholder.** For Stage 0 of the Bishop–Gromov development,
this class is declared with no fields — every measure on a Riemannian
manifold trivially satisfies the predicate. The actual characterizing
content (chart-pullback equation, or Hausdorff-measure normalization) is
the responsibility of Layer 3a `Util/RiemannianVolume.lean` (pending). When
that file lands, populate this class with the real field and register the
canonical instance on every `[HasMetric I M]`; the Bishop–Gromov hypothesis
list does not change. -/
class IsRiemannianVolume [MeasurableSpace M] (μ : MeasureTheory.Measure M) : Prop where

/-! ## The Bishop–Gromov volume comparison theorem -/

open OpenGA.Comparison.BishopGromov

/-- **Math.** **Bishop–Gromov volume comparison.**

Let `(M, g)` be a complete connected `n`-dimensional Riemannian manifold
whose Ricci curvature satisfies `Ric_g ≥ (n - 1) K g` for some `K ∈ ℝ`.
Let `μ` be the Riemannian volume measure on `M`, and let `V_K^n` and `D_K^n`
be the space-form ball-volume and cut-diameter functions of `M_K^n`. Then
for every `p ∈ M`, the function

$$\Phi_p(r) \;:=\; \frac{\mu(B_g(p, r))}{V_K^n(r)}$$

is non-increasing on `(0, D_K^n)`.

Ground truth: do Carmo, Ch. 10 §2 Theorem 2.2; Petersen, Ch. 9 §1 Theorem 27;
Cheeger–Ebin, Theorem 1.93; Burago–Burago–Ivanov, §6.5.

**NORTH-STAR (PRE-PAPER).** This is the headline target driving Stage II
of OpenGA Layer 1+3a+3b development. The statement is landed at the
correct signature so that downstream consumers can already invoke it; the
proof is the multi-stage goal.

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

Each step in this chain depends on Layer 3a infrastructure that is not
yet present (smooth radial distance function on `M ∖ Cut(p)`, Hessian
comparison, polar-coordinates change-of-variables on Riemannian manifolds).
The chain closes the Layer 1 bridge sorry as a side effect — Bishop–Gromov
cannot be invoked without `Metric.ball` being the path-infimum ball, which
forces `IsRiemannianManifold.toLengthSpace` to be 0-sorry. -/
theorem bishopGromov_volume_ratio_antitone
    [PseudoMetricSpace M] [IsRiemannianManifold I M]
    [MeasurableSpace M]
    {n : ℕ} (hdim : Module.finrank ℝ E = n)
    (μ : MeasureTheory.Measure M) [IsRiemannianVolume μ]
    (K : ℝ)
    (hRic : ∀ p : M, ∀ v : TangentSpace I p,
      ((n : ℝ) - 1) * K * ⟪v, v⟫_ℝ ≤ ricciTensor p v v)
    (p : M) :
    AntitoneOn
      (fun r : ℝ ↦
        (μ (Metric.ball p r)).toReal / spaceFormBallVolume n K r)
      (Set.Ioo 0 (spaceFormCutDiameter K).toReal) := by
  sorry

end Riemannian
