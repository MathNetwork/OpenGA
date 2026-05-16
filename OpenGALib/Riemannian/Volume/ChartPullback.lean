import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.Volume.Util.PartitionOfUnityGlue

/-!
# Riemannian volume measure — chart-pullback definition

Anchor for the canonical Riemannian volume measure `vol_g` on a Riemannian
manifold `(M, g)`. Definition is chart-wise:

  `vol_g(A) = ∫_{φ(A ∩ U)} √det(g_ij ∘ φ⁻¹)(y) dy`   for any chart `(U, φ)`,

glued by partition of unity. Chart-invariance follows from the
change-of-variables formula combined with the transformation
`g_ij ↦ Jᵀ · g_ij · J` (so `√det(g_ij)` transforms by `|det J⁻¹|`,
cancelling the Lebesgue Jacobian factor `|det J|`).

Sibling files in `Riemannian/Volume/` provide alternative-view bridges:
* `VolumeForm.lean`           — bridge `vol_g(A) = ∫_A dV_g` (top form view)
* `Hausdorff.lean`            — bridge `vol_g = α(n) · μH[n]_{d_g}`
                                (Federer §3.2.46; closes the BG stopgap)
* `Exponential.lean`          — bridge `vol_g|_{loc} = exp_{p,*}(det(d exp_p)·dx)`
* `UniversalProperty.lean`    — uniqueness characterization

Ground truth: do Carmo, *Riemannian Geometry*, Ch. 1; Petersen,
*Riemannian Geometry*, Ch. 7 §1; Lee, *Smooth Manifolds*, Ch. 16.

This file lands the **anchor signature** for Phase 1 of the
`riemannian-volume` Layer 3a sub-project. The actual chart-pullback
construction (partition-of-unity glue + chart-invariance proof) carries
PRE-PAPER sorries with full repair plans below; subsequent commits in
this branch fill them in.
-/

open scoped ContDiff Manifold

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]

/-- **Math.** The **Riemannian volume measure** `vol_g` on a Riemannian
manifold `(M, g)`. Defined chart-wise as the pullback of Lebesgue measure
weighted by `√det(g_ij)`, glued across charts by partition of unity.

Ground truth: do Carmo Ch.1; Petersen Ch.7 §1; Lee Ch.16.

PRE-PAPER. **Construction sketch** (to be filled in subsequent commits):

1. *Local chart-wise measure.* For each chart `(U, φ)` containing
   `x ∈ M`, define `vol_g^{U,φ}` on `U` as the pushforward under `φ⁻¹` of
   `√det(g_ij ∘ φ⁻¹) · (Lebesgue|_{φ(U)})`. Here `g_ij(x) = g(∂_i|_x, ∂_j|_x)`
   for the chart-frame `∂_i = (φ⁻¹)_*(e_i)`.
2. *Chart-invariance.* Under chart change `(U, φ) → (V, ψ)` with transition
   `ψ ∘ φ⁻¹`, the matrix `g_ij` transforms by `g' = Jᵀ · g · J` where
   `J = d(φ ∘ ψ⁻¹)`. So `√det(g') = |det J| · √det(g)`. Combined with
   Lebesgue's change of variables giving a factor `|det J|⁻¹` (pulling
   back), the chart-wise measures **agree** on `U ∩ V`.
3. *Global glue.* Use a smooth partition of unity `{χ_i}` subordinate to
   a locally finite atlas `{(U_i, φ_i)}`: define
   `vol_g(A) := Σᵢ ∫ χᵢ d(vol_g^{Uᵢ,φᵢ})`. Chart-invariance (step 2)
   ensures the sum is independent of the choice of atlas / partition.

**Implementation.** Steps 1-3 land in `Riemannian/Volume/Util/`:
* `chartLocalMeasure g α` (step 1, per-chart pushforward of
  `√det · Lebesgue`),
* `chartLocalMeasure_lintegral_U_eq_of_overlap` (step 2, chart-overlap
  invariance via change of variables),
* `riemannianMeasure g ρ` (step 3, partition-of-unity sum).

The canonical volume measure picks the canonical chart-atlas partition
of unity `chartAtlasPOU I M`. -/
noncomputable def volumeMeasure (g : RiemannianMetric I M) : MeasureTheory.Measure M :=
  Riemannian.Tensor.riemannianMeasure g (Riemannian.Tensor.chartAtlasPOU I M)

@[inherit_doc] scoped[Riemannian]
  notation:max "dV_g[" g "]" => Riemannian.volumeMeasure g


variable (g : RiemannianMetric I M)

/-- **Math.** `vol_g` is locally finite (every point has a neighborhood of
finite measure). Standard property — every Riemannian metric ball of
finite radius has finite volume since the chart-pullback integrand
`√det(g_ij ∘ φ⁻¹)` is bounded on compact sets.

PRE-PAPER (Phase 1 follow-up). **Repair plan**: take a chart-relative
compact neighborhood, apply the chart-pullback formula
(forthcoming `volumeMeasure_chart_pullback_eq`), bound `√det` by its sup
on the compact image. -/
instance instIsLocallyFiniteMeasure_volumeMeasure :
    MeasureTheory.IsLocallyFiniteMeasure (volumeMeasure g) := by
  sorry

/-- **Math.** `vol_g` is sigma-finite (M is sigma-compact, vol_g is locally
finite, hence sigma-finite).

PRE-PAPER (Phase 1 follow-up). **Repair plan**: follows from
`isLocallyFinite + sigma_compact ⟹ sigma_finite` (Mathlib lemma). -/
instance instSigmaFinite_volumeMeasure :
    MeasureTheory.SigmaFinite (volumeMeasure g) := by
  infer_instance

end Riemannian
