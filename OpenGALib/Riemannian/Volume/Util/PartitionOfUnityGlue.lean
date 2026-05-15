import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import OpenGALib.Riemannian.Volume.Util.ChartLocalMeasure

/-!
# Global Riemannian volume measure via a smooth partition of unity

Glues the chart-local measures `chartLocalMeasure g α` (one per
basepoint `α : M`) into a single global Borel measure on `M` using a
smooth partition of unity subordinate to the chart atlas.

  * `chartAtlasPOU I M` — a smooth partition of unity on `M`, indexed
    by `M`, subordinate to the chart-source family `(chartAt H x).source`.
    Existence via `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`.
  * `riemannianMeasure g ρ : Measure M` — the global Riemannian measure
    built from `g` and a partition `ρ`, defined as

      `riemannianMeasure g ρ := Measure.sum (fun α =>
          (chartLocalMeasure g α).withDensity (ENNReal.ofReal (ρ α)))`.

Independence from the choice of `ρ` is a consequence of the chart-
overlap invariance `chartLocalMeasure_lintegral_U_eq_of_overlap`
(B3 main theorem); this is recorded as a follow-up theorem.

Ground truth: Lee §16, do Carmo Ch.1, Petersen Ch.7 §1.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace H := borel H
private local instance : BorelSpace H := ⟨rfl⟩

/-! ## Canonical chart-atlas partition of unity -/

variable (I M) in
/-- **Math.** Canonical smooth partition of unity on `M`, indexed by `M`,
subordinate to the chart-source family `(chartAt H x).source`. Exists for
any smooth finite-dimensional σ-compact Hausdorff manifold (Mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`); the
specific choice is implementation-detail (via `Classical.choice`). -/
noncomputable def chartAtlasPOU :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace M] [BorelSpace M] in
variable (I M) in
/-- **Eng.** The chart-atlas partition of unity is subordinate to the
chart-source family. -/
lemma chartAtlasPOU_isSubordinate :
    (chartAtlasPOU I M).IsSubordinate (fun x : M => (chartAt H x).source) :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec

/-! ## The glued global Riemannian measure -/

/-- **Math.** The **global Riemannian volume measure** built from a
Riemannian metric `g` and a smooth partition of unity `ρ` subordinate
to the chart atlas: the countable sum, over basepoint `α : M`, of the
`ρ α`-weighted chart-local measures.

Ground truth: Lee §16; do Carmo Ch.1. -/
noncomputable def riemannianMeasure
    (g : RiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.sum fun α : M =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)]
  [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
/-- **Eng.** Unfolding lemma for `riemannianMeasure`. -/
lemma riemannianMeasure_def
    (g : RiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : M =>
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) := rfl

end Riemannian.Tensor
