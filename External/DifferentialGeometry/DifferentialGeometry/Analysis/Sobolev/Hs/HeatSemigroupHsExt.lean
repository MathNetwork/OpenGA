import DifferentialGeometry.Analysis.Sobolev.Hs.HeatSemigroupHs

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Hs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def heatSemigroupHsExt (g : SmoothRiemannianMetric I M) (σ : ℝ) (t : ℝ) :
    scalarHs (I := I) (M := M) g σ →L[ℝ] scalarHs (I := I) (M := M) g σ :=
  if h : 0 < t then
    heatSemigroupHs (I := I) (M := M) (g := g) h (a := σ) (b := σ)
  else
    ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem heatSemigroupHsExt_zero (g : SmoothRiemannianMetric I M)
    (σ : ℝ) :
    heatSemigroupHsExt (I := I) (M := M) g σ 0 =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHsExt
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHsExt_of_pos {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : 0 < t) :
    heatSemigroupHsExt (I := I) (M := M) g σ t =
      heatSemigroupHs (I := I) (M := M) (g := g) ht (a := σ) (b := σ) := by
  unfold heatSemigroupHsExt
  simp [ht]

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHsExt_of_neg {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : t < 0) :
    heatSemigroupHsExt (I := I) (M := M) g σ t =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHsExt
  have : ¬ 0 < t := not_lt.mpr ht.le
  simp [this]

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHsExt_of_nonpos {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : t ≤ 0) :
    heatSemigroupHsExt (I := I) (M := M) g σ t =
      ContinuousLinearMap.id ℝ (scalarHs (I := I) (M := M) g σ) := by
  unfold heatSemigroupHsExt
  have : ¬ 0 < t := not_lt.mpr ht
  simp [this]

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHsExt_add {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    heatSemigroupHsExt (I := I) (M := M) g σ (t + s) =
      (heatSemigroupHsExt (I := I) (M := M) g σ t).comp
        (heatSemigroupHsExt (I := I) (M := M) g σ s) := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    simp [heatSemigroupHsExt_zero]
  · rcases eq_or_lt_of_le hs with hs_eq | hs_pos
    · subst hs_eq
      simp [heatSemigroupHsExt_zero]
    · have hts : 0 < t + s := by linarith
      rw [heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) hts,
          heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos,
          heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) hs_pos]
      exact heatSemigroupHs_add (I := I) (M := M) (g := g) ht_pos hs_pos (a := σ)

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHsExt_opNorm_le_one {g : SmoothRiemannianMetric I M}
    {σ : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ‖heatSemigroupHsExt (I := I) (M := M) g σ t‖ ≤ 1 := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    rw [heatSemigroupHsExt_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos]
    exact heatSemigroupHs_opNorm_le_one (I := I) (M := M) (g := g) ht_pos

omit [NeZero (Module.finrank ℝ E)] in
theorem heatSemigroupHsExt_coeff {g : SmoothRiemannianMetric I M} {σ : ℝ}
    {t : ℝ} (ht : 0 ≤ t) (T : scalarHs (I := I) (M := M) g σ)
    (i : EigenIdx (I := I) (M := M) g) :
    (heatSemigroupHsExt (I := I) (M := M) g σ t T).coeff i =
      Real.exp (-(EigenIdx.lambda (I := I) (M := M) i) * t) * T.coeff i := by
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · subst ht_eq
    rw [heatSemigroupHsExt_zero]
    change T.coeff i = _
    rw [mul_zero, Real.exp_zero, one_mul]
  · rw [heatSemigroupHsExt_of_pos (I := I) (M := M) (g := g) (σ := σ) ht_pos]
    exact heatSemigroupHs_coeff (I := I) (M := M) (g := g) ht_pos T i

end Hs
end Sobolev
end Analysis
end DifferentialGeometry

end
