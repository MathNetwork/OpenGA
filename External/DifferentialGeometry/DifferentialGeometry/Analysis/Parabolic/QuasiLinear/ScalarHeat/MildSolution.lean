import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.MildSolutionExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.ScalarHeat.HeatSemigroupInstance

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Analysis.Laplacian.Spectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_quasilinear_local_existence
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (u₀ : scalarHs (I := I) (M := M) g σ)
    {N : scalarHs (I := I) (M := M) g σ → scalarHs (I := I) (M := M) g σ}
    {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → scalarHs (I := I) (M := M) g σ,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatSemigroupHsExt (I := I) (M := M) g σ t u₀ +
          ∫ τ in (0:ℝ)..t,
            heatSemigroupHsExt (I := I) (M := M) g σ (t - τ) (N (u τ)) := by
  obtain ⟨T, hT_pos, u, hu_cont, hu_zero, hu_eq⟩ :=
    semilinear_mild_solution_existence
      (scalarHsBoundedC0Semigroup (I := I) (M := M) g σ) u₀ hN
  refine ⟨T, hT_pos, u, hu_cont, hu_zero, ?_⟩
  intro t ht
  have h := hu_eq t ht
  simpa only [scalarHsBoundedC0Semigroup_apply] using h

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_quasilinear_local_unique
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (u₀ : scalarHs (I := I) (M := M) g σ)
    {N : scalarHs (I := I) (M := M) g σ → scalarHs (I := I) (M := M) g σ}
    {L : ℝ≥0} (hN : LipschitzWith L N)
    {T : ℝ} (hT : 0 < T) (hTL : (L : ℝ) * T < 1)
    {u v : ℝ → scalarHs (I := I) (M := M) g σ}
    (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = heatSemigroupHsExt (I := I) (M := M) g σ t u₀ +
        ∫ τ in (0:ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g σ (t - τ) (N (u τ)))
    (hv_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = heatSemigroupHsExt (I := I) (M := M) g σ t u₀ +
        ∫ τ in (0:ℝ)..t,
          heatSemigroupHsExt (I := I) (M := M) g σ (t - τ) (N (v τ))) :
    Set.EqOn u v (Set.Icc 0 T) := by
  refine semilinear_mild_solution_unique
    (scalarHsBoundedC0Semigroup (I := I) (M := M) g σ) u₀ hN
    hT hTL hu hv ?_ ?_
  · intro t ht
    simpa only [scalarHsBoundedC0Semigroup_apply] using hu_eq t ht
  · intro t ht
    simpa only [scalarHsBoundedC0Semigroup_apply] using hv_eq t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem scalar_quasilinear_local_existence_Hk
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    (u₀ : HkScalar (I := I) (M := M) g k)
    {N : HkScalar (I := I) (M := M) g k → HkScalar (I := I) (M := M) g k}
    {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → HkScalar (I := I) (M := M) g k,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = heatSemigroupHsExt (I := I) (M := M) g (k : ℝ) t u₀ +
          ∫ τ in (0:ℝ)..t,
            heatSemigroupHsExt (I := I) (M := M) g (k : ℝ) (t - τ) (N (u τ)) :=
  scalar_quasilinear_local_existence (I := I) (M := M) g (k : ℝ) u₀ hN

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
