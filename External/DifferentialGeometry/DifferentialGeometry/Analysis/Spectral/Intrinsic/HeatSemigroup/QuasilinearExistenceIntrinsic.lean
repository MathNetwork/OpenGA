import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.BoundedC0Intrinsic
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.MildSolutionExistence

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

theorem tensor_quasilinear_heat_mild_solution_existence_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T_0 : TensorL2 r s g)
    {N : TensorL2 r s g → TensorL2 r s g} {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → TensorL2 r s g,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = T_0 ∧
      ∀ t ∈ Set.Icc (0:ℝ) T,
        u t = tensorHeatSemigroup g r s t T_0 +
          ∫ τ in (0:ℝ)..t,
            tensorHeatSemigroup g r s (t - τ) (N (u τ)) := by
  obtain ⟨T, hT_pos, u, hu_cont, hu_zero, hu_eq⟩ :=
    semilinear_mild_solution_existence
      (tensorBoundedC0Semigroup (I := I) (M := M) g r s) T_0 hN
  refine ⟨T, hT_pos, u, hu_cont, hu_zero, ?_⟩
  intro t ht
  have h := hu_eq t ht
  simpa only [tensorBoundedC0Semigroup_intrinsic_apply] using h

theorem tensor_quasilinear_parabolic_unique
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T_0 : TensorL2 r s g)
    {N : TensorL2 r s g → TensorL2 r s g} {L : ℝ≥0} (hN : LipschitzWith L N)
    {T : ℝ} (hT : 0 < T) (hTL : (L : ℝ) * T < 1)
    {u v : ℝ → TensorL2 r s g}
    (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      u t = tensorHeatSemigroup g r s t T_0 +
        ∫ τ in (0:ℝ)..t,
          tensorHeatSemigroup g r s (t - τ) (N (u τ)))
    (hv_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      v t = tensorHeatSemigroup g r s t T_0 +
        ∫ τ in (0:ℝ)..t,
          tensorHeatSemigroup g r s (t - τ) (N (v τ))) :
    Set.EqOn u v (Set.Icc 0 T) := by
  refine semilinear_mild_solution_unique
    (tensorBoundedC0Semigroup (I := I) (M := M) g r s) T_0 hN
    hT hTL hu hv ?_ ?_
  · intro t ht
    simpa only [tensorBoundedC0Semigroup_intrinsic_apply] using hu_eq t ht
  · intro t ht
    simpa only [tensorBoundedC0Semigroup_intrinsic_apply] using hv_eq t ht

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
