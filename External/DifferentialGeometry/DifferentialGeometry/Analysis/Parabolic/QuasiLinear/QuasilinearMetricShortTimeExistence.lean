import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.MildSolutionExistence
import DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol
import DifferentialGeometry.Geometry.Flow.RicciFlow.PrincipalSymbol
import Mathlib.Geometry.Manifold.MFDeriv.Basic


namespace DifferentialGeometry
namespace PDE

universe u v

open scoped Manifold ContDiff Topology
open Bundle MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def IsQuasilinearMetricParabolicSolution
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M) (T : ℝ)
    (g_fam : ℝ → SmoothRiemannianMetric I M) : Prop :=
  0 < T ∧ g_fam 0 = g₀ ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
                  (F (g_fam t) x v w) (Set.Ici 0) t

def IsStrictlyParabolicMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
    DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol F g σ

def IsSmoothQuasilinearMetricRHS
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) : Prop :=
  (∀ (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x => F g x
          ((trivializationAt E (TangentSpace I) α).symmL ℝ x
            (DifferentialGeometry.Integral.Measure.chartModelBasis E i))
          ((trivializationAt E (TangentSpace I) α).symmL ℝ x
            (DifferentialGeometry.Integral.Measure.chartModelBasis E j)))
        (chartAt H α).source)
    ∧ ∀ g : SmoothRiemannianMetric I M, IsStrictlyParabolicMetricRHS F g

def IsLinearTensorParabolicMildSolution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (T : ℝ) (u : ℝ → X) : Prop :=
  0 < T ∧ u 0 = u₀ ∧
    ContinuousOn u (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (F τ)

omit [SigmaCompactSpace M] [T2Space M] in
theorem linear_tensor_parabolic_shortTime_exists
    [CompactSpace M]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (S : Analysis.Parabolic.QuasiLinear.BoundedC0Semigroup X) (u₀ : X)
    (F : ℝ → X) (hF : Continuous F) :
    ∃ T : ℝ, ∃ u : ℝ → X,
      IsLinearTensorParabolicMildSolution S u₀ F T u := by
  refine ⟨1, Analysis.Parabolic.QuasiLinear.duhamel S u₀ F, ?_, ?_, ?_, ?_⟩
  · exact zero_lt_one
  · exact Analysis.Parabolic.QuasiLinear.duhamel_zero S u₀ F
  · have h_cont :
        ContinuousOn (Analysis.Parabolic.QuasiLinear.duhamel S u₀ F)
          (Set.Ici (0 : ℝ)) :=
      Analysis.Parabolic.QuasiLinear.duhamel_continuousOn S u₀ hF
    exact h_cont.mono (Set.Icc_subset_Ici_self)
  · intro t _
    rfl

end PDE
end DifferentialGeometry
