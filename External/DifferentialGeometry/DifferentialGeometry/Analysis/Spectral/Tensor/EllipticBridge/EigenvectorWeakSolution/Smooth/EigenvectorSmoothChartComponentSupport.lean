import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSEpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.PouCutoffComponentBridge

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => chartPushedPouWeight (I := I) (M := M) α y *
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
  exact tensorL2ChartComponent_eq_chartPushedPou_mul_cutoff
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i) α Q

omit [CompleteSpace E] in
theorem eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α Q y = 0 := by
  filter_upwards
    [eigenvectorChartComponentFun_ae_eq_chartPushedPouWeight_mul_cutoff
      (I := I) (M := M) g r s i α Q] with y hy hy_zero
  rw [hy, hy_zero, zero_mul]

omit [CompleteSpace E] in
theorem eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_meas : MeasurableSet
      {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0} :=
    measurableSet_eq_fun (chartPushedPouWeight_measurable (I := I) (M := M) α)
      measurable_const
  rw [Filter.EventuallyEq, ae_restrict_iff' h_meas]
  filter_upwards
    [eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
      (I := I) (M := M) g r s i α Q] with y hy hy_zero
  exact hy hy_zero

section ElaborationTestsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      chartPushedPouWeight (I := I) (M := M) α y = 0 →
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α Q y = 0 :=
  eigenvectorChartComponentFun_ae_zero_where_chartPushedPouWeight_zero
    (I := I) (M := M) g r s i α Q

example (α : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α Q
      =ᵐ[(chartL2Measure (I := I) (M := M) α).restrict
        {y : EuclN | chartPushedPouWeight (I := I) (M := M) α y = 0}]
      (fun _ : EuclN => (0 : ℝ)) :=
  eigenvectorChartComponentFun_ae_eq_zero_on_chartPushedPouWeight_zero
    (I := I) (M := M) g r s i α Q

end ElaborationTestsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
