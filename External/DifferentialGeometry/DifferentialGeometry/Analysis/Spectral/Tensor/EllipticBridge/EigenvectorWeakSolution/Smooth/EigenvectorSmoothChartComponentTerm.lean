import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradLeibniz

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

open Classical in

omit [CompleteSpace E] in
private lemma raw_eigenvectorSmoothChart_eq_ite
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α β : M) (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hxβ : x ∈ (chartAt H β).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        β P₀.1 P₀.2 x =
      (if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
              α Q.1 Q.2 x
        else 0) := by
  classical
  by_cases hxα : x ∈ (chartAt H α).source
  · rw [if_pos hxα]
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s
      (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
      α β P₀ ⟨hxα, hxβ⟩
  · rw [if_neg hxα]
    exact tensorChartComponentRaw_eigenvectorSmoothChart_eq_zero_off_source
      (I := I) (M := M) g r s i α β P₀ hxα

open Classical in

omit [CompleteSpace E] in
theorem eigenvectorSmoothChart_tensorL2ChartComponent_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (α β : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α :
          TensorL2 r s g) β P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => chartPushedRaw I β
          (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
        chartPushedRaw I β
          (fun x => if x ∈ (chartAt H α).source then
            ∑ Q : TensorCompIdx (E := E) r s,
              transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
                tensorChartComponentRaw (I := I) (M := M) g r s
                  (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
                  α Q.1 Q.2 x
            else 0) y) := by
  classical
  have h_coeFn :=
    tensorL2ChartComponent_smoothToTensorL2_coeFn (I := I) (M := M) g r s
      (eigenvectorSmoothChart (I := I) (M := M) g r s i α) β P₀
  have h_mem : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∈ chartTargetEuclid (I := I) (M := M) β := by
    rw [chartL2Measure]
    exact ae_restrict_mem (chartTargetEuclid_measurableSet (I := I) (M := M) β)
  filter_upwards [h_coeFn, h_mem] with y hy_coe hy
  rw [hy_coe]
  rw [tensorChartComponent_eq_chartPushedRaw_pou_mul_chartPushedRaw_raw_on_target
    (I := I) (M := M) g r s
    (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
    β P₀.1 P₀.2 hy]
  congr 1
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (tensorChartComponentRaw (I := I) (M := M) g r s
        (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
        β P₀.1 P₀.2) hy,
    chartPushedRaw_apply_of_mem (I := I) (M := M) β
      (fun x => if x ∈ (chartAt H α).source then
        ∑ Q : TensorCompIdx (E := E) r s,
          transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart (I := I) (M := M) g r s i α)
              α Q.1 Q.2 x
        else 0) hy]
  exact raw_eigenvectorSmoothChart_eq_ite (I := I) (M := M) g r s
    i α β P₀ (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
