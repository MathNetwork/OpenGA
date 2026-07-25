import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.POUFDerivBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem fderiv_chartPushed_tensorChartComponentScalar_eq_leibniz_on_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) y =
      chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y •
          fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx)) y +
        chartSmoothExt (I := I) (M := M) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) y •
          fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y := by
  classical
  have hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
    tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx
  exact fderiv_chartPushed_pou_eq_leibniz_on_target
    (I := I) (M := M) (α := α)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    hu_smooth hy

omit [NeZero (Module.finrank ℝ E)] in
theorem fderiv_chartPushed_tensorChartComponentScalar_eventuallyEq_leibniz
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (fun z : EuclN E =>
        fderiv ℝ
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) z) =ᶠ[nhds y]
      (fun z : EuclN E =>
        chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) z •
            fderiv ℝ
              (chartSmoothExt (I := I) (M := M) α
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S α Idx Jdx)) z +
          chartSmoothExt (I := I) (M := M) α
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) z •
            fderiv ℝ
              (chartSmoothExt (I := I) (M := M) α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) z) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine Filter.eventually_of_mem (h_open.mem_nhds hy) ?_
  intro z hz
  exact fderiv_chartPushed_tensorChartComponentScalar_eq_leibniz_on_target
    (I := I) (M := M) g r s α S Idx Jdx hz

omit [NeZero (Module.finrank ℝ E)] in
theorem fderiv_chartPushed_tensorChartComponentPou_eq_leibniz_on_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          (tensorChartComponentPou (I := I) (M := M)
            g r s S α Idx Jdx)) y =
      chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y •
          fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              (tensorChartComponentPou (I := I) (M := M)
                g r s S α Idx Jdx)) y +
        chartSmoothExt (I := I) (M := M) α
            (tensorChartComponentPou (I := I) (M := M)
              g r s S α Idx Jdx) y •
          fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y := by
  have h_eq :
      tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx =
        tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx :=
    tensorChartComponentScalar_def
      (I := I) (M := M) g r s S α Idx Jdx
  have h_main :=
    fderiv_chartPushed_tensorChartComponentScalar_eq_leibniz_on_target
      (I := I) (M := M) g r s α S Idx Jdx hy
  rw [h_eq] at h_main
  exact h_main

example (g : SmoothRiemannianMetric I M) (α : M)
    (S : SmoothCcTensor g 1 2)
    (Idx : Fin 1 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    {y : EuclN E} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          (tensorChartComponentScalar (I := I) (M := M)
            g 1 2 S α Idx Jdx)) y =
      chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y •
          fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              (tensorChartComponentScalar (I := I) (M := M)
                g 1 2 S α Idx Jdx)) y +
        chartSmoothExt (I := I) (M := M) α
            (tensorChartComponentScalar (I := I) (M := M)
              g 1 2 S α Idx Jdx) y •
          fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y :=
  fderiv_chartPushed_tensorChartComponentScalar_eq_leibniz_on_target
    (I := I) (M := M) g 1 2 α S Idx Jdx hy

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
