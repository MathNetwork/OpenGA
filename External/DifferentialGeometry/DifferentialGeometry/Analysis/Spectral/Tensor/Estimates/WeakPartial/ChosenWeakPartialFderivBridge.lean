import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ComponentSobolevBoundDerivBridge
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single k (1 : ℝ))) := by
  have hp_one : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  exact DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chosenWeakPartial_chartPushed_ae_eq_fderiv
    (I := I) (M := M) α hp_one hu k

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem chartPushed_eq_chartSmoothExt_on_target
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u y =
      chartSmoothExt (I := I) (M := M) α
        (fun z : M => ((chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z) y :=
  (DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartSmoothExt_eq_chartPushed_pou_on_target
    (I := I) (M := M) α u hy).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y =
      fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun z : M => ((chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_nhds : chartTargetEuclid (I := I) (M := M) α ∈ nhds y :=
    h_open.mem_nhds hy
  have h_eventually :
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u =ᶠ[nhds y]
        chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z) := by
    refine Filter.eventually_of_mem h_nhds ?_
    intro z hz
    exact chartPushed_eq_chartSmoothExt_on_target (I := I) (M := M) α u hz
  exact Filter.EventuallyEq.fderiv_eq h_eventually

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartPushed
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
          (EuclideanSpace.single k (1 : ℝ))) := by
  classical
  have h_smooth_form :=
    chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
      (I := I) (M := M) (α := α) (u := u) hu k
  have h_fderiv_eq_ae :
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single k (1 : ℝ)))
        =ᵐ[(volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
          (EuclideanSpace.single k (1 : ℝ))) := by
    have h_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    refine Filter.eventually_of_mem (self_mem_ae_restrict h_meas) ?_
    intro y hy
    simp only
    rw [fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target
      (I := I) (M := M) α u hy]
  exact h_smooth_form.trans h_fderiv_eq_ae

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartial'_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartSmoothExt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) β
          (fun z : M => ((chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx z)) y
          (EuclideanSpace.single k (1 : ℝ))) :=
  chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenWeakPartial'_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) y
          (EuclideanSpace.single k (1 : ℝ))) :=
  chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartPushed
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartSmoothExt (I := I) (M := M) α
            (fun z : M => ((chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_congr_ae
    (chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
      (I := I) (M := M) (α := α) (u := u) hu k)

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartPushed
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_congr_ae
    (chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartPushed
      (I := I) (M := M) (α := α) (u := u) hu k)

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartSmoothExt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartSmoothExt (I := I) (M := M) β
            (fun z : M => ((chartAtlasPOU I M β
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
              tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx z)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) :=
  eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) :=
  eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartPushed
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
