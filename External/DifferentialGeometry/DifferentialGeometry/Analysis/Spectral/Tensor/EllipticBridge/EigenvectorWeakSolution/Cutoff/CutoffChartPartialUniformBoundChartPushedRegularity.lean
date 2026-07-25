import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPullCutoff
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.ChartPartialUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartFormLowerOrder
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartKernelCutoff_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ((chartKernelCutoff (I := I) (M := M) α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) :=
  (chartKernelCutoff (I := I) (M := M) α : C^∞⟮I, M; ℝ⟯).contMDiff

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_contDiff_of_contDiff'
    {u : EuclN → ℝ} (hu : ContDiff ℝ ∞ u) (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (euclidPartial (E := E) k u) := by
  have hfd : ContDiff ℝ ∞ (fun z => fderiv ℝ u z) :=
    hu.fderiv_right (m := (∞ : WithTop ℕ∞))
      (by rw [show (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) from rfl])
  have hcomp : euclidPartial (E := E) k u =
      (fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single k 1)) ∘
        (fun z => fderiv ℝ u z) := by
    funext z; rw [euclidPartial_def]; rfl
  rw [hcomp]
  exact (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single k 1)).contDiff.comp hfd

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma cutoffComponentEuclid_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M)
    (cutoffComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S α Idx Jdx)

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartial'_cutoffComponentEuclid_ae_eq_euclidPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      euclidPartial (E := E) k
        (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) := by
  classical
  set u : EuclN → ℝ :=
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx with hu_def
  have hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u :=
    cutoffComponentEuclid_contDiff (I := I) (M := M) g r s S α Idx Jdx
  have hu_cpt : HasCompactSupport u :=
    cutoffComponentEuclid_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx
  have hu_tsupp : tsupport u ⊆ chartTargetEuclid (I := I) (M := M) α :=
    cutoffComponentEuclid_tsupport_subset (I := I) (M := M) g r s S α Idx Jdx
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_W1 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2 u (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩ_open hu_smooth hu_cpt hu_tsupp hp_one 1
  have hu_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hu_W1
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial_smooth_ae_eq
      (d := Module.finrank ℝ E) hp_one hΩ_open hu_smooth hu_W1p k
  refine h_ae.trans (Filter.EventuallyEq.of_eq ?_)
  funext y
  rw [euclidPartial_def]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma chartPushedRaw_rawComponent_continuousOn'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (chartPushedRaw (I := I) (M := M) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (I := I) (M := M) g r s S α Idx Jdx).continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma euclidPartial_chartPushedRaw_rawComponent_continuousOn'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (euclidPartial (E := E) k
        (chartPushedRaw (I := I) (M := M) α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) :=
  (euclidPartial_chartPushedRaw_contDiffOn
    (I := I) (M := M) g r s S α k Idx Jdx).continuousOn

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma cutoffComponentEuclid_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Continuous (cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx) :=
  (cutoffComponentEuclid_contDiff (I := I) (M := M) g r s S α Idx Jdx).continuous

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
