import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCurryFactor
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.ChristoffelDecomp


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorRSChartE_section_repr_eq_tensorTrivProj
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) :
    tensorRSChartE_section_repr (I := I) r s α S.toSection =
      tensorTrivProj (I := I) (M := M) g r s S α :=
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorRSIntrinsicChartCLM_proj_eq_fderiv_component
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source)
    (hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (v : TangentSpace I b) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection b v)) =
      fderiv ℝ
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
          (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b v) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  have hb_baseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ ((trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet)
    exact ⟨hb_base, hb_base⟩
  rw [tensorRSIntrinsicChartCLM_apply (I := I) r s α S.toSection b v]
  unfold tensorRSChartFiberFromModel
  rw [(trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt_symmL
      (R := ℝ) hb_baseRS]
  rw [tensorRSChartE_section_repr_eq_tensorTrivProj (I := I) (M := M) g r s S α]
  rw [tensorChartComponentRaw_partial_decomp (I := I) (M := M) g r s α S
    hb_chart hb_int Idx Jdx (trivToE (I := I) α b v)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem tensorRSIntrinsicChartCLM_component_eq_euclidPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorRSIntrinsicChartCLM (I := I) r s α S.toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (chartBasisVecFiber (I := I) α k
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))))) =
      euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]
    exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hb_chart
  rw [tensorRSIntrinsicChartCLM_proj_eq_fderiv_component (I := I) (M := M)
    g r s S α Idx Jdx hb_chart hb_int (chartBasisVecFiber (I := I) α k b)]
  have htriv_basis :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α k b) =
        chartModelBasis E k := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b (chartModelBasis E k)) = _
    exact trivToE_trivFromE (I := I) α hb_base (chartModelBasis E k)
  rw [htriv_basis, chartModelBasis_apply, hphi_b]
  rw [euclidPartial_def]
  have hpushed_eq :
      chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) =ᶠ[𝓝 y]
        ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
            (extChartAt I α).symm) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hz
  rw [Filter.EventuallyEq.fderiv_eq hpushed_eq]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
      (extChartAt I α).symm) (x := y)]
  rfl

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
