import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.ChartTensorRSCovariantDerivativeOpNorm
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartReprNormBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.TensorRSChartFiberForwardOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartLeviCivitaParallelCLMOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma reprNorm_le_sum_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (b : M) :
    ‖tensorRSChartE_section_repr (I := I) r s α
        (fun y : M => T.toSection y) b‖ ≤
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          |tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b| *
            tensorChartBasisNormConstant (E := E) r s := by
  classical
  set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
    r s α (fun y : M => T.toSection y) b with hR_def
  have hR_recover : R =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComponentProjection (E := E) r s Idx Jdx R •
            tensorChartBasisElement (E := E) r s Idx Jdx :=
    tensorRSModel_eq_sum_basis (E := E) r s R
  have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComponentProjection (E := E) r s Idx Jdx R =
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx b := by
    intro Idx Jdx
    rw [tensorChartComponentRaw_def]
    rfl
  change ‖R‖ ≤ _
  rw [hR_recover]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Idx _
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [norm_smul, Real.norm_eq_abs, hcomp_eq Idx Jdx]
  exact mul_le_mul_of_nonneg_left
    (tensorChartBasisElement_norm_le (E := E) r s Idx Jdx)
    (abs_nonneg _)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma chart_pulled_component_differentiableAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    DifferentiableAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α b) := by
  classical
  have hsmooth_on := tensorChartComponentRaw_contMDiffOn_chart_source
    (I := I) (M := M) g r s T α Idx Jdx
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (chartAt H α).source := by
    intro y hy
    have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rwa [extChartAt_source] at hsrc
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hsmooth_on.comp hsymm hmaps
  have hb_src : b ∈ (extChartAt I α).source :=
    (extChartAt_source (I := I) α).symm ▸ hb_chart
  have hb_target : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have h_open_target : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have hcontDiffOn : ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α).target :=
    hcomp.contDiffOn
  have hcdAt : ContDiffWithinAt ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α).target (extChartAt I α b) :=
    hcontDiffOn _ hb_target
  have hwithin : DifferentiableWithinAt ℝ
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α).target (extChartAt I α b) :=
    hcdAt.differentiableWithinAt (by norm_num)
  exact hwithin.differentiableAt (h_open_target.mem_nhds hb_target)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma fderiv_repr_opNorm_le_sum_fderiv_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source) :
    ‖fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ ≤
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ‖fderiv ℝ (tensorChartComponentRaw (I := I) (M := M) g r s T α
              Idx Jdx ∘ (extChartAt I α).symm) (extChartAt I α b)‖ *
            ‖tensorChartBasisElement (E := E) r s Idx Jdx‖ := by
  classical
  have hψ_eq :
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm) =
        fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx := by
    funext y
    set bb := (extChartAt I α).symm y
    set R : TensorRSModel r s ℝ E := tensorRSChartE_section_repr (I := I)
      r s α (fun z : M => T.toSection z) bb
    have hR_recover : R =
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            tensorChartComponentProjection (E := E) r s Idx Jdx R •
              tensorChartBasisElement (E := E) r s Idx Jdx :=
      tensorRSModel_eq_sum_basis (E := E) r s R
    have hcomp_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s Idx Jdx R =
          tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx bb := by
      intro Idx Jdx
      rw [tensorChartComponentRaw_def]
      rfl
    change R = _
    rw [hR_recover]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    refine Finset.sum_congr rfl ?_
    intro Jdx _
    rw [hcomp_eq Idx Jdx]
    rfl
  rw [hψ_eq]
  have hdiff_each := fun Idx Jdx =>
    chart_pulled_component_differentiableAt (I := I) (M := M)
      g r s T α Idx Jdx hb_chart
  have hfderiv_sum :
      fderiv ℝ
        (fun y : E =>
          ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
        (extChartAt I α b) =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          fderiv ℝ
            (fun y : E =>
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
            (extChartAt I α b) := by
    have hd_inner : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
          DifferentiableAt ℝ
            (fun y : E =>
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                  (extChartAt I α).symm) y •
                tensorChartBasisElement (E := E) r s Idx Jdx)
            (extChartAt I α b) := fun Idx Jdx => (hdiff_each Idx Jdx).smul_const _
    have hd_inner_sum : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ
          (fun y : E => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) y •
              tensorChartBasisElement (E := E) r s Idx Jdx)
          (extChartAt I α b) := fun Idx =>
      DifferentiableAt.fun_sum (fun Jdx _ => hd_inner Idx Jdx)
    rw [fderiv_fun_sum (fun Idx _ => hd_inner_sum Idx)]
    refine Finset.sum_congr rfl ?_
    intro Idx _
    exact fderiv_fun_sum (fun Jdx _ => hd_inner Idx Jdx)
  rw [hfderiv_sum]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Idx _
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [fderiv_smul_const (hdiff_each Idx Jdx)]
  rw [ContinuousLinearMap.norm_smulRight_apply]

end Connection
end Integral
end DifferentialGeometry

end
