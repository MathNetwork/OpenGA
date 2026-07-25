import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.ChartPulledTensorReprChartCompBound


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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma tensorRepr_chart_pulled_component_contDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    ContDiffAt ℝ 2
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
  have hcd_at_inf : ContDiffAt ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
        (extChartAt I α).symm) (extChartAt I α b) :=
    hcontDiffOn.contDiffAt (h_open_target.mem_nhds hb_target)
  have h2_le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  exact hcd_at_inf.of_le h2_le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma iteratedFDeriv_two_smul_const_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → ℝ) (v : F) {y : E}
    (hf : ContDiffAt ℝ 2 f y) :
    ‖iteratedFDeriv ℝ 2 (fun z : E => f z • v) y‖ ≤
      ‖iteratedFDeriv ℝ 2 f y‖ * ‖v‖ := by
  rw [iteratedFDeriv_smul_const_apply (v := v) hf]
  calc
    ‖((ContinuousLinearMap.id ℝ ℝ).smulRight v).compContinuousMultilinearMap
        (iteratedFDeriv ℝ 2 f y)‖
        ≤ ‖(ContinuousLinearMap.id ℝ ℝ).smulRight v‖ *
            ‖iteratedFDeriv ℝ 2 f y‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ = ‖v‖ * ‖iteratedFDeriv ℝ 2 f y‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply,
            ContinuousLinearMap.norm_id, one_mul]
    _ = ‖iteratedFDeriv ℝ 2 f y‖ * ‖v‖ := by rw [mul_comm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma iteratedFDeriv_two_tensorRepr_opNorm_le_sum_iteratedFDeriv_components
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) {b : M}
    (hb_chart : b ∈ (chartAt H α).source) :
    ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ ≤
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          ‖iteratedFDeriv ℝ 2
              (tensorChartComponentRaw (I := I) (M := M) g r s T α
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
  have hcd_each := fun Idx Jdx =>
    tensorRepr_chart_pulled_component_contDiffAt
      (I := I) (M := M) g r s T α Idx Jdx hb_chart
  have hcd_summand : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
        ContDiffAt ℝ 2
          (fun y : E =>
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
                (extChartAt I α).symm) y •
              tensorChartBasisElement (E := E) r s Idx Jdx)
          (extChartAt I α b) := fun Idx Jdx =>
    (hcd_each Idx Jdx).smul_const _
  have hcd_inner_sum : ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ContDiffAt ℝ 2
        (fun y : E => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx ∘
              (extChartAt I α).symm) y •
            tensorChartBasisElement (E := E) r s Idx Jdx)
        (extChartAt I α b) := fun Idx =>
    ContDiffAt.sum (fun Jdx _ => hcd_summand Idx Jdx)
  rw [iteratedFDeriv_fun_sum_apply (fun Idx _ => hcd_inner_sum Idx)]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Idx _
  rw [iteratedFDeriv_fun_sum_apply (fun Jdx _ => hcd_summand Idx Jdx)]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum ?_
  intro Jdx _
  exact iteratedFDeriv_two_smul_const_norm_le _ _ (hcd_each Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem iteratedFDeriv_two_tensorRSChartE_section_repr_opNorm_le_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ (chartAt H α).source →
        ‖iteratedFDeriv ℝ 2
          (tensorRSChartE_section_repr (I := I) r s α
              (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖
        ≤ K * (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ‖iteratedFDeriv ℝ 2
                (tensorChartComponentRaw (I := I) (M := M) g r s T α
                  Idx Jdx ∘ (extChartAt I α).symm) (extChartAt I α b)‖) := by
  classical
  set K_basis : ℝ := tensorChartBasisNormConstant (E := E) r s with hK_basis_def
  have hK_basis_nn : 0 ≤ K_basis :=
    tensorChartBasisNormConstant_nonneg (E := E) r s
  refine ⟨K_basis, hK_basis_nn, ?_⟩
  intro b hb_chart
  refine le_trans
    (iteratedFDeriv_two_tensorRepr_opNorm_le_sum_iteratedFDeriv_components
      (I := I) (M := M) g r s T α (b := b) hb_chart) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro Idx _
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [mul_comm K_basis _]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact tensorChartBasisElement_norm_le (E := E) r s Idx Jdx

end Connection
end Integral
end DifferentialGeometry

end
