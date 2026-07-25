import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.RawTensorConnLapNormSqChartPulledReprBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.IteratedFDerivTensorReprChartCompBound
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.FDerivDecompReal


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

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
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartComponentRaw_eq_proj_comp_repr
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx =
      (fun x : M =>
        tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => S.toSection y) x)) := by
  classical
  funext x
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartComponentRaw_symm_eq_proj_comp_repr_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
      (extChartAt I α).symm) =
      (tensorChartComponentProjection (E := E) r s Idx Jdx) ∘
        (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) ∘ (extChartAt I α).symm) := by
  classical
  funext y
  simp only [Function.comp_apply]
  rw [chartComponentRaw_eq_proj_comp_repr (I := I) (M := M) g r s S α Idx Jdx]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorRepr_chart_pulled_contDiffAt_inf
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    ContDiffAt ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
  classical
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hbase :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun x : M => TensorRSSpace r s I x) α).baseSet =
        (chartAt H α).source := by
    change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E)
          (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (chartAt H α).source
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [Set.inter_self]
    rfl
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  have hcm_on_source :
      ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M => tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) b)
        ((chartAt H α).source) := by
    refine ContMDiffOn.congr hrewrite ?_
    intro x hx
    have hx_base : x ∈ (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet := by
      rw [hbase]; exact hx
    change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ x
        (S.toSection x) = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (chartAt H α).source := by
    intro y hy
    have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rwa [extChartAt_source] at hsrc
  have hcomp : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcm_on_source.comp hsymm hmaps
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart
  have hb_target : extChartAt I α b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have h_open_target : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have hcontDiffOn : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcomp.contDiffOn
  exact hcontDiffOn.contDiffAt (h_open_target.mem_nhds hb_target)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorRepr_chart_pulled_contDiffAt_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    ContDiffAt ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b) := by
  classical
  have h := tensorRepr_chart_pulled_contDiffAt_inf
    (I := I) (M := M) g r s S α (b := b) hb_chart
  have h2_le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  exact h.of_le h2_le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma iteratedFDeriv_two_chartComponentRaw_symm_eq_compCMM
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    iteratedFDeriv ℝ 2
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α b) =
    (tensorChartComponentProjection (E := E) r s Idx Jdx).compContinuousMultilinearMap
      (iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => S.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)) := by
  classical
  rw [chartComponentRaw_symm_eq_proj_comp_repr_symm
    (I := I) (M := M) g r s S α Idx Jdx]
  have hcd : ContDiffAt ℝ 2
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y) ∘ (extChartAt I α).symm)
      (extChartAt I α b) :=
    tensorRepr_chart_pulled_contDiffAt_two (I := I) (M := M) g r s S α hb_chart
  exact (tensorChartComponentProjection (E := E) r s Idx Jdx).iteratedFDeriv_comp_left
    (n := 2) hcd (le_refl _)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma norm_iteratedFDeriv_two_chartComponentRaw_symm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb_chart : b ∈ (chartAt H α).source) :
    ‖iteratedFDeriv ℝ 2
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx ∘
        (extChartAt I α).symm)
      (extChartAt I α b)‖ ≤
    ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ *
      ‖iteratedFDeriv ℝ 2
        (tensorRSChartE_section_repr (I := I) r s α
            (fun y : M => S.toSection y) ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
  classical
  rw [iteratedFDeriv_two_chartComponentRaw_symm_eq_compCMM
    (I := I) (M := M) g r s S α Idx Jdx hb_chart]
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

private noncomputable def projectionNormMax (r s : ℕ) : ℝ :=
  ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
    ‖tensorChartComponentProjection (E := E) r s p.1 p.2‖

omit [NeZero (Module.finrank ℝ E)] in
private lemma projectionNormMax_nonneg (r s : ℕ) :
    0 ≤ projectionNormMax (E := E) r s :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
private lemma projection_norm_le_projectionNormMax (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ≤
      projectionNormMax (E := E) r s := by
  classical
  unfold projectionNormMax
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)))))
    (f := fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) =>
      ‖tensorChartComponentProjection (E := E) r s p.1 p.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (Idx, Jdx))
  exact h

omit [CompactSpace M] in
theorem iteratedFDeriv_two_rawTensorConnLap_chartComponentRaw_norm_sq_le_rawRepr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M}, b ∈ (chartAt H α).source →
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ 2
            ((tensorChartComponentRaw (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) ∘
              (extChartAt I α).symm)
            (extChartAt I α b)‖ ^ 2 ≤
          K *
            ‖iteratedFDeriv ℝ 2
              ((tensorRSChartE_section_repr (I := I) r s α
                  (fun y : M =>
                    (rawTensorConnLapSmooth (I := I) g r s T).toSection y)) ∘
                (extChartAt I α).symm)
              (extChartAt I α b)‖ ^ 2 := by
  classical
  set Kp : ℝ := projectionNormMax (E := E) r s with hKp_def
  have hKp_nn : 0 ≤ Kp := projectionNormMax_nonneg (E := E) r s
  set K : ℝ := Kp ^ 2 with hK_def
  have hK_nn : 0 ≤ K := sq_nonneg _
  refine ⟨K, hK_nn, ?_⟩
  intro T b hb_chart Idx Jdx
  set S : SmoothCcTensor g r s := rawTensorConnLapSmooth (I := I) g r s T with hS_def
  have h_norm_le := norm_iteratedFDeriv_two_chartComponentRaw_symm_le
    (I := I) (M := M) g r s S α Idx Jdx hb_chart
  have h_proj_le : ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ≤ Kp :=
    projection_norm_le_projectionNormMax (E := E) r s Idx Jdx
  set R : ℝ :=
    ‖iteratedFDeriv ℝ 2
      ((tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => S.toSection y)) ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖ with hR_def
  have hR_nn : 0 ≤ R := norm_nonneg _
  have h_proj_nn : 0 ≤ ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ :=
    norm_nonneg _
  have h_lhs_le : ‖iteratedFDeriv ℝ 2
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α b)‖ ≤
      ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ * R := h_norm_le
  have h_lhs_nn : 0 ≤ ‖iteratedFDeriv ℝ 2
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α b)‖ := norm_nonneg _
  have h_rhs_chain_nn : 0 ≤
      ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ * R :=
    mul_nonneg h_proj_nn hR_nn
  have h_sq_le : ‖iteratedFDeriv ℝ 2
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α b)‖ ^ 2 ≤
      (‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ * R) ^ 2 :=
    pow_le_pow_left₀ h_lhs_nn h_lhs_le 2
  have h_proj_R_le : ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ * R ≤
      Kp * R :=
    mul_le_mul_of_nonneg_right h_proj_le hR_nn
  have h_step2 : (‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ * R) ^ 2 ≤
      (Kp * R) ^ 2 :=
    pow_le_pow_left₀ h_rhs_chain_nn h_proj_R_le 2
  have h_eq_K : (Kp * R) ^ 2 = K * R ^ 2 := by
    rw [hK_def]; ring
  have h_chain : (‖iteratedFDeriv ℝ 2
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α b)‖ : ℝ) ^ 2 ≤ K * R ^ 2 := by
    calc (‖iteratedFDeriv ℝ 2
            ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
              (extChartAt I α).symm)
            (extChartAt I α b)‖ : ℝ) ^ 2
        ≤ (‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ * R) ^ 2 := h_sq_le
      _ ≤ (Kp * R) ^ 2 := h_step2
      _ = K * R ^ 2 := h_eq_K
  exact h_chain

end Connection
end Integral
end DifferentialGeometry

end
