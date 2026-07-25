import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

local instance tangentSpaceNormedAddCommGroup (y : M) :
    NormedAddCommGroup (TangentSpace I y) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance tangentSpaceNormedSpace (y : M) :
    NormedSpace ℝ (TangentSpace I y) :=
  inferInstanceAs (NormedSpace ℝ E)

lemma normalized_bilinear_le_opNorm
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    (Δ : E₀ →L[ℝ] E₀ →L[ℝ] ℝ) (a b : E₀) :
    ‖Δ a b‖ / (‖a‖ * ‖b‖ + 1) ≤ ‖Δ‖ := by
  have h_denom_pos : (0 : ℝ) < ‖a‖ * ‖b‖ + 1 := by positivity
  have h_opNorm_nn : 0 ≤ ‖Δ‖ := norm_nonneg (Δ : E₀ →L[ℝ] E₀ →L[ℝ] ℝ)
  have h_num : ‖Δ a b‖ ≤ ‖Δ‖ * ‖a‖ * ‖b‖ := Δ.le_opNorm₂ a b
  rw [div_le_iff₀ h_denom_pos]
  calc ‖Δ a b‖
      ≤ ‖Δ‖ * ‖a‖ * ‖b‖ := h_num
    _ = ‖Δ‖ * (‖a‖ * ‖b‖) := by ring
    _ ≤ ‖Δ‖ * (‖a‖ * ‖b‖ + 1) := by
        nlinarith [h_opNorm_nn, norm_nonneg a, norm_nonneg b]

lemma iSup_iSup_normalized_le_opNorm
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    (Δ : E₀ →L[ℝ] E₀ →L[ℝ] ℝ) :
    ⨆ a : E₀, ⨆ b : E₀, ‖Δ a b‖ / (‖a‖ * ‖b‖ + 1) ≤ ‖Δ‖ := by
  refine ciSup_le ?_
  intro a
  refine ciSup_le ?_
  intro b
  exact normalized_bilinear_le_opNorm Δ a b

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in

theorem bddAbove_iSup_normalized_of_locally_bounded_opNorm
    (Δ : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (h_local_bound : ∀ y₀ : M, ∃ W : Set M, IsOpen W ∧ y₀ ∈ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ W, ‖Δ b‖ ≤ C) :
    BddAbove (Set.range
      (fun y : M => ⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
        ‖Δ y a b‖ / (‖a‖ * ‖b‖ + 1))) := by
  classical
  set W : M → Set M := fun y₀ => (h_local_bound y₀).choose with hW_def
  have hW_open : ∀ y₀, IsOpen (W y₀) := fun y₀ => (h_local_bound y₀).choose_spec.1
  have hW_mem : ∀ y₀, y₀ ∈ W y₀ := fun y₀ => (h_local_bound y₀).choose_spec.2.1
  set Cₐ : M → ℝ := fun y₀ => (h_local_bound y₀).choose_spec.2.2.choose with hCₐ_def
  have hCₐ_nn : ∀ y₀, 0 ≤ Cₐ y₀ := fun y₀ =>
    (h_local_bound y₀).choose_spec.2.2.choose_spec.1
  have hΔ_bound : ∀ y₀, ∀ b ∈ W y₀, ‖Δ b‖ ≤ Cₐ y₀ := fun y₀ =>
    (h_local_bound y₀).choose_spec.2.2.choose_spec.2
  have hW_cover : (Set.univ : Set M) ⊆ ⋃ y₀ : M, W y₀ := by
    intro x _; exact Set.mem_iUnion.mpr ⟨x, hW_mem x⟩
  rcases isCompact_univ.elim_finite_subcover W hW_open hW_cover with ⟨S, hS_sub⟩
  by_cases hS_empty : S = ∅
  · have h_M_empty : (Set.univ : Set M) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      rcases Set.mem_iUnion₂.mp (hS_sub hx) with ⟨y₀, hy₀, _⟩
      rw [hS_empty] at hy₀
      exact Finset.notMem_empty _ hy₀
    have h_range_empty : (Set.range (fun y : M => ⨆ a : TangentSpace I y,
        ⨆ b : TangentSpace I y, ‖Δ y a b‖ / (‖a‖ * ‖b‖ + 1))) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      rcases hx with ⟨y, _⟩
      have : y ∈ (Set.univ : Set M) := Set.mem_univ y
      rw [h_M_empty] at this
      exact absurd this (Set.notMem_empty _)
    rw [h_range_empty]
    exact bddAbove_empty
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set C : ℝ := S.sup' hS_nonempty Cₐ with hC_def
  refine ⟨C, ?_⟩
  intro x hx
  rcases hx with ⟨y, rfl⟩
  have hy_in : y ∈ Set.univ := Set.mem_univ y
  rcases Set.mem_iUnion₂.mp (hS_sub hy_in) with ⟨y₀, hy₀, hy_W⟩
  have h_iSup_le_Δ : (⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
      ‖Δ y a b‖ / (‖a‖ * ‖b‖ + 1)) ≤ ‖Δ y‖ :=
    iSup_iSup_normalized_le_opNorm (E₀ := TangentSpace I y) (Δ y)
  have h_Δ_bound_y : ‖Δ y‖ ≤ Cₐ y₀ := hΔ_bound y₀ y hy_W
  have h_Cₐ_le_C : Cₐ y₀ ≤ C := by
    rw [hC_def]
    exact Finset.le_sup' Cₐ hy₀
  linarith

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem bddAbove_iSup_normalized_of_continuous_opNorm
    (Δ : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (h_cont : Continuous (fun b : M => ‖Δ b‖)) :
    BddAbove (Set.range
      (fun y : M => ⨆ a : TangentSpace I y, ⨆ b : TangentSpace I y,
        ‖Δ y a b‖ / (‖a‖ * ‖b‖ + 1))) := by
  apply bddAbove_iSup_normalized_of_locally_bounded_opNorm
  intro y₀
  have hca : ContinuousAt (fun b : M => ‖Δ b‖) y₀ := h_cont.continuousAt
  have h_mem : Set.Iic (‖Δ y₀‖ + 1) ∈ nhds (‖Δ y₀‖) :=
    Iic_mem_nhds (by linarith : ‖Δ y₀‖ < ‖Δ y₀‖ + 1)
  have h_pre : (fun b : M => ‖Δ b‖) ⁻¹' Set.Iic (‖Δ y₀‖ + 1) ∈ nhds y₀ :=
    hca.preimage_mem_nhds h_mem
  rw [mem_nhds_iff] at h_pre
  obtain ⟨W, hW_sub, hW_open, hy₀_mem⟩ := h_pre
  refine ⟨W, hW_open, hy₀_mem, ‖Δ y₀‖ + 1, by positivity, fun b hb => ?_⟩
  exact hW_sub hb

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in

theorem bddAbove_opNorm_range_of_locally_bounded
    (Δ : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (h_local_bound : ∀ y₀ : M, ∃ W : Set M, IsOpen W ∧ y₀ ∈ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ W, ‖Δ b‖ ≤ C) :
    BddAbove (Set.range (fun y : M => ‖Δ y‖)) := by
  classical
  set W : M → Set M := fun y₀ => (h_local_bound y₀).choose with hW_def
  have hW_open : ∀ y₀, IsOpen (W y₀) := fun y₀ => (h_local_bound y₀).choose_spec.1
  have hW_mem : ∀ y₀, y₀ ∈ W y₀ := fun y₀ => (h_local_bound y₀).choose_spec.2.1
  set Cₐ : M → ℝ := fun y₀ => (h_local_bound y₀).choose_spec.2.2.choose with hCₐ_def
  have hCₐ_nn : ∀ y₀, 0 ≤ Cₐ y₀ := fun y₀ =>
    (h_local_bound y₀).choose_spec.2.2.choose_spec.1
  have hΔ_bound : ∀ y₀, ∀ b ∈ W y₀, ‖Δ b‖ ≤ Cₐ y₀ := fun y₀ =>
    (h_local_bound y₀).choose_spec.2.2.choose_spec.2
  have hW_cover : (Set.univ : Set M) ⊆ ⋃ y₀ : M, W y₀ := by
    intro x _; exact Set.mem_iUnion.mpr ⟨x, hW_mem x⟩
  rcases isCompact_univ.elim_finite_subcover W hW_open hW_cover with ⟨S, hS_sub⟩
  by_cases hS_empty : S = ∅
  · have h_range_empty : (Set.range (fun y : M => ‖Δ y‖)) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro _ ⟨y, _⟩
      have := Set.mem_iUnion₂.mp (hS_sub (Set.mem_univ y))
      obtain ⟨y₀, hy₀, _⟩ := this
      rw [hS_empty] at hy₀; exact Finset.notMem_empty _ hy₀
    rw [h_range_empty]; exact bddAbove_empty
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set C : ℝ := S.sup' hS_nonempty Cₐ
  refine ⟨C, ?_⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨y₀, hy₀, hy_W⟩ := Set.mem_iUnion₂.mp (hS_sub (Set.mem_univ y))
  exact (hΔ_bound y₀ y hy_W).trans (Finset.le_sup' Cₐ hy₀)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in

theorem bddAbove_opNorm_range_of_continuous_opNorm
    (Δ : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (h_cont : Continuous (fun b : M => ‖Δ b‖)) :
    BddAbove (Set.range (fun y : M => ‖Δ y‖)) := by
  apply bddAbove_opNorm_range_of_locally_bounded
  intro y₀
  have hca : ContinuousAt (fun b : M => ‖Δ b‖) y₀ := h_cont.continuousAt
  have h_mem : Set.Iic (‖Δ y₀‖ + 1) ∈ nhds (‖Δ y₀‖) :=
    Iic_mem_nhds (by linarith : ‖Δ y₀‖ < ‖Δ y₀‖ + 1)
  have h_pre : (fun b : M => ‖Δ b‖) ⁻¹' Set.Iic (‖Δ y₀‖ + 1) ∈ nhds y₀ :=
    hca.preimage_mem_nhds h_mem
  rw [mem_nhds_iff] at h_pre
  obtain ⟨W, hW_sub, hW_open, hy₀_mem⟩ := h_pre
  exact ⟨W, hW_open, hy₀_mem, ‖Δ y₀‖ + 1, by positivity, fun b hb => hW_sub hb⟩

end Connection
end Integral
end DifferentialGeometry
