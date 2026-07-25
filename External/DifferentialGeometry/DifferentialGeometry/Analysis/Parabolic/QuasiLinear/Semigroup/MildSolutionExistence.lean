import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.Contraction
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact


noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X]

instance instCompleteSpaceContinuousMapIcc {T : ℝ} :
    CompleteSpace C(↑(Set.Icc (0 : ℝ) T), X) :=
  (ContinuousMap.isometryEquivBoundedOfCompact
    (↑(Set.Icc (0 : ℝ) T)) X).completeSpace

private def pathOfCM {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) : ℝ → X :=
  Set.IccExtend hT0 u

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem continuous_pathOfCM {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) : Continuous (pathOfCM hT0 u) :=
  Continuous.Icc_extend' u.continuous

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem pathOfCM_apply_mem {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    pathOfCM hT0 u τ = u ⟨τ, hτ⟩ :=
  Set.IccExtend_of_mem hT0 u hτ

def duhamelCM (S : BoundedC0Semigroup X) (u₀ : X) {N : X → X} {L : ℝ≥0}
    (hN : LipschitzWith L N) {T : ℝ} (hT0 : (0 : ℝ) ≤ T) :
    C(↑(Set.Icc (0 : ℝ) T), X) → C(↑(Set.Icc (0 : ℝ) T), X) :=
  fun u =>
    ⟨fun t => nlDuhamel S u₀ N (pathOfCM hT0 u) t,
      by
        have h_on : ContinuousOn
            (nlDuhamel S u₀ N (pathOfCM hT0 u)) (Set.Ici 0) :=
          nlDuhamel_continuousOn S u₀ hN (continuous_pathOfCM hT0 u)
        have h_sub : Set.Icc (0 : ℝ) T ⊆ Set.Ici (0 : ℝ) :=
          Set.Icc_subset_Ici_self
        exact (h_on.mono h_sub).restrict⟩

omit [CompleteSpace X] in
@[simp]
theorem duhamelCM_apply (S : BoundedC0Semigroup X) (u₀ : X) {N : X → X}
    {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ} (hT0 : (0 : ℝ) ≤ T)
    (u : C(↑(Set.Icc (0 : ℝ) T), X)) (t : ↑(Set.Icc (0 : ℝ) T)) :
    duhamelCM S u₀ hN hT0 u t =
      nlDuhamel S u₀ N (pathOfCM hT0 u) (t : ℝ) :=
  rfl

omit [CompleteSpace X] in
private theorem duhamelCM_dist_apply_le (S : BoundedC0Semigroup X)
    (u₀ : X) {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) (u v : C(↑(Set.Icc (0 : ℝ) T), X))
    (t : ↑(Set.Icc (0 : ℝ) T)) :
    dist (duhamelCM S u₀ hN hT0 u t) (duhamelCM S u₀ hN hT0 v t) ≤
      (L : ℝ) * T * dist u v := by
  obtain ⟨t, ht⟩ := t
  obtain ⟨ht0, htT⟩ := ht
  have h_forcing_bound : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      ‖pathOfCM hT0 u τ - pathOfCM hT0 v τ‖ ≤ dist u v := by
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T :=
      ⟨hτ.1, le_trans hτ.2 htT⟩
    rw [pathOfCM_apply_mem hT0 u hτT, pathOfCM_apply_mem hT0 v hτT,
      ← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist _
  have h_t_le :
      ‖nlDuhamel S u₀ N (pathOfCM hT0 u) t -
          nlDuhamel S u₀ N (pathOfCM hT0 v) t‖ ≤
        (L : ℝ) * t * dist u v :=
    nlDuhamel_dist_le S u₀ hN (continuous_pathOfCM hT0 u)
      (continuous_pathOfCM hT0 v) ht0 h_forcing_bound
  have h_dist_nn : (0 : ℝ) ≤ dist u v := dist_nonneg
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have h_mono : (L : ℝ) * t * dist u v ≤ (L : ℝ) * T * dist u v := by
    have : (L : ℝ) * t ≤ (L : ℝ) * T :=
      mul_le_mul_of_nonneg_left htT hL_nn
    exact mul_le_mul_of_nonneg_right this h_dist_nn
  calc dist (duhamelCM S u₀ hN hT0 u ⟨t, _⟩)
        (duhamelCM S u₀ hN hT0 v ⟨t, _⟩)
      = ‖nlDuhamel S u₀ N (pathOfCM hT0 u) t -
          nlDuhamel S u₀ N (pathOfCM hT0 v) t‖ := by
        rw [duhamelCM_apply, duhamelCM_apply, dist_eq_norm]
    _ ≤ (L : ℝ) * t * dist u v := h_t_le
    _ ≤ (L : ℝ) * T * dist u v := h_mono

omit [CompleteSpace X] in
private theorem duhamelCM_dist_le (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) (hTL_nn : (0 : ℝ) ≤ (L : ℝ) * T)
    (u v : C(↑(Set.Icc (0 : ℝ) T), X)) :
    dist (duhamelCM S u₀ hN hT0 u) (duhamelCM S u₀ hN hT0 v) ≤
      ((L : ℝ) * T) * dist u v := by
  refine (ContinuousMap.dist_le ?_).mpr ?_
  · exact mul_nonneg hTL_nn dist_nonneg
  · intro t
    exact duhamelCM_dist_apply_le S u₀ hN hT0 u v t

omit [CompleteSpace X] in
theorem duhamelCM_contractingWith (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) (hTL : (L : ℝ) * T < 1) :
    ContractingWith ⟨(L : ℝ) * T, mul_nonneg L.coe_nonneg hT0⟩
      (duhamelCM S u₀ hN hT0) := by
  have hTL_nn : (0 : ℝ) ≤ (L : ℝ) * T := mul_nonneg L.coe_nonneg hT0
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using hTL
  · refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    have h := duhamelCM_dist_le S u₀ hN hT0 hTL_nn u v
    simpa using h

theorem semilinear_mild_solution_existence (S : BoundedC0Semigroup X)
    (u₀ : X) {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → X,
      ContinuousOn u (Set.Icc 0 T) ∧
      u 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ)) := by
  set T : ℝ := 1 / ((L : ℝ) + 1) with hT_def
  have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos L.coe_nonneg one_pos
  have hT_pos : 0 < T := by
    rw [hT_def]
    positivity
  have hT0 : (0 : ℝ) ≤ T := le_of_lt hT_pos
  have hTL : (L : ℝ) * T < 1 := by
    rw [hT_def, mul_one_div, div_lt_one hLp1_pos]
    linarith
  have h_contr := duhamelCM_contractingWith S u₀ hN hT0 hTL
  haveI : Nonempty (↑(Set.Icc (0 : ℝ) T)) :=
    ⟨⟨0, Set.left_mem_Icc.mpr hT0⟩⟩
  set uStar : C(↑(Set.Icc (0 : ℝ) T), X) :=
    ContractingWith.fixedPoint (duhamelCM S u₀ hN hT0) h_contr
      with huStar_def
  have huStar_fix : duhamelCM S u₀ hN hT0 uStar = uStar :=
    (ContractingWith.fixedPoint_isFixedPt h_contr)
  refine ⟨T, hT_pos, pathOfCM hT0 uStar, ?_, ?_, ?_⟩
  · exact (continuous_pathOfCM hT0 uStar).continuousOn
  · have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T :=
      Set.left_mem_Icc.mpr hT0
    rw [pathOfCM_apply_mem hT0 uStar h0_mem]
    have h_fix0 :
        (duhamelCM S u₀ hN hT0 uStar) ⟨0, h0_mem⟩ =
          uStar ⟨0, h0_mem⟩ := by
      rw [huStar_fix]
    rw [← h_fix0, duhamelCM_apply]
    exact nlDuhamel_zero S u₀ N (pathOfCM hT0 uStar)
  · intro t ht
    rw [pathOfCM_apply_mem hT0 uStar ht]
    have h_fixt :
        (duhamelCM S u₀ hN hT0 uStar) ⟨t, ht⟩ = uStar ⟨t, ht⟩ := by
      rw [huStar_fix]
    rw [← h_fixt, duhamelCM_apply]
    unfold nlDuhamel duhamel
    rfl

omit [CompleteSpace X] in
private theorem duhamel_congr (S : BoundedC0Semigroup X) (u₀ : X)
    {F₁ F₂ : ℝ → X} {t : ℝ} (ht : 0 ≤ t)
    (hF : Set.EqOn F₁ F₂ (Set.Icc 0 t)) :
    duhamel S u₀ F₁ t = duhamel S u₀ F₂ t := by
  unfold duhamel
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro τ hτ
  rw [Set.uIcc_of_le ht] at hτ
  change S (t - τ) (F₁ τ) = S (t - τ) (F₂ τ)
  rw [hF hτ]

omit [CompleteSpace X] in
private theorem nlDuhamel_congr (S : BoundedC0Semigroup X) (u₀ : X)
    (N : X → X) {u₁ u₂ : ℝ → X} {t : ℝ} (ht : 0 ≤ t)
    (hu : Set.EqOn u₁ u₂ (Set.Icc 0 t)) :
    nlDuhamel S u₀ N u₁ t = nlDuhamel S u₀ N u₂ t := by
  unfold nlDuhamel
  refine duhamel_congr S u₀ ht ?_
  intro τ hτ
  change N (u₁ τ) = N (u₂ τ)
  rw [hu hτ]

omit [CompleteSpace X] in
private theorem isFixedPt_of_duhamel_solution (S : BoundedC0Semigroup X)
    (u₀ : X) {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ}
    (hT0 : (0 : ℝ) ≤ T) {u : ℝ → X}
    (hu : ContinuousOn u (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ))) :
    duhamelCM S u₀ hN hT0 ⟨_, hu.restrict⟩ = ⟨_, hu.restrict⟩ := by
  ext t
  obtain ⟨t, ht⟩ := t
  have h_eqOn : Set.EqOn
      (pathOfCM hT0 (⟨_, hu.restrict⟩ : C(↑(Set.Icc (0 : ℝ) T), X)))
      u (Set.Icc 0 t) := by
    intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) T :=
      ⟨hτ.1, le_trans hτ.2 ht.2⟩
    rw [pathOfCM_apply_mem hT0 _ hτT]
    rfl
  rw [duhamelCM_apply]
  have h_congr :
      nlDuhamel S u₀ N
          (pathOfCM hT0 (⟨_, hu.restrict⟩ : C(↑(Set.Icc (0 : ℝ) T), X)))
          t =
        nlDuhamel S u₀ N u t :=
    nlDuhamel_congr S u₀ N ht.1 h_eqOn
  rw [h_congr]
  change nlDuhamel S u₀ N u t = u t
  unfold nlDuhamel duhamel
  rw [hu_eq t ht]

theorem semilinear_mild_solution_unique (S : BoundedC0Semigroup X) (u₀ : X)
    {N : X → X} {L : ℝ≥0} (hN : LipschitzWith L N) {T : ℝ} (hT : 0 < T)
    (hTL : (L : ℝ) * T < 1) {u v : ℝ → X}
    (hu : ContinuousOn u (Set.Icc 0 T)) (hv : ContinuousOn v (Set.Icc 0 T))
    (hu_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      u t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (u τ)))
    (hv_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      v t = S t u₀ + ∫ τ in (0 : ℝ)..t, S (t - τ) (N (v τ))) :
    Set.EqOn u v (Set.Icc 0 T) := by
  have hT0 : (0 : ℝ) ≤ T := le_of_lt hT
  have h_contr := duhamelCM_contractingWith S u₀ hN hT0 hTL
  haveI : Nonempty (↑(Set.Icc (0 : ℝ) T)) :=
    ⟨⟨0, Set.left_mem_Icc.mpr hT0⟩⟩
  have hu_fix :
      duhamelCM S u₀ hN hT0 ⟨_, hu.restrict⟩ = ⟨_, hu.restrict⟩ :=
    isFixedPt_of_duhamel_solution S u₀ hN hT0 hu hu_eq
  have hv_fix :
      duhamelCM S u₀ hN hT0 ⟨_, hv.restrict⟩ = ⟨_, hv.restrict⟩ :=
    isFixedPt_of_duhamel_solution S u₀ hN hT0 hv hv_eq
  have h_eq :
      (⟨_, hu.restrict⟩ : C(↑(Set.Icc (0 : ℝ) T), X)) =
        ⟨_, hv.restrict⟩ := by
    rw [ContractingWith.fixedPoint_unique h_contr hu_fix,
      ContractingWith.fixedPoint_unique h_contr hv_fix]
  intro t ht
  have h_ap := ContinuousMap.congr_fun h_eq ⟨t, ht⟩
  simpa using h_ap

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
