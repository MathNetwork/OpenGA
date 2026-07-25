import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.IteratedInvGramJetLipschitz


noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure HasChartJetLip
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M) (K : Set E)
    (F : SmoothRiemannianMetric I M → E → ℝ) (d : ℕ) : Prop where

  contDiff : ∀ g : SmoothRiemannianMetric I M,
    ContDiffOn ℝ ∞ (F g) (interior (extChartAt I α).target)

  bound : ∀ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ∀ m : ℕ, m ≤ N →
    ‖iteratedFDerivWithin ℝ m (F g₁) (interior (extChartAt I α).target) y‖ ≤ B ∧
      ‖iteratedFDerivWithin ℝ m (F g₂) (interior (extChartAt I α).target) y‖ ≤ B

  lip : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K,
    ‖iteratedFDerivWithin ℝ N (fun z => F g₁ z - F g₂ z)
        (interior (extChartAt I α).target) y‖ ≤
      C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α
        (interior (extChartAt I α).target) y

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.congr
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    {F F' : SmoothRiemannianMetric I M → E → ℝ} {d : ℕ}
    (hF : HasChartJetLip g₁ g₂ α K F d)
    (hFF' : ∀ g, F g = F' g) :
    HasChartJetLip g₁ g₂ α K F' d := by
  have hrw : F' = F := by funext g; exact (hFF' g).symm
  rw [hrw]; exact hF

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.of_le
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    {F : SmoothRiemannianMetric I M → E → ℝ} {d d' : ℕ} (hd : d ≤ d')
    (hF : HasChartJetLip g₁ g₂ α K F d) :
    HasChartJetLip g₁ g₂ α K F d' := by
  refine ⟨hF.contDiff, hF.bound, fun N => ?_⟩
  obtain ⟨C, hC_pos, hC⟩ := hF.lip N
  refine ⟨C, hC_pos, fun y hy => (hC y hy).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hC_pos.le
  exact chartGramJetDiffSeminormSum_mono (I := I) (M := M) (by omega) g₁ g₂ α _ y

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.const_smul
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F : SmoothRiemannianMetric I M → E → ℝ} {d : ℕ}
    (hF : HasChartJetLip g₁ g₂ α K F d) (c : ℝ) :
    HasChartJetLip g₁ g₂ α K (fun g => fun z => c * F g z) d := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  have hsmul : ∀ (g : SmoothRiemannianMetric I M) (m : ℕ) {y : E}, y ∈ s →
      iteratedFDerivWithin ℝ m (fun z => c * F g z) s y =
        c • iteratedFDerivWithin ℝ m (F g) s y := by
    intro g m y hy
    have hfun : (fun z => c * F g z) = (c • F g) := by funext z; rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact iteratedFDerivWithin_const_smul_apply
      (((hF.contDiff g).contDiffWithinAt hy).of_le (by exact_mod_cast le_top))
      hs_open.uniqueDiffOn hy
  refine ⟨fun g => contDiffOn_const.mul (hF.contDiff g), fun N => ?_, fun N => ?_⟩
  · obtain ⟨B, hB_nn, hB⟩ := hF.bound N
    refine ⟨|c| * B, mul_nonneg (abs_nonneg _) hB_nn, fun y hy m hm => ?_⟩
    have hyS : y ∈ s := hKsub hy
    obtain ⟨hB1, hB2⟩ := hB y hy m hm
    constructor
    · rw [hsmul g₁ m hyS]
      refine (norm_smul_le c _).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)
    · rw [hsmul g₂ m hyS]
      refine (norm_smul_le c _).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hB2 (abs_nonneg _)
  · obtain ⟨C, hC_pos, hC⟩ := hF.lip N
    refine ⟨|c| * C + 1, by positivity, fun y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hdiff : (fun z => c * F g₁ z - c * F g₂ z) =
        (c • (fun w => F g₁ w - F g₂ w)) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hdiff,
      iteratedFDerivWithin_const_smul_apply
        ((((hF.contDiff g₁).sub (hF.contDiff g₂)).contDiffWithinAt hyS).of_le
          (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hyS]
    refine (norm_smul_le c _).trans ?_
    rw [Real.norm_eq_abs]
    have hsem_nn : 0 ≤ chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + d) g₁ g₂ α s y
    calc |c| * ‖iteratedFDerivWithin ℝ N (fun w => F g₁ w - F g₂ w) s y‖
        ≤ |c| * (C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y) :=
          mul_le_mul_of_nonneg_left (hC y hy) (abs_nonneg _)
      _ = (|c| * C) * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y := by ring
      _ ≤ (|c| * C + 1) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y := by
          refine mul_le_mul_of_nonneg_right ?_ hsem_nn; linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.add
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F G : SmoothRiemannianMetric I M → E → ℝ} {dF dG : ℕ}
    (hF : HasChartJetLip g₁ g₂ α K F dF) (hG : HasChartJetLip g₁ g₂ α K G dG) :
    HasChartJetLip g₁ g₂ α K (fun g => fun z => F g z + G g z) (max dF dG) := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  have hF' := hF.of_le (le_max_left dF dG)
  have hG' := hG.of_le (le_max_right dF dG)
  refine ⟨fun g => (hF.contDiff g).add (hG.contDiff g), fun N => ?_, fun N => ?_⟩
  · obtain ⟨BF, hBF_nn, hBF⟩ := hF.bound N
    obtain ⟨BG, hBG_nn, hBG⟩ := hG.bound N
    refine ⟨BF + BG, by linarith, fun y hy m hm => ?_⟩
    have hyS : y ∈ s := hKsub hy
    obtain ⟨hBF1, hBF2⟩ := hBF y hy m hm
    obtain ⟨hBG1, hBG2⟩ := hBG y hy m hm
    have haddF : iteratedFDerivWithin ℝ m (fun z => F g₁ z + G g₁ z) s y =
        iteratedFDerivWithin ℝ m (F g₁) s y + iteratedFDerivWithin ℝ m (G g₁) s y :=
      iteratedFDerivWithin_add_apply (((hF.contDiff g₁).contDiffWithinAt hyS).of_le
        (by exact_mod_cast le_top)) (((hG.contDiff g₁).contDiffWithinAt hyS).of_le
        (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hyS
    have haddG : iteratedFDerivWithin ℝ m (fun z => F g₂ z + G g₂ z) s y =
        iteratedFDerivWithin ℝ m (F g₂) s y + iteratedFDerivWithin ℝ m (G g₂) s y :=
      iteratedFDerivWithin_add_apply (((hF.contDiff g₂).contDiffWithinAt hyS).of_le
        (by exact_mod_cast le_top)) (((hG.contDiff g₂).contDiffWithinAt hyS).of_le
        (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hyS
    refine ⟨?_, ?_⟩
    · rw [haddF]; exact (norm_add_le _ _).trans (add_le_add hBF1 hBG1)
    · rw [haddG]; exact (norm_add_le _ _).trans (add_le_add hBF2 hBG2)
  · obtain ⟨CF, hCF_pos, hCF⟩ := hF'.lip N
    obtain ⟨CG, hCG_pos, hCG⟩ := hG'.lip N
    refine ⟨CF + CG, by linarith, fun y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hdiff : (fun z => (F g₁ z + G g₁ z) - (F g₂ z + G g₂ z)) =
        (fun z => (fun w => F g₁ w - F g₂ w) z + (fun w => G g₁ w - G g₂ w) z) := by
      funext z; ring
    rw [hdiff]
    have hadd : iteratedFDerivWithin ℝ N
          (fun z => (fun w => F g₁ w - F g₂ w) z + (fun w => G g₁ w - G g₂ w) z) s y =
        iteratedFDerivWithin ℝ N (fun w => F g₁ w - F g₂ w) s y +
          iteratedFDerivWithin ℝ N (fun w => G g₁ w - G g₂ w) s y :=
      iteratedFDerivWithin_add_apply
        ((((hF.contDiff g₁).sub (hF.contDiff g₂)).contDiffWithinAt hyS).of_le
          (by exact_mod_cast le_top))
        ((((hG.contDiff g₁).sub (hG.contDiff g₂)).contDiffWithinAt hyS).of_le
          (by exact_mod_cast le_top)) hs_open.uniqueDiffOn hyS
    rw [hadd]
    have hsem_nn : 0 ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (hCF y hy) (hCG y hy)).trans ?_
    rw [← add_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.seminorm_le
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    {F : SmoothRiemannianMetric I M → E → ℝ} {d : ℕ}
    (hF : HasChartJetLip g₁ g₂ α K F d) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K,
      iteratedFDerivSeminorm N (fun z => F g₁ z - F g₂ z)
          (interior (extChartAt I α).target) y ≤
        C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hper : ∀ l : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K,
      ‖iteratedFDerivWithin ℝ l (fun z => F g₁ z - F g₂ z) s y‖ ≤
        C * chartGramJetDiffSeminormSum (I := I) (M := M) (l + d) g₁ g₂ α s y :=
    fun l => hF.lip l
  choose Cl hCl_pos hCl using hper
  refine ⟨∑ l ∈ Finset.range (N + 1), Cl l, ?_, fun y hy => ?_⟩
  · refine Finset.sum_pos (fun l _ => hCl_pos l) ⟨0, Finset.mem_range.mpr (by omega)⟩
  · have hsem_nn : 0 ≤ chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + d) g₁ g₂ α s y
    unfold iteratedFDerivSeminorm
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    have hlN : l ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    refine (hCl l y hy).trans ?_
    have hmono : chartGramJetDiffSeminormSum (I := I) (M := M) (l + d) g₁ g₂ α s y ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + d) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_mono (I := I) (M := M) (by omega) g₁ g₂ α s y
    exact mul_le_mul_of_nonneg_left hmono (hCl_pos l).le

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.uniformBound
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    {F : SmoothRiemannianMetric I M → E → ℝ} {d : ℕ}
    (hF : HasChartJetLip g₁ g₂ α K F d) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : SmoothRiemannianMetric I M),
      (g = g₁ ∨ g = g₂) → ∀ y ∈ K, ∀ m : ℕ, m ≤ N →
        ‖iteratedFDerivWithin ℝ m (F g) (interior (extChartAt I α).target) y‖ ≤ B := by
  obtain ⟨B, hB_nn, hB⟩ := hF.bound N
  refine ⟨B, hB_nn, fun g hg y hy m hm => ?_⟩
  rcases hg with rfl | rfl
  · exact (hB y hy m hm).1
  · exact (hB y hy m hm).2

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.mul
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F G : SmoothRiemannianMetric I M → E → ℝ} {dF dG : ℕ}
    (hF : HasChartJetLip g₁ g₂ α K F dF) (hG : HasChartJetLip g₁ g₂ α K G dG) :
    HasChartJetLip g₁ g₂ α K (fun g => fun z => F g z * G g z) (max dF dG) := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  refine ⟨fun g => (hF.contDiff g).mul (hG.contDiff g), fun N => ?_, fun N => ?_⟩
  · obtain ⟨BF, hBF_nn, hBF⟩ := hF.bound N
    obtain ⟨BG, hBG_nn, hBG⟩ := hG.bound N
    refine ⟨2 ^ N * (BF * BG), by positivity, fun y hy m hm => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hprod : ∀ g : SmoothRiemannianMetric I M,
        (∀ k, k ≤ m → ‖iteratedFDerivWithin ℝ k (F g) s y‖ ≤ BF) →
        (∀ k, k ≤ m → ‖iteratedFDerivWithin ℝ k (G g) s y‖ ≤ BG) →
        ‖iteratedFDerivWithin ℝ m (fun z => F g z * G g z) s y‖ ≤ 2 ^ N * (BF * BG) := by
      intro g hFb hGb
      refine (norm_iteratedFDerivWithin_mul_le (hF.contDiff g) (hG.contDiff g)
        hs_open.uniqueDiffOn hyS (by exact_mod_cast le_top)).trans ?_
      refine (Finset.sum_le_sum (g := fun k => (m.choose k : ℝ) * BF * BG)
        (fun k hk => ?_)).trans ?_
      · have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hFb k hkm) (by positivity))
          (hGb (m - k) (Nat.sub_le m k)) (norm_nonneg _) ?_
        exact mul_nonneg (by positivity) hBF_nn
      · rw [← Finset.sum_mul]
        have hsum : (∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * BF) =
            2 ^ m * BF := by
          rw [← Finset.sum_mul]
          congr 1
          calc (∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ))
              = ((∑ k ∈ Finset.range (m + 1), m.choose k : ℕ) : ℝ) := by push_cast; rfl
            _ = ((2 ^ m : ℕ) : ℝ) := by rw [Nat.sum_range_choose]
            _ = 2 ^ m := by push_cast; ring
        rw [hsum]
        have h2m : (2 : ℝ) ^ m ≤ 2 ^ N := by
          refine pow_le_pow_right₀ (by norm_num) hm
        have : 2 ^ m * BF * BG ≤ 2 ^ N * (BF * BG) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right h2m (mul_nonneg hBF_nn hBG_nn)
        exact this
    constructor
    · exact hprod g₁ (fun k hk => (hBF y hy k (hk.trans hm)).1)
        (fun k hk => (hBG y hy k (hk.trans hm)).1)
    · exact hprod g₂ (fun k hk => (hBF y hy k (hk.trans hm)).2)
        (fun k hk => (hBG y hy k (hk.trans hm)).2)
  · obtain ⟨BF, hBF_nn, hBF⟩ := hF.bound N
    obtain ⟨BG, hBG_nn, hBG⟩ := hG.bound N
    set B : ℝ := max BF BG with hB_def
    have hB_nn : 0 ≤ B := le_max_of_le_left hBF_nn
    obtain ⟨CF, hCF_pos, hCF⟩ := hF.seminorm_le N
    obtain ⟨CG, hCG_pos, hCG⟩ := hG.seminorm_le N
    refine ⟨2 ^ N * B * (CF + CG) + 1, by positivity, fun y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hbnd := norm_iteratedFDerivWithin_two_prod_sub_le (s := s) hs_open
      (hF.contDiff g₁) (hG.contDiff g₁) (hF.contDiff g₂) (hG.contDiff g₂)
      hKsub hB_nn N
      (fun y' hy' m hm => le_trans (hBG y' hy' m hm).1 (le_max_right _ _))
      (fun y' hy' m hm => le_trans (hBF y' hy' m hm).2 (le_max_left _ _))
      hy
    refine hbnd.trans ?_
    have hsem_nn : 0 ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y
    have hF_le : iteratedFDerivSeminorm N (fun z => F g₁ z - F g₂ z) s y ≤
        CF * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by
      refine (hCF y hy).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCF_pos.le
      exact chartGramJetDiffSeminormSum_mono (I := I) (M := M)
        (by omega) g₁ g₂ α s y
    have hG_le : iteratedFDerivSeminorm N (fun z => G g₁ z - G g₂ z) s y ≤
        CG * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by
      refine (hCG y hy).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCG_pos.le
      exact chartGramJetDiffSeminormSum_mono (I := I) (M := M)
        (by omega) g₁ g₂ α s y
    calc 2 ^ N * B *
          (iteratedFDerivSeminorm N (fun z => F g₁ z - F g₂ z) s y +
            iteratedFDerivSeminorm N (fun z => G g₁ z - G g₂ z) s y)
        ≤ 2 ^ N * B *
            (CF * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y +
              CG * chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y) :=
          mul_le_mul_of_nonneg_left (add_le_add hF_le hG_le) (by positivity)
      _ = (2 ^ N * B * (CF + CG)) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by ring
      _ ≤ (2 ^ N * B * (CF + CG) + 1) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + max dF dG) g₁ g₂ α s y := by
          refine mul_le_mul_of_nonneg_right ?_ hsem_nn; linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.partialDeriv
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F : SmoothRiemannianMetric I M → E → ℝ} {d : ℕ}
    (hF : HasChartJetLip g₁ g₂ α K F d) (i : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K
      (fun g => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i (F g))
      (d + 1) := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  refine ⟨fun g => partialDeriv_contDiffOn_of_isOpen hs_open (hF.contDiff g) i,
    fun N => ?_, fun N => ?_⟩
  · obtain ⟨B, hB_nn, hB⟩ := hF.bound (N + 1)
    refine ⟨‖(chartModelBasis E) i‖ * B,
      mul_nonneg (norm_nonneg _) hB_nn, fun y hy m hm => ?_⟩
    have hyS : y ∈ s := hKsub hy
    obtain ⟨hB1, hB2⟩ := hB y hy (m + 1) (by omega)
    refine ⟨?_, ?_⟩
    · refine (norm_iteratedFDerivWithin_partialDeriv_le hs_open (hF.contDiff g₁) i m hyS).trans ?_
      exact mul_le_mul_of_nonneg_left hB1 (norm_nonneg _)
    · refine (norm_iteratedFDerivWithin_partialDeriv_le hs_open (hF.contDiff g₂) i m hyS).trans ?_
      exact mul_le_mul_of_nonneg_left hB2 (norm_nonneg _)
  · obtain ⟨C, hC_pos, hC⟩ := hF.lip (N + 1)
    refine ⟨‖(chartModelBasis E) i‖ * C + 1, by positivity, fun y hy => ?_⟩
    have hyS : y ∈ s := hKsub hy
    have hEqOn : EqOn
        (fun z => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i (F g₁) z -
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i (F g₂) z)
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
          (fun z => F g₁ z - F g₂ z)) s :=
      partialDeriv_sub_eqOn hs_open (hF.contDiff g₁) (hF.contDiff g₂) i
    rw [iteratedFDerivWithin_congr hEqOn hyS N]
    refine (norm_iteratedFDerivWithin_partialDeriv_le hs_open
      ((hF.contDiff g₁).sub (hF.contDiff g₂)) i N hyS).trans ?_
    have hsem_nn : 0 ≤
        chartGramJetDiffSeminormSum (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y :=
      chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y
    have hN1d : N + 1 + d = N + (d + 1) := by omega
    calc ‖(chartModelBasis E) i‖ *
            ‖iteratedFDerivWithin ℝ (N + 1) (fun z => F g₁ z - F g₂ z) s y‖
        ≤ ‖(chartModelBasis E) i‖ *
            (C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 1 + d) g₁ g₂ α s y) :=
          mul_le_mul_of_nonneg_left (hC y hy) (norm_nonneg _)
      _ = (‖(chartModelBasis E) i‖ * C) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y := by
          rw [hN1d]; ring
      _ ≤ (‖(chartModelBasis E) i‖ * C + 1) *
            chartGramJetDiffSeminormSum (I := I) (M := M) (N + (d + 1)) g₁ g₂ α s y := by
          refine mul_le_mul_of_nonneg_right ?_ hsem_nn; linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem hasChartJetLip_const
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {F : SmoothRiemannianMetric I M → E → ℝ} {f₀ : E → ℝ}
    (hf₀ : ContDiffOn ℝ ∞ f₀ (interior (extChartAt I α).target))
    (hFconst : ∀ g, F g = f₀) :
    HasChartJetLip g₁ g₂ α K F 0 := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  refine ⟨fun g => by rw [hFconst g]; exact hf₀, fun N => ?_, fun N => ?_⟩
  · obtain ⟨B, hB_nn, hB⟩ := exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      hs_open hf₀ hK hKsub N
    refine ⟨B, hB_nn, fun y hy m hm => ?_⟩
    rw [hFconst g₁, hFconst g₂]
    exact ⟨hB y hy m hm, hB y hy m hm⟩
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    have hzero : (fun z => F g₁ z - F g₂ z) = (fun _ : E => (0 : ℝ)) := by
      funext z; rw [hFconst g₁, hFconst g₂, sub_self]
    rw [hzero, iteratedFDerivWithin_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg one_pos.le
      (chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + 0) g₁ g₂ α s y)

omit [NeZero (Module.finrank ℝ E)] in
theorem HasChartJetLip.sum
    {g₁ g₂ : SmoothRiemannianMetric I M} {α : M} {K : Set E}
    (hKsub : K ⊆ interior (extChartAt I α).target)
    {ι : Type*} (u : Finset ι)
    {F : ι → SmoothRiemannianMetric I M → E → ℝ} {d : ℕ}
    (hF : ∀ j ∈ u, HasChartJetLip g₁ g₂ α K (F j) d) :
    HasChartJetLip g₁ g₂ α K (fun g => fun z => ∑ j ∈ u, F j g z) d := by
  classical
  induction u using Finset.induction with
  | empty =>
    refine ⟨fun g => by simpa using (contDiffOn_const (c := (0 : ℝ))),
      fun N => ⟨0, le_refl 0, fun y hy m hm => ?_⟩,
      fun N => ⟨1, one_pos, fun y hy => ?_⟩⟩
    · simp only [Finset.sum_empty]
      constructor <;>
        · rw [show (fun _ : E => (0 : ℝ)) = (fun z => (0 : ℝ)) from rfl,
            iteratedFDerivWithin_fun_zero]; simp
    · simp only [Finset.sum_empty, sub_self]
      rw [iteratedFDerivWithin_fun_zero]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg one_pos.le
        (chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + d) g₁ g₂ α _ y)
  | insert a u ha IH =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hF
    have hhead := hF.1
    have hIH := IH hF.2
    have hsumeq : (fun g => fun z => ∑ j ∈ insert a u, F j g z) =
        (fun g => fun z => F a g z + (∑ j ∈ u, F j g z)) := by
      funext g z; rw [Finset.sum_insert ha]
    rw [hsumeq]
    have := (hhead.add (G := fun g => fun z => ∑ j ∈ u, F j g z) hKsub hIH)
    simpa only [max_self] using this

omit [NeZero (Module.finrank ℝ E)] in
theorem hasChartJetLip_chartGramOnE
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (a b : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K (fun g => chartGramOnE (I := I) g α a b) 0 := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  refine ⟨fun g => chartGramOnE_contDiffOn_int (I := I) g α a b, fun N => ?_, fun N => ?_⟩
  · obtain ⟨B1, hB1_nn, hB1⟩ := exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      hs_open (chartGramOnE_contDiffOn_int (I := I) g₁ α a b) hK hKsub N
    obtain ⟨B2, hB2_nn, hB2⟩ := exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      hs_open (chartGramOnE_contDiffOn_int (I := I) g₂ α a b) hK hKsub N
    refine ⟨max B1 B2, le_max_of_le_left hB1_nn, fun y hy m hm => ?_⟩
    exact ⟨(hB1 y hy m hm).trans (le_max_left _ _), (hB2 y hy m hm).trans (le_max_right _ _)⟩
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    rw [one_mul, add_zero]
    have h1 : ‖iteratedFDerivWithin ℝ N
        (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y‖ ≤
        iteratedFDerivSeminorm N
          (fun z => chartGramOnE (I := I) g₁ α a b z - chartGramOnE (I := I) g₂ α a b z) s y :=
      norm_iteratedFDerivWithin_le_seminorm (le_refl N) _ s y
    exact h1.trans (iteratedFDerivSeminorm_gramDiff_le_sum (I := I) (M := M) N g₁ g₂ α s y a b)

theorem hasChartJetLip_chartInvGramOnE
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (k l : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K (fun g => chartInvGramOnE (I := I) g α k l) 0 := by
  classical
  set s : Set E := interior (extChartAt I α).target with hs_def
  have hs_open : IsOpen s := isOpen_interior
  refine ⟨fun g => chartInvGramOnE_contDiffOn_int (I := I) g α k l, fun N => ?_, fun N => ?_⟩
  · obtain ⟨B1, hB1_nn, hB1⟩ := exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      hs_open (chartInvGramOnE_contDiffOn_int (I := I) g₁ α k l) hK hKsub N
    obtain ⟨B2, hB2_nn, hB2⟩ := exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
      hs_open (chartInvGramOnE_contDiffOn_int (I := I) g₂ α k l) hK hKsub N
    refine ⟨max B1 B2, le_max_of_le_left hB1_nn, fun y hy m hm => ?_⟩
    exact ⟨(hB1 y hy m hm).trans (le_max_left _ _), (hB2 y hy m hm).trans (le_max_right _ _)⟩
  · obtain ⟨C, hC_pos, hC⟩ :=
      exists_chartInvGramOnE_iteratedFDeriv_lipschitz_on_compact
        (I := I) (M := M) g₁ g₂ α hK hKsub N
    refine ⟨C, hC_pos, fun y hy => ?_⟩
    rw [add_zero]
    exact hC y hy k l

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
