import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.Order.Compact

noncomputable section

open Set Filter Topology
open scoped Nat

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

universe uE uF uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem norm_le_pow_of_le_of_one_le
    {a D : ℝ} (hD1 : 1 ≤ D) {i : ℕ} (hi : 1 ≤ i) (ha : a ≤ D) :
    a ≤ D ^ i := by
  refine ha.trans ?_
  calc D = D ^ 1 := (pow_one D).symm
    _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi

theorem norm_iteratedFDeriv_comp_le_max_pow
    {g : E → F} {f : F → G} {n : ℕ} {N : WithTop ℕ∞}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) (hn : (n : WithTop ℕ∞) ≤ N) (x : E)
    {Cf Cg : ℝ}
    (hCf : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i f (g x)‖ ≤ Cf)
    (hCg : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g x‖ ≤ Cg) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ n ! * Cf * (max Cg 1) ^ n := by
  have hD1 : (1 : ℝ) ≤ max Cg 1 := le_max_right _ _
  have hCg' : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i g x‖ ≤ (max Cg 1) ^ i := by
    intro i hi1 hin
    exact norm_le_pow_of_le_of_one_le hD1 hi1
      ((hCg i hi1 hin).trans (le_max_left _ _))
  exact norm_iteratedFDeriv_comp_le (𝕜 := ℝ) hf hg hn x hCf hCg'

theorem norm_iteratedFDeriv_comp_le_envelope
    {g : E → F} {f : F → G} {n : ℕ} {N : WithTop ℕ∞}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) (hn : (n : WithTop ℕ∞) ≤ N) (x : E)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i f (g x)‖ ≤ Cf)
    (hCg : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g x‖ ≤ Cg) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ n ! * Cf * (1 + Cg) ^ n := by
  refine (norm_iteratedFDeriv_comp_le_max_pow hf hg hn x hCf hCg).trans ?_
  have hmax_le : max Cg 1 ≤ 1 + Cg := by
    rcases le_total Cg 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hbase_nonneg : (0 : ℝ) ≤ max Cg 1 := le_trans zero_le_one (le_max_right _ _)
  have hpow : (max Cg 1) ^ n ≤ (1 + Cg) ^ n :=
    pow_le_pow_left₀ hbase_nonneg hmax_le n
  have hcoef_nonneg : 0 ≤ (n ! : ℝ) * Cf :=
    mul_nonneg (by positivity) hCf0
  exact mul_le_mul_of_nonneg_left hpow hcoef_nonneg

private theorem exists_uniform_iteratedFDeriv_bound
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {h : E → H} {N : WithTop ℕ∞} (hh : ContDiff ℝ N h)
    {A : Set E} (hA : IsCompact A) (hAne : A.Nonempty) {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, i ≤ n → ∀ y ∈ A, ‖iteratedFDeriv ℝ i h y‖ ≤ C := by
  classical
  have hcont : ∀ i, i ≤ n → Continuous fun y => iteratedFDeriv ℝ i h y := by
    intro i hi
    have hin : (i : WithTop ℕ∞) ≤ N :=
      le_trans (by exact_mod_cast (Nat.cast_le.mpr hi : (i : ℕ∞) ≤ (n : ℕ∞))) hn
    exact (hh.of_le hin).continuous_iteratedFDeriv (m := i) le_rfl
  have hmax : ∀ i, i ≤ n → ∃ Mi : ℝ, 0 ≤ Mi ∧ ∀ y ∈ A, ‖iteratedFDeriv ℝ i h y‖ ≤ Mi := by
    intro i hi
    obtain ⟨z, hzA, hzmax⟩ :=
      hA.exists_isMaxOn hAne ((hcont i hi).norm.continuousOn)
    refine ⟨‖iteratedFDeriv ℝ i h z‖, norm_nonneg _, ?_⟩
    intro y hy
    exact hzmax hy
  choose Mi hMi0 hMib using hmax
  let C : ℝ := (Finset.range (n + 1)).sup' (by simp) fun i =>
    if hi : i ≤ n then Mi i hi else 0
  have hCnonneg : 0 ≤ C := by
    refine Finset.le_sup'_of_le _ (by simp : (0 : ℕ) ∈ Finset.range (n + 1)) ?_
    simp only [Nat.zero_le, dif_pos]
    exact hMi0 0 (Nat.zero_le n)
  refine ⟨C, hCnonneg, ?_⟩
  intro i hi y hy
  refine (hMib i hi y hy).trans ?_
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  refine Finset.le_sup'_of_le _ hmem ?_
  simp only [hi, dif_pos, le_refl]

theorem norm_iteratedFDeriv_comp_le_on_compact
    {g : E → F} {f : F → G} {n : ℕ} {N : WithTop ℕ∞}
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) (hn : (n : WithTop ℕ∞) ≤ N)
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ C := by
  have hgK : IsCompact (g '' K) := hK.image hg.continuous
  have hgKne : (g '' K).Nonempty := hKne.image g
  obtain ⟨Cf, hCf0, hCfb⟩ :=
    exists_uniform_iteratedFDeriv_bound (E := F) hf hgK hgKne hn
  obtain ⟨Cg, hCg0, hCgb⟩ :=
    exists_uniform_iteratedFDeriv_bound (E := E) hg hK hKne hn
  refine ⟨n ! * Cf * (1 + Cg) ^ n, ?_, ?_⟩
  · have : (0 : ℝ) ≤ n ! * Cf := mul_nonneg (by positivity) hCf0
    have hpow : (0 : ℝ) ≤ (1 + Cg) ^ n := by positivity
    exact mul_nonneg this hpow
  · intro x hx
    have hCf : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i f (g x)‖ ≤ Cf := fun i hi =>
      hCfb i hi (g x) (mem_image_of_mem g hx)
    have hCg : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g x‖ ≤ Cg := fun i _ hi =>
      hCgb i hi x hx
    exact norm_iteratedFDeriv_comp_le_envelope hf hg hn x hCf0 hCg0 hCf hCg

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
