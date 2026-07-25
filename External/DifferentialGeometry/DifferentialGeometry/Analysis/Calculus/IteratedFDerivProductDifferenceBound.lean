import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Order.Compact

noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def iteratedFDerivSeminorm (N : ℕ) (f : E → ℝ) (s : Set E) (y : E) : ℝ :=
  ∑ l ∈ Finset.range (N + 1), ‖iteratedFDerivWithin ℝ l f s y‖

lemma iteratedFDerivSeminorm_nonneg (N : ℕ) (f : E → ℝ) (s : Set E) (y : E) :
    0 ≤ iteratedFDerivSeminorm N f s y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma iteratedFDerivSeminorm_mono
    {N N' : ℕ} (hN : N ≤ N') (f : E → ℝ) (s : Set E) (y : E) :
    iteratedFDerivSeminorm N f s y ≤ iteratedFDerivSeminorm N' f s y := by
  unfold iteratedFDerivSeminorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  exact Finset.range_mono (Nat.succ_le_succ hN)

lemma norm_iteratedFDerivWithin_le_seminorm
    {N l : ℕ} (hl : l ≤ N) (f : E → ℝ) (s : Set E) (y : E) :
    ‖iteratedFDerivWithin ℝ l f s y‖ ≤ iteratedFDerivSeminorm N f s y :=
  Finset.single_le_sum (f := fun l => ‖iteratedFDerivWithin ℝ l f s y‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

lemma iteratedFDerivSeminorm_sub_comm
    {f g : E → ℝ} {s : Set E} (hs : UniqueDiffOn ℝ s) {y : E} (hy : y ∈ s) (N : ℕ) :
    iteratedFDerivSeminorm N (fun z => f z - g z) s y =
      iteratedFDerivSeminorm N (fun z => g z - f z) s y := by
  classical
  unfold iteratedFDerivSeminorm
  refine Finset.sum_congr rfl fun l _ => ?_
  have hvec : iteratedFDerivWithin ℝ l (fun z => g z - f z) s y =
      -iteratedFDerivWithin ℝ l (fun z => f z - g z) s y :=
    calc iteratedFDerivWithin ℝ l (fun z => g z - f z) s y
        = iteratedFDerivWithin ℝ l (fun z => -((fun w => f w - g w) z)) s y :=
          iteratedFDerivWithin_congr (f₁ := fun z => g z - f z)
            (f := fun z => -((fun w => f w - g w) z)) (by intro z _; ring) hy l
      _ = -iteratedFDerivWithin ℝ l (fun w => f w - g w) s y :=
          iteratedFDerivWithin_neg_apply hs hy
  rw [hvec, norm_neg]

theorem exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
    {f : E → ℝ} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {K : Set E} (hK : IsCompact K) (hKsub : K ⊆ s) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K, ∀ m : ℕ, m ≤ N →
      ‖iteratedFDerivWithin ℝ m f s y‖ ≤ B := by
  classical
  have hper : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K,
      ‖iteratedFDerivWithin ℝ m f s y‖ ≤ B := by
    intro m
    have hcont : ContinuousOn
        (fun y => iteratedFDerivWithin ℝ m f s y) s :=
      hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs.uniqueDiffOn
    have hcontK : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ m f s y‖) K :=
      (hcont.mono hKsub).norm
    by_cases hKe : K = ∅
    · exact ⟨0, le_refl 0, fun y hy => absurd (hKe ▸ hy) (Set.notMem_empty _)⟩
    obtain ⟨C, hC⟩ := hK.bddAbove_image hcontK
    refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
    exact (hC ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  choose Bm hBm_nn hBm using hper
  refine ⟨∑ m ∈ Finset.range (N + 1), Bm m, Finset.sum_nonneg fun m _ => hBm_nn m, ?_⟩
  intro y hy m hmN
  refine (hBm m y hy).trans ?_
  exact Finset.single_le_sum (f := fun m => Bm m) (fun i _ => hBm_nn i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hmN))

theorem norm_iteratedFDerivWithin_mul_le_uniformBound
    {δ h : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hδ : ContDiffOn ℝ ∞ δ s) (hh : ContDiffOn ℝ ∞ h s)
    {K : Set E} (hKsub : K ⊆ s) {B : ℝ} (_hB_nn : 0 ≤ B) (N : ℕ)
    (hHbound : ∀ y ∈ K, ∀ m : ℕ, m ≤ N → ‖iteratedFDerivWithin ℝ m h s y‖ ≤ B)
    {y : E} (hy : y ∈ K) :
    ‖iteratedFDerivWithin ℝ N (fun z => δ z * h z) s y‖ ≤
      2 ^ N * B * iteratedFDerivSeminorm N δ s y := by
  classical
  have hyS : y ∈ s := hKsub hy
  have hLeibniz :
      ‖iteratedFDerivWithin ℝ N (fun z => δ z * h z) s y‖ ≤
        ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i δ s y‖ * ‖iteratedFDerivWithin ℝ (N - i) h s y‖ :=
    norm_iteratedFDerivWithin_mul_le hδ hh hs.uniqueDiffOn hyS (by exact_mod_cast le_top)
  refine hLeibniz.trans ?_
  have hseminorm_nn : 0 ≤ iteratedFDerivSeminorm N δ s y :=
    iteratedFDerivSeminorm_nonneg N δ s y
  have hterm : ∀ i ∈ Finset.range (N + 1),
      (N.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i δ s y‖ *
          ‖iteratedFDerivWithin ℝ (N - i) h s y‖ ≤
        (N.choose i : ℝ) * (B * iteratedFDerivSeminorm N δ s y) := by
    intro i hi
    have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hδ_le : ‖iteratedFDerivWithin ℝ i δ s y‖ ≤ iteratedFDerivSeminorm N δ s y :=
      norm_iteratedFDerivWithin_le_seminorm hiN δ s y
    have hh_le : ‖iteratedFDerivWithin ℝ (N - i) h s y‖ ≤ B :=
      hHbound y hy (N - i) (Nat.sub_le N i)
    have hchoose_nn : (0 : ℝ) ≤ (N.choose i : ℝ) := by positivity
    calc (N.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i δ s y‖ *
            ‖iteratedFDerivWithin ℝ (N - i) h s y‖
        ≤ (N.choose i : ℝ) * iteratedFDerivSeminorm N δ s y * B := by
          refine mul_le_mul ?_ hh_le (norm_nonneg _)
            (mul_nonneg hchoose_nn hseminorm_nn)
          exact mul_le_mul_of_nonneg_left hδ_le hchoose_nn
      _ = (N.choose i : ℝ) * (B * iteratedFDerivSeminorm N δ s y) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum_choose : (∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ)) = 2 ^ N := by
    have := Nat.sum_range_choose N
    calc (∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ))
        = ((∑ i ∈ Finset.range (N + 1), N.choose i : ℕ) : ℝ) := by
          push_cast; rfl
      _ = ((2 ^ N : ℕ) : ℝ) := by rw [this]
      _ = 2 ^ N := by push_cast; ring
  rw [hsum_choose]
  exact le_of_eq (by ring)

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
