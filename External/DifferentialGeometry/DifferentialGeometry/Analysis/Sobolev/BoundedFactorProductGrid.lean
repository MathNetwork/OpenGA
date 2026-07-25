import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid

open scoped BigOperators

namespace DifferentialGeometry
namespace Combinatorics

noncomputable def boundedFactorGrid (b : ℕ → ℝ) (K k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1),
    ∑ e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
      ∏ m : Fin n, b (e m)

lemma boundedFactorGrid_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (K k : ℕ) :
    0 ≤ boundedFactorGrid b K k :=
  Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => hb _)))

lemma boundedFactorGrid_le_antidiagonalTupleGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (K k : ℕ) :
    boundedFactorGrid b K k ≤ antidiagonalTupleGrid b k := by
  rw [boundedFactorGrid, antidiagonalTupleGrid]
  refine Finset.sum_le_sum (fun n _ => ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun e _ _ => Finset.prod_nonneg (fun _ _ => hb _))

lemma antidiagonalTupleGrid_eq_boundedFactorGrid (b : ℕ → ℝ) {K k : ℕ} (hk : k ≤ K) :
    antidiagonalTupleGrid b k = boundedFactorGrid b K k := by
  rw [boundedFactorGrid, antidiagonalTupleGrid]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine (Finset.sum_congr ?_ (fun _ _ => rfl)).symm
  refine Finset.filter_true_of_mem (fun e he => ?_)
  intro m
  have hsum : ∑ m' : Fin n, e m' = k := Finset.Nat.mem_antidiagonalTuple.mp he
  have hle : e m ≤ ∑ m' : Fin n, e m' :=
    Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  omega

lemma boundedFactorGrid_zero (b : ℕ → ℝ) (K : ℕ) : boundedFactorGrid b K 0 = 1 := by
  rw [← antidiagonalTupleGrid_eq_boundedFactorGrid b (Nat.zero_le K)]
  exact antidiagonalTupleGrid_zero b

lemma boundedFactorGrid_mono_bound (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {K K' : ℕ}
    (hK : K ≤ K') (k : ℕ) :
    boundedFactorGrid b K k ≤ boundedFactorGrid b K' k := by
  rw [boundedFactorGrid, boundedFactorGrid]
  refine Finset.sum_le_sum (fun n _ => ?_)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun e _ _ => Finset.prod_nonneg (fun _ _ => hb _))
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun m => le_trans (he.2 m) hK⟩

private def consB (q n : ℕ) (e : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cons q e

private lemma consB_injective (q n : ℕ) : Function.Injective (consB q n) := by
  intro e₁ e₂ h
  have h₁ : Fin.tail (consB q n e₁) = Fin.tail (consB q n e₂) := by rw [h]
  rwa [consB, consB, Fin.tail_cons, Fin.tail_cons] at h₁

private lemma consB_mem_filter (q k n K : ℕ) (hqK : q ≤ K) (e : Fin n → ℕ)
    (he : e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K)) :
    consB q n e ∈
      (Finset.Nat.antidiagonalTuple (n + 1) (k + q)).filter (fun e => ∀ m, e m ≤ K) := by
  rw [Finset.mem_filter] at he ⊢
  refine ⟨?_, ?_⟩
  · rw [Finset.Nat.mem_antidiagonalTuple] at he ⊢
    rw [consB, Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [he.1]
    omega
  · intro m
    refine Fin.cases ?_ (fun m' => ?_) m
    · rw [consB, Fin.cons_zero]; exact hqK
    · rw [consB, Fin.cons_succ]; exact he.2 m'

lemma single_factor_mul_boundedFactorGrid_le
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {K : ℕ} (k q : ℕ) (hq : 1 ≤ q) (hqK : q ≤ K) :
    b q * boundedFactorGrid b K k ≤ boundedFactorGrid b K (k + q) := by
  classical
  have hterm : ∀ n : ℕ,
      b q * (∑ e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
          ∏ m : Fin n, b (e m)) ≤
        ∑ e' ∈ (Finset.Nat.antidiagonalTuple (n + 1) (k + q)).filter (fun e => ∀ m, e m ≤ K),
          ∏ m : Fin (n + 1), b (e' m) := by
    intro n
    rw [Finset.mul_sum]
    have hcons : ∀ e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
        b q * ∏ m : Fin n, b (e m) = ∏ m : Fin (n + 1), b (consB q n e m) := by
      intro e _
      rw [consB, Fin.prod_univ_succ, Fin.cons_zero]
      refine congrArg (fun t => b q * t) (Finset.prod_congr rfl (fun m _ => ?_))
      rw [Fin.cons_succ]
    rw [Finset.sum_congr rfl hcons]
    rw [← Finset.sum_image
      (f := fun e' : Fin (n + 1) → ℕ => ∏ m : Fin (n + 1), b (e' m))
      (g := consB q n)
      ((consB_injective q n).injOn)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun e' _ _ => Finset.prod_nonneg (fun _ _ => hb _))
    intro e' he'
    rw [Finset.mem_image] at he'
    obtain ⟨e, he, rfl⟩ := he'
    exact consB_mem_filter q k n K hqK e he
  have hstep : b q * boundedFactorGrid b K k ≤
      ∑ n ∈ Finset.range (k + 1),
        ∑ e' ∈ (Finset.Nat.antidiagonalTuple (n + 1) (k + q)).filter (fun e => ∀ m, e m ≤ K),
          ∏ m : Fin (n + 1), b (e' m) := by
    rw [boundedFactorGrid, Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => hterm n)
  refine hstep.trans ?_
  rw [boundedFactorGrid]
  have hshift : ∑ n ∈ Finset.range (k + 1),
        ∑ e' ∈ (Finset.Nat.antidiagonalTuple (n + 1) (k + q)).filter (fun e => ∀ m, e m ≤ K),
          ∏ m : Fin (n + 1), b (e' m) =
      ∑ N ∈ Finset.Ico 1 (k + 2),
        ∑ e' ∈ (Finset.Nat.antidiagonalTuple N (k + q)).filter (fun e => ∀ m, e m ≤ K),
          ∏ m : Fin N, b (e' m) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by rw [show k + 2 - 1 = k + 1 from by omega]) (fun n _ => ?_)
    rw [show 1 + n = n + 1 from by omega]
  rw [hshift]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun N _ _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun _ _ => hb _)))
  intro N hN
  rw [Finset.mem_Ico] at hN
  rw [Finset.mem_range]
  omega

noncomputable def gridCellCount (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), ((Finset.Nat.antidiagonalTuple n k).card : ℝ)

lemma gridCellCount_nonneg (k : ℕ) : 0 ≤ gridCellCount k :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

private lemma prodCell_le_boundedFactorGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (K k n : ℕ)
    (hn : n < k + 1) (e : Fin n → ℕ)
    (he : e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K)) :
    (∏ m : Fin n, b (e m)) ≤ boundedFactorGrid b K k := by
  rw [boundedFactorGrid]
  have h1 : (∏ m : Fin n, b (e m)) ≤
      ∑ e' ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
        ∏ m : Fin n, b (e' m) :=
    Finset.single_le_sum (f := fun e' : Fin n → ℕ => ∏ m : Fin n, b (e' m))
      (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)) he
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n' : ℕ => ∑ e' ∈ (Finset.Nat.antidiagonalTuple n' k).filter
      (fun e => ∀ m, e m ≤ K), ∏ m : Fin n', b (e' m))
    (fun n' _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)))
    (Finset.mem_range.mpr hn)

lemma boundedFactorGrid_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (K k₁ k₂ : ℕ) :
    boundedFactorGrid b K k₁ * boundedFactorGrid b K k₂ ≤
      (gridCellCount k₁ * gridCellCount k₂) * boundedFactorGrid b K (k₁ + k₂) := by
  classical
  have hpair : ∀ n₁ ∈ Finset.range (k₁ + 1),
      ∀ e₁ ∈ (Finset.Nat.antidiagonalTuple n₁ k₁).filter (fun e => ∀ m, e m ≤ K),
      ∀ n₂ ∈ Finset.range (k₂ + 1),
      ∀ e₂ ∈ (Finset.Nat.antidiagonalTuple n₂ k₂).filter (fun e => ∀ m, e m ≤ K),
      (∏ m : Fin n₁, b (e₁ m)) * (∏ m : Fin n₂, b (e₂ m)) ≤
        boundedFactorGrid b K (k₁ + k₂) := by
    intro n₁ hn₁ e₁ he₁ n₂ hn₂ e₂ he₂
    rw [Finset.mem_filter] at he₁ he₂
    have happend : (∏ m : Fin n₁, b (e₁ m)) * (∏ m : Fin n₂, b (e₂ m)) =
        ∏ m : Fin (n₁ + n₂), b (Fin.append e₁ e₂ m) := by
      rw [Fin.prod_univ_add]
      congr 1
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_left])
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_right])
    rw [happend]
    have hmem : Fin.append e₁ e₂ ∈
        (Finset.Nat.antidiagonalTuple (n₁ + n₂) (k₁ + k₂)).filter (fun e => ∀ m, e m ≤ K) := by
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.Nat.mem_antidiagonalTuple]
        rw [Fin.sum_univ_add]
        have h1 : (∑ m : Fin n₁, Fin.append e₁ e₂ (Fin.castAdd n₂ m)) = k₁ := by
          rw [← Finset.Nat.mem_antidiagonalTuple.mp he₁.1]
          exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_left])
        have h2 : (∑ m : Fin n₂, Fin.append e₁ e₂ (Fin.natAdd n₁ m)) = k₂ := by
          rw [← Finset.Nat.mem_antidiagonalTuple.mp he₂.1]
          exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_right])
        rw [h1, h2]
      · intro m
        refine Fin.addCases (fun m₁ => ?_) (fun m₂ => ?_) m
        · rw [Fin.append_left]
          exact he₁.2 m₁
        · rw [Fin.append_right]
          exact he₂.2 m₂
    have hnn' : n₁ + n₂ < k₁ + k₂ + 1 := by
      rw [Finset.mem_range] at hn₁ hn₂
      omega
    exact prodCell_le_boundedFactorGrid b hb K (k₁ + k₂) (n₁ + n₂) hnn' _ hmem
  calc boundedFactorGrid b K k₁ * boundedFactorGrid b K k₂
      = ∑ n₁ ∈ Finset.range (k₁ + 1),
          ∑ e₁ ∈ (Finset.Nat.antidiagonalTuple n₁ k₁).filter (fun e => ∀ m, e m ≤ K),
            ((∏ m : Fin n₁, b (e₁ m)) * boundedFactorGrid b K k₂) := by
        rw [boundedFactorGrid, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
    _ ≤ ∑ n₁ ∈ Finset.range (k₁ + 1),
          ∑ e₁ ∈ (Finset.Nat.antidiagonalTuple n₁ k₁).filter (fun e => ∀ m, e m ≤ K),
            (gridCellCount k₂ * boundedFactorGrid b K (k₁ + k₂)) := by
        refine Finset.sum_le_sum (fun n₁ hn₁ => Finset.sum_le_sum (fun e₁ he₁ => ?_))
        calc (∏ m : Fin n₁, b (e₁ m)) * boundedFactorGrid b K k₂
            = ∑ n₂ ∈ Finset.range (k₂ + 1),
                ∑ e₂ ∈ (Finset.Nat.antidiagonalTuple n₂ k₂).filter (fun e => ∀ m, e m ≤ K),
                  ((∏ m : Fin n₁, b (e₁ m)) * ∏ m : Fin n₂, b (e₂ m)) := by
              rw [boundedFactorGrid, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n₂ _ => by rw [Finset.mul_sum])
          _ ≤ ∑ n₂ ∈ Finset.range (k₂ + 1),
                ∑ e₂ ∈ (Finset.Nat.antidiagonalTuple n₂ k₂).filter (fun e => ∀ m, e m ≤ K),
                  boundedFactorGrid b K (k₁ + k₂) := by
              refine Finset.sum_le_sum (fun n₂ hn₂ => Finset.sum_le_sum (fun e₂ he₂ => ?_))
              exact hpair n₁ hn₁ e₁ he₁ n₂ hn₂ e₂ he₂
          _ ≤ gridCellCount k₂ * boundedFactorGrid b K (k₁ + k₂) := by
              have hcard : ∀ n₂ : ℕ,
                  ((Finset.Nat.antidiagonalTuple n₂ k₂).filter
                    (fun e => ∀ m, e m ≤ K)).card ≤
                  (Finset.Nat.antidiagonalTuple n₂ k₂).card :=
                fun n₂ => Finset.card_filter_le _ _
              have hbfg_nn : 0 ≤ boundedFactorGrid b K (k₁ + k₂) :=
                boundedFactorGrid_nonneg b hb K (k₁ + k₂)
              calc ∑ n₂ ∈ Finset.range (k₂ + 1),
                    ∑ _e₂ ∈ (Finset.Nat.antidiagonalTuple n₂ k₂).filter
                      (fun e => ∀ m, e m ≤ K),
                      boundedFactorGrid b K (k₁ + k₂)
                  = ∑ n₂ ∈ Finset.range (k₂ + 1),
                      (((Finset.Nat.antidiagonalTuple n₂ k₂).filter
                        (fun e => ∀ m, e m ≤ K)).card : ℝ) *
                        boundedFactorGrid b K (k₁ + k₂) := by
                    exact Finset.sum_congr rfl (fun n₂ _ => by
                      rw [Finset.sum_const, nsmul_eq_mul])
                _ ≤ ∑ n₂ ∈ Finset.range (k₂ + 1),
                      ((Finset.Nat.antidiagonalTuple n₂ k₂).card : ℝ) *
                        boundedFactorGrid b K (k₁ + k₂) := by
                    refine Finset.sum_le_sum (fun n₂ _ => ?_)
                    exact mul_le_mul_of_nonneg_right
                      (by exact_mod_cast hcard n₂) hbfg_nn
                _ = gridCellCount k₂ * boundedFactorGrid b K (k₁ + k₂) := by
                    rw [gridCellCount, Finset.sum_mul]
    _ = ∑ n₁ ∈ Finset.range (k₁ + 1),
          (((Finset.Nat.antidiagonalTuple n₁ k₁).filter (fun e => ∀ m, e m ≤ K)).card : ℝ) *
            (gridCellCount k₂ * boundedFactorGrid b K (k₁ + k₂)) := by
        exact Finset.sum_congr rfl (fun n₁ _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ ≤ (gridCellCount k₁ * gridCellCount k₂) * boundedFactorGrid b K (k₁ + k₂) := by
        have hbfg_nn : 0 ≤ boundedFactorGrid b K (k₁ + k₂) :=
          boundedFactorGrid_nonneg b hb K (k₁ + k₂)
        have hterm_nn : 0 ≤ gridCellCount k₂ * boundedFactorGrid b K (k₁ + k₂) :=
          mul_nonneg (gridCellCount_nonneg k₂) hbfg_nn
        calc ∑ n₁ ∈ Finset.range (k₁ + 1),
              (((Finset.Nat.antidiagonalTuple n₁ k₁).filter
                (fun e => ∀ m, e m ≤ K)).card : ℝ) *
                (gridCellCount k₂ * boundedFactorGrid b K (k₁ + k₂))
            ≤ ∑ n₁ ∈ Finset.range (k₁ + 1),
                ((Finset.Nat.antidiagonalTuple n₁ k₁).card : ℝ) *
                  (gridCellCount k₂ * boundedFactorGrid b K (k₁ + k₂)) := by
              refine Finset.sum_le_sum (fun n₁ _ => ?_)
              refine mul_le_mul_of_nonneg_right ?_ hterm_nn
              exact_mod_cast Finset.card_filter_le _ _
          _ = (gridCellCount k₁ * gridCellCount k₂) * boundedFactorGrid b K (k₁ + k₂) := by
              rw [← Finset.sum_mul]
              rw [show (∑ n₁ ∈ Finset.range (k₁ + 1),
                  ((Finset.Nat.antidiagonalTuple n₁ k₁).card : ℝ)) =
                gridCellCount k₁ from rfl]
              ring

noncomputable def boundedFactorGridWindow (b : ℕ → ℝ) (K W : ℕ) : ℝ :=
  ∑ k ∈ Finset.range W, boundedFactorGrid b K k

lemma boundedFactorGridWindow_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (K W : ℕ) :
    0 ≤ boundedFactorGridWindow b K W :=
  Finset.sum_nonneg (fun k _ => boundedFactorGrid_nonneg b hb K k)

lemma boundedFactorGrid_le_boundedFactorGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {K k W : ℕ} (hk : k < W) :
    boundedFactorGrid b K k ≤ boundedFactorGridWindow b K W :=
  Finset.single_le_sum (fun k' _ => boundedFactorGrid_nonneg b hb K k')
    (Finset.mem_range.mpr hk)

lemma one_le_boundedFactorGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {K W : ℕ}
    (hW : 1 ≤ W) : 1 ≤ boundedFactorGridWindow b K W := by
  rw [← boundedFactorGrid_zero b K]
  exact boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)

lemma boundedFactorGridWindow_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {K K' W W' : ℕ}
    (hK : K ≤ K') (hW : W ≤ W') :
    boundedFactorGridWindow b K W ≤ boundedFactorGridWindow b K' W' := by
  calc boundedFactorGridWindow b K W
      ≤ boundedFactorGridWindow b K' W := by
        exact Finset.sum_le_sum (fun k _ => boundedFactorGrid_mono_bound b hb hK k)
    _ ≤ boundedFactorGridWindow b K' W' := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hW) ?_
        intro k _ _
        exact boundedFactorGrid_nonneg b hb K' k

lemma antidiagonalTupleGrid_le_boundedFactorGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {K k W : ℕ} (hk : k ≤ K) (hkW : k < W) :
    antidiagonalTupleGrid b k ≤ boundedFactorGridWindow b K W := by
  rw [antidiagonalTupleGrid_eq_boundedFactorGrid b hk]
  exact boundedFactorGrid_le_boundedFactorGridWindow b hb hkW

lemma single_factor_mul_boundedFactorGridWindow_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {K q W : ℕ} (hq : 1 ≤ q) (hqK : q ≤ K) :
    b q * boundedFactorGridWindow b K W ≤ boundedFactorGridWindow b K (W + q) := by
  rw [boundedFactorGridWindow, Finset.mul_sum]
  calc ∑ k ∈ Finset.range W, b q * boundedFactorGrid b K k
      ≤ ∑ k ∈ Finset.range W, boundedFactorGrid b K (k + q) :=
        Finset.sum_le_sum (fun k _ =>
          single_factor_mul_boundedFactorGrid_le b hb k q hq hqK)
    _ ≤ boundedFactorGridWindow b K (W + q) := by
        rw [boundedFactorGridWindow]
        have himage : ∑ k ∈ Finset.range W, boundedFactorGrid b K (k + q) =
            ∑ k' ∈ (Finset.range W).image (fun k => k + q), boundedFactorGrid b K k' := by
          rw [Finset.sum_image (fun k₁ _ k₂ _ h => by omega)]
        rw [himage]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun k _ _ => boundedFactorGrid_nonneg b hb K k)
        intro k' hk'
        rw [Finset.mem_image] at hk'
        obtain ⟨k, hk, rfl⟩ := hk'
        rw [Finset.mem_range] at hk ⊢
        omega

noncomputable def windowPairCellCount (W₁ W₂ : ℕ) : ℝ :=
  ∑ k₁ ∈ Finset.range W₁, ∑ k₂ ∈ Finset.range W₂, gridCellCount k₁ * gridCellCount k₂

lemma windowPairCellCount_nonneg (W₁ W₂ : ℕ) : 0 ≤ windowPairCellCount W₁ W₂ :=
  Finset.sum_nonneg (fun k₁ _ => Finset.sum_nonneg (fun k₂ _ =>
    mul_nonneg (gridCellCount_nonneg k₁) (gridCellCount_nonneg k₂)))

lemma boundedFactorGridWindow_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (K W₁ W₂ : ℕ)
    (hW₁ : 1 ≤ W₁) (hW₂ : 1 ≤ W₂) :
    boundedFactorGridWindow b K W₁ * boundedFactorGridWindow b K W₂ ≤
      windowPairCellCount W₁ W₂ * boundedFactorGridWindow b K (W₁ + W₂ - 1) := by
  have hcell : ∀ k₁ ∈ Finset.range W₁, ∀ k₂ ∈ Finset.range W₂,
      boundedFactorGrid b K k₁ * boundedFactorGrid b K k₂ ≤
        (gridCellCount k₁ * gridCellCount k₂) *
          boundedFactorGridWindow b K (W₁ + W₂ - 1) := by
    intro k₁ hk₁ k₂ hk₂
    rw [Finset.mem_range] at hk₁ hk₂
    refine le_trans (boundedFactorGrid_mul_le b hb K k₁ k₂) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (gridCellCount_nonneg k₁) (gridCellCount_nonneg k₂))
    exact boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
  calc boundedFactorGridWindow b K W₁ * boundedFactorGridWindow b K W₂
      = ∑ k₁ ∈ Finset.range W₁, ∑ k₂ ∈ Finset.range W₂,
          boundedFactorGrid b K k₁ * boundedFactorGrid b K k₂ := by
        rw [boundedFactorGridWindow, boundedFactorGridWindow, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k₁ _ => by rw [Finset.mul_sum])
    _ ≤ ∑ k₁ ∈ Finset.range W₁, ∑ k₂ ∈ Finset.range W₂,
          (gridCellCount k₁ * gridCellCount k₂) *
            boundedFactorGridWindow b K (W₁ + W₂ - 1) :=
        Finset.sum_le_sum (fun k₁ hk₁ => Finset.sum_le_sum (fun k₂ hk₂ =>
          hcell k₁ hk₁ k₂ hk₂))
    _ = windowPairCellCount W₁ W₂ * boundedFactorGridWindow b K (W₁ + W₂ - 1) := by
        rw [windowPairCellCount, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k₁ _ => by rw [Finset.sum_mul])

end Combinatorics
end DifferentialGeometry
