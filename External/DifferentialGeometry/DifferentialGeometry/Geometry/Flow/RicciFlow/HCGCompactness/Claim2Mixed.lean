import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AkMFold
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Claim1Wiring

set_option autoImplicit false
set_option linter.style.longLine false


























noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]






def akAct {q : ℕ} (A : (Fin (2 + 1) → Idx) → Real) (B : (Fin q → Idx) → Real) :
    (Fin (q + 1) → Idx) → Real :=
  fun n => ∑ s : Fin q, ∑ p : Idx,
    A ![n 0, Fin.tail n s, p] * B (Function.update (Fin.tail n) s p)




omit [DecidableEq Idx] in
theorem covStep_chr_convert {q : ℕ}
    (ext : (Fin q → Idx) → Idx → Real)
    (chrR chrK : Idx → Idx → Idx → Real)
    (B : (Fin q → Idx) → Real) (n : Fin (q + 1) → Idx) :
    covDerivStepComp ext chrR B n =
      covDerivStepComp ext chrK B n +
        akAct (fun m => chrK (m 0) (m 1) (m 2) - chrR (m 0) (m 1) (m 2)) B n := by
  unfold covDerivStepComp akAct
  have hdiff : (∑ s : Fin q, ∑ p : Idx,
        (fun m : Fin (2 + 1) → Idx =>
            chrK (m 0) (m 1) (m 2) - chrR (m 0) (m 1) (m 2))
          ![n 0, Fin.tail n s, p] * B (Function.update (Fin.tail n) s p)) =
      (∑ s : Fin q, ∑ p : Idx,
        chrK (n 0) (Fin.tail n s) p * B (Function.update (Fin.tail n) s p)) -
      (∑ s : Fin q, ∑ p : Idx,
        chrR (n 0) (Fin.tail n s) p * B (Function.update (Fin.tail n) s p)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hdiff]
  ring






def akInnerPerm {q : ℕ} (s : Fin (q + 1)) : Equiv.Perm (Fin (q + 1)) :=
  ((finRotate (q + 1)).symm).trans (Equiv.swap s (Fin.last q))

theorem akInnerPerm_zero {q : ℕ} (s : Fin (q + 1)) :
    akInnerPerm s 0 = s := by
  have h0 : (finRotate (q + 1)).symm 0 = Fin.last q := by
    rw [Equiv.symm_apply_eq, finRotate_succ_apply, Fin.last_add_one]
  rcases eq_or_ne s (Fin.last q) with rfl | hs
  · simp [akInnerPerm, h0]
  · simp [akInnerPerm, h0, Equiv.swap_apply_right]

theorem akInnerPerm_succ {q : ℕ} (s : Fin (q + 1)) (i : Fin q) :
    akInnerPerm s i.succ =
      if Fin.castSucc i = s then Fin.last q else Fin.castSucc i := by
  have hrot : (finRotate (q + 1)).symm i.succ = Fin.castSucc i := by
    rw [Equiv.symm_apply_eq, finRotate_succ_apply]
    exact Fin.ext (by
      rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i)]
      simp)
  rcases eq_or_ne (Fin.castSucc i) s with h | h
  · simp [akInnerPerm, hrot, h]
  · have hlast : Fin.castSucc i ≠ Fin.last q := (Fin.castSucc_lt_last i).ne
    simp [akInnerPerm, hrot, Equiv.swap_apply_of_ne_of_ne h hlast, h]



def akSlotEquiv {q : ℕ} (s : Fin (q + 1)) : Fin (2 + q) ≃ Fin (q + 1 + 1) :=
  (finCongr (show 2 + q = q + 1 + 1 by omega)).trans (frontExtendEquiv (akInnerPerm s))

theorem akSlotEquiv_castAdd0 {q : ℕ} (s : Fin (q + 1)) :
    akSlotEquiv s (Fin.castAdd q (0 : Fin 2)) = 0 := by
  have h : (finCongr (show 2 + q = q + 1 + 1 by omega)
      (Fin.castAdd q (0 : Fin 2)) : Fin (q + 1 + 1)) = 0 := Fin.ext (by simp)
  simp [akSlotEquiv, h, frontExtendEquiv_zero]

theorem akSlotEquiv_castAdd1 {q : ℕ} (s : Fin (q + 1)) :
    akSlotEquiv s (Fin.castAdd q (1 : Fin 2)) = s.succ := by
  have h : (finCongr (show 2 + q = q + 1 + 1 by omega)
      (Fin.castAdd q (1 : Fin 2)) : Fin (q + 1 + 1)) = (0 : Fin (q + 1)).succ :=
    Fin.ext (by simp)
  rw [akSlotEquiv, Equiv.trans_apply, h, frontExtendEquiv_succ, akInnerPerm_zero]

theorem akSlotEquiv_natAdd {q : ℕ} (s : Fin (q + 1)) (i : Fin q) :
    akSlotEquiv s (Fin.natAdd 2 i) =
      (if Fin.castSucc i = s then Fin.last q else Fin.castSucc i).succ := by
  have h : (finCongr (show 2 + q = q + 1 + 1 by omega)
      (Fin.natAdd 2 i) : Fin (q + 1 + 1)) = (i.succ).succ :=
    Fin.ext (by simp)
  rw [akSlotEquiv, Equiv.trans_apply, h, frontExtendEquiv_succ, akInnerPerm_succ]




omit [DecidableEq Idx] in
theorem akActTerm_eq {q : ℕ} (A : (Fin (2 + 1) → Idx) → Real)
    (B : (Fin (q + 1) → Idx) → Real) (s : Fin (q + 1)) (n : Fin (q + 1 + 1) → Idx) :
    (∑ p : Idx, A ![n 0, Fin.tail n s, p] * B (Function.update (Fin.tail n) s p)) =
      contrTail A (fun w => B (fun j => w (Equiv.swap s (Fin.last q) j)))
        (fun j => n (akSlotEquiv s j)) := by
  classical
  rw [contrTail_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  ·
    congr 1
    funext m
    refine Fin.lastCases ?_ (fun m' => ?_) m
    · rw [Fin.snoc_last]
      rfl
    · rw [Fin.snoc_castSucc]
      refine Fin.cases ?_ (fun m'' => ?_) m'
      · show (![n 0, Fin.tail n s, c] : Fin 3 → Idx) 0 =
          n (akSlotEquiv s (Fin.castAdd q (0 : Fin 2)))
        rw [akSlotEquiv_castAdd0]
        rfl
      · have hm : m'' = 0 := Subsingleton.elim _ _
        subst hm
        show (![n 0, Fin.tail n s, c] : Fin 3 → Idx) 1 =
          n (akSlotEquiv s (Fin.castAdd q (1 : Fin 2)))
        rw [akSlotEquiv_castAdd1]
        rfl
  ·
    congr 1
    funext j
    rcases eq_or_ne j s with rfl | hjs
    · rw [Function.update_self, Equiv.swap_apply_left, Fin.snoc_last]
    · rw [Function.update_of_ne hjs]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hjl : Fin.castSucc j' ≠ Fin.last q := (Fin.castSucc_lt_last j').ne
        rw [Equiv.swap_apply_of_ne_of_ne hjs hjl, Fin.snoc_castSucc,
          show n (akSlotEquiv s (Fin.natAdd 2 j')) = n ((Fin.castSucc j').succ) from by
            rw [akSlotEquiv_natAdd, if_neg hjs]]
        rfl
      · rw [Equiv.swap_apply_right]
        have hs : s ≠ Fin.last q := fun h => hjs h.symm
        rcases Fin.eq_castSucc_or_eq_last s with ⟨s', rfl⟩ | rfl
        · rw [Fin.snoc_castSucc,
            show n (akSlotEquiv (Fin.castSucc s') (Fin.natAdd 2 s')) =
              n ((Fin.last q).succ) from by
              rw [akSlotEquiv_natAdd, if_pos rfl]]
          rfl
        · exact absurd rfl hs



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem contMDiffOn_finsetSum' {ι : Type*} {u : Set M} (t : Finset ι)
    (F : ι → M → Real)
    (hF : ∀ i ∈ t, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (F i) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ t, F i y) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using contMDiffOn_const (c := (0 : ℝ))
  | insert a s has ih =>
    have hsum : (fun y => ∑ i ∈ insert a s, F i y) =
        fun y => F a y + ∑ i ∈ s, F i y := by
      funext y
      rw [Finset.sum_insert has]
    rw [hsum]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_sum {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    {ι : Type*} (t : Finset ι) (F : ι → M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hF : ∀ i ∈ t, ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => F i y m) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun z k => ∑ i ∈ t, F i z k) a y n =
        ∑ i ∈ t, iterCovComp (I := I) frame chr (F i) a y n := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro y hy n
    have hzero : (fun (z : M) (k : Fin r → Idx) => ∑ i ∈ (∅ : Finset ι), F i z k) =
        fun z k => (0 : ℝ) * (0 : ℝ) := by
      funext z k
      simp
    rw [hzero,
      iterCovComp_smul hu frame chr 0 (fun _ _ => (0 : ℝ)) hframe hchr
        (fun m => contMDiffOn_const) a y hy n]
    simp
  | insert b s hbs ih =>
    intro y hy n
    have hsplit : (fun (z : M) (k : Fin r → Idx) => ∑ i ∈ insert b s, F i z k) =
        fun z k => F b z k + ∑ i ∈ s, F i z k := by
      funext z k
      rw [Finset.sum_insert hbs]
    rw [hsplit,
      iterCovComp_add hu frame chr (F b) (fun z k => ∑ i ∈ s, F i z k) hframe hchr
        (hF b (Finset.mem_insert_self b s))
        (fun m => contMDiffOn_finsetSum' s (fun i y => F i y m)
          (fun i hi => hF i (Finset.mem_insert_of_mem hi) m)) a y hy n,
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) y hy n,
      Finset.sum_insert hbs]


omit [DecidableEq Idx] in
theorem compL2_sum_le {r : ℕ} {ι : Type*} (t : Finset ι)
    (F : ι → (Fin r → Idx) → Real) :
    compL2 (fun n => ∑ i ∈ t, F i n) ≤ ∑ i ∈ t, compL2 (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : compL2 (fun _ : Fin r → Idx => (0 : ℝ)) = 0 := by
      simp [compL2, compL2Sq]
    exact le_of_eq this
  | insert b s hbs ih =>
    simp only [Finset.sum_insert hbs]
    exact le_trans (compL2_add_le (F b) (fun n => ∑ i ∈ s, F i n))
      (add_le_add le_rfl ih)







omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem compL2_akAct_le {q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (A : M → (Fin (2 + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (hA : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hB : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u)
    (a : ℕ) {y : M} (hy : y ∈ u) :
    compL2 (iterCovComp (I := I) frame chr (fun z => akAct (A z) (B z)) a y) ≤
      (q + 1 : ℝ) * ∑ c ∈ Finset.range (a + 1), (a.choose c : Real) *
        compL2 (iterCovCompU (I := I) frame chr A c y) *
        compL2 (iterCovComp (I := I) frame chr B (a - c) y) := by
  classical

  have hbase : (fun z => akAct (A z) (B z)) =
      fun z (n : Fin (q + 1 + 1) → Idx) => ∑ s : Fin (q + 1),
        contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
          (fun j => n (akSlotEquiv s j)) := by
    funext z n
    unfold akAct
    exact Finset.sum_congr rfl fun s _ => akActTerm_eq (A z) (B z) s n

  have hFsm : ∀ s : Fin (q + 1), ∀ k : Fin (q + 1 + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun z => contrTail (A z)
          (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
          (fun j => k (akSlotEquiv s j))) u :=
    fun s k => contMDiffOn_contrTail _ _ hA
      (fun k' => hB (fun j => k' (Equiv.swap s (Fin.last q) j))) _
  rw [hbase]

  have htower := iterCovComp_sum hu frame chr Finset.univ
    (fun (s : Fin (q + 1)) (z : M) (n : Fin (q + 1 + 1) → Idx) =>
      contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
        (fun j => n (akSlotEquiv s j)))
    hframe hchr (fun s _ => hFsm s) a y hy
  calc compL2 (iterCovComp (I := I) frame chr
        (fun z n => ∑ s : Fin (q + 1),
          contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
            (fun j => n (akSlotEquiv s j))) a y)
      = compL2 (fun n : Fin (q + 1 + 1 + a) → Idx => ∑ s : Fin (q + 1),
          iterCovComp (I := I) frame chr
            (fun z (nn : Fin (q + 1 + 1) → Idx) =>
              contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
                (fun j => nn (akSlotEquiv s j))) a y n) :=
        congrArg compL2 (funext fun n => htower n)
    _ ≤ ∑ s : Fin (q + 1), compL2 (iterCovComp (I := I) frame chr
          (fun z (nn : Fin (q + 1 + 1) → Idx) =>
            contrTail (A z) (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
              (fun j => nn (akSlotEquiv s j))) a y) :=
        compL2_sum_le Finset.univ _
    _ ≤ ∑ _s : Fin (q + 1), ∑ c ∈ Finset.range (a + 1), (a.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c y) *
          compL2 (iterCovComp (I := I) frame chr B (a - c) y) := by
        refine Finset.sum_le_sum fun s _ => ?_

        rw [compL2_iterCovComp_compReindex (akSlotEquiv s) frame chr
          (fun z => contrTail (A z)
            (fun w => B z (fun j => w (Equiv.swap s (Fin.last q) j)))) a y]
        refine le_trans (compL2_iterCovComp_contrTail_le hu frame chr hframe hchr a A
          (fun z (w : Fin (q + 1) → Idx) => B z (fun j => w (Equiv.swap s (Fin.last q) j)))
          hA (fun k' => hB (fun j => k' (Equiv.swap s (Fin.last q) j))) hy)
          (le_of_eq ?_)
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [compL2_iterCovComp_compReindex (Equiv.swap s (Fin.last q)) frame chr B (a - c) y]
    _ = (q + 1 : ℝ) * ∑ c ∈ Finset.range (a + 1), (a.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c y) *
          compL2 (iterCovComp (I := I) frame chr B (a - c) y) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring






omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem iterCov_chr_convert {q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrR chrK : M → Idx → Idx → Idx → Real)
    (B : M → (Fin q → Idx) → Real) (y : M) (n : Fin (q + 1) → Idx) :
    iterCovComp (I := I) frame chrR B 1 y n =
      iterCovComp (I := I) frame chrK B 1 y n +
        akAct (fun m => chrK y (m 0) (m 1) (m 2) - chrR y (m 0) (m 1) (m 2)) (B y) n := by
  simp only [iterCovComp_succ, iterCovComp_zero]
  exact covStep_chr_convert _ _ _ _ n












omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem claim2core {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrR chrK : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrR : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrR y d i j) u)
    (hchrK : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrK y d i j) u)
    (L : ℕ) (CA : ℕ → ℝ) (hCA0 : ∀ c, 0 ≤ CA c)
    (hCA : ∀ c, c < L → ∀ y ∈ u,
      compL2 (iterCovCompU (I := I) frame chrR
        (fun z (m : Fin (2 + 1) → Idx) =>
          chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) c y) ≤ CA c)
    (a : ℕ) :
    a ≤ L → ∀ {Q : ℕ} (B : M → (Fin (Q + 1) → Idx) → Real),
      (∀ k : Fin (Q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u) →
      ∀ (S : ℕ → ℝ),
      (∀ j, j ≤ a → ∀ y ∈ u, compL2 (iterCovComp (I := I) frame chrK B j y) ≤ S j) →
      ∃ C, 0 ≤ C ∧ ∀ y ∈ u,
        compL2 (iterCovComp (I := I) frame chrR B a y) ≤ C := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro haL Q B hB S hKt
    classical
    cases a with
    | zero =>
      refine ⟨max (S 0) 0, le_max_right _ _, fun y hy => ?_⟩
      have h := hKt 0 le_rfl y hy
      rw [iterCovComp_zero] at h ⊢
      exact le_trans h (le_max_left _ _)
    | succ a' =>

      have hakSm : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun y => chrK y (k 0) (k 1) (k 2) - chrR y (k 0) (k 1) (k 2)) u :=
        fun k => (hchrK (k 0) (k 1) (k 2)).sub (hchrR (k 0) (k 1) (k 2))
      have hB'sm : ∀ k : Fin (Q + 1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun y => iterCovComp (I := I) frame chrK B 1 y k) u :=
        iterCovComp_contMDiffOn hu frame chrK B hframe hchrK hB 1
      have hakActSm : ∀ k : Fin (Q + 1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun y => akAct
            (fun m => chrK y (m 0) (m 1) (m 2) - chrR y (m 0) (m 1) (m 2)) (B y) k) u := by
        intro k
        have hexp : (fun y => akAct
            (fun m => chrK y (m 0) (m 1) (m 2) - chrR y (m 0) (m 1) (m 2)) (B y) k) =
          fun y => ∑ s : Fin (Q + 1), ∑ p : Idx,
            (chrK y ((![k 0, Fin.tail k s, p] : Fin 3 → Idx) 0)
                ((![k 0, Fin.tail k s, p] : Fin 3 → Idx) 1)
                ((![k 0, Fin.tail k s, p] : Fin 3 → Idx) 2) -
              chrR y ((![k 0, Fin.tail k s, p] : Fin 3 → Idx) 0)
                ((![k 0, Fin.tail k s, p] : Fin 3 → Idx) 1)
                ((![k 0, Fin.tail k s, p] : Fin 3 → Idx) 2)) *
              B y (Function.update (Fin.tail k) s p) := rfl
        rw [hexp]
        exact contMDiffOn_finsetSum' _ _ fun s _ =>
          contMDiffOn_finsetSum' _ _ fun p _ =>
            (hakSm ![k 0, Fin.tail k s, p]).mul (hB _)

      have hKt' : ∀ j, j ≤ a' → ∀ y ∈ u,
          compL2 (iterCovComp (I := I) frame chrK
            (fun z => iterCovComp (I := I) frame chrK B 1 z) j y) ≤ S (j + 1) := by
        intro j hj y hy
        rw [← compL2_iterCovComp_shift frame chrK B j y]
        exact hKt (j + 1) (by omega) y hy
      obtain ⟨C1, hC10, hC1⟩ := ih a' (Nat.lt_succ_self a') (by omega)
        (fun z => iterCovComp (I := I) frame chrK B 1 z) hB'sm (fun j => S (j + 1)) hKt'

      have hmixc : ∀ c, c ≤ a' → ∃ C, 0 ≤ C ∧ ∀ y ∈ u,
          compL2 (iterCovComp (I := I) frame chrR B (a' - c) y) ≤ C :=
        fun c hc => ih (a' - c) (by omega) (by omega) B hB S (fun j hj => hKt j (by omega))
      choose! Cm hCm0 hCmB using hmixc

      have hsumnn : (0 : ℝ) ≤ ∑ c ∈ Finset.range (a' + 1),
          (a'.choose c : ℝ) * CA c * Cm c :=
        Finset.sum_nonneg fun c hc =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA0 c))
            (hCm0 c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)))
      refine ⟨C1 + (Q + 1 : ℝ) * ∑ c ∈ Finset.range (a' + 1),
        (a'.choose c : ℝ) * CA c * Cm c,
        add_nonneg hC10 (mul_nonneg (by positivity) hsumnn), fun y hy => ?_⟩
      calc compL2 (iterCovComp (I := I) frame chrR B (a' + 1) y)
          = compL2 (iterCovComp (I := I) frame chrR
              (fun z => iterCovComp (I := I) frame chrR B 1 z) a' y) :=
            compL2_iterCovComp_shift frame chrR B a' y
        _ = compL2 (iterCovComp (I := I) frame chrR
              (fun z (n : Fin (Q + 1 + 1) → Idx) =>
                iterCovComp (I := I) frame chrK B 1 z n +
                  akAct (fun m => chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2))
                    (B z) n) a' y) := by
            refine congrArg compL2 (iterCovComp_congr_on hu frame chrR ?_ a' y hy)
            intro z _
            funext n
            exact iterCov_chr_convert frame chrR chrK B z n
        _ = compL2 (fun n : Fin (Q + 1 + 1 + a') → Idx =>
              iterCovComp (I := I) frame chrR
                (fun z => iterCovComp (I := I) frame chrK B 1 z) a' y n +
              iterCovComp (I := I) frame chrR
                (fun z => akAct
                  (fun m => chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) (B z))
                a' y n) :=
            congrArg compL2 (funext fun n => iterCovComp_add hu frame chrR _ _ hframe hchrR
              hB'sm hakActSm a' y hy n)
        _ ≤ compL2 (iterCovComp (I := I) frame chrR
              (fun z => iterCovComp (I := I) frame chrK B 1 z) a' y) +
            compL2 (iterCovComp (I := I) frame chrR
              (fun z => akAct
                (fun m => chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) (B z))
              a' y) := compL2_add_le _ _
        _ ≤ C1 + (Q + 1 : ℝ) * ∑ c ∈ Finset.range (a' + 1),
              (a'.choose c : ℝ) * CA c * Cm c := by
            refine add_le_add (hC1 y hy) ?_
            refine le_trans (compL2_akAct_le hu frame chrR hframe hchrR
              (fun z (m : Fin (2 + 1) → Idx) =>
                chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) B
              hakSm hB a' hy) ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine Finset.sum_le_sum fun c hc => ?_
            have hc' : c ≤ a' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
            have h1 := hCA c (by omega) y hy
            have h2 := hCmB c hc' y hy
            calc (a'.choose c : ℝ) *
                  compL2 (iterCovCompU (I := I) frame chrR
                    (fun z (m : Fin (2 + 1) → Idx) =>
                      chrK z (m 0) (m 1) (m 2) - chrR z (m 0) (m 1) (m 2)) c y) *
                  compL2 (iterCovComp (I := I) frame chrR B (a' - c) y)
                ≤ (a'.choose c : ℝ) * CA c *
                  compL2 (iterCovComp (I := I) frame chrR B (a' - c) y) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) (compL2_nonneg _)
              _ ≤ (a'.choose c : ℝ) * CA c * Cm c :=
                  mul_le_mul_of_nonneg_left h2
                    (mul_nonneg (Nat.cast_nonneg _) (hCA0 c))



set_option backward.isDefEq.respectTransparency false in






omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem claim2_geom
    (e₀ : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e₀]
    (gK gRef : SmoothRiemannianMetric I M) (basisE : Module.Basis Idx Real E)
    (C0 K : Real) (hK0 : 0 ≤ K)
    (hGinv : ∀ y ∈ e₀.baseSet, compL2 (ginvCompField (I := I) e₀ gK basisE y) ≤ C0)
    (L : ℕ)
    (hgK : ∀ y ∈ e₀.baseSet, ∀ j, 1 ≤ j → j ≤ L →
      compL2 (iterCovComp (I := I) (fun a y' => e₀.localFrame basisE a y')
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a y'' => e₀.localFrame basisE a y'')
          (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y')
        (frameComp0S (I := I) (metricTensorField (I := I) gK)
          (fun a y' => e₀.localFrame basisE a y')) j y) ≤ K)
    {Q : ℕ} (B : M → (Fin (Q + 1) → Idx) → Real)
    (hB : ∀ k : Fin (Q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) e₀.baseSet)
    (a : ℕ) (haL : a ≤ L) (S : ℕ → ℝ)
    (hBk : ∀ j, j ≤ a → ∀ y ∈ e₀.baseSet,
      compL2 (iterCovComp (I := I) (fun a' y' => e₀.localFrame basisE a' y')
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK)
          (fun a'' y'' => e₀.localFrame basisE a'' y'')
          (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y') B j y) ≤ S j) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ e₀.baseSet,
      compL2 (iterCovComp (I := I) (fun a' y' => e₀.localFrame basisE a' y')
        (fun y' => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef)
          (fun a'' y'' => e₀.localFrame basisE a'' y'')
          (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y') B a y) ≤ C := by
  classical
  set frame : Idx → (x : M) → TangentSpace I x :=
    fun a' y' => e₀.localFrame basisE a' y' with hframedef
  set chrRf : M → Idx → Idx → Idx → Real := fun y' =>
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gRef) frame
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y' with hchrRdef
  set chrKf : M → Idx → Idx → Idx → Real := fun y' =>
    christoffelSymbolInFrame (leviCivitaConnectionOfMetric (I := I) gK) frame
      (e₀.isLocalFrameOn_localFrame_baseSet I 1 basisE) y' with hchrKdef
  have hframeSm : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) e₀.baseSet :=
    fun d => frame_e_mdiffOn e₀ basisE d
  have hchrRsm : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrRf y d i j) e₀.baseSet :=
    fun d i j => lcChrist_e_mdiffOn e₀ gRef basisE d i j
  have hchrKsm : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrKf y d i j) e₀.baseSet :=
    fun d i j => lcChrist_e_mdiffOn e₀ gK basisE d i j

  have hCAex : ∀ c, c < L → ∃ Cc, 0 ≤ Cc ∧ ∀ y ∈ e₀.baseSet,
      compL2 (iterCovCompU (I := I) frame chrRf
        (fun z (m : Fin (2 + 1) → Idx) =>
          chrKf z (m 0) (m 1) (m 2) - chrRf z (m 0) (m 1) (m 2)) c y) ≤ Cc := by
    intro c hcL
    obtain ⟨Cc, hCc0, hCc⟩ := claim1_geom e₀ gK gRef basisE C0 K hGinv c
      (fun y' hy' j h1 h2 => hgK y' hy' j h1 (by omega))
    refine ⟨Cc * (1 + K), mul_nonneg hCc0 (by linarith), fun y hy => ?_⟩
    refine le_trans (hCc y hy) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCc0
    have hgkc := hgK y hy (c + 1) (by omega) (by omega)
    linarith
  choose! CA hCA0 hCA using hCAex
  exact claim2core e₀.open_baseSet frame chrRf chrKf hframeSm hchrRsm hchrKsm
    L (fun c => max (CA c) 0) (fun c => le_max_right _ _)
    (fun c hc y hy => le_trans (hCA c hc y hy) (le_max_left _ _)) a haL B hB S hBk

end DifferentialGeometry.PDE.RicciFlow
