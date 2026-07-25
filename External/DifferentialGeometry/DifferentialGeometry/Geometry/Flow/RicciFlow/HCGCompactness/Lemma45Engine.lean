import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AkMFold
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Lemma45CovariantAbstract
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.KoszulDifference

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false























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




noncomputable def claim1MulConst (C0 KR L : Real) (m : ℕ) : Real :=
  Nat.strongRecOn' m fun n C =>
    max C0 0 * (max KR 0 * L +
      ∑ c : Fin n, (n.choose c : Real) * C c c.isLt * L)


theorem claim1MulConst_eq (C0 KR L : Real) (m : ℕ) :
    claim1MulConst C0 KR L m =
      max C0 0 * (max KR 0 * L +
        ∑ c ∈ Finset.range m, (m.choose c : Real) * claim1MulConst C0 KR L c * L) := by
  rw [claim1MulConst, Nat.strongRecOn'_beta, ← Fin.sum_univ_eq_sum_range]
  rfl



theorem claim1MulConst_nonneg {C0 KR L : Real} (hL : 0 ≤ L) (m : ℕ) :
    0 ≤ claim1MulConst C0 KR L m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      rw [claim1MulConst_eq]
      refine mul_nonneg (le_max_right C0 0) (add_nonneg (mul_nonneg (le_max_right KR 0) hL) ?_)
      exact Finset.sum_nonneg fun c hc =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih c (Finset.mem_range.mp hc))) hL




omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1_eps_mul_bound {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (1 + 1) → Idx) → Real)
    (hg : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 KR L eps : Real) (hL : 0 ≤ L)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (m : ℕ) :
    (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m + 1 →
      compL2 (iterCovComp (I := I) frame chr g j x) ≤ L * eps) →
    (∀ x ∈ u, ∀ m', m' ≤ m →
      compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m' x) ≤
        KR * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x)) →
    ∀ x ∈ u, compL2 (iterCovCompU (I := I) frame chr A m x) ≤
      claim1MulConst C0 KR L m * eps := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hK hrelB x hx
    classical
    have hKR0 : (0 : Real) ≤ max KR 0 := le_max_right KR 0
    have hCcB : ∀ c, c < m → ∀ x ∈ u,
        compL2 (iterCovCompU (I := I) frame chr A c x) ≤
          claim1MulConst C0 KR L c * eps := fun c hc =>
      ih c hc (fun x hx j h1 h2 => hK x hx j h1 (by omega))
        (fun x hx m' h' => hrelB x hx m' (le_trans h' (le_of_lt hc)))
    set S := ∑ c ∈ Finset.range m,
      (m.choose c : Real) * claim1MulConst C0 KR L c * L with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun c hc =>
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (claim1MulConst_nonneg hL c)) hL
    have hgm1eps : compL2 (iterCovComp (I := I) frame chr g (m + 1) x) ≤ L * eps :=
      hK x hx (m + 1) (by omega) le_rfl
    have hgm1 : (0 : Real) ≤ compL2 (iterCovComp (I := I) frame chr g (m + 1) x) :=
      compL2_nonneg _
    have hrel3 : compL2 (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (g z)) m x) ≤
        max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) :=
      le_trans (hrelB x hx m le_rfl)
        (mul_le_mul_of_nonneg_right (le_max_left KR 0) hgm1)
    have hcore : compL2 (iterCovCompU (I := I) frame chr A m x) ≤
        compL2 (Ginv x) *
          (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
          ∑ c ∈ Finset.range m, (m.choose c : Real) *
            compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)) := by
      calc compL2 (iterCovCompU (I := I) frame chr A m x)
          ≤ compL2 (contrTail (iterCovCompU (I := I) frame chr A m x) (g x)) *
              compL2 (Ginv x) :=
            compL2_le_contrTail_inv _ (g x) (Ginv x) (hinv x hx)
        _ ≤ (compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x) +
              ∑ c ∈ Finset.range m, (m.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chr A c x) *
                compL2 (iterCovComp (I := I) frame chr g (m - c) x)) * compL2 (Ginv x) :=
            mul_le_mul_of_nonneg_right
              (compL2_contrTail_topU_le hu frame chr hframe hchr g hg m A hA hx)
              (compL2_nonneg _)
        _ ≤ (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
              ∑ c ∈ Finset.range m, (m.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chr A c x) *
                compL2 (iterCovComp (I := I) frame chr g (m - c) x)) * compL2 (Ginv x) :=
            mul_le_mul_of_nonneg_right (add_le_add hrel3 le_rfl) (compL2_nonneg _)
        _ = compL2 (Ginv x) *
              (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
              ∑ c ∈ Finset.range m, (m.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chr A c x) *
                compL2 (iterCovComp (I := I) frame chr g (m - c) x)) := mul_comm _ _
    have hsum : (∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x)) ≤ S * eps := by
      rw [hSdef, Finset.sum_mul]
      refine Finset.sum_le_sum fun c hc => ?_
      have hc' := Finset.mem_range.mp hc
      have hAc := hCcB c hc' x hx
      have hgmc : compL2 (iterCovComp (I := I) frame chr g (m - c) x) ≤ L * eps :=
        hK x hx (m - c) (by omega) (by omega)
      have hCc0 : 0 ≤ claim1MulConst C0 KR L c :=
        claim1MulConst_nonneg (C0 := C0) (KR := KR) hL c
      have hb0 : (0 : Real) ≤ (m.choose c : Real) * claim1MulConst C0 KR L c * L :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCc0) hL
      calc (m.choose c : Real) * compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)
          ≤ (m.choose c : Real) * (claim1MulConst C0 KR L c * eps) *
              compL2 (iterCovComp (I := I) frame chr g (m - c) x) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg _)) (compL2_nonneg _)
        _ ≤ (m.choose c : Real) * (claim1MulConst C0 KR L c * eps) * (L * eps) :=
            mul_le_mul_of_nonneg_left hgmc
              (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCc0 heps0))
        _ ≤ ((m.choose c : Real) * claim1MulConst C0 KR L c * L) * eps := by
            nlinarith [mul_nonneg hb0 heps0]
    have htop : max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) ≤
        max KR 0 * L * eps := by
      calc
        max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x)
            ≤ max KR 0 * (L * eps) := mul_le_mul_of_nonneg_left hgm1eps hKR0
        _ = max KR 0 * L * eps := by ring
    have hbr : max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
          (∑ c ∈ Finset.range m, (m.choose c : Real) *
            compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)) ≤
        (max KR 0 * L + S) * eps := by
      rw [add_mul]
      exact add_le_add htop hsum
    have hbr0 : (0 : Real) ≤
        max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x) :=
      add_nonneg (mul_nonneg hKR0 hgm1) (Finset.sum_nonneg fun c _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (compL2_nonneg _)) (compL2_nonneg _))
    have hGx : compL2 (Ginv x) ≤ max C0 0 :=
      le_trans (hGinv x hx) (le_max_left C0 0)
    calc compL2 (iterCovCompU (I := I) frame chr A m x)
        ≤ compL2 (Ginv x) *
            (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
            ∑ c ∈ Finset.range m, (m.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chr A c x) *
              compL2 (iterCovComp (I := I) frame chr g (m - c) x)) := hcore
      _ ≤ max C0 0 * ((max KR 0 * L + S) * eps) :=
        mul_le_mul hGx hbr hbr0 (le_max_right C0 0)
      _ = claim1MulConst C0 KR L m * eps := by
        rw [claim1MulConst_eq, hSdef]
        ring







omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1_eps_mul {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (1 + 1) → Idx) → Real)
    (hg : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 KR L eps : Real) (hL : 0 ≤ L)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (m : ℕ) :
    (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m + 1 →
      compL2 (iterCovComp (I := I) frame chr g j x) ≤ L * eps) →
    (∀ x ∈ u, ∀ m', m' ≤ m →
      compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m' x) ≤
        KR * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x)) →
    ∃ C, 0 ≤ C ∧ ∀ x ∈ u,
      compL2 (iterCovCompU (I := I) frame chr A m x) ≤ C * eps := by
  intro hK hrelB
  exact ⟨claim1MulConst C0 KR L m, claim1MulConst_nonneg hL m,
    claim1_eps_mul_bound hu frame chr hframe hchr g hg Ginv A hA hinv C0 KR L eps
      hL heps0 heps1 hGinv m hK hrelB⟩



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1_eps {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (1 + 1) → Idx) → Real)
    (hg : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 KR eps : Real)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (m : ℕ) :
    (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m + 1 →
      compL2 (iterCovComp (I := I) frame chr g j x) ≤ eps) →
    (∀ x ∈ u, ∀ m', m' ≤ m →
      compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m' x) ≤
        KR * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x)) →
    ∃ C, 0 ≤ C ∧ ∀ x ∈ u,
      compL2 (iterCovCompU (I := I) frame chr A m x) ≤ C * eps := by
  intro hK
  refine claim1_eps_mul hu frame chr hframe hchr g hg Ginv A hA hinv C0 KR 1 eps
    zero_le_one heps0 heps1 hGinv m ?_
  simpa only [one_mul] using hK











def chrDiffField (chrG chrH : M → Idx → Idx → Idx → Real) :
    M → (Fin (2 + 1) → Idx) → Real :=
  fun y v => chrG y (v 0) (v 1) (v 2) - chrH y (v 0) (v 1) (v 2)



def chrCorrField (D : M → Idx → Idx → Idx → Real) {r : ℕ}
    (X : M → (Fin r → Idx) → Real) (s : Fin r) :
    M → (Fin (r + 1) → Idx) → Real :=
  fun y n => ∑ p : Idx,
    D y (n 0) (Fin.tail n s) p * X y (Function.update (Fin.tail n) s p)



def slotRotEquiv {r' : ℕ} (s : Fin (r' + 1)) : Fin (r' + 1) ≃ Fin (r' + 1) :=
  (finSuccEquiv' s).trans (finSuccEquiv' (Fin.last r')).symm

theorem slotRotEquiv_self {r' : ℕ} (s : Fin (r' + 1)) :
    slotRotEquiv s s = Fin.last r' := by
  simp only [slotRotEquiv, Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv'_symm_none]

theorem slotRotEquiv_succAbove {r' : ℕ} (s : Fin (r' + 1)) (i : Fin r') :
    slotRotEquiv s (s.succAbove i) = i.castSucc := by
  simp only [slotRotEquiv, Equiv.trans_apply, finSuccEquiv'_succAbove,
    finSuccEquiv'_symm_some, Fin.succAbove_last]





def corrSlotMap {r' : ℕ} (s : Fin (r' + 1)) : Fin (2 + r') → Fin (r' + 1 + 1) :=
  Fin.addCases (fun i : Fin 2 => if i = 0 then 0 else s.succ)
    (fun i : Fin r' => (s.succAbove i).succ)

theorem corrSlotMap_injective {r' : ℕ} (s : Fin (r' + 1)) :
    Function.Injective (corrSlotMap s) := by
  intro a b
  refine Fin.addCases (fun ia => Fin.addCases (fun ib => ?_) (fun ib => ?_) b)
    (fun ia => Fin.addCases (fun ib => ?_) (fun ib => ?_) b) a <;>
    intro hab <;>
    simp only [corrSlotMap, Fin.addCases_left, Fin.addCases_right] at hab
  ·
    congr 1
    by_cases h1 : ia = 0 <;> by_cases h2 : ib = 0
    · rw [h1, h2]
    · rw [if_pos h1, if_neg h2] at hab
      exact absurd hab.symm (Fin.succ_ne_zero s)
    · rw [if_neg h1, if_pos h2] at hab
      exact absurd hab (Fin.succ_ne_zero s)
    · omega
  ·
    by_cases h1 : ia = 0
    · rw [if_pos h1] at hab
      exact absurd hab.symm (Fin.succ_ne_zero _)
    · rw [if_neg h1] at hab
      have hs := Fin.succ_injective _ hab
      exact absurd hs.symm (Fin.succAbove_ne s ib)
  ·
    by_cases h2 : ib = 0
    · rw [if_pos h2] at hab
      exact absurd hab (Fin.succ_ne_zero _)
    · rw [if_neg h2] at hab
      have hs := Fin.succ_injective _ hab
      exact absurd hs (Fin.succAbove_ne s ia)
  ·
    have hs := Fin.succ_injective _ hab
    have hi : ia = ib := Fin.succAbove_right_injective (p := s) hs
    rw [hi]

theorem corrSlotMap_bijective {r' : ℕ} (s : Fin (r' + 1)) :
    Function.Bijective (corrSlotMap s) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨corrSlotMap_injective s, by simp [Fintype.card_fin]; omega⟩


def corrSlotEquiv {r' : ℕ} (s : Fin (r' + 1)) : Fin (2 + r') ≃ Fin (r' + 1 + 1) :=
  Equiv.ofBijective (corrSlotMap s) (corrSlotMap_bijective s)




omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem chrCorrField_eq_contrTail {r' : ℕ}
    (D : M → Idx → Idx → Idx → Real) (X : M → (Fin (r' + 1) → Idx) → Real)
    (s : Fin (r' + 1)) :
    chrCorrField D X s = fun y n =>
      contrTail (fun v : Fin (2 + 1) → Idx => D y (v 0) (v 1) (v 2))
        (fun w : Fin (r' + 1) → Idx => X y (fun j => w (slotRotEquiv s j)))
        (fun j => n (corrSlotEquiv s j)) := by
  funext y n
  rw [chrCorrField, contrTail_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcorr0 : corrSlotEquiv s (Fin.castAdd r' (0 : Fin 2)) = 0 := by
    show corrSlotMap s (Fin.castAdd r' (0 : Fin 2)) = 0
    rw [corrSlotMap, Fin.addCases_left, if_pos rfl]
  have hcorr1 : corrSlotEquiv s (Fin.castAdd r' (1 : Fin 2)) = s.succ := by
    show corrSlotMap s (Fin.castAdd r' (1 : Fin 2)) = s.succ
    rw [corrSlotMap, Fin.addCases_left, if_neg (by decide)]
  have hcorrR : ∀ i : Fin r',
      corrSlotEquiv s (Fin.natAdd 2 i) = (s.succAbove i).succ := by
    intro i
    show corrSlotMap s (Fin.natAdd 2 i) = (s.succAbove i).succ
    rw [corrSlotMap, Fin.addCases_right]
  have h0 : (Fin.snoc (fun i : Fin 2 => n (corrSlotEquiv s (Fin.castAdd r' i))) c
      : Fin (2 + 1) → Idx) 0 = n 0 := by
    rw [show (0 : Fin (2 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc, hcorr0]
  have h1 : (Fin.snoc (fun i : Fin 2 => n (corrSlotEquiv s (Fin.castAdd r' i))) c
      : Fin (2 + 1) → Idx) 1 = Fin.tail n s := by
    rw [show (1 : Fin (2 + 1)) = Fin.castSucc 1 from rfl, Fin.snoc_castSucc, hcorr1]
    rfl
  have h2 : (Fin.snoc (fun i : Fin 2 => n (corrSlotEquiv s (Fin.castAdd r' i))) c
      : Fin (2 + 1) → Idx) 2 = c := by
    rw [show (2 : Fin (2 + 1)) = Fin.last 2 from rfl, Fin.snoc_last]
  have hX : Function.update (Fin.tail n) s c = fun j =>
      (Fin.snoc (fun j' : Fin r' => n (corrSlotEquiv s (Fin.natAdd 2 j'))) c
        : Fin (r' + 1) → Idx) (slotRotEquiv s j) := by
    funext j
    refine Fin.succAboveCases s ?_ (fun i => ?_) j
    · rw [Function.update_self, slotRotEquiv_self, Fin.snoc_last]
    · rw [Function.update_of_ne (Fin.succAbove_ne s i), slotRotEquiv_succAbove,
        Fin.snoc_castSucc, hcorrR i]
      rfl
  rw [h0, h1, h2, hX]




omit [DecidableEq Idx] in
theorem covDerivStepComp_chr_sub {r : ℕ}
    (ext : (Fin r → Idx) → Idx → Real) (chrG chrH : Idx → Idx → Idx → Real)
    (A : (Fin r → Idx) → Real) (n : Fin (r + 1) → Idx) :
    covDerivStepComp ext chrG A n =
      covDerivStepComp ext chrH A n -
        ∑ s : Fin r, ∑ p : Idx,
          (chrG (n 0) (Fin.tail n s) p - chrH (n 0) (Fin.tail n s) p) *
            A (Function.update (Fin.tail n) s p) := by
  unfold covDerivStepComp
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring




omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem iterCov_one_chr_change {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrG chrH : M → Idx → Idx → Idx → Real)
    (X : M → (Fin r → Idx) → Real) (y : M) (n : Fin (r + 1) → Idx) :
    iterCovComp (I := I) frame chrG X 1 y n =
      iterCovComp (I := I) frame chrH X 1 y n -
        ∑ s : Fin r,
          chrCorrField (fun z d b p => chrG z d b p - chrH z d b p) X s y n := by
  show covDerivStepComp (frameExtData (I := I) frame X y) (chrG y) (X y) n = _
  rw [covDerivStepComp_chr_sub (frameExtData (I := I) frame X y) (chrG y) (chrH y) (X y) n]
  rfl



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem contMDiffOn_finsetSum' {ι : Type*} {u : Set M} (t : Finset ι)
    (f : ι → M → Real) (hf : ∀ i ∈ t, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f i y) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ t, f i y) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (contMDiffOn_const : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun _ => (0 : Real)) u)
  | insert a t ha ih =>
    rw [show (fun y => ∑ i ∈ insert a t, f i y) = fun y => f a y + ∑ i ∈ t, f i y from by
      funext y; rw [Finset.sum_insert ha]]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))


omit [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem contMDiffOn_chrCorrField {r : ℕ} {u : Set M}
    (D : M → Idx → Idx → Idx → Real)
    (hD : ∀ d b p : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => D y d b p) u)
    (X : M → (Fin r → Idx) → Real)
    (hX : ∀ k : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => X y k) u)
    (s : Fin r) (n : Fin (r + 1) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrCorrField D X s y n) u :=
  contMDiffOn_finsetSum' Finset.univ _ (fun p _ => (hD _ _ p).mul (hX _))


omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_zero_field {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun (_ : M) (_ : Fin r → Idx) => (0 : Real)) a y n
        = 0 := by
  intro y hy n
  have h : (fun (_ : M) (_ : Fin r → Idx) => (0 : Real)) =
      fun z k => (0 : Real) * ((fun (_ : M) (_ : Fin r → Idx) => (0 : Real)) z k) := by
    funext z k; ring
  rw [h, iterCovComp_smul hu frame chr 0 _ hframe hchr (fun _ => contMDiffOn_const) a y hy n,
    zero_mul]


omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_finsetSum {ι : Type*} {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (t : Finset ι) (f : ι → M → (Fin r → Idx) → Real)
    (hf : ∀ i ∈ t, ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f i y m) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun z k => ∑ i ∈ t, f i z k) a y n =
        ∑ i ∈ t, iterCovComp (I := I) frame chr (f i) a y n := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro y hy n
    simpa using iterCovComp_zero_field hu frame chr hframe hchr a y hy n
  | insert b t hb ih =>
    intro y hy n
    have hrw : (fun z (k : Fin r → Idx) => ∑ i ∈ insert b t, f i z k) =
        fun z k => f b z k + ∑ i ∈ t, f i z k := by
      funext z k; rw [Finset.sum_insert hb]
    rw [hrw,
      iterCovComp_add hu frame chr (f b) (fun z k => ∑ i ∈ t, f i z k) hframe hchr
        (hf b (Finset.mem_insert_self b t))
        (fun m => contMDiffOn_finsetSum' t _
          (fun i hi => hf i (Finset.mem_insert_of_mem hi) m)) a y hy n,
      ih (fun i hi m => hf i (Finset.mem_insert_of_mem hi) m) y hy n,
      Finset.sum_insert hb]


omit [DecidableEq Idx] in
private theorem compL2_finsetSum_le {ι : Type*} {r : ℕ} (t : Finset ι)
    (f : ι → (Fin r → Idx) → Real) :
    compL2 (fun n : Fin r → Idx => ∑ i ∈ t, f i n) ≤ ∑ i ∈ t, compL2 (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : compL2 (fun _ : Fin r → Idx => (0 : Real)) = 0 := by
      simp [compL2, compL2Sq]
    exact le_of_eq h0
  | insert b t hb ih =>
    have hrw : (fun n : Fin r → Idx => ∑ i ∈ insert b t, f i n) =
        fun n => f b n + ∑ i ∈ t, f i n := by
      funext n; rw [Finset.sum_insert hb]
    rw [hrw, Finset.sum_insert hb]
    exact le_trans (compL2_add_le _ _) (by linarith [ih])



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem compL2_iterCov_chrCorr_le {r' : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (D : M → Idx → Idx → Idx → Real)
    (hD : ∀ d b p : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => D y d b p) u)
    (X : M → (Fin (r' + 1) → Idx) → Real)
    (hX : ∀ k : Fin (r' + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => X y k) u)
    (s : Fin (r' + 1)) (k : ℕ) {x : M} (hx : x ∈ u) :
    compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) ≤
      ∑ c ∈ Finset.range (k + 1), (k.choose c : Real) *
        compL2 (iterCovCompU (I := I) frame chrH
          (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
        compL2 (iterCovComp (I := I) frame chrH X (k - c) x) := by
  have h1 : compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)
      = compL2 (iterCovComp (I := I) frame chrH
          (fun z (w : Fin (2 + r') → Idx) => contrTail
            (fun v : Fin (2 + 1) → Idx => D z (v 0) (v 1) (v 2))
            (fun w' : Fin (r' + 1) → Idx => X z (fun j => w' (slotRotEquiv s j))) w) k x) := by
    rw [chrCorrField_eq_contrTail D X s]
    exact compL2_iterCovComp_compReindex (corrSlotEquiv s) frame chrH _ k x
  have hA : ∀ v : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => D y (v 0) (v 1) (v 2)) u := fun v => hD _ _ _
  have hB : ∀ w : Fin (r' + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => X y (fun j => w (slotRotEquiv s j))) u := fun w => hX _
  have hP := compL2_iterCovComp_contrTail_le hu frame chrH hframe hchrH k
    (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2))
    (fun y (w : Fin (r' + 1) → Idx) => X y (fun j => w (slotRotEquiv s j))) hA hB hx
  refine le_trans (le_of_eq h1) (le_trans hP (le_of_eq ?_))
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [compL2_iterCovComp_compReindex (slotRotEquiv s) frame chrH X (k - c) x]


omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_sub {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (f₁ f₂ : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hf₁ : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f₁ y m) u)
    (hf₂ : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f₂ y m) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun z k => f₁ z k - f₂ z k) a y n =
        iterCovComp (I := I) frame chr f₁ a y n -
          iterCovComp (I := I) frame chr f₂ a y n := by
  intro y hy n
  have h1 : (fun z (k : Fin r → Idx) => f₁ z k - f₂ z k) =
      fun z k => f₁ z k + (-1 : Real) * f₂ z k := by funext z k; ring
  rw [h1,
    iterCovComp_add hu frame chr f₁ (fun z k => (-1 : Real) * f₂ z k) hframe hchr hf₁
      (fun m => contMDiffOn_const.mul (hf₂ m)) a y hy n,
    iterCovComp_smul hu frame chr (-1) f₂ hframe hchr hf₂ a y hy n]
  ring








omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem mixed_oneStep_le {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrG chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (X : M → (Fin r → Idx) → Real)
    (hX : ∀ k : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => X y k) u)
    (B : ℕ → Real) (hB : ∀ i : ℕ, 0 ≤ B i) (eps : Real) (heps0 : 0 ≤ eps)
    (k : ℕ)
    (hDbound : ∀ c : ℕ, c ≤ k → ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c * eps)
    {x : M} (hx : x ∈ u) :
    compL2 (iterCovComp (I := I) frame chrH
        (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) ≤
      compL2 (iterCovComp (I := I) frame chrH X (k + 1) x) +
        eps * oneStepConst B k r *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH X j x) := by
  classical
  set D : M → Idx → Idx → Idx → Real := fun z d b p => chrG z d b p - chrH z d b p with hDdef
  have hDsm : ∀ d b p : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => D y d b p) u :=
    fun d b p => (hchrG d b p).sub (hchrH d b p)

  have hsplit : (fun y => iterCovComp (I := I) frame chrG X 1 y) =
      fun z (n : Fin (r + 1) → Idx) =>
        iterCovComp (I := I) frame chrH X 1 z n -
          ∑ s : Fin r, chrCorrField D X s z n := by
    funext z n
    exact iterCov_one_chr_change frame chrG chrH X z n
  have hHstep_sm : ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chrH X 1 y m) u :=
    fun m => iterCovComp_contMDiffOn hu frame chrH X hframe hchrH hX 1 m
  have hcorr_sm : ∀ s : Fin r, ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrCorrField D X s y m) u :=
    fun s m => contMDiffOn_chrCorrField D hDsm X hX s m
  have hcorrSum_sm : ∀ m : Fin (r + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ s : Fin r, chrCorrField D X s y m) u :=
    fun m => contMDiffOn_finsetSum' Finset.univ _ (fun s _ => hcorr_sm s m)

  have harr : iterCovComp (I := I) frame chrH
      (fun y => iterCovComp (I := I) frame chrG X 1 y) k x =
      fun n => iterCovComp (I := I) frame chrH
          (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x n -
        ∑ s : Fin r, iterCovComp (I := I) frame chrH (chrCorrField D X s) k x n := by
    funext n
    rw [hsplit,
      iterCovComp_sub hu frame chrH
        (fun z m => iterCovComp (I := I) frame chrH X 1 z m)
        (fun z m => ∑ s : Fin r, chrCorrField D X s z m)
        hframe hchrH hHstep_sm hcorrSum_sm k x hx n,
      iterCovComp_finsetSum hu frame chrH hframe hchrH Finset.univ
        (fun s => chrCorrField D X s) (fun s _ m => hcorr_sm s m) k x hx n]

  have htri : compL2 (iterCovComp (I := I) frame chrH
      (fun y => iterCovComp (I := I) frame chrG X 1 y) k x) ≤
      compL2 (iterCovComp (I := I) frame chrH
        (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) +
      ∑ s : Fin r, compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) := by
    rw [harr]
    refine le_trans (compL2_sub_le _ _) ?_
    have hsum := compL2_finsetSum_le (Finset.univ : Finset (Fin r))
      (fun s => iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)
    linarith

  have hshift : compL2 (iterCovComp (I := I) frame chrH
      (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) =
      compL2 (iterCovComp (I := I) frame chrH X (k + 1) x) :=
    (compL2_iterCovComp_shift frame chrH X k x).symm

  have hXsum0 : (0 : Real) ≤ ∑ j ∈ Finset.range (k + 1),
      compL2 (iterCovComp (I := I) frame chrH X j x) :=
    Finset.sum_nonneg fun j _ => compL2_nonneg _
  have hcorrBound : (∑ s : Fin r,
      compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)) ≤
      eps * oneStepConst B k r *
        ∑ j ∈ Finset.range (k + 1),
          compL2 (iterCovComp (I := I) frame chrH X j x) := by
    cases r with
    | zero =>
      rw [show (∑ s : Fin 0,
          compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x)) = 0 from
        Finset.sum_of_isEmpty _]
      have h0 : oneStepConst B k 0 = 0 := by
        rw [oneStepConst]
        norm_num
      rw [h0, mul_zero, zero_mul]
    | succ r' =>

      have hslot : ∀ s : Fin (r' + 1),
          compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) ≤
            eps * (∑ c ∈ Finset.range (k + 1), (k.choose c : Real) * B c) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
        intro s
        refine le_trans (compL2_iterCov_chrCorr_le hu frame chrH hframe hchrH D hDsm X hX
          s k hx) ?_
        have hterm : ∀ c ∈ Finset.range (k + 1),
            (k.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chrH
                (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
              compL2 (iterCovComp (I := I) frame chrH X (k - c) x) ≤
            (k.choose c : Real) * (B c * eps) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
          intro c hc
          have hc' := Finset.mem_range.mp hc
          have hDc : compL2 (iterCovCompU (I := I) frame chrH
              (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) ≤ B c * eps :=
            hDbound c (by omega) x hx
          have hXc : compL2 (iterCovComp (I := I) frame chrH X (k - c) x) ≤
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) :=
            Finset.single_le_sum
              (f := fun j => compL2 (iterCovComp (I := I) frame chrH X j x))
              (fun j _ => compL2_nonneg _) (Finset.mem_range.mpr (by omega))
          calc (k.choose c : Real) *
                compL2 (iterCovCompU (I := I) frame chrH
                  (fun y (v : Fin (2 + 1) → Idx) => D y (v 0) (v 1) (v 2)) c x) *
                compL2 (iterCovComp (I := I) frame chrH X (k - c) x)
              ≤ (k.choose c : Real) * (B c * eps) *
                  compL2 (iterCovComp (I := I) frame chrH X (k - c) x) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDc (Nat.cast_nonneg _)) (compL2_nonneg _)
            _ ≤ (k.choose c : Real) * (B c * eps) *
                  ∑ j ∈ Finset.range (k + 1),
                    compL2 (iterCovComp (I := I) frame chrH X j x) :=
                mul_le_mul_of_nonneg_left hXc
                  (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hB c) heps0))
        refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      calc (∑ s : Fin (r' + 1),
            compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x))
          ≤ ∑ _s : Fin (r' + 1),
              eps * (∑ c ∈ Finset.range (k + 1), (k.choose c : Real) * B c) *
                ∑ j ∈ Finset.range (k + 1),
                  compL2 (iterCovComp (I := I) frame chrH X j x) :=
            Finset.sum_le_sum fun s _ => hslot s
        _ = eps * oneStepConst B k (r' + 1) *
              ∑ j ∈ Finset.range (k + 1),
                compL2 (iterCovComp (I := I) frame chrH X j x) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, oneStepConst]
            push_cast
            ring
  calc compL2 (iterCovComp (I := I) frame chrH
        (fun y => iterCovComp (I := I) frame chrG X 1 y) k x)
      ≤ compL2 (iterCovComp (I := I) frame chrH
          (fun z m => iterCovComp (I := I) frame chrH X 1 z m) k x) +
        ∑ s : Fin r, compL2 (iterCovComp (I := I) frame chrH (chrCorrField D X s) k x) :=
        htri
    _ ≤ compL2 (iterCovComp (I := I) frame chrH X (k + 1) x) +
        eps * oneStepConst B k r *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH X j x) := by
        rw [hshift]
        linarith [hcorrBound]










omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem lemma45_component {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrG chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (T : M → (Fin r₀ → Idx) → Real)
    (hT : ∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u)
    (B : ℕ → Real) (hB : ∀ n : ℕ, 0 ≤ B n)
    (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hDbound : ∀ c : ℕ, ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c * eps)
    {x : M} (hx : x ∈ u) :
    ∀ p i ρ : ℕ, 0 < ρ → ρ ≤ p →
      compL2 (iterCovComp (I := I) frame chrG T (i + ρ) x) ≤
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T i) ρ x) +
        eps * lemma45Const B p (r₀ + i) *
          ∑ j ∈ Finset.range ρ,
            compL2 (iterCovComp (I := I) frame chrH
              (iterCovComp (I := I) frame chrG T i) j x) := by
  have hX_sm : ∀ i : ℕ, ∀ k : Fin (r₀ + i) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chrG T i y k) u :=
    fun i => iterCovComp_contMDiffOn hu frame chrG T hframe hchrG hT i
  have hOne : ∀ i' k : ℕ,
      compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T (i' + 1)) k x) ≤
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T i') (k + 1) x) +
        eps * oneStepConst B k (r₀ + i') *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH
              (iterCovComp (I := I) frame chrG T i') j x) := by
    intro i' k
    exact mixed_oneStep_le hu frame chrG chrH hframe hchrG hchrH
      (iterCovComp (I := I) frame chrG T i') (hX_sm i') B hB eps heps0 k
      (fun c _ z hz => hDbound c z hz) hx
  exact lemma45Double (eps := eps) (B := B) (s := r₀) heps0 heps1 hB
    (fun i' k => compL2 (iterCovComp (I := I) frame chrH
      (iterCovComp (I := I) frame chrG T i') k x))
    (fun i' k => compL2_nonneg _) hOne



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem lemma45_component₀ {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrG chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (T : M → (Fin r₀ → Idx) → Real)
    (hT : ∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u)
    (B : ℕ → Real) (hB : ∀ n : ℕ, 0 ≤ B n)
    (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hDbound : ∀ c : ℕ, ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c * eps)
    {x : M} (hx : x ∈ u) (p ρ : ℕ) (hρ0 : 0 < ρ) (hρp : ρ ≤ p) :
    compL2 (iterCovComp (I := I) frame chrG T ρ x) ≤
      compL2 (iterCovComp (I := I) frame chrH T ρ x) +
      eps * lemma45Const B p r₀ *
        ∑ j ∈ Finset.range ρ,
          compL2 (iterCovComp (I := I) frame chrH T j x) := by
  have h := lemma45_component hu frame chrG chrH hframe hchrG hchrH T hT B hB eps heps0 heps1
    hDbound hx p 0 ρ hρ0 hρp
  rw [zero_add] at h
  exact h







omit [I.Boundaryless] [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem hkoszul_of_leviCivita {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (y : M) (hy : y ∈ u) :
    contrTail
      (chrDiffField
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
          frame hframe z)
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe z) y)
      (frameComp0S (I := I) (metricTensorField (I := I) g) frame y) =
    fun idx : Fin 3 → Idx =>
      (1 / 2 : Real) * iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z)
          (frameComp0S (I := I) (metricTensorField (I := I) g) frame) 1 y
          (fun j => idx (Equiv.refl (Fin 3) j)) +
      ((1 / 2 : Real) * iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z)
          (frameComp0S (I := I) (metricTensorField (I := I) g) frame) 1 y
          (fun j => idx (Equiv.swap (0 : Fin 3) 1 j)) +
        (-(1 / 2) : Real) * iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z)
          (frameComp0S (I := I) (metricTensorField (I := I) g) frame) 1 y
          (fun j => idx ((finRotate 3).symm j))) := by
  classical
  set covG := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g
    with hcovG
  set covH := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
    with hcovH
  funext idx

  obtain ⟨Xa, hXa⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) y (frame (idx 0) y)
  obtain ⟨Xb, hXb⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) y (frame (idx 1) y)
  obtain ⟨Xe, hXe⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) y (frame (idx 2) y)

  have hexp : ∀ v : TangentSpace I y, (∑ c : Idx, hframe.coeff c y v • frame c y) = v := by
    intro v
    have h := Module.Basis.sum_repr (hframe.toBasisAt hy) v
    calc (∑ c : Idx, hframe.coeff c y v • frame c y)
        = ∑ c : Idx, (hframe.toBasisAt hy).repr v c • (hframe.toBasisAt hy) c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [IsLocalFrameOn.toBasisAt_coe hframe hy]
          congr 1
          simp [IsLocalFrameOn.coeff, hy]
      _ = v := h

  have hLHS : contrTail
      (chrDiffField
        (fun z => christoffelSymbolInFrame covG frame hframe z)
        (fun z => christoffelSymbolInFrame covH frame hframe z) y)
      (frameComp0S (I := I) (metricTensorField (I := I) g) frame y) idx =
      g.inner y (frame (idx 2) y)
        (((CovariantDerivative.difference covG covH y) (frame (idx 1) y)) (frame (idx 0) y)) := by
    rw [contrTail_apply]
    have hframe_b_md := ((hframe.contMDiffOn (idx 1)).contMDiffAt
      (hu.mem_nhds hy)).mdifferentiableAt (by simp)
    have hdiff := IsCovariantDerivativeOn.difference_apply
      (hcov := covG.isCovariantDerivativeOnUniv) (hcov' := covH.isCovariantDerivativeOnUniv)
      (σ := frame (idx 1)) (x := y) (hx := by trivial) hframe_b_md
    calc (∑ c : Idx,
          chrDiffField
            (fun z => christoffelSymbolInFrame covG frame hframe z)
            (fun z => christoffelSymbolInFrame covH frame hframe z) y
            (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) c) *
          frameComp0S (I := I) (metricTensorField (I := I) g) frame y
            (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) c))
        = ∑ c : Idx,
            hframe.coeff c y
              (((CovariantDerivative.difference covG covH y) (frame (idx 1) y))
                (frame (idx 0) y)) *
            g.inner y (frame (idx 2) y) (frame c y) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          have hA0 : (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) c
              : Fin (2 + 1) → Idx) 0 = idx 0 := by
            rw [show (0 : Fin (2 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
            rfl
          have hA1 : (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) c
              : Fin (2 + 1) → Idx) 1 = idx 1 := by
            rw [show (1 : Fin (2 + 1)) = Fin.castSucc 1 from rfl, Fin.snoc_castSucc]
            rfl
          have hA2 : (Fin.snoc (fun i : Fin 2 => idx (Fin.castAdd 1 i)) c
              : Fin (2 + 1) → Idx) 2 = c := by
            rw [show (2 : Fin (2 + 1)) = Fin.last 2 from rfl, Fin.snoc_last]
          have hB0 : (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) c
              : Fin (1 + 1) → Idx) 0 = idx 2 := by
            rw [show (0 : Fin (1 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
            rfl
          have hB1 : (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) c
              : Fin (1 + 1) → Idx) 1 = c := by
            rw [show (1 : Fin (1 + 1)) = Fin.last 1 from rfl, Fin.snoc_last]
          rw [chrDiffField, hA0, hA1, hA2]
          rw [show frameComp0S (I := I) (metricTensorField (I := I) g) frame y
              (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) c) =
              g.inner y (frame (idx 2) y) (frame c y) from by
            rw [frameComp0S_apply, metricTensorField_apply]
            rw [show (Fin.snoc (fun j : Fin 1 => idx (Fin.natAdd 2 j)) c : Fin (1 + 1) → Idx) =
                fun q => if q = 0 then idx 2 else c from by
              funext q
              by_cases hq : q = 0
              · rw [hq, if_pos rfl, hB0]
              · rw [if_neg hq, show q = 1 from Fin.eq_one_of_ne_zero q hq, hB1]]
            simp]
          congr 1

          show christoffelSymbolInFrame covG frame hframe y (idx 0) (idx 1) c -
              christoffelSymbolInFrame covH frame hframe y (idx 0) (idx 1) c = _
          rw [show christoffelSymbolInFrame covG frame hframe y (idx 0) (idx 1) c =
              hframe.coeff c y ((covG (frame (idx 1)) y) (frame (idx 0) y)) from rfl,
            show christoffelSymbolInFrame covH frame hframe y (idx 0) (idx 1) c =
              hframe.coeff c y ((covH (frame (idx 1)) y) (frame (idx 0) y)) from rfl]
          rw [← LinearMap.map_sub]
          congr 1
          have happ := congrArg
            (fun L : TangentSpace I y →L[Real] TangentSpace I y => L (frame (idx 0) y)) hdiff
          simpa using happ.symm
      _ = g.inner y (frame (idx 2) y)
            (∑ c : Idx, hframe.coeff c y
              (((CovariantDerivative.difference covG covH y) (frame (idx 1) y))
                (frame (idx 0) y)) • frame c y) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul]
          simp [smul_eq_mul, mul_comm]
      _ = g.inner y (frame (idx 2) y)
            (((CovariantDerivative.difference covG covH y) (frame (idx 1) y))
              (frame (idx 0) y)) := by
          rw [hexp]

  have htower : ∀ (P : Equiv.Perm (Fin 3))
      (S : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)),
      S y = frame (idx (P 0)) y →
      iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame covH frame hframe z)
          (frameComp0S (I := I) (metricTensorField (I := I) g) frame) 1 y
          (fun j => idx (P j)) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 covH S
          (metricTensorField (I := I) g) y
          (fun q : Fin 2 => if q = 0 then frame (idx (P 1)) y else frame (idx (P 2)) y) := by
    intro P S hS
    rw [iterCovComp_eq_iterCov gRef (metricTensorField (I := I) g) frame hframe hu 1 hy
      (fun j => idx (P j))]
    rw [show iterCov (I := I) gRef 2 (metricTensorField (I := I) g) 1 =
        covStep (I := I) gRef 2 (metricTensorField (I := I) g) from rfl]
    rw [covStep_apply]
    rw [frameTuple_eq_cons, ← hS]
    rw [totalNabla0SFun_apply_section (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 covH S (metricTensorField (I := I) g) y _]
    congr 1
    funext q
    refine Fin.cases ?_ (fun q' => ?_) q
    · rw [if_pos rfl]
      rfl
    · rw [if_neg (by simp [Fin.ext_iff])]
      have hq' : q' = 0 := Subsingleton.elim q' 0
      rw [hq']
      rfl

  have hK := Tensor0SBundle.koszul_difference (I := I) covG covH g
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
      (I := I) g)
    ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree
      (I := I) g) y)
    ((DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_isTorsionFree
      (I := I) gRef) y)
    Xa Xb Xe
  rw [hXa, hXb, hXe] at hK
  have h1 := htower (Equiv.refl (Fin 3)) Xa
    (by rw [hXa, show ((Equiv.refl (Fin 3)) (0 : Fin 3)) = 0 from rfl])
  have h2 := htower (Equiv.swap (0 : Fin 3) 1) Xb
    (by rw [hXb, show ((Equiv.swap (0 : Fin 3) 1) (0 : Fin 3)) = 1 from by decide])
  have h3 := htower ((finRotate 3).symm) Xe
    (by rw [hXe, show (((finRotate 3).symm) (0 : Fin 3)) = 2 from by decide])

  rw [show ((Equiv.refl (Fin 3)) (1 : Fin 3)) = 1 from rfl,
    show ((Equiv.refl (Fin 3)) (2 : Fin 3)) = 2 from rfl] at h1
  rw [show ((Equiv.swap (0 : Fin 3) 1) (1 : Fin 3)) = 0 from by decide,
    show ((Equiv.swap (0 : Fin 3) 1) (2 : Fin 3)) = 2 from by decide] at h2
  rw [show (((finRotate 3).symm) (1 : Fin 3)) = 0 from by decide,
    show (((finRotate 3).symm) (2 : Fin 3)) = 1 from by decide] at h3
  have hsymmg := g.symm y (frame (idx 2) y)
    (((CovariantDerivative.difference covG covH y) (frame (idx 1) y)) (frame (idx 0) y))
  rw [hLHS, h1, h2, h3]
  linarith [hK, hsymmg]










omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1_koszul_bound {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (1 + 1) → Idx) → Real)
    (hg : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (A : M → (Fin (2 + 1) → Idx) → Real)
    (hA : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (c₁ c₂ c₃ : Real) (P₁ P₂ P₃ : Fin 3 ≃ Fin 3)
    (hkoszul : ∀ y ∈ u, contrTail (A y) (g y) =
      fun idx : Fin 3 → Idx =>
        c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
        (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
          c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j))))
    (C0 L eps : Real) (hL : 0 ≤ L) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (m : ℕ)
    (hK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m + 1 →
      compL2 (iterCovComp (I := I) frame chr g j x) ≤ L * eps) :
    ∀ x ∈ u, compL2 (iterCovCompU (I := I) frame chr A m x) ≤
      claim1MulConst C0 (|c₁| + |c₂| + |c₃|) L m * eps := by
  refine claim1_eps_mul_bound hu frame chr hframe hchr g hg Ginv A hA hinv C0
    (|c₁| + |c₂| + |c₃|) L eps hL heps0 heps1 hGinv m hK ?_
  intro x hx m' _
  have hterm : ∀ (ci : Real) (Pi : Fin 3 ≃ Fin 3),
      compL2 (iterCovComp (I := I) frame chr
        (fun z (k : Fin 3 → Idx) => ci * iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
        m' x) = |ci| * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x) := by
    intro ci Pi
    rw [show iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => ci * iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
          m' x =
        fun n => ci * iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
          m' x n from
        funext (iterCovComp_smul hu frame chr ci
          (fun z (k : Fin 3 → Idx) => iterCovComp (I := I) frame chr g 1 z (fun j => k (Pi j)))
          hframe hchr
          (fun k => iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1 (fun j => k (Pi j)))
          m' x hx),
      compL2_smul,
      compL2_iterCovComp_compReindex Pi frame chr (iterCovComp (I := I) frame chr g 1) m' x,
      ← compL2_iterCovComp_shift frame chr g m' x]
  have hFsm : ∀ (ci : Real) (Pi : Fin 3 ≃ Fin 3), ∀ k : Fin 3 → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => ci * iterCovComp (I := I) frame chr g 1 y (fun j => k (Pi j))) u :=
    fun ci Pi k =>
      contMDiffOn_const.mul
        (iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1 (fun j => k (Pi j)))
  rw [iterCovComp_congr_on hu frame chr hkoszul m' x hx,
    show iterCovComp (I := I) frame chr
        (fun y (idx : Fin 3 → Idx) =>
          c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
          (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
            c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j)))) m' x =
      fun n => iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₁ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₁ j)))
          m' x n +
        iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) =>
            c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
            c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m' x n from
      funext (iterCovComp_add hu frame chr _ _ hframe hchr (hFsm c₁ P₁)
        (fun k => (hFsm c₂ P₂ k).add (hFsm c₃ P₃ k)) m' x hx)]
  refine le_trans (compL2_add_le _ _) ?_
  rw [hterm c₁ P₁,
    show iterCovComp (I := I) frame chr
        (fun z (k : Fin 3 → Idx) =>
          c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)) +
          c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m' x =
      fun n => iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j)))
          m' x n +
        iterCovComp (I := I) frame chr
          (fun z (k : Fin 3 → Idx) => c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j)))
          m' x n from
      funext (iterCovComp_add hu frame chr _ _ hframe hchr (hFsm c₂ P₂) (hFsm c₃ P₃) m' x hx)]
  have h23 := compL2_add_le
    (iterCovComp (I := I) frame chr
      (fun z (k : Fin 3 → Idx) => c₂ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₂ j))) m' x)
    (iterCovComp (I := I) frame chr
      (fun z (k : Fin 3 → Idx) => c₃ * iterCovComp (I := I) frame chr g 1 z (fun j => k (P₃ j))) m' x)
  rw [hterm c₂ P₂, hterm c₃ P₃] at h23
  have hG0 : (0 : Real) ≤ compL2 (iterCovComp (I := I) frame chr g (m' + 1) x) := compL2_nonneg _
  nlinarith [abs_nonneg c₁, abs_nonneg c₂, abs_nonneg c₃, hG0, h23]


omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1_koszul_mul {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (1 + 1) → Idx) → Real)
    (hg : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (A : M → (Fin (2 + 1) → Idx) → Real)
    (hA : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (c₁ c₂ c₃ : Real) (P₁ P₂ P₃ : Fin 3 ≃ Fin 3)
    (hkoszul : ∀ y ∈ u, contrTail (A y) (g y) =
      fun idx : Fin 3 → Idx =>
        c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
        (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
          c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j))))
    (C0 L eps : Real) (hL : 0 ≤ L) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (m : ℕ)
    (hK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m + 1 →
      compL2 (iterCovComp (I := I) frame chr g j x) ≤ L * eps) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ u,
      compL2 (iterCovCompU (I := I) frame chr A m x) ≤ C * eps := by
  refine ⟨claim1MulConst C0 (|c₁| + |c₂| + |c₃|) L m,
    claim1MulConst_nonneg hL m, ?_⟩
  exact claim1_koszul_bound hu frame chr hframe hchr g hg Ginv A hA hinv
    c₁ c₂ c₃ P₁ P₂ P₃ hkoszul C0 L eps hL heps0 heps1 hGinv m hK



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1_eps_koszul {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (1 + 1) → Idx) → Real)
    (hg : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (A : M → (Fin (2 + 1) → Idx) → Real)
    (hA : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (c₁ c₂ c₃ : Real) (P₁ P₂ P₃ : Fin 3 ≃ Fin 3)
    (hkoszul : ∀ y ∈ u, contrTail (A y) (g y) =
      fun idx : Fin 3 → Idx =>
        c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
        (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
          c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j))))
    (C0 eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (m : ℕ)
    (hK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m + 1 →
      compL2 (iterCovComp (I := I) frame chr g j x) ≤ eps) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ u,
      compL2 (iterCovCompU (I := I) frame chr A m x) ≤ C * eps := by
  refine claim1_koszul_mul hu frame chr hframe hchr g hg Ginv A hA hinv
    c₁ c₂ c₃ P₁ P₂ P₃ hkoszul C0 1 eps zero_le_one heps0 heps1 hGinv m ?_
  simpa only [one_mul] using hK




omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem lemma45_component_bdd {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chrG chrH : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrG y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chrH y d i j) u)
    (T : M → (Fin r₀ → Idx) → Real)
    (hT : ∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u)
    (B : ℕ → Real) (hB : ∀ n : ℕ, 0 ≤ B n)
    (eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (P : ℕ)
    (hDbound : ∀ c : ℕ, c < P → ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c * eps)
    {x : M} (hx : x ∈ u) :
    ∀ p i ρ : ℕ, 0 < ρ → ρ ≤ p → i + p ≤ P →
      compL2 (iterCovComp (I := I) frame chrG T (i + ρ) x) ≤
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T i) ρ x) +
        eps * lemma45Const B p (r₀ + i) *
          ∑ j ∈ Finset.range ρ,
            compL2 (iterCovComp (I := I) frame chrH
              (iterCovComp (I := I) frame chrG T i) j x) := by
  have hX_sm : ∀ i : ℕ, ∀ k : Fin (r₀ + i) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chrG T i y k) u :=
    fun i => iterCovComp_contMDiffOn hu frame chrG T hframe hchrG hT i
  have hOne : ∀ i' k : ℕ, i' + k < P →
      compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T (i' + 1)) k x) ≤
        compL2 (iterCovComp (I := I) frame chrH
          (iterCovComp (I := I) frame chrG T i') (k + 1) x) +
        eps * oneStepConst B k (r₀ + i') *
          ∑ j ∈ Finset.range (k + 1),
            compL2 (iterCovComp (I := I) frame chrH
              (iterCovComp (I := I) frame chrG T i') j x) := by
    intro i' k hik
    exact mixed_oneStep_le hu frame chrG chrH hframe hchrG hchrH
      (iterCovComp (I := I) frame chrG T i') (hX_sm i') B hB eps heps0 k
      (fun c hck z hz => hDbound c (by omega) z hz) hx
  exact lemma45DoubleBdd (eps := eps) (B := B) (s := r₀) heps0 heps1 hB P
    (fun i' k => compL2 (iterCovComp (I := I) frame chrH
      (iterCovComp (I := I) frame chrG T i') k x))
    (fun i' k => compL2_nonneg _) hOne









omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lemma45_F3_bound {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hframeS : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
        frame hframe y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y d i j) u)
    (hgsm : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g) frame y k) u)
    (T : M → (Fin r₀ → Idx) → Real)
    (hT : ∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, frameComp0S (I := I) (metricTensorField (I := I) g) frame x
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 L eps : Real) (hL : 0 ≤ L) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (p : ℕ)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      compL2 (iterCovComp (I := I) frame
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe z)
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j x) ≤ L * eps) :
    ∀ x ∈ u, ∀ ρ : ℕ, 0 < ρ → ρ ≤ p →
      compL2 (iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
            frame hframe z) T ρ x) ≤
        compL2 (iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z) T ρ x) +
        eps * lemma45Const
          (fun c => claim1MulConst C0 (|(1 / 2 : Real)| + |(1 / 2 : Real)| + |-(1 / 2 : Real)|) L c)
          p r₀ *
          ∑ j ∈ Finset.range ρ,
            compL2 (iterCovComp (I := I) frame
              (fun z => christoffelSymbolInFrame
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                frame hframe z) T j x) := by
  classical
  set chrG : M → Idx → Idx → Idx → Real := fun z => christoffelSymbolInFrame
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
    frame hframe z with hchrGdef
  set chrH : M → Idx → Idx → Idx → Real := fun z => christoffelSymbolInFrame
    (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
    frame hframe z with hchrHdef
  have hDsm : ∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => chrDiffField chrG chrH y k) u :=
    fun k => (hchrG _ _ _).sub (hchrH _ _ _)
  let B : ℕ → Real := fun c =>
    claim1MulConst C0 (|(1 / 2 : Real)| + |(1 / 2 : Real)| + |-(1 / 2 : Real)|) L c
  have hB0 : ∀ c, 0 ≤ B c := fun c => claim1MulConst_nonneg hL c
  have hBb : ∀ c, c < p → ∀ z ∈ u,
      compL2 (iterCovCompU (I := I) frame chrH (chrDiffField chrG chrH) c z) ≤ B c * eps := by
    intro c hc
    exact claim1_koszul_bound hu frame chrH hframeS hchrH
      (frameComp0S (I := I) (metricTensorField (I := I) g) frame) hgsm Ginv
      (chrDiffField chrG chrH) hDsm hinv
      (1 / 2) (1 / 2) (-(1 / 2))
      (Equiv.refl (Fin 3)) (Equiv.swap (0 : Fin 3) 1) ((finRotate 3).symm)
      (fun y hy => hkoszul_of_leviCivita hu g gRef frame hframe y hy)
      C0 L eps hL heps0 heps1 hGinv c
      (fun z hz j h1 h2 => hgK z hz j h1 (by omega))
  intro x hx ρ hρ0 hρp
  have h := lemma45_component_bdd hu frame chrG chrH hframeS hchrG hchrH T hT B hB0
    eps heps0 heps1 p (fun c hc z hz => hBb c hc z hz) hx p 0 ρ hρ0 hρp (by omega)
  rw [zero_add] at h
  simpa only [B] using h


omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lemma45_F3_mul {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hframeS : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
        frame hframe y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y d i j) u)
    (hgsm : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g) frame y k) u)
    (T : M → (Fin r₀ → Idx) → Real)
    (hT : ∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, frameComp0S (I := I) (metricTensorField (I := I) g) frame x
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 L eps : Real) (hL : 0 ≤ L) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (p : ℕ)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      compL2 (iterCovComp (I := I) frame
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe z)
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j x) ≤ L * eps) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x ∈ u, ∀ ρ : ℕ, 0 < ρ → ρ ≤ p →
      compL2 (iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
            frame hframe z) T ρ x) ≤
        compL2 (iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z) T ρ x) +
        eps * C *
          ∑ j ∈ Finset.range ρ,
            compL2 (iterCovComp (I := I) frame
              (fun z => christoffelSymbolInFrame
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                frame hframe z) T j x) := by
  let B : ℕ → Real := fun c =>
    claim1MulConst C0 (|(1 / 2 : Real)| + |(1 / 2 : Real)| + |-(1 / 2 : Real)|) L c
  refine ⟨lemma45Const B p r₀,
    lemma45Const_nonneg (fun c => claim1MulConst_nonneg hL c) p r₀, ?_⟩
  simpa only [B] using lemma45_F3_bound hu g gRef frame hframe hframeS hchrG hchrH
    hgsm T hT Ginv hinv C0 L eps hL heps0 heps1 hGinv p hgK



omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lemma45_F3 {r₀ : ℕ} {u : Set M} (hu : IsOpen u)
    (g gRef : SmoothRiemannianMetric I M)
    (frame : Idx → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hframeS : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchrG : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
        frame hframe y d i j) u)
    (hchrH : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => christoffelSymbolInFrame
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
        frame hframe y d i j) u)
    (hgsm : ∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun y => frameComp0S (I := I) (metricTensorField (I := I) g) frame y k) u)
    (T : M → (Fin r₀ → Idx) → Real)
    (hT : ∀ k : Fin r₀ → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => T y k) u)
    (Ginv : M → (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ x ∈ u, ∀ c e : Idx,
      (∑ l : Idx, frameComp0S (I := I) (metricTensorField (I := I) g) frame x
          (Fin.snoc (fun _ : Fin 1 => l) c) *
        Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0)
    (C0 eps : Real) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hGinv : ∀ x ∈ u, compL2 (Ginv x) ≤ C0)
    (p : ℕ)
    (hgK : ∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
      compL2 (iterCovComp (I := I) frame
        (fun z => christoffelSymbolInFrame
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          frame hframe z)
        (frameComp0S (I := I) (metricTensorField (I := I) g) frame) j x) ≤ eps) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x ∈ u, ∀ ρ : ℕ, 0 < ρ → ρ ≤ p →
      compL2 (iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
            frame hframe z) T ρ x) ≤
        compL2 (iterCovComp (I := I) frame
          (fun z => christoffelSymbolInFrame
            (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
            frame hframe z) T ρ x) +
        eps * C *
          ∑ j ∈ Finset.range ρ,
            compL2 (iterCovComp (I := I) frame
              (fun z => christoffelSymbolInFrame
                (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
                frame hframe z) T j x) := by
  refine lemma45_F3_mul hu g gRef frame hframe hframeS hchrG hchrH hgsm T hT Ginv hinv
    C0 1 eps zero_le_one heps0 heps1 hGinv p ?_
  simpa only [one_mul] using hgK

end DifferentialGeometry.PDE.RicciFlow
