import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContr
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CovDerivStepCompContrNorm
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSectionsLocal
import DifferentialGeometry.Tensor.RSTensor.NablaDomDomCongr

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





def shiftEquivC (r : ℕ) : (m : ℕ) → Fin ((r + 1) + m) ≃ Fin (r + (m + 1))
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (shiftEquivC r m)






omit [DecidableEq Idx] in
theorem covDerivStepComp_compReindex {s s' : ℕ} (e : Fin s ≃ Fin s')
    (ext : (Fin s → Idx) → Idx → Real) (chr : Idx → Idx → Idx → Real)
    (A : (Fin s → Idx) → Real) (n : Fin (s' + 1) → Idx) :
    covDerivStepComp (fun m' d => ext (fun i => m' (e i)) d) chr
        (fun n' => A (fun i => n' (e i))) n =
      covDerivStepComp ext chr A (fun j => n (frontExtendEquiv e j)) := by
  classical
  have htail : Fin.tail (fun j => n (frontExtendEquiv e j)) = fun i => Fin.tail n (e i) := by
    funext i; simp only [Fin.tail, frontExtendEquiv_succ]
  unfold covDerivStepComp
  simp only [frontExtendEquiv_zero, htail]
  congr 1
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p _ => ?_
  have hupd : (fun i => Function.update (Fin.tail n) (e t) p (e i)) =
      Function.update (fun i => Fin.tail n (e i)) t p := by
    funext i
    by_cases h : i = t
    · subst h; simp only [Function.update_self]
    · rw [Function.update_of_ne (fun he => h (e.injective he)),
        Function.update_of_ne h]
  rw [hupd]








omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem iterCovComp_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) (m : ℕ) (x : M) :
    iterCovComp (I := I) frame chr base (m + 1) x =
      fun n : Fin (r + (m + 1)) → Idx =>
        iterCovComp (I := I) frame chr (fun y => iterCovComp (I := I) frame chr base 1 y) m x
          (fun j => n (shiftEquivC r m j)) := by
  induction m generalizing x with
  | zero =>
    funext n
    simp only [shiftEquivC, iterCovComp_zero, Equiv.refl_apply]
  | succ m ih =>
    funext n
    rw [iterCovComp_succ,
      show iterCovComp (I := I) frame chr base (m + 1) =
          (fun y (nn : Fin (r + (m + 1)) → Idx) =>
            iterCovComp (I := I) frame chr (fun z => iterCovComp (I := I) frame chr base 1 z) m y
              (fun j => nn (shiftEquivC r m j))) from funext ih,
      show frameExtData (I := I) frame
            (fun y (nn : Fin (r + (m + 1)) → Idx) =>
              iterCovComp (I := I) frame chr (fun z => iterCovComp (I := I) frame chr base 1 z) m y
                (fun j => nn (shiftEquivC r m j))) x =
          fun (m' : Fin (r + (m + 1)) → Idx) d =>
            frameExtData (I := I) frame
              (iterCovComp (I := I) frame chr
                (fun z => iterCovComp (I := I) frame chr base 1 z) m) x
              (fun i => m' (shiftEquivC r m i)) d from rfl,
      covDerivStepComp_compReindex (shiftEquivC r m), ← iterCovComp_succ]
    rfl




omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem compL2_iterCovComp_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real) (m : ℕ) (x : M) :
    compL2 (iterCovComp (I := I) frame chr base (m + 1) x) =
      compL2 (iterCovComp (I := I) frame chr
        (fun y => iterCovComp (I := I) frame chr base 1 y) m x) := by
  rw [iterCovComp_shift]
  exact compL2_comp_equiv
    (iterCovComp (I := I) frame chr (fun y => iterCovComp (I := I) frame chr base 1 y) m x)
    (shiftEquivC r m)


def frontExtendIterC {s s' : ℕ} (e : Fin s ≃ Fin s') :
    (m : ℕ) → Fin (s + m) ≃ Fin (s' + m)
  | 0 => e
  | (m + 1) => frontExtendEquiv (frontExtendIterC e m)




def rotEquiv (p q : ℕ) : Fin (p + (q + 1)) ≃ Fin (p + q + 1) :=
  (finCongr (by omega)).trans (Fin.cycleRange ⟨p, by omega⟩)



omit [Fintype Idx] [DecidableEq Idx] in
private theorem slotId1 {p q : ℕ} (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    (Fin.append (Fin.cons d aPart) bPart : Fin (p + 1 + q) → Idx) =
      fun j => (Fin.cons d (Fin.append aPart bPart) : Fin (p + q + 1) → Idx)
        (Fin.cast (show p + 1 + q = p + q + 1 by omega) j) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · rw [Fin.append_left]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [Fin.cons_zero]
      rw [show (Fin.cast (by omega) (Fin.castAdd q (0 : Fin (p + 1))) : Fin (p + q + 1)) = 0 by
        apply Fin.ext; simp, Fin.cons_zero]
    · rw [Fin.cons_succ]
      rw [show (Fin.cast (by omega) (Fin.castAdd q i'.succ) : Fin (p + q + 1)) =
          (Fin.castAdd q i').succ by apply Fin.ext; simp, Fin.cons_succ, Fin.append_left]
  · rw [Fin.append_right]
    rw [show (Fin.cast (by omega) (Fin.natAdd (p + 1) k) : Fin (p + q + 1)) =
        (Fin.natAdd p k).succ by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega, Fin.cons_succ, Fin.append_right]




omit [Fintype Idx] [DecidableEq Idx] in
private theorem slotId2 {p q : ℕ} (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    (Fin.append aPart (Fin.cons d bPart) : Fin (p + (q + 1)) → Idx) =
      fun i => (Fin.cons d (Fin.append aPart bPart) : Fin (p + q + 1) → Idx)
        (rotEquiv p q i) := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
  ·
    rw [Fin.append_left,
      show rotEquiv p q (Fin.castAdd (q + 1) i') = (Fin.castAdd q i').succ by
        apply Fin.ext
        simp only [rotEquiv, Equiv.trans_apply, Fin.val_succ, Fin.val_castAdd]
        rw [Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; simp)]
        simp,
      Fin.cons_succ, Fin.append_left]
  · refine Fin.cases ?_ (fun j => ?_) k
    ·
      rw [Fin.append_right, Fin.cons_zero,
        show rotEquiv p q (Fin.natAdd p (0 : Fin (q + 1))) = 0 by
          simp only [rotEquiv, Equiv.trans_apply]
          rw [Fin.cycleRange_of_eq (by apply Fin.ext; simp)],
        Fin.cons_zero]
    ·
      rw [Fin.append_right, Fin.cons_succ,
        show rotEquiv p q (Fin.natAdd p j.succ) = (Fin.natAdd p j).succ by
          simp only [rotEquiv, Equiv.trans_apply]
          rw [Fin.cycleRange_of_gt (by rw [Fin.lt_def]; simp)]
          apply Fin.ext
          simp only [finCongr_apply_coe, Fin.val_natAdd, Fin.val_succ]
          omega,
        Fin.cons_succ, Fin.append_right]



def extendLastEquiv {p p' : ℕ} (e₀ : Fin p ≃ Fin p') : Fin (p + 1) ≃ Fin (p' + 1) :=
  finSuccEquivLast.trans (e₀.optionCongr.trans finSuccEquivLast.symm)

@[simp] theorem extendLastEquiv_castSucc {p p' : ℕ} (e₀ : Fin p ≃ Fin p') (i : Fin p) :
    extendLastEquiv e₀ (Fin.castSucc i) = Fin.castSucc (e₀ i) := by
  simp [extendLastEquiv, finSuccEquivLast_castSucc]

@[simp] theorem extendLastEquiv_last {p p' : ℕ} (e₀ : Fin p ≃ Fin p') :
    extendLastEquiv e₀ (Fin.last p) = Fin.last p' := by
  simp [extendLastEquiv, finSuccEquivLast_last]

@[simp] theorem extendLastEquiv_refl {p : ℕ} :
    extendLastEquiv (Equiv.refl (Fin p)) = Equiv.refl (Fin (p + 1)) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [extendLastEquiv_last]; rfl
  · rw [extendLastEquiv_castSucc]; rfl


theorem extendLast_frontExtend_comm {p p' : ℕ} (e : Fin p ≃ Fin p') :
    frontExtendEquiv (extendLastEquiv e) = extendLastEquiv (frontExtendEquiv e) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [extendLastEquiv_last,
      show (Fin.last (p + 1) : Fin (p + 1 + 1)) = (Fin.last p).succ from (Fin.succ_last p).symm,
      frontExtendEquiv_succ, extendLastEquiv_last, Fin.succ_last]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · conv_lhs => rw [Fin.castSucc_zero, frontExtendEquiv_zero]
      rw [extendLastEquiv_castSucc, frontExtendEquiv_zero, Fin.castSucc_zero]
    · rw [extendLastEquiv_castSucc, frontExtendEquiv_succ,
        show (Fin.castSucc j'.succ : Fin (p + 1 + 1)) = (Fin.castSucc j').succ from
          (Fin.succ_castSucc j').symm,
        frontExtendEquiv_succ, extendLastEquiv_castSucc, Fin.succ_castSucc]



omit [Fintype Idx] [DecidableEq Idx] in
private theorem update_comp_equiv' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (g : β → Idx) (e : α ≃ β) (s : α) (sv : β) (hsv : e s = sv) (a : Idx) :
    (fun i => Function.update g sv a (e i)) = Function.update (fun i => g (e i)) s a := by
  subst hsv
  funext i
  by_cases h : i = s
  · subst h; simp only [Function.update_self]
  · rw [Function.update_of_ne (fun he => h (e.injective he)), Function.update_of_ne h]





omit [DecidableEq Idx] in
theorem covDerivStepCompU_compReindex {p p' : ℕ} (e₀ : Fin p ≃ Fin p')
    (ext : (Fin (p + 1) → Idx) → Idx → Real) (chr : Idx → Idx → Idx → Real)
    (A : (Fin (p + 1) → Idx) → Real) (n : Fin (p' + 1 + 1) → Idx) :
    covDerivStepCompU (fun m' d => ext (fun i => m' (extendLastEquiv e₀ i)) d) chr
        (fun n' => A (fun i => n' (extendLastEquiv e₀ i))) n =
      covDerivStepCompU ext chr A (fun j => n (frontExtendEquiv (extendLastEquiv e₀) j)) := by
  classical
  have htail : Fin.tail (fun j => n (frontExtendEquiv (extendLastEquiv e₀) j)) =
      fun i => Fin.tail n (extendLastEquiv e₀ i) := by
    funext i; simp only [Fin.tail, frontExtendEquiv_succ]
  unfold covDerivStepCompU
  simp only [frontExtendEquiv_zero, htail, extendLastEquiv_castSucc, extendLastEquiv_last]
  congr 1
  · congr 1
    rw [← Equiv.sum_comp e₀]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => ?_
    rw [update_comp_equiv' (Fin.tail n) (extendLastEquiv e₀) (Fin.castSucc t)
      (Fin.castSucc (e₀ t)) (extendLastEquiv_castSucc e₀ t) a]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [update_comp_equiv' (Fin.tail n) (extendLastEquiv e₀) (Fin.last p)
      (Fin.last p') (extendLastEquiv_last e₀) a]





omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem iterCovComp_compReindex {s s' : ℕ} (e : Fin s ≃ Fin s')
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (F : M → (Fin s → Idx) → Real) (m : ℕ) (x : M) :
    iterCovComp (I := I) frame chr (fun y (nn : Fin s' → Idx) => F y (fun i => nn (e i))) m x =
      fun n : Fin (s' + m) → Idx =>
        iterCovComp (I := I) frame chr F m x (fun j => n (frontExtendIterC e m j)) := by
  induction m generalizing x with
  | zero =>
    funext n
    rfl
  | succ m ih =>
    funext n
    rw [iterCovComp_succ,
      show iterCovComp (I := I) frame chr (fun y (nn : Fin s' → Idx) => F y (fun i => nn (e i)))
            m =
          (fun y (nn : Fin (s' + m) → Idx) =>
            iterCovComp (I := I) frame chr F m y (fun j => nn (frontExtendIterC e m j)))
        from funext ih,
      show frameExtData (I := I) frame
            (fun y (nn : Fin (s' + m) → Idx) =>
              iterCovComp (I := I) frame chr F m y (fun j => nn (frontExtendIterC e m j))) x =
          fun (m' : Fin (s' + m) → Idx) d =>
            frameExtData (I := I) frame (iterCovComp (I := I) frame chr F m) x
              (fun i => m' (frontExtendIterC e m i)) d from rfl,
      covDerivStepComp_compReindex (frontExtendIterC e m), ← iterCovComp_succ]
    rfl






def iterCovCompU {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) :
    (a : ℕ) → M → (Fin ((r + a) + 1) → Idx) → Real
  | 0 => base
  | (a + 1) => fun x =>
      covDerivStepCompU
        (frameExtData (I := I) frame
          (fun y : M => iterCovCompU frame chr base a y) x)
        (chr x)
        (iterCovCompU frame chr base a x)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
@[simp] theorem iterCovCompU_zero {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) :
    iterCovCompU (I := I) frame chr base 0 = base := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
@[simp] theorem iterCovCompU_succ {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) (a : ℕ) (x : M) :
    iterCovCompU (I := I) frame chr base (a + 1) x =
      covDerivStepCompU
        (frameExtData (I := I) frame
          (fun y : M => iterCovCompU (I := I) frame chr base a y) x)
        (chr x)
        (iterCovCompU (I := I) frame chr base a x) := rfl





omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem iterCovCompU_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) (m : ℕ) (x : M) :
    iterCovCompU (I := I) frame chr base (m + 1) x =
      fun n : Fin (r + (m + 1) + 1) → Idx =>
        iterCovCompU (I := I) frame chr (fun y => iterCovCompU (I := I) frame chr base 1 y) m x
          (fun j => n (extendLastEquiv (shiftEquivC r m) j)) := by
  induction m generalizing x with
  | zero =>
    funext n
    simp only [shiftEquivC, extendLastEquiv_refl, iterCovCompU_zero, Equiv.refl_apply]
  | succ m ih =>
    funext n
    rw [iterCovCompU_succ,
      show iterCovCompU (I := I) frame chr base (m + 1) =
          (fun y (nn : Fin (r + (m + 1) + 1) → Idx) =>
            iterCovCompU (I := I) frame chr (fun z => iterCovCompU (I := I) frame chr base 1 z) m y
              (fun j => nn (extendLastEquiv (shiftEquivC r m) j))) from funext ih,
      show frameExtData (I := I) frame
            (fun y (nn : Fin (r + (m + 1) + 1) → Idx) =>
              iterCovCompU (I := I) frame chr (fun z => iterCovCompU (I := I) frame chr base 1 z) m y
                (fun j => nn (extendLastEquiv (shiftEquivC r m) j))) x =
          fun (m' : Fin (r + (m + 1) + 1) → Idx) d =>
            frameExtData (I := I) frame
              (iterCovCompU (I := I) frame chr
                (fun z => iterCovCompU (I := I) frame chr base 1 z) m) x
              (fun i => m' (extendLastEquiv (shiftEquivC r m) i)) d from rfl,
      covDerivStepCompU_compReindex (shiftEquivC r m), ← iterCovCompU_succ,
      extendLast_frontExtend_comm]
    rfl


omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem compL2_iterCovCompU_shift {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real) (m : ℕ) (x : M) :
    compL2 (iterCovCompU (I := I) frame chr base (m + 1) x) =
      compL2 (iterCovCompU (I := I) frame chr
        (fun y => iterCovCompU (I := I) frame chr base 1 y) m x) := by
  rw [iterCovCompU_shift]
  exact compL2_comp_equiv
    (iterCovCompU (I := I) frame chr (fun y => iterCovCompU (I := I) frame chr base 1 y) m x)
    (extendLastEquiv (shiftEquivC r m))









omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem frameExtData_contrTail {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x)
    (idx : Fin (p + q) → Idx) (d : Idx) :
    frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x idx d =
      ∑ c : Idx,
        (frameExtData (I := I) frame A x
              (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) d *
            B x (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) +
          A x (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
            frameExtData (I := I) frame B x
              (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c) d) := by
  classical
  unfold frameExtData
  rw [show (fun y : M => contrTail (A y) (B y) idx) =
      (fun y : M => ∑ c : Idx,
        A y (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c) *
          B y (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c)) from by
    funext y; rw [contrTail_apply]]
  rw [extDerivFun_finset_sum_mul_at (I := I) Finset.univ
    (fun c y => A y (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c))
    (fun c y => B y (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c))
    (frame d x)
    (fun c _ => hA (Fin.snoc (fun i : Fin p => idx (Fin.castAdd q i)) c))
    (fun c _ => hB (Fin.snoc (fun j : Fin q => idx (Fin.natAdd p j)) c))]
  exact Finset.sum_congr rfl fun c _ => by ring




omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] [DecidableEq Idx] in
theorem frameExtData_add {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (f₁ f₂ : M → (Fin r → Idx) → Real) (x : M)
    (hf₁ : ∀ m : Fin r → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => f₁ y m) x)
    (hf₂ : ∀ m : Fin r → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => f₂ y m) x)
    (m : Fin r → Idx) (d : Idx) :
    frameExtData (I := I) frame (fun y k => f₁ y k + f₂ y k) x m d =
      frameExtData (I := I) frame f₁ x m d + frameExtData (I := I) frame f₂ x m d := by
  unfold frameExtData
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f₁ y m + f₂ y m) x
      (frame d x),
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f₁ y m) x (frame d x),
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f₂ y m) x (frame d x),
    show (fun y : M => f₁ y m + f₂ y m) = (fun y : M => f₁ y m) + (fun y : M => f₂ y m) from rfl,
    mfderiv_add (hf₁ m) (hf₂ m)]
  rfl


omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [Fintype Idx] [DecidableEq Idx] in
theorem frameExtData_smul {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (c : Real) (f : M → (Fin r → Idx) → Real) (x : M)
    (hf : ∀ m : Fin r → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => f y m) x)
    (m : Fin r → Idx) (d : Idx) :
    frameExtData (I := I) frame (fun y k => c * f y k) x m d =
      c * frameExtData (I := I) frame f x m d := by
  unfold frameExtData
  rw [DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => c * f y m) x (frame d x),
    DifferentialGeometry.extDerivFun_real_eq_mfderiv I (fun y : M => f y m) x (frame d x),
    show (fun y : M => c * f y m) = c • (fun y : M => f y m) from rfl,
    const_smul_mfderiv (hf m) c]
  rfl










omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem contMDiffOn_finsetSum {ι : Type*} {u : Set M} (t : Finset ι)
    (F : ι → M → Real)
    (hF : ∀ i ∈ t, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (F i) u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => ∑ i ∈ t, F i y) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using contMDiffOn_const (c := (0 : ℝ))
  | insert a s has ih =>
    have hsum : (fun y => ∑ i ∈ insert a s, F i y) =
        fun y => F a y + ∑ i ∈ s, F i y := by
      funext y; rw [Finset.sum_insert has]
    rw [hsum]
    exact (hF a (by simp)).add (ih fun i hi => hF i (by simp [hi]))




omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_contMDiffOn {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    (a : ℕ) :
    ∀ n : Fin (r + a) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => iterCovComp (I := I) frame chr base a y n) u := by
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro n
    have hstep : (fun y => iterCovComp (I := I) frame chr base (a + 1) y n) =
        fun y =>
          extDerivFun (I := I)
              (fun z => iterCovComp (I := I) frame chr base a z (Fin.tail n)) y
              (frame (n 0) y) -
            ∑ s : Fin (r + a), ∑ p : Idx,
              chr y (n 0) (Fin.tail n s) p *
                iterCovComp (I := I) frame chr base a y
                  (Function.update (Fin.tail n) s p) := by
      funext y
      rw [iterCovComp_succ]
      rfl
    rw [hstep]
    refine ContMDiffOn.sub ?_ ?_
    · intro z hz
      exact (contMDiffAt_extDerivFun_apply hu hz (ih (Fin.tail n))
        (hframe (n 0))).contMDiffWithinAt
    · refine contMDiffOn_finsetSum _ _ fun s _ => ?_
      refine contMDiffOn_finsetSum _ _ fun p _ => ?_
      exact (hchr (n 0) (Fin.tail n s) p).mul (ih (Function.update (Fin.tail n) s p))




omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovCompU_contMDiffOn {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin (r + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    (a : ℕ) :
    ∀ n : Fin ((r + a) + 1) → Idx,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovCompU (I := I) frame chr base a y n) u := by
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro n
    have hstep : (fun y => iterCovCompU (I := I) frame chr base (a + 1) y n) =
        fun y =>
          extDerivFun (I := I)
              (fun z => iterCovCompU (I := I) frame chr base a z (Fin.tail n)) y
              (frame (n 0) y) -
            ∑ j : Fin (r + a), ∑ c : Idx,
              chr y (n 0) (Fin.tail n (Fin.castSucc j)) c *
                iterCovCompU (I := I) frame chr base a y
                  (Function.update (Fin.tail n) (Fin.castSucc j) c) +
            ∑ c : Idx,
              chr y (n 0) c (Fin.tail n (Fin.last (r + a))) *
                iterCovCompU (I := I) frame chr base a y
                  (Function.update (Fin.tail n) (Fin.last (r + a)) c) := by
      funext y
      rw [iterCovCompU_succ]
      rfl
    rw [hstep]
    refine ContMDiffOn.add (ContMDiffOn.sub ?_ ?_) ?_
    · intro z hz
      exact (contMDiffAt_extDerivFun_apply hu hz (ih (Fin.tail n))
        (hframe (n 0))).contMDiffWithinAt
    · refine contMDiffOn_finsetSum _ _ fun j _ => ?_
      refine contMDiffOn_finsetSum _ _ fun c _ => ?_
      exact (hchr (n 0) (Fin.tail n (Fin.castSucc j)) c).mul
        (ih (Function.update (Fin.tail n) (Fin.castSucc j) c))
    · refine contMDiffOn_finsetSum _ _ fun c _ => ?_
      exact (hchr (n 0) c (Fin.tail n (Fin.last (r + a)))).mul
        (ih (Function.update (Fin.tail n) (Fin.last (r + a)) c))



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_mdiffAt {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    {x : M} (hx : x ∈ u) (a : ℕ) (n : Fin (r + a) → Idx) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => iterCovComp (I := I) frame chr base a y n) x :=
  ((iterCovComp_contMDiffOn hu frame chr base hframe hchr hbase a n).contMDiffAt
    (hu.mem_nhds hx)).mdifferentiableAt (by simp)



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovCompU_mdiffAt {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (base : M → (Fin (r + 1) → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hbase : ∀ m : Fin (r + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => base y m) u)
    {x : M} (hx : x ∈ u) (a : ℕ) (n : Fin ((r + a) + 1) → Idx) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => iterCovCompU (I := I) frame chr base a y n) x :=
  ((iterCovCompU_contMDiffOn hu frame chr base hframe hchr hbase a n).contMDiffAt
    (hu.mem_nhds hx)).mdifferentiableAt (by simp)


omit [Fintype Idx] [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem frameExtData_congr_nhds {r : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    {F₁ F₂ : M → (Fin r → Idx) → Real} {y : M}
    (h : ∀ᶠ z in nhds y, F₁ z = F₂ z) :
    frameExtData (I := I) frame F₁ y = frameExtData (I := I) frame F₂ y := by
  funext m d
  refine extDerivFun_eventuallyEq_congr (I := I) (frame d y) ?_
  filter_upwards [h] with z hz
  rw [hz]





omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_add {r : ℕ} {u : Set M} (hu : IsOpen u)
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
      iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a y n =
        iterCovComp (I := I) frame chr f₁ a y n + iterCovComp (I := I) frame chr f₂ a y n := by
  induction a with
  | zero => intro y _ n; rfl
  | succ a ih =>
    intro y hy n
    have hfield : ∀ᶠ z in nhds y,
        iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a z =
          fun k => iterCovComp (I := I) frame chr f₁ a z k +
            iterCovComp (I := I) frame chr f₂ a z k := by
      filter_upwards [hu.mem_nhds hy] with z hz
      funext k; exact ih z hz k
    have hext : frameExtData (I := I) frame
          (iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a) y =
        fun m d => frameExtData (I := I) frame (iterCovComp (I := I) frame chr f₁ a) y m d +
          frameExtData (I := I) frame (iterCovComp (I := I) frame chr f₂ a) y m d := by
      rw [frameExtData_congr_nhds frame hfield]
      funext m d
      exact frameExtData_add frame (iterCovComp (I := I) frame chr f₁ a)
        (iterCovComp (I := I) frame chr f₂ a) y
        (fun m => iterCovComp_mdiffAt hu frame chr f₁ hframe hchr hf₁ hy a m)
        (fun m => iterCovComp_mdiffAt hu frame chr f₂ hframe hchr hf₂ hy a m) m d
    have harr : iterCovComp (I := I) frame chr (fun z k => f₁ z k + f₂ z k) a y =
        fun k => iterCovComp (I := I) frame chr f₁ a y k +
          iterCovComp (I := I) frame chr f₂ a y k := funext (ih y hy)
    rw [iterCovComp_succ, iterCovComp_succ, iterCovComp_succ, hext, harr,
      covDerivStepComp_add]



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_smul {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (c : Real) (f : M → (Fin r → Idx) → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (hf : ∀ m : Fin r → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => f y m) u)
    (a : ℕ) :
    ∀ y ∈ u, ∀ n : Fin (r + a) → Idx,
      iterCovComp (I := I) frame chr (fun z k => c * f z k) a y n =
        c * iterCovComp (I := I) frame chr f a y n := by
  induction a with
  | zero => intro y _ n; rfl
  | succ a ih =>
    intro y hy n
    have hfield : ∀ᶠ z in nhds y,
        iterCovComp (I := I) frame chr (fun z k => c * f z k) a z =
          fun k => c * iterCovComp (I := I) frame chr f a z k := by
      filter_upwards [hu.mem_nhds hy] with z hz
      funext k; exact ih z hz k
    have hext : frameExtData (I := I) frame
          (iterCovComp (I := I) frame chr (fun z k => c * f z k) a) y =
        fun m d => c * frameExtData (I := I) frame (iterCovComp (I := I) frame chr f a) y m d := by
      rw [frameExtData_congr_nhds frame hfield]
      funext m d
      exact frameExtData_smul frame c (iterCovComp (I := I) frame chr f a) y
        (fun m => iterCovComp_mdiffAt hu frame chr f hframe hchr hf hy a m) m d
    have harr : iterCovComp (I := I) frame chr (fun z k => c * f z k) a y =
        fun k => c * iterCovComp (I := I) frame chr f a y k := funext (ih y hy)
    rw [iterCovComp_succ, iterCovComp_succ, hext, harr, covDerivStepComp_smul]






omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem covDerivStepComp_frameExtData_contrTail {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x)
    (d : Idx) (aPart : Fin p → Idx) (bPart : Fin q → Idx) :
    covDerivStepComp (frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x)
        (chr x) (contrTail (A x) (B x)) (Fin.cons d (Fin.append aPart bPart)) =
      contrTail (covDerivStepCompU (frameExtData (I := I) frame A x) (chr x) (A x)) (B x)
          (Fin.append (Fin.cons d aPart) bPart) +
        contrTail (A x) (covDerivStepComp (frameExtData (I := I) frame B x) (chr x) (B x))
          (Fin.append aPart (Fin.cons d bPart)) :=
  covDerivStepCompU_contrTail_leibniz
    (frameExtData (I := I) frame A x) (frameExtData (I := I) frame B x)
    (frameExtData (I := I) frame (fun y : M => contrTail (A y) (B y)) x)
    (chr x) (A x) (B x)
    (frameExtData_contrTail (I := I) frame A B x hA hB)
    d aPart bPart








omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem covStep_contrTail_field {p q : ℕ}
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (x : M)
    (hA : ∀ m : Fin (p + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => A y m) x)
    (hB : ∀ m : Fin (q + 1) → Idx, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => B y m) x) :
    iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 x =
      fun n : Fin (p + q + 1) → Idx =>
        contrTail (iterCovCompU (I := I) frame chr A 1 x) (B x)
            (fun j => n (finCongr (show p + 1 + q = p + q + 1 by omega) j)) +
          contrTail (A x) (iterCovComp (I := I) frame chr B 1 x)
            (fun i => n (rotEquiv p q i)) := by
  funext n
  simp only [iterCovComp_succ, iterCovComp_zero, iterCovCompU_succ, iterCovCompU_zero]
  set d : Idx := n 0 with hd
  set aPart : Fin p → Idx := fun i => Fin.tail n (Fin.castAdd q i) with haP
  set bPart : Fin q → Idx := fun j => Fin.tail n (Fin.natAdd p j) with hbP
  have hn : n = Fin.cons d (Fin.append aPart bPart) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
      change Fin.tail n i' = Fin.append aPart bPart i'
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i'
      · rw [Fin.append_left]
      · rw [Fin.append_right]
  conv_lhs => rw [hn]
  rw [covDerivStepComp_frameExtData_contrTail frame chr A B x hA hB d aPart bPart,
    slotId1 d aPart bPart, slotId2 d aPart bPart, ← hn]
  simp only [finCongr_apply]







omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem compL2_iterCovComp_compReindex {s s' : ℕ} (e : Fin s ≃ Fin s')
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (F : M → (Fin s → Idx) → Real) (m : ℕ) (x : M) :
    compL2 (iterCovComp (I := I) frame chr
        (fun y (nn : Fin s' → Idx) => F y (fun i => nn (e i))) m x) =
      compL2 (iterCovComp (I := I) frame chr F m x) := by
  rw [iterCovComp_compReindex]
  exact compL2_comp_equiv (iterCovComp (I := I) frame chr F m x) (frontExtendIterC e m)





omit [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem iterCovComp_congr_on {r : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    {F₁ F₂ : M → (Fin r → Idx) → Real}
    (h : ∀ y ∈ u, F₁ y = F₂ y) (a : ℕ) :
    ∀ x ∈ u, iterCovComp (I := I) frame chr F₁ a x = iterCovComp (I := I) frame chr F₂ a x := by
  induction a with
  | zero => intro x hx; exact h x hx
  | succ a ih =>
    intro x hx
    have hfield : ∀ᶠ z in nhds x, iterCovComp (I := I) frame chr F₁ a z =
        iterCovComp (I := I) frame chr F₂ a z := by
      filter_upwards [hu.mem_nhds hx] with z hz
      exact ih z hz
    rw [iterCovComp_succ, iterCovComp_succ, frameExtData_congr_nhds frame hfield, ih x hx]



omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem contMDiffOn_contrTail {p q : ℕ} {u : Set M}
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hB : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u)
    (m : Fin (p + q) → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => contrTail (A y) (B y) m) u := by
  classical
  rw [show (fun y => contrTail (A y) (B y) m) =
      (fun y => ∑ c : Idx, A y (Fin.snoc (fun i : Fin p => m (Fin.castAdd q i)) c) *
        B y (Fin.snoc (fun j : Fin q => m (Fin.natAdd p j)) c)) from by funext y; rw [contrTail_apply]]
  exact contMDiffOn_finsetSum Finset.univ _ (fun c _ => (hA _).mul (hB _))










omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem compL2_iterCovComp_contrTail_le {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (m : ℕ) : ∀ {p q : ℕ}
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real),
    (∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
    (∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u) →
    ∀ {x : M}, x ∈ u →
    compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) m x) ≤
      ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
        compL2 (iterCovCompU (I := I) frame chr A c x) *
        compL2 (iterCovComp (I := I) frame chr B (m - c) x) := by
  induction m with
  | zero =>
    intro p q A B _ _ x _
    rw [Finset.sum_range_one]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
      iterCovComp_zero, iterCovCompU_zero]
    exact compL2_contrTail_le (A x) (B x)
  | succ m ih =>
    intro p q A B hA hB x hx

    have hAU : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovCompU (I := I) frame chr A 1 y k) u :=
      iterCovCompU_contMDiffOn hu frame chr A hframe hchr hA 1
    have hB1 : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovComp (I := I) frame chr B 1 y k) u :=
      iterCovComp_contMDiffOn hu frame chr B hframe hchr hB 1


    set HL : M → (Fin (p + 1 + q) → Idx) → Real :=
      fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (B z) with hHL
    set HR : M → (Fin (p + (q + 1)) → Idx) → Real :=
      fun z => contrTail (A z) (iterCovComp (I := I) frame chr B 1 z) with hHR
    set LF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HL y (fun j => nn (finCongr (show p + 1 + q = p + q + 1 by omega) j)) with hLF
    set RF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HR y (fun i => nn (rotEquiv p q i)) with hRF
    have hLsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => LF y k) u := by
      intro k; simp only [hLF, hHL]; exact contMDiffOn_contrTail _ _ hAU hB _
    have hRsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => RF y k) u := by
      intro k; simp only [hRF, hHR]; exact contMDiffOn_contrTail _ _ hA hB1 _

    have hsplit : ∀ y ∈ u, iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 y =
        fun nn => LF y nn + RF y nn := by
      intro y hy
      rw [covStep_contrTail_field frame chr A B y
        (fun k => ((hA k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))
        (fun k => ((hB k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))]

    have hL : compL2 (iterCovComp (I := I) frame chr HL m x) ≤
        ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A (c + 1) x) *
          compL2 (iterCovComp (I := I) frame chr B (m - c) x) := by
      rw [hHL]
      refine le_trans (ih (fun y => iterCovCompU (I := I) frame chr A 1 y) B hAU hB hx)
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovCompU_shift frame chr A c x]

    have hR : compL2 (iterCovComp (I := I) frame chr HR m x) ≤
        ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr B (m - c + 1) x) := by
      rw [hHR]
      refine le_trans (ih A (fun y => iterCovComp (I := I) frame chr B 1 y) hA hB1 hx)
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovComp_shift frame chr B (m - c) x]

    calc compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) (m + 1) x)
        = compL2 (iterCovComp (I := I) frame chr
            (fun y => iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 y) m x) :=
          compL2_iterCovComp_shift frame chr (fun z => contrTail (A z) (B z)) m x
      _ = compL2 (iterCovComp (I := I) frame chr (fun y nn => LF y nn + RF y nn) m x) :=
          congrArg compL2 (iterCovComp_congr_on hu frame chr hsplit m x hx)
      _ = compL2 (fun n : Fin (p + q + 1 + m) → Idx =>
            iterCovComp (I := I) frame chr LF m x n + iterCovComp (I := I) frame chr RF m x n) :=
          congrArg compL2 (funext fun n =>
            iterCovComp_add hu frame chr LF RF hframe hchr hLsm hRsm m x hx n)
      _ ≤ compL2 (iterCovComp (I := I) frame chr LF m x) +
          compL2 (iterCovComp (I := I) frame chr RF m x) := compL2_add_le _ _
      _ = compL2 (iterCovComp (I := I) frame chr HL m x) +
          compL2 (iterCovComp (I := I) frame chr HR m x) := by
          rw [hLF, hRF,
            compL2_iterCovComp_compReindex (finCongr (show p + 1 + q = p + q + 1 by omega))
              frame chr HL m x,
            compL2_iterCovComp_compReindex (rotEquiv p q) frame chr HR m x]
      _ ≤ (∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chr A (c + 1) x) *
              compL2 (iterCovComp (I := I) frame chr B (m - c) x)) +
            ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chr A c x) *
              compL2 (iterCovComp (I := I) frame chr B (m - c + 1) x) := add_le_add hL hR
      _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : Real) *
            (compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr B (m + 1 - c) x)) := by
          rw [← pascal_sum m (fun c => compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr B (m + 1 - c) x))]
          congr 1
          · refine Finset.sum_congr rfl fun c _ => ?_
            have hsub : m + 1 - (c + 1) = m - c := by omega
            rw [hsub]; ring
          · refine Finset.sum_congr rfl fun c hc => ?_
            have hsub : m - c + 1 = m + 1 - c := by
              simp only [Finset.mem_range] at hc; omega
            rw [hsub]; ring
      _ = ∑ c ∈ Finset.range (m + 1 + 1), ((m + 1).choose c : Real) *
            compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr B (m + 1 - c) x) :=
          Finset.sum_congr rfl fun c _ => (mul_assoc _ _ _).symm









omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem iterCovComp_contrTail_succ {p q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (A : M → (Fin (p + 1) → Idx) → Real) (B : M → (Fin (q + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    (hB : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => B y k) u)
    (m : ℕ) {x : M} (hx : x ∈ u) :
    iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) (m + 1) x =
      fun n : Fin (p + q + (m + 1)) → Idx =>
        iterCovComp (I := I) frame chr
            (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (B z)) m x
            (fun j => n ((frontExtendIterC (finCongr (show p + 1 + q = p + q + 1 by omega)) m).trans
              (shiftEquivC (p + q) m) j)) +
          iterCovComp (I := I) frame chr
            (fun z => contrTail (A z) (iterCovComp (I := I) frame chr B 1 z)) m x
            (fun j => n ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m) j)) := by
    set HL : M → (Fin (p + 1 + q) → Idx) → Real :=
      fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (B z) with hHL
    set HR : M → (Fin (p + (q + 1)) → Idx) → Real :=
      fun z => contrTail (A z) (iterCovComp (I := I) frame chr B 1 z) with hHR
    set LF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HL y (fun j => nn (finCongr (show p + 1 + q = p + q + 1 by omega) j)) with hLF
    set RF : M → (Fin (p + q + 1) → Idx) → Real :=
      fun y nn => HR y (fun i => nn (rotEquiv p q i)) with hRF
    have hLsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => LF y k) u := by
      intro k; simp only [hLF, hHL]; exact contMDiffOn_contrTail _ _
        (iterCovCompU_contMDiffOn hu frame chr A hframe hchr hA 1) hB _
    have hRsm : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => RF y k) u := by
      intro k; simp only [hRF, hHR]; exact contMDiffOn_contrTail _ _
        hA (iterCovComp_contMDiffOn hu frame chr B hframe hchr hB 1) _
    have hsplit : ∀ y ∈ u, iterCovComp (I := I) frame chr (fun z => contrTail (A z) (B z)) 1 y =
        fun nn => LF y nn + RF y nn := by
      intro y hy
      rw [covStep_contrTail_field frame chr A B y
        (fun k => ((hA k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))
        (fun k => ((hB k).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))]
    rw [iterCovComp_shift frame chr (fun z => contrTail (A z) (B z)) m x]
    funext n
    rw [iterCovComp_congr_on hu frame chr hsplit m x hx,
      iterCovComp_add hu frame chr LF RF hframe hchr hLsm hRsm m x hx,
      hLF, hRF, iterCovComp_compReindex (finCongr (show p + 1 + q = p + q + 1 by omega)) frame chr HL m x,
      iterCovComp_compReindex (rotEquiv p q) frame chr HR m x]
    simp only [Equiv.trans_apply]




def isoReindex (p q m : ℕ) : Fin (p + 1 + q + m) ≃ Fin (p + q + (m + 1)) :=
  (frontExtendIterC (finCongr (show p + 1 + q = p + q + 1 by omega)) m).trans (shiftEquivC (p + q) m)




def isoTop {q : ℕ} (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real) :
    (m : ℕ) → {p : ℕ} → (A : M → (Fin (p + 1) → Idx) → Real) → (x : M) →
      (Fin (p + q + m) → Idx) → Real
  | 0, p, A, x => contrTail (p := p) (q := q) (A x) (g x)
  | (m + 1), p, A, x => fun n =>
      isoTop g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
        (fun j => n (isoReindex p q m j))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
@[simp] theorem isoTop_zero {q : ℕ} (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real)
    {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real) (x : M) :
    isoTop (I := I) g frame chr 0 A x = contrTail (A x) (g x) := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
@[simp] theorem isoTop_succ {q : ℕ} (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real)
    {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real) (m : ℕ) (x : M) :
    isoTop (I := I) g frame chr (m + 1) A x =
      fun n => isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
        (fun j => n (isoReindex p q m j)) := rfl







omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem compL2_isoResidual_le {q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (q + 1) → Idx) → Real)
    (hg : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (m : ℕ) : ∀ {p : ℕ}
    (A : M → (Fin (p + 1) → Idx) → Real),
    (∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
    ∀ {x : M}, x ∈ u →
    compL2 (fun n : Fin (p + q + m) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x n -
          isoTop (I := I) g frame chr m A x n) ≤
      ∑ c ∈ Finset.range m, (m.choose c : Real) *
        compL2 (iterCovCompU (I := I) frame chr A c x) *
        compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
  induction m with
  | zero =>
    intro p A _ x _
    rw [Finset.sum_range_zero]
    have hzero : (fun n : Fin (p + q + 0) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) 0 x n -
          isoTop (I := I) g frame chr 0 A x n) = fun _ => (0 : Real) := by
      funext n
      rw [iterCovComp_zero, isoTop_zero]
      exact sub_self _
    rw [hzero]
    simp [compL2, compL2Sq]
  | succ m ih =>
    intro p A hA x hx
    have hAU : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovCompU (I := I) frame chr A 1 y k) u :=
      iterCovCompU_contMDiffOn hu frame chr A hframe hchr hA 1
    have hg1 : ∀ k, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun y => iterCovComp (I := I) frame chr g 1 y k) u :=
      iterCovComp_contMDiffOn hu frame chr g hframe hchr hg 1

    have hdec : (fun n : Fin (p + q + (m + 1)) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) (m + 1) x n -
          isoTop (I := I) g frame chr (m + 1) A x n) =
        fun n =>
          (iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x
              (fun j => n (isoReindex p q m j)) -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
              (fun j => n (isoReindex p q m j))) +
          iterCovComp (I := I) frame chr
              (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x
              (fun j => n ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m) j)) := by
      funext n
      rw [iterCovComp_contrTail_succ hu frame chr hframe hchr A g hA hg m hx, isoTop_succ]
      exact add_sub_right_comm _ _ _
    rw [hdec]
    refine le_trans (compL2_add_le _ _) ?_
    have hψ : compL2 (fun n : Fin (p + q + (m + 1)) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x
              (fun j => n (isoReindex p q m j)) -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
              (fun j => n (isoReindex p q m j))) =
        compL2 (fun nn : Fin (p + 1 + q + m) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x nn -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x nn) :=
      compL2_comp_equiv
        (fun nn : Fin (p + 1 + q + m) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x nn -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x nn)
        (isoReindex p q m)
    have hψR : compL2 (fun n : Fin (p + q + (m + 1)) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x
              (fun j => n ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m) j))) =
        compL2 (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x) :=
      compL2_comp_equiv
        (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x)
        ((frontExtendIterC (rotEquiv p q) m).trans (shiftEquivC (p + q) m))
    rw [hψ, hψR]

    have hL : compL2 (fun nn : Fin (p + 1 + q + m) → Idx =>
          iterCovComp (I := I) frame chr
              (fun z => contrTail (iterCovCompU (I := I) frame chr A 1 z) (g z)) m x nn -
            isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x nn) ≤
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A (c + 1) x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
      refine le_trans (ih (fun y => iterCovCompU (I := I) frame chr A 1 y) hAU hx)
        (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovCompU_shift frame chr A c x]

    have hR : compL2 (iterCovComp (I := I) frame chr
          (fun z => contrTail (A z) (iterCovComp (I := I) frame chr g 1 z)) m x) ≤
        ∑ c ∈ Finset.range (m + 1), (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c + 1) x) := by
      refine le_trans (compL2_iterCovComp_contrTail_le hu frame chr hframe hchr m A
        (fun y => iterCovComp (I := I) frame chr g 1 y) hA hg1 hx) (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [compL2_iterCovComp_shift frame chr g (m - c) x]
    refine le_trans (add_le_add hL hR) (le_of_eq ?_)

    have hregroup : (∑ c ∈ Finset.range (m + 1), ((m + 1).choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m + 1 - c) x)) =
        ∑ c ∈ Finset.range (m + 1), ((m + 1).choose c : Real) *
          (compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m + 1 - c) x)) :=
      Finset.sum_congr rfl fun c _ => mul_assoc _ _ _
    rw [hregroup,
      ← pascal_sum_notop m (fun c => compL2 (iterCovCompU (I := I) frame chr A c x) *
        compL2 (iterCovComp (I := I) frame chr g (m + 1 - c) x))]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hsub : m + 1 - (c + 1) = m - c := by omega
      rw [hsub]; ring
    · refine Finset.sum_congr rfl fun c hc => ?_
      have hsub : m - c + 1 = m + 1 - c := by
        simp only [Finset.mem_range] at hc; omega
      rw [hsub]; ring





def blockLeftEquiv {a a' : ℕ} (e₀ : Fin a ≃ Fin a') (b : ℕ) : Fin (a + b) ≃ Fin (a' + b) :=
  finSumFinEquiv.symm.trans ((e₀.sumCongr (Equiv.refl (Fin b))).trans finSumFinEquiv)

@[simp] theorem blockLeftEquiv_castAdd {a a' : ℕ} (e₀ : Fin a ≃ Fin a') (b : ℕ) (i : Fin a) :
    blockLeftEquiv e₀ b (Fin.castAdd b i) = Fin.castAdd b (e₀ i) := by
  simp [blockLeftEquiv]

@[simp] theorem blockLeftEquiv_natAdd {a a' : ℕ} (e₀ : Fin a ≃ Fin a') (b : ℕ) (j : Fin b) :
    blockLeftEquiv e₀ b (Fin.natAdd a j) = Fin.natAdd a' j := by
  simp [blockLeftEquiv]




omit [DecidableEq Idx] in
theorem contrTail_extendLast {pT pF q : ℕ} (e₀ : Fin pT ≃ Fin pF)
    (T : (Fin (pT + 1) → Idx) → Real) (B : (Fin (q + 1) → Idx) → Real) :
    contrTail (fun n : Fin (pF + 1) → Idx => T (fun j => n (extendLastEquiv e₀ j))) B =
      fun idx : Fin (pF + q) → Idx =>
        contrTail T B (fun j => idx (blockLeftEquiv e₀ q j)) := by
  funext idx
  rw [contrTail_apply, contrTail_apply]
  have hAvec : (fun i : Fin pT => idx (blockLeftEquiv e₀ q (Fin.castAdd q i))) =
      fun i => idx (Fin.castAdd q (e₀ i)) := by
    funext i; rw [blockLeftEquiv_castAdd]
  have hBvec : (fun j : Fin q => idx (blockLeftEquiv e₀ q (Fin.natAdd pT j))) =
      fun j => idx (Fin.natAdd pF j) := by
    funext j; rw [blockLeftEquiv_natAdd]
  rw [hAvec, hBvec]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [extendLastEquiv_last, Fin.snoc_last, Fin.snoc_last]
  · rw [extendLastEquiv_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]




omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
omit [DecidableEq Idx] in
theorem compL2_isoTop_eq {q : ℕ}
    (g : M → (Fin (q + 1) → Idx) → Real)
    (frame : Idx → (x : M) → TangentSpace I x) (chr : M → Idx → Idx → Idx → Real)
    (m : ℕ) : ∀ {p : ℕ} (A : M → (Fin (p + 1) → Idx) → Real) (x : M),
    compL2 (isoTop (I := I) g frame chr m A x) =
      compL2 (contrTail (iterCovCompU (I := I) frame chr A m x) (g x)) := by
  induction m with
  | zero => intro p A x; rfl
  | succ m ih =>
    intro p A x
    rw [isoTop_succ,
      show compL2 (fun n : Fin (p + q + (m + 1)) → Idx =>
          isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x
            (fun j => n (isoReindex p q m j))) =
        compL2 (isoTop (I := I) g frame chr m
          (fun z => iterCovCompU (I := I) frame chr A 1 z) x) from
        compL2_comp_equiv
          (isoTop (I := I) g frame chr m (fun z => iterCovCompU (I := I) frame chr A 1 z) x)
          (isoReindex p q m),
      ih (fun z => iterCovCompU (I := I) frame chr A 1 z) x,
      show contrTail (iterCovCompU (I := I) frame chr A (m + 1) x) (g x) =
        fun idx : Fin (p + (m + 1) + q) → Idx =>
          contrTail (iterCovCompU (I := I) frame chr
              (fun y => iterCovCompU (I := I) frame chr A 1 y) m x) (g x)
            (fun j => idx (blockLeftEquiv (shiftEquivC p m) q j)) from by
        rw [iterCovCompU_shift frame chr A m x, contrTail_extendLast]]
    exact (compL2_comp_equiv
      (contrTail (iterCovCompU (I := I) frame chr
        (fun y => iterCovCompU (I := I) frame chr A 1 y) m x) (g x))
      (blockLeftEquiv (shiftEquivC p m) q)).symm



omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [DecidableEq Idx] in
theorem compL2_contrTail_topU_le {q : ℕ} {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (g : M → (Fin (q + 1) → Idx) → Real)
    (hg : ∀ k : Fin (q + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u)
    (m : ℕ) {p : ℕ}
    (A : M → (Fin (p + 1) → Idx) → Real)
    (hA : ∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u)
    {x : M} (hx : x ∈ u) :
    compL2 (contrTail (iterCovCompU (I := I) frame chr A m x) (g x)) ≤
      compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x) +
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
  rw [← compL2_isoTop_eq g frame chr m A x,
    show isoTop (I := I) g frame chr m A x =
      fun n : Fin (p + q + m) → Idx =>
        iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x n -
          (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m x n -
            isoTop (I := I) g frame chr m A x n) from
      funext fun n => (sub_sub_cancel _ _).symm]
  exact le_trans (compL2_sub_le _ _)
    (add_le_add le_rfl (compL2_isoResidual_le hu frame chr hframe hchr g hg m A hA hx))






theorem contrTail_contrTail_inv {P : ℕ}
    (T : (Fin (P + 1) → Idx) → Real) (G Ginv : (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ c e : Idx,
      (∑ l : Idx, G (Fin.snoc (fun _ : Fin 1 => l) c) * Ginv (Fin.snoc (fun _ : Fin 1 => e) l)) =
        if c = e then 1 else 0) :
    contrTail (contrTail T G) Ginv = T := by
  classical
  funext v
  rw [contrTail_apply]
  have hinner : ∀ l : Idx,
      contrTail T G (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) l) =
        ∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
          G (Fin.snoc (fun _ : Fin 1 => l) c) := by
    intro l
    rw [contrTail_apply]
    have h1 : (fun i : Fin P =>
        (Fin.snoc (fun i' : Fin P => v (Fin.castAdd 1 i')) l : Fin (P + 1) → Idx)
          (Fin.castAdd 1 i)) = fun i : Fin P => v (Fin.castAdd 1 i) := by
      funext i
      rw [show (Fin.castAdd 1 i : Fin (P + 1)) = Fin.castSucc i from rfl, Fin.snoc_castSucc]
      rfl
    have h2 : (fun j : Fin 1 =>
        (Fin.snoc (fun i' : Fin P => v (Fin.castAdd 1 i')) l : Fin (P + 1) → Idx)
          (Fin.natAdd P j)) = fun _ : Fin 1 => l := by
      funext j
      rw [show (Fin.natAdd P j : Fin (P + 1)) = Fin.last P from
          Fin.ext (by simp [Subsingleton.elim j (0 : Fin 1)]),
        Fin.snoc_last]
    rw [h1, h2]
  simp only [hinner]
  have hvN : (fun j : Fin 1 => v (Fin.natAdd P j)) = fun _ : Fin 1 => v (Fin.natAdd P 0) := by
    funext j; rw [Subsingleton.elim j (0 : Fin 1)]
  rw [hvN]
  calc (∑ l : Idx, (∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
            G (Fin.snoc (fun _ : Fin 1 => l) c)) *
          Ginv (Fin.snoc (fun _ : Fin 1 => v (Fin.natAdd P 0)) l))
      = ∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
          (∑ l : Idx, G (Fin.snoc (fun _ : Fin 1 => l) c) *
            Ginv (Fin.snoc (fun _ : Fin 1 => v (Fin.natAdd P 0)) l)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ c : Idx, T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c) *
          (if c = v (Fin.natAdd P 0) then 1 else 0) :=
        Finset.sum_congr rfl fun c _ => by rw [hinv c (v (Fin.natAdd P 0))]
    _ = T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) (v (Fin.natAdd P 0))) := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (v (Fin.natAdd P 0))
          (fun c => T (Fin.snoc (fun i : Fin P => v (Fin.castAdd 1 i)) c))]
        simp
    _ = T v := by
        congr 1
        funext k
        refine Fin.lastCases ?_ (fun i => ?_) k
        · rw [Fin.snoc_last,
            show (Fin.natAdd P 0 : Fin (P + 1)) = Fin.last P from Fin.ext (by simp)]
        · rw [Fin.snoc_castSucc]
          rfl



theorem compL2_le_contrTail_inv {P : ℕ}
    (T : (Fin (P + 1) → Idx) → Real) (G Ginv : (Fin (1 + 1) → Idx) → Real)
    (hinv : ∀ c e : Idx,
      (∑ l : Idx, G (Fin.snoc (fun _ : Fin 1 => l) c) * Ginv (Fin.snoc (fun _ : Fin 1 => e) l)) =
        if c = e then 1 else 0) :
    compL2 T ≤ compL2 (contrTail T G) * compL2 Ginv := by
  calc compL2 T = compL2 (contrTail (contrTail T G) Ginv) := by
        rw [contrTail_contrTail_inv T G Ginv hinv]
    _ ≤ compL2 (contrTail T G) * compL2 Ginv := compL2_contrTail_le _ _












omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1_abstract {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    {p : ℕ} (C0 KR K : Real) (m : ℕ) :
    ∃ C, 0 ≤ C ∧
      ∀ (g : M → (Fin (1 + 1) → Idx) → Real),
        (∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u) →
      ∀ (Ginv : M → (Fin (1 + 1) → Idx) → Real)
        (A : M → (Fin (p + 1) → Idx) → Real),
        (∀ k : Fin (p + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
        (∀ x ∈ u, ∀ c e : Idx,
          (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
            Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0) →
        (∀ x ∈ u, compL2 (Ginv x) ≤ C0) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m →
          compL2 (iterCovComp (I := I) frame chr g j x) ≤ K) →
        (∀ x ∈ u, ∀ m', m' ≤ m →
          compL2 (iterCovComp (I := I) frame chr (fun z => contrTail (A z) (g z)) m' x) ≤
            KR * compL2 (iterCovComp (I := I) frame chr g (m' + 1) x)) →
        ∀ x ∈ u,
          compL2 (iterCovCompU (I := I) frame chr A m x) ≤
            C * (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    classical
    have hK'0 : (0 : Real) ≤ max K 0 := le_max_right K 0
    have hKR0 : (0 : Real) ≤ max KR 0 := le_max_right KR 0

    have hCc := fun c (hc : c < m) => ih c hc
    choose! Cc hCc0 hCcB using hCc

    refine ⟨max C0 0 * (max KR 0 + ∑ c ∈ Finset.range m,
        (m.choose c : Real) * (Cc c * (1 + max K 0)) * max K 0), ?_, ?_⟩
    · refine mul_nonneg (le_max_right C0 0) ?_
      have : (0 : Real) ≤ ∑ c ∈ Finset.range m,
          (m.choose c : Real) * (Cc c * (1 + max K 0)) * max K 0 :=
        Finset.sum_nonneg fun c hc =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (hCc0 c (Finset.mem_range.mp hc)) (by linarith))) hK'0
      linarith
    intro g hg Ginv A hA hinv hGinv hK hrelB x hx
    set S := ∑ c ∈ Finset.range m,
      (m.choose c : Real) * (Cc c * (1 + max K 0)) * max K 0 with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun c hc =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (hCc0 c (Finset.mem_range.mp hc)) (by linarith))) hK'0
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
          compL2 (iterCovComp (I := I) frame chr g (m - c) x)) ≤ S := by
      refine Finset.sum_le_sum fun c hc => ?_
      have hc' := Finset.mem_range.mp hc
      have hgc1 : compL2 (iterCovComp (I := I) frame chr g (c + 1) x) ≤ max K 0 :=
        le_trans (hK x hx (c + 1) (by omega) (by omega)) (le_max_left K 0)
      have hAc : compL2 (iterCovCompU (I := I) frame chr A c x) ≤ Cc c * (1 + max K 0) := by
        refine le_trans (hCcB c hc' g hg Ginv A hA hinv hGinv
          (fun x' hx' j h1 h2 => hK x' hx' j h1 (by omega))
          (fun x' hx' m' h' => hrelB x' hx' m' (by omega)) x hx) ?_
        exact mul_le_mul_of_nonneg_left (by linarith) (hCc0 c hc')
      have hgmc : compL2 (iterCovComp (I := I) frame chr g (m - c) x) ≤ max K 0 :=
        le_trans (hK x hx (m - c) (by omega) (by omega)) (le_max_left K 0)
      calc (m.choose c : Real) * compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)
          ≤ (m.choose c : Real) * (Cc c * (1 + max K 0)) *
              compL2 (iterCovComp (I := I) frame chr g (m - c) x) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hAc (Nat.cast_nonneg _)) (compL2_nonneg _)
        _ ≤ (m.choose c : Real) * (Cc c * (1 + max K 0)) * max K 0 :=
            mul_le_mul_of_nonneg_left hgmc
              (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (hCc0 c hc') (by linarith)))

    have hbr : max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
          (∑ c ∈ Finset.range m, (m.choose c : Real) *
            compL2 (iterCovCompU (I := I) frame chr A c x) *
            compL2 (iterCovComp (I := I) frame chr g (m - c) x)) ≤
        (max KR 0 + S) * (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
      nlinarith [hsum, mul_nonneg hS0 hgm1]
    have hbr0 : (0 : Real) ≤
        max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
        ∑ c ∈ Finset.range m, (m.choose c : Real) *
          compL2 (iterCovCompU (I := I) frame chr A c x) *
          compL2 (iterCovComp (I := I) frame chr g (m - c) x) := by
      refine add_nonneg (mul_nonneg hKR0 hgm1) (Finset.sum_nonneg fun c _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (compL2_nonneg _)) (compL2_nonneg _))
    have hGx : compL2 (Ginv x) ≤ max C0 0 := le_trans (hGinv x hx) (le_max_left C0 0)
    calc compL2 (iterCovCompU (I := I) frame chr A m x)
        ≤ compL2 (Ginv x) *
            (max KR 0 * compL2 (iterCovComp (I := I) frame chr g (m + 1) x) +
            ∑ c ∈ Finset.range m, (m.choose c : Real) *
              compL2 (iterCovCompU (I := I) frame chr A c x) *
              compL2 (iterCovComp (I := I) frame chr g (m - c) x)) := hcore
      _ ≤ max C0 0 * ((max KR 0 + S) *
            (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x))) :=
          mul_le_mul hGx hbr hbr0 (le_max_right C0 0)
      _ = max C0 0 * (max KR 0 + S) *
            (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by ring









omit [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] in
theorem claim1 {u : Set M} (hu : IsOpen u)
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr : M → Idx → Idx → Idx → Real)
    (hframe : ∀ d : Idx, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (frame d y)) u)
    (hchr : ∀ d i j : Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => chr y d i j) u)
    (c₁ c₂ c₃ : Real) (P₁ P₂ P₃ : Fin 3 ≃ Fin 3)
    (C0 K : Real) (m : ℕ) :
    ∃ C, 0 ≤ C ∧
      ∀ (g : M → (Fin (1 + 1) → Idx) → Real),
        (∀ k : Fin (1 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => g y k) u) →
      ∀ (Ginv : M → (Fin (1 + 1) → Idx) → Real)
        (A : M → (Fin (2 + 1) → Idx) → Real),
        (∀ k : Fin (2 + 1) → Idx, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun y => A y k) u) →
        (∀ x ∈ u, ∀ c e : Idx,
          (∑ l : Idx, g x (Fin.snoc (fun _ : Fin 1 => l) c) *
            Ginv x (Fin.snoc (fun _ : Fin 1 => e) l)) = if c = e then 1 else 0) →
        (∀ y ∈ u, contrTail (A y) (g y) =
          fun idx : Fin 3 → Idx =>
            c₁ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₁ j)) +
            (c₂ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₂ j)) +
              c₃ * iterCovComp (I := I) frame chr g 1 y (fun j => idx (P₃ j)))) →
        (∀ x ∈ u, compL2 (Ginv x) ≤ C0) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ m →
          compL2 (iterCovComp (I := I) frame chr g j x) ≤ K) →
        ∀ x ∈ u,
          compL2 (iterCovCompU (I := I) frame chr A m x) ≤
            C * (1 + compL2 (iterCovComp (I := I) frame chr g (m + 1) x)) := by
  obtain ⟨C, hC0, hCb⟩ := claim1_abstract (p := 2) hu frame chr hframe hchr C0
    (|c₁| + |c₂| + |c₃|) K m
  refine ⟨C, hC0, ?_⟩
  intro g hg Ginv A hA hinv hkoszul hGinv hK
  refine hCb g hg Ginv A hA hinv hGinv hK ?_
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

end DifferentialGeometry.PDE.RicciFlow
