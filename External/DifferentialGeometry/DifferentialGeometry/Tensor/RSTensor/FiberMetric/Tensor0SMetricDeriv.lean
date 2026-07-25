import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option linter.style.longLine false












































namespace Tensor0SBundle

noncomputable section

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]








section Coord

variable {Idx : Type*} [Fintype Idx]




def coordContract {s : Nat}
    (gInv : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∏ a : Fin s, gInv (I0 a) (J0 a)) * cA I0 * cB J0






def coordContractDt {s : Nat}
    (gInv gInvDt : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) : Real :=
  ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∑ b : Fin s,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
          gInvDt (I0 b) (J0 b)) *
      cA I0 * cB J0












theorem hasDerivWithinAt_coordContract {s : Nat}
    {u : Set Real} {t : Real}
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt : Idx -> Idx -> Real)
    (cA cB : Real -> (Fin s -> Idx) -> Real)
    (cAdt cBdt : (Fin s -> Idx) -> Real)
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hcA : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt (fun r : Real => cA r I0) (cAdt I0) u t)
    (hcB : ∀ J0 : Fin s -> Idx,
      HasDerivWithinAt (fun r : Real => cB r J0) (cBdt J0) u t) :
    HasDerivWithinAt
      (fun r : Real => coordContract (gInv r) (cA r) (cB r))
      (coordContractDt (gInv t) gInvDt (cA t) (cB t) +
        coordContract (gInv t) cAdt (cB t) +
        coordContract (gInv t) (cA t) cBdt)
      u t := by
  classical
  unfold coordContract coordContractDt



  rw [show
      (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv t (I0 a) (J0 a)) *
                gInvDt (I0 b) (J0 b)) *
            cA t I0 * cB t J0) +
        (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, gInv t (I0 a) (J0 a)) * cAdt I0 * cB t J0) +
        (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
            (∏ a : Fin s, gInv t (I0 a) (J0 a)) * cA t I0 * cBdt J0) =
      ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
        ((∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv t (I0 a) (J0 a)) *
                gInvDt (I0 b) (J0 b)) *
            cA t I0 * cB t J0 +
          ((∏ a : Fin s, gInv t (I0 a) (J0 a)) * cAdt I0 * cB t J0 +
            (∏ a : Fin s, gInv t (I0 a) (J0 a)) * cA t I0 * cBdt J0)) by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    ring]
  refine HasDerivWithinAt.fun_sum ?_
  intro I0 _
  refine HasDerivWithinAt.fun_sum ?_
  intro J0 _


  have hP :
      HasDerivWithinAt
        (fun r : Real => ∏ a : Fin s, gInv r (I0 a) (J0 a))
        (∑ b : Fin s,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv t (I0 a) (J0 a)) *
            gInvDt (I0 b) (J0 b))
        u t := by
    have h :=
      HasDerivWithinAt.fun_finset_prod
        (u := (Finset.univ : Finset (Fin s)))
        (f := fun a r => gInv r (I0 a) (J0 a))
        (f' := fun a => gInvDt (I0 a) (J0 a))
        (x := t) (s := u)
        (fun a _ => hgInv (I0 a) (J0 a))
    simpa [smul_eq_mul, mul_comm] using h

  have hprodA := hP.mul (hcA I0)
  have hfull := hprodA.mul (hcB J0)
  refine hfull.congr_deriv ?_


  simp only [Pi.mul_apply]
  ring



omit [FiniteDimensional ℝ E] in
theorem coordContract_eq_coordInner0S {s : Nat} {x : M}
    (gInv : Idx -> Idx -> Real)
    (A B : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x)) :
    coordContract gInv
        (fun I0 => tensor0SComponent (I := I) A (fun i => basis i) I0)
        (fun J0 => tensor0SComponent (I := I) B (fun i => basis i) J0) =
      coordInner0S (I := I) (x := x) s gInv A B basis := by
  rfl


















def ricReactionContract {s : Nat}
    (gInv ric : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real) : Real :=
  2 * ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
    (∑ b : Fin s,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
          (∑ p : Idx, ∑ q : Idx, gInv (I0 b) p * gInv (J0 b) q * ric p q)) *
      cA I0 * cB J0







theorem coordContractDt_eq_ricReactionContract {s : Nat}
    (gInv gInvDt ric : Idx -> Idx -> Real)
    (cA cB : (Fin s -> Idx) -> Real)
    (hflow : ∀ i j : Idx,
      gInvDt i j = 2 * (∑ p : Idx, ∑ q : Idx, gInv i p * gInv j q * ric p q)) :
    coordContractDt gInv gInvDt cA cB =
      ricReactionContract gInv ric cA cB := by
  classical
  unfold coordContractDt ricReactionContract


  have hsub :
      (∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          (∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                gInvDt (I0 b) (J0 b)) *
            cA I0 * cB J0) =
        ∑ I0 : Fin s -> Idx, ∑ J0 : Fin s -> Idx,
          2 *
            ((∑ b : Fin s,
                (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                  (∑ p : Idx, ∑ q : Idx, gInv (I0 b) p * gInv (J0 b) q * ric p q)) *
              cA I0 * cB J0) := by
    refine Finset.sum_congr rfl fun I0 _ => ?_
    refine Finset.sum_congr rfl fun J0 _ => ?_

    rw [show
        (∑ b : Fin s,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
              gInvDt (I0 b) (J0 b)) =
          ∑ b : Fin s,
            2 *
              ((∏ a ∈ (Finset.univ : Finset (Fin s)).erase b, gInv (I0 a) (J0 a)) *
                (∑ p : Idx, ∑ q : Idx, gInv (I0 b) p * gInv (J0 b) q * ric p q)) from ?_]
    · rw [← Finset.mul_sum]; ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hflow (I0 b) (J0 b)]; ring
  rw [hsub, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I0 _ => ?_
  rw [Finset.mul_sum]

private theorem sum_one_idx {Idx : Type*} [Fintype Idx]
    {A : Type*} [AddCommMonoid A]
    (F : (Fin 1 -> Idx) -> A) :
    (∑ I0 : Fin 1 -> Idx, F I0) =
      ∑ i : Idx, F (fun _ : Fin 1 => i) := by
  classical
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Idx)
    F (fun i : Idx => F (fun _ : Fin 1 => i))]
  intro I0
  congr 1
  funext a
  simpa [Equiv.funUnique] using congrArg I0 (Subsingleton.elim a (0 : Fin 1))

omit [FiniteDimensional ℝ E] in
private theorem eval2_sum_left {Idx : Type*} [Fintype Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Q : Tensor0SSpace 2 I x) (c : Idx -> Real)
    (Y : TangentSpace I x) :
    Q (fun q : Fin 2 =>
        if q = 0 then (∑ i : Idx, c i • basis i) else Y) =
      ∑ i : Idx, c i *
        Q (fun q : Fin 2 => if q = 0 then basis i else Y) := by
  classical
  let base : Fin 2 -> TangentSpace I x := fun q =>
    if q = 0 then (∑ i : Idx, c i • basis i) else Y
  have hbase :
      Function.update base (0 : Fin 2) (∑ i : Idx, c i • basis i) = base := by
    funext q
    fin_cases q <;> simp [base]
  have hupdate (Z : TangentSpace I x) :
      Function.update base (0 : Fin 2) Z =
        fun q : Fin 2 => if q = 0 then Z else Y := by
    funext q
    fin_cases q <;> simp [base]
  have hsum := Q.toMultilinearMap.map_update_sum
    (Finset.univ : Finset Idx) (0 : Fin 2)
    (fun i : Idx => c i • basis i) base
  have hsum' :
      Q (Function.update base (0 : Fin 2) (∑ i : Idx, c i • basis i)) =
        ∑ i : Idx, c i * Q (Function.update base (0 : Fin 2) (basis i)) := by
    simpa using hsum
  change Q base = _
  rw [← hbase]
  calc
    Q (Function.update base (0 : Fin 2) (∑ i : Idx, c i • basis i)) =
        ∑ i : Idx, c i * Q (Function.update base (0 : Fin 2) (basis i)) := hsum'
    _ = ∑ i : Idx, c i *
          Q (fun q : Fin 2 => if q = 0 then basis i else Y) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hupdate]

omit [FiniteDimensional ℝ E] in
private theorem eval2_sum_right {Idx : Type*} [Fintype Idx] {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Q : Tensor0SSpace 2 I x) (X : TangentSpace I x)
    (c : Idx -> Real) :
    Q (fun q : Fin 2 =>
        if q = 0 then X else (∑ i : Idx, c i • basis i)) =
      ∑ i : Idx, c i *
        Q (fun q : Fin 2 => if q = 0 then X else basis i) := by
  classical
  let base : Fin 2 -> TangentSpace I x := fun q =>
    if q = 0 then X else (∑ i : Idx, c i • basis i)
  have hbase :
      Function.update base (1 : Fin 2) (∑ i : Idx, c i • basis i) = base := by
    funext q
    fin_cases q <;> simp [base]
  have hupdate (Z : TangentSpace I x) :
      Function.update base (1 : Fin 2) Z =
        fun q : Fin 2 => if q = 0 then X else Z := by
    funext q
    fin_cases q <;> simp [base]
  have hsum := Q.toMultilinearMap.map_update_sum
    (Finset.univ : Finset Idx) (1 : Fin 2)
    (fun i : Idx => c i • basis i) base
  have hsum' :
      Q (Function.update base (1 : Fin 2) (∑ i : Idx, c i • basis i)) =
        ∑ i : Idx, c i * Q (Function.update base (1 : Fin 2) (basis i)) := by
    simpa using hsum
  change Q base = _
  rw [← hbase]
  calc
    Q (Function.update base (1 : Fin 2) (∑ i : Idx, c i • basis i)) =
        ∑ i : Idx, c i * Q (Function.update base (1 : Fin 2) (basis i)) := hsum'
    _ = ∑ i : Idx, c i *
          Q (fun q : Fin 2 => if q = 0 then X else basis i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hupdate]



theorem ricReact_one {x : M}
    (g : SmoothMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Q : Tensor0SSpace 2 I x) (A B : Tensor0SSpace 1 I x) :
    ricReactionContract
        (basisInvMetric (I := I) g x basis)
        (fun i j => Q (fun a : Fin 2 => if a = 0 then basis i else basis j))
        (fun I0 => tensor0SComponent (I := I) A (fun i => basis i) I0)
        (fun J0 => tensor0SComponent (I := I) B (fun i => basis i) J0) =
      2 * Q (fun a : Fin 2 =>
        if a = 0 then cotangentSharp (I := I) g x A
        else cotangentSharp (I := I) g x B) := by
  classical
  let gInv : Idx -> Idx -> Real := basisInvMetric (I := I) g x basis
  let a : Idx -> Real := fun i => cotangentToDual (I := I) A (basis i)
  let b : Idx -> Real := fun j => cotangentToDual (I := I) B (basis j)
  let q : Idx -> Idx -> Real := fun i j =>
    Q (fun k : Fin 2 => if k = 0 then basis i else basis j)
  have hreact :
      ricReactionContract gInv q
          (fun I0 => tensor0SComponent (I := I) A (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) B (fun i => basis i) J0) =
        2 * ∑ i : Idx, ∑ j : Idx,
          (∑ p : Idx, ∑ r : Idx, gInv i p * gInv j r * q p r) *
            a i * b j := by
    unfold ricReactionContract
    rw [sum_one_idx]
    refine congrArg (fun z : Real => 2 * z) ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_one_idx]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [tensor0SComponent, cotangentToDual_apply, a, b]
  have hsharpA :
      cotangentSharp (I := I) g x A =
        ∑ p : Idx, (∑ i : Idx, gInv p i * a i) • basis p := by
    simpa [gInv, a] using
      (cotangentSharp_eq_sum_inv (I := I) g x basis gInv
        (by simpa [gInv] using basisInvMetric_real (I := I) g x basis) A)
  have hsharpB :
      cotangentSharp (I := I) g x B =
        ∑ r : Idx, (∑ j : Idx, gInv r j * b j) • basis r := by
    simpa [gInv, b] using
      (cotangentSharp_eq_sum_inv (I := I) g x basis gInv
        (by simpa [gInv] using basisInvMetric_real (I := I) g x basis) B)
  have hswap
      (F : Idx -> Idx -> Idx -> Idx -> Real) :
      (∑ i : Idx, ∑ j : Idx, ∑ p : Idx, ∑ r : Idx, F i j p r) =
        ∑ p : Idx, ∑ r : Idx, ∑ i : Idx, ∑ j : Idx, F i j p r := by
    calc
      (∑ i : Idx, ∑ j : Idx, ∑ p : Idx, ∑ r : Idx, F i j p r) =
          ∑ i : Idx, ∑ p : Idx, ∑ j : Idx, ∑ r : Idx, F i j p r := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ p : Idx, ∑ i : Idx, ∑ j : Idx, ∑ r : Idx, F i j p r := by
            rw [Finset.sum_comm]
      _ = ∑ p : Idx, ∑ i : Idx, ∑ r : Idx, ∑ j : Idx, F i j p r := by
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ p : Idx, ∑ r : Idx, ∑ i : Idx, ∑ j : Idx, F i j p r := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_comm]
  rw [show basisInvMetric (I := I) g x basis = gInv by rfl,
    show (fun i j => Q (fun a : Fin 2 => if a = 0 then basis i else basis j)) = q by rfl]
  rw [hreact, hsharpA, hsharpB]
  rw [eval2_sum_left]
  simp_rw [eval2_sum_right]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [hswap]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [gInv, q]
  rw [basisInvMetric_symm (I := I) g x basis i p,
    basisInvMetric_symm (I := I) g x basis j r]
  ring

end Coord











section Intrinsic

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]





private noncomputable def bmat :
    (Idx → Idx → Real) →L[Real]
      ((Idx → Real) →L[Real] (Idx → Real)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        LinearMap.toContinuousLinearMap
          { toFun := fun v i => ∑ j : Idx, A i j * v j
            map_add' := by
              intro v w
              ext i
              simp only [Pi.add_apply]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
            map_smul' := by
              intro c v
              ext i
              simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring }
      map_add' := by
        intro A B
        ext v i
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c A
        ext v i
        change (∑ j : Idx, (c * A i j) * v j) =
          c * ∑ j : Idx, A i j * v j
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring }

omit [DecidableEq Idx] in
@[simp] private theorem bmat_apply
    (A : Matrix Idx Idx Real) (v : Idx → Real) (i : Idx) :
    bmat A v i = ∑ j : Idx, A i j * v j := by
  rfl

@[simp] private theorem bmat_single
    (A : Matrix Idx Idx Real) (i j : Idx) :
    bmat A (Pi.single j (1 : Real)) i = A i j := by
  classical
  rw [bmat_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [Pi.single_eq_of_ne hbj]
  · simp

private theorem bmat_inv_entry
    (A D : Matrix Idx Idx Real) (i j : Idx) :
    ((-(bmat A * bmat D * bmat A))
        (Pi.single j (1 : Real))) i =
      -(∑ a : Idx, ∑ b : Idx, A i a * D a b * A b j) := by
  change -(bmat A (bmat D (bmat A (Pi.single j (1 : Real)))) i) = _
  rw [bmat_apply]
  apply congrArg (fun z : Real => -z)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [bmat_apply]
  simp_rw [bmat_single]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

omit [DecidableEq Idx] in



theorem basisInv_time {x : M} {t : Real}
    (g : Real → SmoothMetric I M)
    (gdot : Idx → Idx → Real)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hg : ∀ i j : Idx,
      HasDerivAt
        (fun r : Real => (g r).inner x (basis i) (basis j))
        (gdot i j) t)
    (i j : Idx) :
    HasDerivAt
      (fun r : Real => basisInvMetric (I := I) (g r) x basis i j)
      (-(∑ a : Idx, ∑ b : Idx,
        basisInvMetric (I := I) (g t) x basis i a * gdot a b *
          basisInvMetric (I := I) (g t) x basis b j))
      t := by
  classical
  let G : Real → Idx → Idx → Real := fun r a b =>
    (g r).inner x (basis a) (basis b)
  let B : Real → Idx → Idx → Real := fun r =>
    basisInvMetric (I := I) (g r) x basis
  have hG : HasDerivAt G gdot t := by
    exact hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun b => hg a b
  have hGram :
      HasDerivAt (fun r : Real => bmat (G r)) (bmat gdot) t := by
    simpa [Function.comp_def] using
      (bmat (Idx := Idx)).hasFDerivAt.comp_hasDerivAt (f := G) t hG
  have hleft (r : Real) :
      bmat (G r) ∘L bmat (B r) =
        ContinuousLinearMap.id Real (Idx → Real) := by
    ext v a
    simp only [ContinuousLinearMap.comp_apply, bmat_apply,
      ContinuousLinearMap.id_apply]
    calc
      (∑ k : Idx, G r a k * ∑ b : Idx, B r k b * v b) =
          ∑ k : Idx, ∑ b : Idx, G r a k * (B r k b * v b) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ b : Idx, ∑ k : Idx, G r a k * (B r k b * v b) :=
        Finset.sum_comm
      _ = ∑ b : Idx, (∑ k : Idx, G r a k * B r k b) * v b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      _ = ∑ b : Idx, (if a = b then 1 else 0) * v b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [show (∑ k : Idx, G r a k * B r k b) =
            (if a = b then 1 else 0) by
          simpa [G, B] using
            ((basisInvMetric_real (I := I) (g r) x basis a b).2)]
      _ = v a := by simp
  have hright (r : Real) :
      bmat (B r) ∘L bmat (G r) =
        ContinuousLinearMap.id Real (Idx → Real) := by
    ext v a
    simp only [ContinuousLinearMap.comp_apply, bmat_apply,
      ContinuousLinearMap.id_apply]
    calc
      (∑ k : Idx, B r a k * ∑ b : Idx, G r k b * v b) =
          ∑ k : Idx, ∑ b : Idx, B r a k * (G r k b * v b) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
      _ = ∑ b : Idx, ∑ k : Idx, B r a k * (G r k b * v b) :=
        Finset.sum_comm
      _ = ∑ b : Idx, (∑ k : Idx, B r a k * G r k b) * v b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      _ = ∑ b : Idx, (if a = b then 1 else 0) * v b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [show (∑ k : Idx, B r a k * G r k b) =
            (if a = b then 1 else 0) by
          simpa [G, B] using
            ((basisInvMetric_real (I := I) (g r) x basis a b).1)]
      _ = v a := by simp
  have hInvertible (r : Real) : (bmat (G r)).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (hleft r) (hright r)
  have hInvEq (r : Real) :
      ContinuousLinearMap.inverse (bmat (G r)) = bmat (B r) :=
    ContinuousLinearMap.inverse_eq (hleft r) (hright r)
  have hInvF :
      HasFDerivAt ContinuousLinearMap.inverse
        (-(ContinuousLinearMap.mulLeftRight Real
          ((Idx → Real) →L[Real] (Idx → Real))
          (bmat (G t)).inverse (bmat (G t)).inverse))
        (bmat (G t)) := by
    rcases hInvertible t with ⟨e, he⟩
    rw [← he]
    rw [← ContinuousLinearMap.ringInverse_eq_inverse]
    simpa [ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.toUnit] using
      (hasFDerivAt_ringInverse (ContinuousLinearEquiv.toUnit e))
  have hInv :
      HasDerivAt
        (fun r : Real => ContinuousLinearMap.inverse (bmat (G r)))
        ((-(ContinuousLinearMap.mulLeftRight Real
          ((Idx → Real) →L[Real] (Idx → Real))
          (bmat (G t)).inverse (bmat (G t)).inverse)) (bmat gdot))
        t := by
    simpa [Function.comp_def] using hInvF.comp_hasDerivAt t hGram
  have hB :
      HasDerivAt (fun r : Real => bmat (B r))
        ((-(ContinuousLinearMap.mulLeftRight Real
          ((Idx → Real) →L[Real] (Idx → Real))
          (bmat (G t)).inverse (bmat (G t)).inverse)) (bmat gdot))
        t := by
    exact hInv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (hInvEq r).symm)
  have hcol := hB.clm_apply
    (hasDerivAt_const t (Pi.single j (1 : Real)))
  have hentry := hasDerivAt_pi.mp hcol i
  have hentry' :
      HasDerivAt
        (fun r : Real => bmat (B r) (Pi.single j (1 : Real)) i)
        (((-(ContinuousLinearMap.mulLeftRight Real
          ((Idx → Real) →L[Real] (Idx → Real))
          (bmat (G t)).inverse (bmat (G t)).inverse)) (bmat gdot))
            (Pi.single j (1 : Real)) i)
        t := by
    simpa using hentry
  have hcanon :
      HasDerivAt (fun r : Real => B r i j)
        (((-(ContinuousLinearMap.mulLeftRight Real
          ((Idx → Real) →L[Real] (Idx → Real))
          (bmat (G t)).inverse (bmat (G t)).inverse)) (bmat gdot))
            (Pi.single j (1 : Real)) i)
        t := by
    exact hentry'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (bmat_single (B r) i j).symm)
  rw [hInvEq t] at hcanon
  simpa [B, ContinuousLinearMap.mulLeftRight_apply, bmat_inv_entry] using hcanon

























theorem hasDerivWithinAt_normSq0S_coord {s : Nat} {x : M}
    {u : Set Real} {t : Real}
    (g : Real -> SmoothMetric I M)
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt : Idx -> Idx -> Real)
    (T : Real -> Tensor0SSpace s I x)
    (Tdt : (Fin s -> Idx) -> Real)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gInv r))
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hT : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) u t) :
    HasDerivWithinAt
      (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (coordContractDt (gInv t) gInvDt
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        coordContract (gInv t) Tdt
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        coordContract (gInv t)
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0) Tdt)
      u t := by
  classical

  have hpt : ∀ r : Real,
      normSq0S (I := I) (g r) x s (T r) =
        coordContract (gInv r)
          (fun I0 => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T r) (fun i => basis i) J0) := by
    intro r
    rw [coordContract_eq_coordInner0S (I := I) (gInv r) (T r) (T r) basis]
    rw [normSq0S_eq_coord (I := I) (g r) x s basis (gInv r) (hinvAll r) (T r)]

  have hderiv :=
    hasDerivWithinAt_coordContract (s := s) (u := u) (t := t)
      (gInv := gInv) (gInvDt := gInvDt)
      (cA := fun r I0 => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
      (cB := fun r J0 => tensor0SComponent (I := I) (T r) (fun i => basis i) J0)
      (cAdt := Tdt) (cBdt := Tdt)
      hgInv hT hT

  refine hderiv.congr ?_ ?_
  · intro r _; exact hpt r
  · exact hpt t

















theorem hasDerivWithinAt_normSq0S {s : Nat} {x : M}
    {u : Set Real} {t : Real}
    (g : Real -> SmoothMetric I M)
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt : Idx -> Idx -> Real)
    (T : Real -> Tensor0SSpace s I x)
    (Tdt : (Fin s -> Idx) -> Real)
    (Tdot : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gInv r))
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hT : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) u t)
    (hTdot : ∀ I0 : Fin s -> Idx,
      tensor0SComponent (I := I) Tdot (fun i => basis i) I0 = Tdt I0) :
    HasDerivWithinAt
      (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (coordContractDt (gInv t) gInvDt
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        2 * inner0S (I := I) (g t) x s Tdot (T t))
      u t := by
  classical

  have hderiv :=
    hasDerivWithinAt_normSq0S_coord (s := s) (u := u) (t := t)
      g gInv gInvDt T Tdt basis hinvAll hgInv hT
  refine hderiv.congr_deriv ?_



  have hcompTdot :
      (fun I0 => tensor0SComponent (I := I) Tdot (fun i => basis i) I0) = Tdt := by
    funext I0; exact hTdot I0

  have hleft :
      coordContract (gInv t) Tdt
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) =
        inner0S (I := I) (g t) x s Tdot (T t) := by
    rw [← hcompTdot]
    rw [coordContract_eq_coordInner0S (I := I) (gInv t) Tdot (T t) basis]
    rw [← inner0S_eq_coord (I := I) (g t) x s basis (gInv t) (hinvAll t) Tdot (T t)]

  have hright :
      coordContract (gInv t)
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0) Tdt =
        inner0S (I := I) (g t) x s (T t) Tdot := by
    rw [← hcompTdot]
    rw [coordContract_eq_coordInner0S (I := I) (gInv t) (T t) Tdot basis]
    rw [← inner0S_eq_coord (I := I) (g t) x s basis (gInv t) (hinvAll t) (T t) Tdot]
  rw [hleft, hright]


  have hsymm :
      inner0S (I := I) (g t) x s (T t) Tdot =
        inner0S (I := I) (g t) x s Tdot (T t) := by
    unfold inner0S MetricFiberData.inner
    exact (tensor0SMetricData (I := I) (g t) x s).symm (T t) Tdot
  rw [hsymm]; ring



















theorem hasDerivWithinAt_normSq0S_ricciFlow {s : Nat} {x : M}
    {u : Set Real} {t : Real}
    (g : Real -> SmoothMetric I M)
    (gInv : Real -> Idx -> Idx -> Real)
    (gInvDt ric : Idx -> Idx -> Real)
    (T : Real -> Tensor0SSpace s I x)
    (Tdt : (Fin s -> Idx) -> Real)
    (Tdot : Tensor0SSpace s I x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinvAll : ∀ r : Real, MetricInverseInBasis (I := I) (g r) x basis (gInv r))
    (hgInv : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) u t)
    (hT : ∀ I0 : Fin s -> Idx,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (T r) (fun i => basis i) I0)
        (Tdt I0) u t)
    (hTdot : ∀ I0 : Fin s -> Idx,
      tensor0SComponent (I := I) Tdot (fun i => basis i) I0 = Tdt I0)
    (hflow : ∀ i j : Idx,
      gInvDt i j = 2 * (∑ p : Idx, ∑ q : Idx, gInv t i p * gInv t j q * ric p q)) :
    HasDerivWithinAt
      (fun r : Real => normSq0S (I := I) (g r) x s (T r))
      (ricReactionContract (gInv t) ric
          (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
          (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) +
        2 * inner0S (I := I) (g t) x s Tdot (T t))
      u t := by
  have hbase :=
    hasDerivWithinAt_normSq0S (s := s) (u := u) (t := t)
      g gInv gInvDt T Tdt Tdot basis hinvAll hgInv hT hTdot
  rw [coordContractDt_eq_ricReactionContract (gInv t) gInvDt ric
      (fun I0 => tensor0SComponent (I := I) (T t) (fun i => basis i) I0)
      (fun J0 => tensor0SComponent (I := I) (T t) (fun i => basis i) J0) hflow]
    at hbase
  exact hbase

end Intrinsic






theorem normSq_one_time {x : M} {t : Real}
    (g : Real -> SmoothMetric I M)
    (Q : Tensor0SSpace 2 I x)
    (A : Real -> Tensor0SSpace 1 I x)
    (Adot : Tensor0SSpace 1 I x)
    (hg : ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun r : Real => (g r).inner x X Y)
        ((-2 : Real) * Q (fun a : Fin 2 => if a = 0 then X else Y)) t)
    (hA : ∀ X : TangentSpace I x,
      HasDerivAt
        (fun r : Real => A r (fun _ : Fin 1 => X))
        (Adot (fun _ : Fin 1 => X)) t) :
    HasDerivAt
      (fun r : Real => normSq0S (I := I) (g r) x 1 (A r))
      (2 * Q (fun a : Fin 2 =>
          if a = 0 then cotangentSharp (I := I) (g t) x (A t)
          else cotangentSharp (I := I) (g t) x (A t)) +
        2 * inner0S (I := I) (g t) x 1 Adot (A t)) t := by
  classical
  let basis : Module.Basis
      (Fin (Module.finrank Real (TangentSpace I x))) Real (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  let gInv : Real ->
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun r =>
    basisInvMetric (I := I) (g r) x basis
  let ric :
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun i j =>
    Q (fun a : Fin 2 => if a = 0 then basis i else basis j)
  let gInvDt :
      Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real := fun i j =>
    -(∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j)
  let Tdt :
      (Fin 1 -> Fin (Module.finrank Real (TangentSpace I x))) -> Real := fun I0 =>
    tensor0SComponent (I := I) Adot (fun i => basis i) I0
  have hinvAll (r : Real) :
      MetricInverseInBasis (I := I) (g r) x basis (gInv r) := by
    simpa [gInv] using basisInvMetric_real (I := I) (g r) x basis
  have hgInv (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt (fun r : Real => gInv r i j) (gInvDt i j) Set.univ t := by
    simpa [gInv, gInvDt, ric] using
      (basisInv_time (I := I) g
        (fun p q => (-2 : Real) * ric p q) basis
        (fun p q => by simpa [ric] using hg (basis p) (basis q)) i j)
  have hT (I0 : Fin 1 -> Fin (Module.finrank Real (TangentSpace I x))) :
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I) (A r) (fun i => basis i) I0)
        (Tdt I0) Set.univ t := by
    have hslots :
        (fun a : Fin 1 => basis (I0 a)) = fun _ : Fin 1 => basis (I0 0) := by
      funext a
      exact congrArg (fun i => basis i) (congrArg I0 (Subsingleton.elim a (0 : Fin 1)))
    change HasDerivWithinAt
      (fun r : Real => A r (fun a : Fin 1 => basis (I0 a)))
      (Adot (fun a : Fin 1 => basis (I0 a))) Set.univ t
    rw [hslots]
    exact (hA (basis (I0 0))).hasDerivWithinAt
  have hTdot (I0 : Fin 1 -> Fin (Module.finrank Real (TangentSpace I x))) :
      tensor0SComponent (I := I) Adot (fun i => basis i) I0 = Tdt I0 := by
    rfl
  have hflow (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      gInvDt i j =
        2 * (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
    have hterm :
        (∑ p, ∑ q, gInv t i p * ((-2 : Real) * ric p q) * gInv t q j) =
          ∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [gInv]
      rw [basisInvMetric_symm (I := I) (g t) x basis q j]
      ring
    have hfactor :
        (∑ p, ∑ q, (-2 : Real) *
            (gInv t i p * gInv t j q * ric p q)) =
          (-2 : Real) *
            (∑ p, ∑ q, gInv t i p * gInv t j q * ric p q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    simp only [gInvDt]
    rw [hterm, hfactor]
    ring
  have hbase :=
    hasDerivWithinAt_normSq0S_ricciFlow
      (I := I) (s := 1) (u := Set.univ) (t := t)
      g gInv gInvDt ric A Tdt Adot basis hinvAll hgInv hT hTdot hflow
  have hat := hbase.hasDerivAt (by simp)
  rw [show gInv t = basisInvMetric (I := I) (g t) x basis by rfl,
    show ric = fun i j =>
      Q (fun a : Fin 2 => if a = 0 then basis i else basis j) by rfl,
    ricReact_one (I := I) (g t) basis Q (A t) (A t)] at hat
  exact hat

end

end Tensor0SBundle
