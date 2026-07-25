import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFrameInvariant
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false













































































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]








section OrthonormalCollapse

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]










omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem inner0S_orthoBasis_eq_compContract
    [Module.Finite ℝ E]
    (g : SmoothMetric_gen I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A B =
      ∑ m : Fin s → Idx,
        tensor0SComponent (I := I) A (fun i => basis i) m *
          tensor0SComponent (I := I) B (fun i => basis i) m := by
  classical
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx))
    (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth) A B]
  rw [coordInner0S_identity_eq_sum (I := I) (x := x) s A B basis]

end OrthonormalCollapse














section RicReactionCollapse

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]










theorem sum_delta_erase_slot_eq {s : ℕ}
    (I0 : Fin s → Idx) (b : Fin s) (G : (Fin s → Idx) → Real) :
    (∑ J0 : Fin s → Idx,
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 a) (J0 a)) * G J0) =
      ∑ e : Idx, G (Function.update I0 b e) := by
  classical

  have hinj : Function.Injective (fun e : Idx => Function.update I0 b e) := by
    intro e e' he
    have := congrFun he b
    simpa [Function.update_self] using this


  have himg :
      (∑ e : Idx, G (Function.update I0 b e)) =
        ∑ J0 ∈ (Finset.univ : Finset Idx).image
            (fun e : Idx => Function.update I0 b e),
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) * G J0 := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_congr rfl fun e _ => ?_

    have hprod :
        (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
            identityInvMetric (Idx := Idx) (I0 a) (Function.update I0 b e a)) = 1 := by
      refine Finset.prod_eq_one fun a ha => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      rw [identityInvMetric_apply_self]
    rw [hprod, one_mul]
  rw [himg]

  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro J0 _ hJ0

  have hne : J0 ≠ Function.update I0 b (J0 b) := by
    intro h
    exact hJ0 (Finset.mem_image.mpr ⟨J0 b, Finset.mem_univ _, h.symm⟩)

  have hsome : ∃ a : Fin s, a ≠ b ∧ I0 a ≠ J0 a := by
    by_contra hnone

    apply hne
    funext a
    by_cases hab : a = b
    · subst hab; rw [Function.update_self]
    · rw [Function.update_of_ne hab]
      by_contra hcon
      exact hnone ⟨a, hab, fun h => hcon h.symm⟩
  obtain ⟨a, hab, hdis⟩ := hsome
  refine mul_eq_zero_of_left ?_ _
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩) ?_
  rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hdis]









def ricStarArray {s : ℕ}
    (ric : Idx → Idx → Real) (cB : (Fin s → Idx) → Real) :
    (Fin s → Idx) → Real :=
  fun I0 => ∑ b : Fin s, ∑ e : Idx, ric (I0 b) e * cB (Function.update I0 b e)












omit [DecidableEq Idx] in
theorem abs_ricStarArray_le {s : ℕ}
    (ric : Idx → Idx → Real) (cB : (Fin s → Idx) → Real)
    (Rbnd : Real) (hRbnd_nonneg : (0 : Real) ≤ Rbnd)
    (hRbnd : ∀ p q : Idx, |ric p q| ≤ Rbnd)
    (I0 : Fin s → Idx) :
    |ricStarArray ric cB I0| ≤
      (s : Real) * (Fintype.card Idx : Real) * Rbnd *
        Real.sqrt (compNormSqMulti cB) := by
  classical
  have hNB : (0 : Real) ≤ Real.sqrt (compNormSqMulti cB) := Real.sqrt_nonneg _
  unfold ricStarArray

  have hstep :
      |∑ b : Fin s, ∑ e : Idx, ric (I0 b) e * cB (Function.update I0 b e)| ≤
        ∑ b : Fin s, ∑ e : Idx, Rbnd * Real.sqrt (compNormSqMulti cB) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun e _ => ?_
    rw [abs_mul]
    exact mul_le_mul (hRbnd (I0 b) e)
      (abs_le_sqrt_compNormSqMulti cB (Function.update I0 b e))
      (abs_nonneg _) hRbnd_nonneg
  refine le_trans hstep ?_

  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  rw [show ((Fintype.card Idx : Real) * (Rbnd * Real.sqrt (compNormSqMulti cB))) =
    (Fintype.card Idx : Real) * Rbnd * Real.sqrt (compNormSqMulti cB) from by ring]

  rw [show ((s : Real) *
        ((Fintype.card Idx : Real) * Rbnd * Real.sqrt (compNormSqMulti cB))) =
      (s : Real) * (Fintype.card Idx : Real) * Rbnd *
        Real.sqrt (compNormSqMulti cB) from by ring]









theorem ricReactionContract_delta_eq_compContract {s : ℕ}
    (ric : Idx → Idx → Real) (cA cB : (Fin s → Idx) → Real) :
    ricReactionContract (identityInvMetric (Idx := Idx)) ric cA cB =
      2 * ∑ I0 : Fin s → Idx, cA I0 * ricStarArray ric cB I0 := by
  classical
  unfold ricReactionContract ricStarArray
  congr 1

  refine Finset.sum_congr rfl fun I0 _ => ?_


  have hric : ∀ (J0 : Fin s → Idx) (b : Fin s),
      (∑ p : Idx, ∑ q : Idx,
          identityInvMetric (Idx := Idx) (I0 b) p *
            identityInvMetric (Idx := Idx) (J0 b) q * ric p q) =
        ric (I0 b) (J0 b) := by
    intro J0 b
    rw [Finset.sum_eq_single (I0 b)]
    · rw [Finset.sum_eq_single (J0 b)]
      · rw [identityInvMetric_apply_self, identityInvMetric_apply_self]; ring
      · intro q _ hq
        rw [show identityInvMetric (Idx := Idx) (J0 b) q = 0 from
          diagonalInvMetric_eq_zero_of_ne (fun h => hq h.symm)]
        ring
      · intro h; exact absurd (Finset.mem_univ (J0 b)) h
    · intro p _ hp

      refine Finset.sum_eq_zero fun q _ => ?_
      rw [show identityInvMetric (Idx := Idx) (I0 b) p = 0 from
        diagonalInvMetric_eq_zero_of_ne (fun h => hp h.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ (I0 b)) h

  have hstep1 :
      (∑ J0 : Fin s → Idx,
          (∑ b : Fin s,
              (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                  identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
                (∑ p : Idx, ∑ q : Idx,
                  identityInvMetric (Idx := Idx) (I0 b) p *
                    identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) *
            cA I0 * cB J0) =
        ∑ b : Fin s, ∑ J0 : Fin s → Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
            (ric (I0 b) (J0 b) * cB J0) * cA I0 := by

    have hdist :
        (∑ J0 : Fin s → Idx,
            (∑ b : Fin s,
                (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                    identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
                  (∑ p : Idx, ∑ q : Idx,
                    identityInvMetric (Idx := Idx) (I0 b) p *
                      identityInvMetric (Idx := Idx) (J0 b) q * ric p q)) *
              cA I0 * cB J0) =
          ∑ J0 : Fin s → Idx, ∑ b : Fin s,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
              (ric (I0 b) (J0 b) * cB J0) * cA I0 := by
      refine Finset.sum_congr rfl fun J0 _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hric J0 b]
      ring
    rw [hdist, Finset.sum_comm]
  rw [hstep1]

  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_

  have hstep2 :
      (∑ J0 : Fin s → Idx,
          (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
              identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
            (ric (I0 b) (J0 b) * cB J0) * cA I0) =
        cA I0 *
          ∑ J0 : Fin s → Idx,
            (∏ a ∈ (Finset.univ : Finset (Fin s)).erase b,
                identityInvMetric (Idx := Idx) (I0 a) (J0 a)) *
              (ric (I0 b) (J0 b) * cB J0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J0 _ => ?_
    ring
  rw [hstep2, sum_delta_erase_slot_eq (Idx := Idx) I0 b
    (fun J0 : Fin s → Idx => ric (I0 b) (J0 b) * cB J0)]

  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Function.update_self]

end RicReactionCollapse



















section ReactionBridge

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]








def combinedStarArray {s : ℕ}
    (ric : Idx → Idx → Real)
    (rmComp residualComp : (Fin s → Idx) → Real) :
    (Fin s → Idx) → Real :=
  fun m => ricStarArray ric rmComp m + residualComp m


















omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04Reaction_orthoBasis_eq_compContract
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (basis : (x : M) → Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real → M → Idx → Idx → Real)
    (ric : Real → M → Idx → Idx → Real)
    (Tdot : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (4 + k) x)
    (t : Real) (x : M)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis x i) (basis x j) =
        if i = j then (1 : Real) else 0)
    (hgInv : gInv t x = identityInvMetric (Idx := Idx)) :
    nablaKRm04ReactionIntrinsic (I := I) S k basis gInv ric Tdot t x =
      2 * ∑ m : Fin (4 + k) → Idx,
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis x i) m *
          combinedStarArray (ric t x)
            (fun I0 : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
                (fun i => basis x i) I0)
            (fun m : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I)
                (Tdot t x -
                  metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
                    (nablaKRm04Field (I := I) S t (k + 2) x))
                (fun i => basis x i) m)
            m := by
  classical



  rw [nablaKRm04ReactionIntrinsic]
  set rmC : (Fin (4 + k) → Idx) → Real :=
    fun I0 => tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
      (fun i => basis x i) I0 with hrmC
  set resid : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (4 + k) x :=
    Tdot t x -
      metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
        (nablaKRm04Field (I := I) S t (k + 2) x) with hresid
  set residC : (Fin (4 + k) → Idx) → Real :=
    fun m => tensor0SComponent (I := I) resid (fun i => basis x i) m with hresidC


  rw [hgInv]
  rw [ricReactionContract_delta_eq_compContract (Idx := Idx) (ric t x) rmC rmC]

  rw [inner0S_orthoBasis_eq_compContract (I := I) (S.base.metric t) (basis x) horth
    resid (nablaKRm04Field (I := I) S t k x)]



  have hcombine :
      (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
          (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        ∑ m : Fin (4 + k) → Idx,
          rmC m * combinedStarArray (ric t x) rmC residC m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold combinedStarArray
    ring

  rw [show
      2 * (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
          2 * (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        2 * ((∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray (ric t x) rmC I0) +
              (∑ m : Fin (4 + k) → Idx, residC m * rmC m)) from by ring]
  rw [hcombine]



omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKReactionAt_eq
    [Module.Finite ℝ E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x)
    (horth : ∀ i j : Idx,
      (S.base.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (hgInv : gInv = identityInvMetric (Idx := Idx)) :
    nablaKReactionAt (I := I) S k t x basis gInv ric Tdot =
      2 * ∑ m : Fin (4 + k) → Idx,
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis i) m *
          combinedStarArray ric
            (fun I0 : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
                (fun i => basis i) I0)
            (fun m : Fin (4 + k) → Idx =>
              tensor0SComponent (I := I)
                (Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
                    (nablaKRm04Field (I := I) S t (k + 2) x))
                (fun i => basis i) m)
            m := by
  classical
  rw [nablaKReactionAt]
  set rmC : (Fin (4 + k) → Idx) → Real :=
    fun I0 => tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
      (fun i => basis i) I0 with hrmC
  set resid : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x :=
    Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
      (nablaKRm04Field (I := I) S t (k + 2) x) with hresid
  set residC : (Fin (4 + k) → Idx) → Real :=
    fun m => tensor0SComponent (I := I) resid (fun i => basis i) m with hresidC
  rw [hgInv]
  rw [ricReactionContract_delta_eq_compContract (Idx := Idx) ric rmC rmC]
  rw [inner0S_orthoBasis_eq_compContract (I := I) (S.base.metric t) basis horth
    resid (nablaKRm04Field (I := I) S t k x)]
  have hcombine :
      (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
          (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        ∑ m : Fin (4 + k) → Idx,
          rmC m * combinedStarArray ric rmC residC m := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold combinedStarArray
    ring
  rw [show
      2 * (∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
          2 * (∑ m : Fin (4 + k) → Idx, residC m * rmC m) =
        2 * ((∑ I0 : Fin (4 + k) → Idx, rmC I0 * ricStarArray ric rmC I0) +
              (∑ m : Fin (4 + k) → Idx, residC m * rmC m)) from by ring]
  rw [hcombine]

end ReactionBridge












































































end DifferentialGeometry.PDE.RicciFlow
