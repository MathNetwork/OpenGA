import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}









def ricciVariationFromConnectionRHSInFrame
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (∑ k : Idx, nablaGammaDt t x k k i j) -
    (∑ k : Idx, nablaGammaDt t x i k k j)







def RicciVariationFormulaInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciVariationFromConnectionRHSInFrame (M := M) nablaGammaDt
        (t : Real) x i j)
      D.carrier
      (t : Real)


def RicciVariationFormulaInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciVariationFromConnectionRHSInFrame (M := M) nablaGammaDt
          (t : Real) x i j)
        D.carrier
        (t : Real)



def RicciEvolutionEquationInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j : Idx,
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j)
        D.carrier
        (t : Real)

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
@[deprecated "use the OnLocal predicate or a pointwise frame statement instead" (since := "2026-05-22")]
theorem ricciVariationFormulaInFrameOn_of_local_cover
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nablaGammaDt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hcover : forall x : M, x ∈ u)
    (hlocal : RicciVariationFormulaInFrameOnLocal
      (I := I) S frame u nablaGammaDt) :
    RicciVariationFormulaInFrameOn (I := I) S frame nablaGammaDt := by
  intro t x i j
  exact hlocal t x (hcover x) i j









def nablaGammaDtFromNabla2RicInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d k i j : Idx) : Real :=
  ∑ l : Idx,
    gInv t x k l *
      (-nabla2Ric t x d i j l -
        nabla2Ric t x d j i l +
        nabla2Ric t x d l i j)

section CoordinateConnectionVariation

open DifferentialGeometry.Tensor.Coordinates

section RaisedContractAlgebra

variable {ι : Type*} [Fintype ι]

def lowerRHS
    (N : ι -> ι -> ι -> Real) (i j l : ι) : Real :=
  -N i j l - N j i l + N l i j

def covD3
    (Γ : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (i j l : ι) : Real :=
  dB i j l -
    (∑ p : ι, Γ p i * B p j l) -
    (∑ p : ι, Γ p j * B i p l) -
    (∑ p : ι, Γ p l * B i j p)

def covDInv
    (Γ G dG : ι -> ι -> Real) (k l : ι) : Real :=
  dG k l +
    (∑ a : ι, Γ k a * G a l) +
    (∑ a : ι, Γ l a * G k a)

def covDChristoffelVariation
    (Γ : ι -> ι -> ι -> Real) (A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (dir k i j : ι) : Real :=
  dA dir i j k +
    (∑ a : ι, Γ dir a k * A i j a) -
    (∑ a : ι, Γ dir i a * A a j k) -
    (∑ a : ι, Γ dir j a * A i a k)

theorem christoffel_curv_variation_algebra
    (Γ : ι -> ι -> ι -> Real) (A : ι -> ι -> ι -> Real)
    (dA : ι -> ι -> ι -> ι -> Real)
    (hΓsymm : ∀ a b c : ι, Γ a b c = Γ b a c)
    (i k j m : ι) :
    dA i k j m - dA k i j m +
        (∑ a : ι, (A k j a * Γ i a m + Γ k j a * A i a m)) -
        (∑ a : ι, (A i j a * Γ k a m + Γ i j a * A k a m)) =
      covDChristoffelVariation Γ A dA i m k j -
        covDChristoffelVariation Γ A dA k m i j := by
  classical
  unfold covDChristoffelVariation
  have hmid :
      (∑ a : ι, Γ i k a * A a j m) =
        ∑ a : ι, Γ k i a * A a j m := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hΓsymm i k a]
  have hleft :
      (∑ a : ι, A k j a * Γ i a m) =
        ∑ a : ι, Γ i a m * A k j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hright :
      (∑ a : ι, A i j a * Γ k a m) =
        ∑ a : ι, Γ k a m * A i j a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleft, hright, hmid]
  ring

private theorem sum_swap_inverse_metric_third_slot
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real)
    (k i j : ι) :
    (∑ l : ι, (∑ a : ι, Γ l a * G k a) * B i j l) =
      ∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a) := by
  classical
  calc
    (∑ l : ι, (∑ a : ι, Γ l a * G k a) * B i j l)
        = ∑ l : ι, ∑ a : ι, (Γ l a * G k a) * B i j l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
    _ = ∑ a : ι, ∑ l : ι, (Γ l a * G k a) * B i j l := by
            rw [Finset.sum_comm]
    _ = ∑ l : ι, ∑ a : ι, (Γ a l * G k l) * B i j a := by
            rfl
    _ = ∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring

private theorem sum_upper_contract
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real)
    (k i j : ι) :
    (∑ l : ι, (∑ a : ι, Γ k a * G a l) * B i j l) =
      ∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l) := by
  classical
  calc
    (∑ l : ι, (∑ a : ι, Γ k a * G a l) * B i j l)
        = ∑ l : ι, ∑ a : ι, (Γ k a * G a l) * B i j l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
    _ = ∑ a : ι, ∑ l : ι, (Γ k a * G a l) * B i j l := by
            rw [Finset.sum_comm]
    _ = ∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring

private theorem sum_lower_contract
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real)
    (k j q : ι) :
    (∑ l : ι, G k l * (∑ a : ι, Γ a q * B a j l)) =
      ∑ a : ι, Γ a q * (∑ l : ι, G k l * B a j l) := by
  classical
  calc
    (∑ l : ι, G k l * (∑ a : ι, Γ a q * B a j l))
        = ∑ l : ι, ∑ a : ι, G k l * (Γ a q * B a j l) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
    _ = ∑ a : ι, ∑ l : ι, G k l * (Γ a q * B a j l) := by
            rw [Finset.sum_comm]
    _ = ∑ a : ι, Γ a q * (∑ l : ι, G k l * B a j l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring

private theorem raised_contract_covD_algebra
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (k i j : ι) :
    (∑ l : ι, (dG k l * B i j l + G k l * dB i j l)) +
        (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) -
        (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
        (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) =
      (∑ l : ι, covDInv Γ G dG k l * B i j l) +
        ∑ l : ι, G k l * covD3 Γ B dB i j l := by
  classical
  symm
  unfold covDInv covD3
  have hfirst :
      (∑ l : ι,
          (dG k l + (∑ a : ι, Γ k a * G a l) +
            (∑ a : ι, Γ l a * G k a)) * B i j l) =
        (∑ l : ι, dG k l * B i j l) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) +
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
    calc
      (∑ l : ι,
          (dG k l + (∑ a : ι, Γ k a * G a l) +
            (∑ a : ι, Γ l a * G k a)) * B i j l)
          =
        (∑ l : ι, dG k l * B i j l) +
          (∑ l : ι, (∑ a : ι, Γ k a * G a l) * B i j l) +
          (∑ l : ι, (∑ a : ι, Γ l a * G k a) * B i j l) := by
            simp [add_mul, Finset.sum_add_distrib, add_assoc]
      _ =
        (∑ l : ι, dG k l * B i j l) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) +
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
            rw [sum_upper_contract (Γ := Γ) (G := G) (B := B)
              (k := k) (i := i) (j := j)]
            rw [sum_swap_inverse_metric_third_slot (Γ := Γ) (G := G) (B := B)
              (k := k) (i := i) (j := j)]
  have hsecond :
      (∑ l : ι,
          G k l *
            (dB i j l - (∑ p : ι, Γ p i * B p j l) -
              (∑ p : ι, Γ p j * B i p l) -
              (∑ p : ι, Γ p l * B i j p))) =
        (∑ l : ι, G k l * dB i j l) -
          (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) -
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
    calc
      (∑ l : ι,
          G k l *
            (dB i j l - (∑ p : ι, Γ p i * B p j l) -
              (∑ p : ι, Γ p j * B i p l) -
              (∑ p : ι, Γ p l * B i j p)))
          =
        (∑ l : ι, G k l * dB i j l) -
          (∑ l : ι, G k l * (∑ p : ι, Γ p i * B p j l)) -
          (∑ l : ι, G k l * (∑ p : ι, Γ p j * B i p l)) -
          (∑ l : ι, G k l * (∑ p : ι, Γ p l * B i j p)) := by
            simp only [mul_sub]
            rw [Finset.sum_sub_distrib]
            rw [Finset.sum_sub_distrib]
            rw [Finset.sum_sub_distrib]
      _ =
        (∑ l : ι, G k l * dB i j l) -
          (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) -
          (∑ l : ι, G k l * (∑ a : ι, Γ a l * B i j a)) := by
            rw [sum_lower_contract (Γ := Γ) (G := G) (B := B)
              (k := k) (j := j) (q := i)]
            rw [sum_lower_contract (Γ := Γ) (G := G)
              (B := fun a q l => B q a l) (k := k) (j := i) (q := j)]
  rw [hfirst, hsecond]
  rw [Finset.sum_add_distrib]
  ring

theorem raised_contract_covD_of_inv_zero
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (k i j : ι) (hzero : ∀ l : ι, covDInv Γ G dG k l = 0) :
    (∑ l : ι, (dG k l * B i j l + G k l * dB i j l)) +
        (∑ a : ι, Γ k a * (∑ l : ι, G a l * B i j l)) -
        (∑ a : ι, Γ a i * (∑ l : ι, G k l * B a j l)) -
        (∑ a : ι, Γ a j * (∑ l : ι, G k l * B i a l)) =
      ∑ l : ι, G k l * covD3 Γ B dB i j l := by
  rw [raised_contract_covD_algebra (Γ := Γ) (G := G) (dG := dG)
    (B := B) (dB := dB) (k := k) (i := i) (j := j)]
  simp [hzero]

theorem covD3_lowerRHS
    (Γ : ι -> ι -> Real) (N dN : ι -> ι -> ι -> Real)
    (i j l : ι) :
    covD3 Γ (lowerRHS N) (lowerRHS dN) i j l =
      -covD3 Γ N dN i j l -
        covD3 Γ N dN j i l +
        covD3 Γ N dN l i j := by
  classical
  unfold covD3 lowerRHS
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    mul_add, mul_sub, mul_neg]
  ring

private theorem trace13_connection_terms_cancel
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B k j l)) =
      ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B a j l) := by
  classical
  calc
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B k j l))
        = ∑ a : ι, ∑ k : ι, Γ k a * (∑ l : ι, G a l * B k j l) := by
            rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B a j l) := by
            rfl

private theorem trace23_connection_terms_cancel
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B j k l)) =
      ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B j a l) := by
  classical
  calc
    (∑ k : ι, ∑ a : ι, Γ k a * (∑ l : ι, G a l * B j k l))
        = ∑ a : ι, ∑ k : ι, Γ k a * (∑ l : ι, G a l * B j k l) := by
            rw [Finset.sum_comm]
    _ = ∑ k : ι, ∑ a : ι, Γ a k * (∑ l : ι, G k l * B j a l) := by
            rfl

private theorem trace13_lower_slot_sum
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B k a l)) =
      ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B k a l) := by
  classical
  calc
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B k a l))
        = ∑ a : ι, ∑ k : ι, Γ a j * (∑ l : ι, G k l * B k a l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
    _ = ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B k a l) := by
            rw [Finset.sum_comm]

private theorem trace23_lower_slot_sum
    (Γ G : ι -> ι -> Real) (B : ι -> ι -> ι -> Real) (j : ι) :
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B a k l)) =
      ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B a k l) := by
  classical
  calc
    (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B a k l))
        = ∑ a : ι, ∑ k : ι, Γ a j * (∑ l : ι, G k l * B a k l) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
    _ = ∑ k : ι, ∑ a : ι, Γ a j * (∑ l : ι, G k l * B a k l) := by
            rw [Finset.sum_comm]

private theorem trace13_contract_covD_of_inv_zero
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (j : ι) (hzero : ∀ k l : ι, covDInv Γ G dG k l = 0) :
    (∑ k : ι, ∑ l : ι, (dG k l * B k j l + G k l * dB k j l)) -
        (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B k a l)) =
      ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB k j l := by
  classical
  have hsum :
      (∑ k : ι,
        ((∑ l : ι, (dG k l * B k j l + G k l * dB k j l)) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B k j l)) -
          (∑ a : ι, Γ a k * (∑ l : ι, G k l * B a j l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B k a l)))) =
        ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB k j l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    exact raised_contract_covD_of_inv_zero
      (Γ := Γ) (G := G) (dG := dG) (B := B) (dB := dB)
      (k := k) (i := k) (j := j) (hzero k)
  have hcancel := trace13_connection_terms_cancel (Γ := Γ) (G := G) (B := B) (j := j)
  rw [← hsum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hcancel]
  rw [trace13_lower_slot_sum (Γ := Γ) (G := G) (B := B) (j := j)]
  ring

private theorem trace23_contract_covD_of_inv_zero
    (Γ G dG : ι -> ι -> Real) (B dB : ι -> ι -> ι -> Real)
    (j : ι) (hzero : ∀ k l : ι, covDInv Γ G dG k l = 0) :
    (∑ k : ι, ∑ l : ι, (dG k l * B j k l + G k l * dB j k l)) -
        (∑ a : ι, Γ a j * (∑ k : ι, ∑ l : ι, G k l * B a k l)) =
      ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB j k l := by
  classical
  have hsum :
      (∑ k : ι,
        ((∑ l : ι, (dG k l * B j k l + G k l * dB j k l)) +
          (∑ a : ι, Γ k a * (∑ l : ι, G a l * B j k l)) -
          (∑ a : ι, Γ a j * (∑ l : ι, G k l * B a k l)) -
          (∑ a : ι, Γ a k * (∑ l : ι, G k l * B j a l)))) =
        ∑ k : ι, ∑ l : ι, G k l * covD3 Γ B dB j k l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    exact raised_contract_covD_of_inv_zero
      (Γ := Γ) (G := G) (dG := dG) (B := B) (dB := dB)
      (k := k) (i := j) (j := k) (hzero k)
  have hcancel := trace23_connection_terms_cancel (Γ := Γ) (G := G) (B := B) (j := j)
  rw [← hsum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hcancel]
  rw [trace23_lower_slot_sum (Γ := Γ) (G := G) (B := B) (j := j)]
  ring

end RaisedContractAlgebra

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem ricci_mdiffAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (mdifferentiableAt_const
        (I := I) (I' := 𝓘(Real, Real)) (c := (0 : Real)) (x := x))
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(Real, Real) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ricci_extDerivFun_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> Real)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    extDerivFun (I := I) (t.sum f) x v =
      t.sum (fun i => extDerivFun (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(Real, Real) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(Real, Real) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(Real, Real) (t.sum f) x := by
        exact ricci_mdiffAt_finset_sum (I := I) t f hft
      calc
        extDerivFun (I := I) ((insert i t).sum f) x v
            = extDerivFun (I := I) (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = extDerivFun (I := I) (f i) x v +
              extDerivFun (I := I) (t.sum f) x v := by
              have hadd := congr($(extDerivFun_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (insert i t).sum (fun j => extDerivFun (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ricci_extDerivFun_mul
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ricci_extDerivFun_add
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y + g y) x v =
      extDerivFun (I := I) f x v + extDerivFun (I := I) g x v := by
  have hadd := congr($(extDerivFun_add
    (I := I) (g := f) (g' := g) (x := x) hf hg) v)
  simpa [Pi.add_apply] using hadd

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ricci_extDerivFun_neg
    {f : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    extDerivFun (I := I) (fun y : M => -f y) x v =
      -extDerivFun (I := I) f x v := by
  have hfun : (fun y : M => -f y) = ((fun _ : M => (-1 : Real)) • f) := by
    ext y
    simp
  rw [hfun]
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := fun _ : M => (-1 : Real)) (g := f)
    (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := (-1 : Real)) (x := x))
    hf v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul] using hprod

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ricci_extDerivFun_sub
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y - g y) x v =
      extDerivFun (I := I) f x v - extDerivFun (I := I) g x v := by
  have hneg := ricci_extDerivFun_neg (I := I) (f := g) (x := x) v hg
  have hadd := congr($(extDerivFun_add
    (I := I) (g := f) (g' := fun y : M => -g y)
    (x := x) hf hg.neg) v)
  simpa [Pi.add_apply, sub_eq_add_neg, hneg] using hadd

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem ricci_extDerivFun_congr_eventually
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[nhds x] g) :
    extDerivFun (I := I) f x v = extDerivFun (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(Real, Real)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold extDerivFun
  rw [hmf, hx]

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem contractedTrace13CovDeriv_eq_nabla2RicTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x)
    (hginv_zero : ∀ k l : Idx,
      inverseMetricCovDerivCompInFrame (I := I) gInv
        (S.family.connection t) frame hframe t x d k l = 0) :
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y k j l)
        x (frame d x) -
      (∑ a : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x k a l)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d k j l := by
  classical
  let Γ : Idx -> Idx -> Real := fun up low =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (S.family.connection t) frame hframe x d low up
  let G : Idx -> Idx -> Real := fun k l => gInv t x k l
  let dG : Idx -> Idx -> Real := fun k l =>
    extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x)
  let N : Idx -> Idx -> Idx -> Real := fun a b c => nablaRic t x a b c
  let dN : Idx -> Idx -> Idx -> Real := fun a b c =>
    extDerivFun (I := I) (fun y : M => nablaRic t y a b c) x (frame d x)
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => ∑ k : Idx, ∑ l : Idx,
            gInv t y k l * nablaRic t y k j l)
          x (frame d x) =
        ∑ k : Idx, ∑ l : Idx,
          (dG k l * N k j l + G k l * dN k j l) := by
    have hsumfun :
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y k j l) =
          ((Finset.univ : Finset Idx).sum
            (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y k j l)) := by
      ext y
      simp
    rw [hsumfun]
    rw [ricci_extDerivFun_finset_sum (I := I)
      (t := (Finset.univ : Finset Idx))
      (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y k j l)
      (x := x) (v := frame d x)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y k j l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y k j l)) := by
        ext y
        simp
      rw [hsumfun_l]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y k j l)
        (x := x) (v := frame d x)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x)
          (f := fun y : M => gInv t y k l)
          (g := fun y : M => nablaRic t y k j l)
          (hginv_mdiff k l) (hN_mdiff k j l)]
        simp [G, dG, N, dN]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hN_mdiff k j l)
    · intro k _hk
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y k j l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y k j l)) := by
        ext y
        simp
      rw [hsumfun_l]
      exact ricci_mdiffAt_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y k j l)
        (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff k j l))
  have hInv : ∀ k l : Idx, covDInv Γ G dG k l = 0 := by
    intro k l
    have hz := hginv_zero k l
    simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame] using hz
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y k j l)
        x (frame d x) -
      (∑ a : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x k a l))
        =
      (∑ k : Idx, ∑ l : Idx, (dG k l * N k j l + G k l * dN k j l)) -
        (∑ a : Idx, Γ a j * (∑ k : Idx, ∑ l : Idx, G k l * N k a l)) := by
          rw [hderiv]
    _ = ∑ k : Idx, ∑ l : Idx, G k l * covD3 Γ N dN k j l := by
          exact trace13_contract_covD_of_inv_zero
            (Γ := Γ) (G := G) (dG := dG) (B := N) (dB := dN)
            (j := j) hInv
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d k j l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp [covD3, Γ, G, N, dN, ricciSecondCovDerivCompInFrame]

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem contractedTrace23CovDeriv_eq_nabla2RicTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x)
    (hginv_zero : ∀ k l : Idx,
      inverseMetricCovDerivCompInFrame (I := I) gInv
        (S.family.connection t) frame hframe t x d k l = 0) :
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y j k l)
        x (frame d x) -
      (∑ a : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x a k l)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d j k l := by
  classical
  let Γ : Idx -> Idx -> Real := fun up low =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (S.family.connection t) frame hframe x d low up
  let G : Idx -> Idx -> Real := fun k l => gInv t x k l
  let dG : Idx -> Idx -> Real := fun k l =>
    extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x)
  let N : Idx -> Idx -> Idx -> Real := fun a b c => nablaRic t x a b c
  let dN : Idx -> Idx -> Idx -> Real := fun a b c =>
    extDerivFun (I := I) (fun y : M => nablaRic t y a b c) x (frame d x)
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => ∑ k : Idx, ∑ l : Idx,
            gInv t y k l * nablaRic t y j k l)
          x (frame d x) =
        ∑ k : Idx, ∑ l : Idx,
          (dG k l * N j k l + G k l * dN j k l) := by
    have hsumfun :
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y j k l) =
          ((Finset.univ : Finset Idx).sum
            (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l)) := by
      ext y
      simp
    rw [hsumfun]
    rw [ricci_extDerivFun_finset_sum (I := I)
      (t := (Finset.univ : Finset Idx))
      (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l)
      (x := x) (v := frame d x)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y j k l)) := by
        ext y
        simp
      rw [hsumfun_l]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y j k l)
        (x := x) (v := frame d x)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x)
          (f := fun y : M => gInv t y k l)
          (g := fun y : M => nablaRic t y j k l)
          (hginv_mdiff k l) (hN_mdiff j k l)]
        simp [G, dG, N, dN]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hN_mdiff j k l)
    · intro k _hk
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y j k l)) := by
        ext y
        simp
      rw [hsumfun_l]
      exact ricci_mdiffAt_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y j k l)
        (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff j k l))
  have hInv : ∀ k l : Idx, covDInv Γ G dG k l = 0 := by
    intro k l
    have hz := hginv_zero k l
    simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame] using hz
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y j k l)
        x (frame d x) -
      (∑ a : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x a k l))
        =
      (∑ k : Idx, ∑ l : Idx, (dG k l * N j k l + G k l * dN j k l)) -
        (∑ a : Idx, Γ a j * (∑ k : Idx, ∑ l : Idx, G k l * N a k l)) := by
          rw [hderiv]
    _ = ∑ k : Idx, ∑ l : Idx, G k l * covD3 Γ N dN j k l := by
          exact trace23_contract_covD_of_inv_zero
            (Γ := Γ) (G := G) (dG := dG) (B := N) (dB := dN)
            (j := j) hInv
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d j k l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp [covD3, Γ, G, N, dN, ricciSecondCovDerivCompInFrame]

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem contractedTraceBianchiCovDeriv_eq_nabla2RicTrace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (d j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x)
    (hginv_zero : ∀ k l : Idx,
      inverseMetricCovDerivCompInFrame (I := I) gInv
        (S.family.connection t) frame hframe t x d k l = 0) :
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y l k j)
        x (frame d x) -
      (∑ a : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x l k a)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d l k j := by
  classical
  let Γ : Idx -> Idx -> Real := fun up low =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (S.family.connection t) frame hframe x d low up
  let G : Idx -> Idx -> Real := fun k l => gInv t x k l
  let dG : Idx -> Idx -> Real := fun k l =>
    extDerivFun (I := I) (fun y : M => gInv t y k l) x (frame d x)
  let N : Idx -> Idx -> Idx -> Real := fun a b c => nablaRic t x a b c
  let dN : Idx -> Idx -> Idx -> Real := fun a b c =>
    extDerivFun (I := I) (fun y : M => nablaRic t y a b c) x (frame d x)
  let B : Idx -> Idx -> Idx -> Real := fun a b c => N c b a
  let dB : Idx -> Idx -> Idx -> Real := fun a b c => dN c b a
  have hderiv :
      extDerivFun (I := I)
          (fun y : M => ∑ k : Idx, ∑ l : Idx,
            gInv t y k l * nablaRic t y l k j)
          x (frame d x) =
        ∑ k : Idx, ∑ l : Idx,
          (dG k l * B j k l + G k l * dB j k l) := by
    have hsumfun :
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y l k j) =
          ((Finset.univ : Finset Idx).sum
            (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y l k j)) := by
      ext y
      simp
    rw [hsumfun]
    rw [ricci_extDerivFun_finset_sum (I := I)
      (t := (Finset.univ : Finset Idx))
      (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y l k j)
      (x := x) (v := frame d x)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y l k j) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y l k j)) := by
        ext y
        simp
      rw [hsumfun_l]
      rw [ricci_extDerivFun_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y l k j)
        (x := x) (v := frame d x)]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ricci_extDerivFun_mul (I := I) (v := frame d x)
          (f := fun y : M => gInv t y k l)
          (g := fun y : M => nablaRic t y l k j)
          (hginv_mdiff k l) (hN_mdiff l k j)]
        simp [G, dG, N, dN, B, dB]
        ring
      · intro l _hl
        exact (hginv_mdiff k l).mul (hN_mdiff l k j)
    · intro k _hk
      have hsumfun_l :
          (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y l k j) =
            ((Finset.univ : Finset Idx).sum
              (fun l y => gInv t y k l * nablaRic t y l k j)) := by
        ext y
        simp
      rw [hsumfun_l]
      exact ricci_mdiffAt_finset_sum (I := I)
        (t := (Finset.univ : Finset Idx))
        (f := fun l y => gInv t y k l * nablaRic t y l k j)
        (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff l k j))
  have hInv : ∀ k l : Idx, covDInv Γ G dG k l = 0 := by
    intro k l
    have hz := hginv_zero k l
    simpa [covDInv, Γ, G, dG, inverseMetricCovDerivCompInFrame] using hz
  calc
    extDerivFun (I := I)
        (fun y : M => ∑ k : Idx, ∑ l : Idx,
          gInv t y k l * nablaRic t y l k j)
        x (frame d x) -
      (∑ a : Idx,
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (S.family.connection t) frame hframe x d j a *
          (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x l k a))
        =
      (∑ k : Idx, ∑ l : Idx, (dG k l * B j k l + G k l * dB j k l)) -
        (∑ a : Idx, Γ a j * (∑ k : Idx, ∑ l : Idx, G k l * B a k l)) := by
          rw [hderiv]
    _ = ∑ k : Idx, ∑ l : Idx, G k l * covD3 Γ B dB j k l := by
          exact trace23_contract_covD_of_inv_zero
            (Γ := Γ) (G := G) (dG := dG) (B := B) (dB := dB)
            (j := j) hInv
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          ricciSecondCovDerivCompInFrame
            (I := I) S frame hframe nablaRic t x d l k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          dsimp [covD3, Γ, G, N, dN, B, dB, ricciSecondCovDerivCompInFrame]
          ring

omit [DecidableEq Idx] in
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem contractedTrace23_mdiffAt
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (t : Real) {x : M} (j : Idx)
    (hginv_mdiff : ∀ a b : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => gInv t y a b) x)
    (hN_mdiff : ∀ a b c : Idx,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => nablaRic t y a b c) x) :
    MDifferentiableAt I 𝓘(Real, Real)
      (fun y : M => ∑ k : Idx, ∑ l : Idx,
        gInv t y k l * nablaRic t y j k l) x := by
  classical
  have hsumfun :
      (fun y : M => ∑ k : Idx, ∑ l : Idx,
        gInv t y k l * nablaRic t y j k l) =
        ((Finset.univ : Finset Idx).sum
          (fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l)) := by
    ext y
    simp
  rw [hsumfun]
  refine ricci_mdiffAt_finset_sum (I := I)
    (t := (Finset.univ : Finset Idx))
    (f := fun k y => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) ?_
  intro k _hk
  change MDifferentiableAt I 𝓘(Real, Real)
    (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) x
  have hsumfun_l :
      (fun y : M => ∑ l : Idx, gInv t y k l * nablaRic t y j k l) =
        ((Finset.univ : Finset Idx).sum
          (fun l y => gInv t y k l * nablaRic t y j k l)) := by
    ext y
    simp
  rw [hsumfun_l]
  exact ricci_mdiffAt_finset_sum (I := I)
    (t := (Finset.univ : Finset Idx))
    (f := fun l y => gInv t y k l * nablaRic t y j k l)
    (fun l _hl => (hginv_mdiff k l).mul (hN_mdiff j k l))

end CoordinateConnectionVariation

end Components

end DifferentialGeometry.PDE.RicciFlow
