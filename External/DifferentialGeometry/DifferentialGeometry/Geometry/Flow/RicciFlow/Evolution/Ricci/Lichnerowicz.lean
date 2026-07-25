import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.CoordinateIdentities

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

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem evol_ricci_inFrame_of_variation_commutators
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j)
      D.carrier
      (t : Real) := by
  have h :=
    ricciEvolutionEquationInFrame_apply
      (I := I)
      (h :=
        ricciEvolution_of_variation_commutators
          (I := I) S Rm04 gInv frame nabla2Ric h_var hcomm)
      t x i j
  simpa [ricciEvolutionRHSInFrame] using h



def ricciTraceDerivRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x k l *
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x k i j l +
    gInv t x k l * rm04Dt t x k i j l)




def RicciTraceDerivativeSimplifiesInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem ricciEvolutionEquationInFrame_of_riemann_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_trace : RicciTensorRealizesRm04TraceInFrameOn
      (I := I) S Rm04 gInv frame)
    (h_rm : RiemannEvolutionEquationInFrameOn (I := I) (D := D) Rm04 frame rm04Dt)
    (h_simplify : RicciTraceDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapRic) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  let traceComp : Real -> Real :=
    fun s => ∑ k : Idx, ∑ l : Idx,
      gInv s x k l *
        DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 s) frame x k i j l
  have htraceDeriv :
      HasDerivWithinAt traceComp
        (ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          (t : Real) x i j)
        D.carrier
        (t : Real) := by
    dsimp [traceComp, ricciTraceDerivRHSInFrame]
    simpa [Finset.sum_apply] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset Idx))
        (A := fun k s =>
          ∑ l : Idx,
            gInv s x k l *
              DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 s) frame x k i j l)
        (A' := fun k =>
          ∑ l : Idx,
            (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x k l *
              DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 (t : Real)) frame x k i j l +
            gInv (t : Real) x k l * rm04Dt (t : Real) x k i j l))
        (s := D.carrier) (x := (t : Real))
        (fun k _hk =>
          by
            simpa [Finset.sum_apply] using
              (HasDerivWithinAt.fun_sum
                (u := (Finset.univ : Finset Idx))
                (A := fun l s =>
                  gInv s x k l *
                    DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 s) frame x k i j l)
                (A' := fun l =>
                  inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x k l *
                    DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 (t : Real)) frame x k i j l +
                  gInv (t : Real) x k l * rm04Dt (t : Real) x k i j l)
                (s := D.carrier) (x := (t : Real))
                (fun l _hl =>
                  by
                    exact (h_inv t x (by simp) k l).mul (h_rm t x k i j l)))))
  have hricci :
      HasDerivWithinAt
        (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
        (ricciTraceDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          (t : Real) x i j)
        D.carrier
        (t : Real) := by
    refine htraceDeriv.congr ?_ ?_
    · intro s _hs
      exact ricciCompInFrame_eq_rm04_trace
        (I := I) S Rm04 gInv frame h_trace s x i j
    · exact ricciCompInFrame_eq_rm04_trace
        (I := I) S Rm04 gInv frame h_trace (t : Real) x i j
  exact hricci.congr_deriv (h_simplify t x i j)




def tensorOneUpCompInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i k : Idx) : Real :=
  ∑ a : Idx, gInv t x k a * h t x i a


def ricciLeftActionCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x i k *
      h t x k j


def ricciRightActionCompInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (h : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx,
    ricciOneUpCompInFrame (I := I) S gInv frame t x j k *
      h t x k i







def lichnerowiczRHSInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapH h hRaised : Real -> M -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  roughLapH t x i j -
    2 * (∑ k : Idx, ∑ l : Idx,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l *
        hRaised t x k l) -
    ricciLeftActionCompInFrame (I := I) S gInv frame h t x i j -
    ricciRightActionCompInFrame (I := I) S gInv frame h t x i j


def RicciLichnerowiczEquationInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (ricciCompInFrame (I := I) S frame)
        (raisedRicciCompInFrame (I := I) S gInv frame)
        (t : Real) x i j)
      D.carrier
      (t : Real)





def RicciLichnerowiczSpecializesInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (ricciCompInFrame (I := I) S frame)
        (raisedRicciCompInFrame (I := I) S gInv frame)
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j


def RicciSymmetricInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t x i j,
    ricciCompInFrame (I := I) S frame t x i j =
      ricciCompInFrame (I := I) S frame t x j i



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciLeftActionCompInFrame_eq_quadratic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx) :
    ricciLeftActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  rfl



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciRightActionCompInFrame_eq_quadratic_of_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv)
    (t : Real) (x : M) (i j : Idx) :
    ricciRightActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  unfold ricciRightActionCompInFrame ricciQuadraticCompInFrame ricciOneUpCompInFrame
  calc
    (∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x j a) *
          ricciCompInFrame (I := I) S frame t x k i)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hRic t x j a, hRic t x k i]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x a k *
          ricciCompInFrame (I := I) S frame t x i k *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv t x k a]
          ring
    _ = ∑ a : Idx,
        (∑ k : Idx,
          gInv t x a k * ricciCompInFrame (I := I) S frame t x i k) *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j := by
          rfl



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciRightActionCompInFrame_eq_quadratic_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx)
    (hInv : forall a b : Idx, gInv t x a b = gInv t x b a)
    (hRic : forall a b : Idx,
      ricciCompInFrame (I := I) S frame t x a b =
        ricciCompInFrame (I := I) S frame t x b a) :
    ricciRightActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  unfold ricciRightActionCompInFrame ricciQuadraticCompInFrame ricciOneUpCompInFrame
  calc
    (∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x j a) *
          ricciCompInFrame (I := I) S frame t x k i)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hRic j a, hRic k i]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x a k *
          ricciCompInFrame (I := I) S frame t x i k *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv k a]
          ring
    _ = ∑ a : Idx,
        (∑ k : Idx,
          gInv t x a k * ricciCompInFrame (I := I) S frame t x i k) *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j := by
          rfl

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
private theorem rightActAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (i j : Idx)
    (hInv : forall a b : Idx, gInv t x a b = gInv t x b a)
    (hRic : forall a b : Idx,
      ricciCompInFrame (I := I) S frame t x a b =
        ricciCompInFrame (I := I) S frame t x b a) :
    ricciRightActionCompInFrame (I := I) S gInv frame
        (ricciCompInFrame (I := I) S frame) t x i j =
      ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  unfold ricciRightActionCompInFrame ricciQuadraticCompInFrame ricciOneUpCompInFrame
  calc
    (∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x j a) *
          ricciCompInFrame (I := I) S frame t x k i)
        =
      ∑ k : Idx, ∑ a : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hRic j a, hRic k i]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x k a *
          ricciCompInFrame (I := I) S frame t x a j *
          ricciCompInFrame (I := I) S frame t x i k := by
          rw [Finset.sum_comm]
    _ = ∑ a : Idx, ∑ k : Idx,
        gInv t x a k *
          ricciCompInFrame (I := I) S frame t x i k *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInv k a]
          ring
    _ = ∑ a : Idx,
        (∑ k : Idx,
          gInv t x a k * ricciCompInFrame (I := I) S frame t x i k) *
          ricciCompInFrame (I := I) S frame t x a j := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul]
    _ = ∑ k : Idx,
        (∑ a : Idx,
          gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j := by
          rfl




omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciLichnerowiczSpecializesInFrame_of_actions
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_left : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      ricciLeftActionCompInFrame (I := I) S gInv frame
          (ricciCompInFrame (I := I) S frame) (t : Real) x i j =
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j)
    (h_right : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
      ricciRightActionCompInFrame (I := I) S gInv frame
          (ricciCompInFrame (I := I) S frame) (t : Real) x i j =
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  simp [lichnerowiczRHSInFrame,
    ricciEvolutionRHSInFrame, rmRicciContractionCompInFrame,
    h_left t x i j, h_right t x i j]
  ring



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciLichnerowiczSpecializesInFrame_of_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczSpecializesInFrame_of_actions
    (I := I) S Rm04 gInv frame roughLapRic
    (fun t x i j =>
      ricciLeftActionCompInFrame_eq_quadratic
        (I := I) S gInv frame (t : Real) x i j)
    (fun t x i j =>
      ricciRightActionCompInFrame_eq_quadratic_of_symm
        (I := I) S gInv frame hRic hInv (t : Real) x i j)




omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciLichnerowiczSpecializesInFrame_regular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hRic : RicciSymmetricInFrameOnRegular (I := I) S frame)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  refine ricciLichnerowiczSpecializesInFrame_of_actions
    (I := I) S Rm04 gInv frame roughLapRic ?_ ?_
  · intro t x i j
    exact ricciLeftActionCompInFrame_eq_quadratic
      (I := I) S gInv frame (t : Real) x i j
  · intro t x i j
    exact ricciRightActionCompInFrame_eq_quadratic_at
      (I := I) S gInv frame (t : Real) x i j
      (fun a b => hInv (t : Real) x a b) (hRic t x)



@[deprecated "use a local or pointwise Lichnerowicz specialization instead" (since := "2026-05-22")]
theorem ricciLichnerowiczSpecializesInFrame_lc
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hTrace : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (hinv : InvMetricLocal (I := I) S gInv frame u) :
    RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  have hOutput :=
    rm04OutputSkew_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hPair :=
    rm04PairSymm_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hInput :=
    rm04InputSkew_regular (I := I) S Rm13 Rm04 hRm13 hLower
  have hRic : RicciSymmetricInFrameOnRegular (I := I) S frame :=
    ricciSymm_regular (I := I) S Rm04 gInv frame hframe
      hcover hinv
      hTrace hPair hOutput hInput
  have hInv : SymmetricInverseMetricComponentsInFrameOn gInv := by
    intro t x i j
    have hinvAt :
        Tensor0SBundle.MetricInverseInBasis_gen
          (I := I) (M := M) (S.family.metric t) x
          (hframe.toBasisAt (hcover x)) (fun a b : Idx => gInv t x a b) :=
      metricInverseInBasis_of_local (I := I) S gInv frame hframe hinv t (hcover x)
    exact Tensor0SBundle.invMetric_symm
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt (hcover x)) (fun a b : Idx => gInv t x a b)
      hinvAt i j
  exact ricciLichnerowiczSpecializesInFrame_regular
    (I := I) S Rm04 gInv frame roughLapRic hRic hInv



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_spec : RicciLichnerowiczSpecializesInFrame
      (I := I) S Rm04 gInv frame roughLapRic) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic := by
  intro t x i j
  exact (h_ricci t x i j).congr_deriv (h_spec t x i j).symm




omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hRic : RicciSymmetricInFrameOn (I := I) S frame)
    (hInv : SymmetricInverseMetricComponentsInFrameOn gInv) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczEquationInFrame_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic h_ricci
    (ricciLichnerowiczSpecializesInFrame_of_symm
      (I := I) S Rm04 gInv frame roughLapRic hRic hInv)



@[deprecated "use a local or pointwise Lichnerowicz equation route instead" (since := "2026-05-22")]
theorem ricciLichnerowiczEquationInFrame_of_ricciEvolution_lc
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hTrace : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hinv : InvMetricLocal (I := I) S gInv frame u) :
    RicciLichnerowiczEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic :=
  ricciLichnerowiczEquationInFrame_of_ricciEvolution
    (I := I) S Rm04 gInv frame roughLapRic h_ricci
    (ricciLichnerowiczSpecializesInFrame_lc
      (I := I) S hS Rm13 Rm04 gInv frame roughLapRic hframe hcover
      hTrace hRm13 hLower hinv)






omit [SigmaCompactSpace M] in
theorem evol_ricci_lichnerowicz_coordFrameAt_of_christoffelEvolution_nabla2_commutators
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv :
      Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (gInvDt :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hmetricReg :
      MetricFrameSpacetimeRegularityInFrameOnLocal
        (I := I) S gInv gInvDt (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀))
    (hnablaReg :
      Nabla2RicciComponentsRegularInFrameOnLocal
        (I := I) S (coordinateFrameAt (I := I) x₀)
        (coordinateFrameSet (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic nabla2Ric)
    (hRicTrace : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I) (S.ricci s) (Rm13 s))
    (hRm : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I) (S.family.connection s) (Rm13 s))
    (hcurv : ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀)
    (hmix :
      ChristoffelVariationMixedDerivativeInFrameOnRegular (I := I) S
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) nabla2Ric)
    (hRic : RicciSymmetricInFrameOn (I := I) S (coordinateFrameAt (I := I) x₀))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j)
      (lichnerowiczRHSInFrame (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀)
        (roughLapRicInFrame (M := M) gInv nabla2Ric)
        (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀))
        (raisedRicciCompInFrame (I := I) S gInv (coordinateFrameAt (I := I) x₀))
        (t : Real) x₀ i j)
      D.carrier
      (t : Real) := by
  have hRicci :=
    evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators
      (I := I) S hS Rm13 Rm04 gInv gInvDt nablaRic nabla2Ric x₀ hmetricReg
      hnablaReg hRicTrace hRm hcurv hmix hcomm t i j
  have hx₀ : x₀ ∈ coordinateFrameSet (I := I) x₀ :=
    coordinateFrameAt_mem (I := I) x₀
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x₀
        ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx₀)
        (fun a b : CoordinateIdx (𝕜 := Real) E => gInv (t : Real) x₀ a b) :=
    metricInverseInBasis_of_local
      (I := I) S gInv (coordinateFrameAt (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      hmetricReg.nondegenerateGram (t : Real) hx₀
  have hInvAt :
      forall a b : CoordinateIdx (𝕜 := Real) E,
        gInv (t : Real) x₀ a b = gInv (t : Real) x₀ b a := by
    intro a b
    simpa using
      Tensor0SBundle.invMetric_symm
        (I := I) (M := M) (S.family.metric (t : Real)) x₀
        ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx₀)
        (fun a b : CoordinateIdx (𝕜 := Real) E => gInv (t : Real) x₀ a b)
        hinvAt a b
  have hLeft :
      ricciLeftActionCompInFrame (I := I) S gInv (coordinateFrameAt (I := I) x₀)
          (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀))
          (t : Real) x₀ i j =
        ricciQuadraticCompInFrame (I := I) S gInv (coordinateFrameAt (I := I) x₀)
          (t : Real) x₀ i j :=
    ricciLeftActionCompInFrame_eq_quadratic
      (I := I) S gInv (coordinateFrameAt (I := I) x₀) (t : Real) x₀ i j
  have hRight :
      ricciRightActionCompInFrame (I := I) S gInv (coordinateFrameAt (I := I) x₀)
          (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀))
          (t : Real) x₀ i j =
        ricciQuadraticCompInFrame (I := I) S gInv (coordinateFrameAt (I := I) x₀)
          (t : Real) x₀ i j :=
    rightActAt (I := I) S gInv (coordinateFrameAt (I := I) x₀)
      (t : Real) x₀ i j hInvAt (fun a b => hRic (t : Real) x₀ a b)
  have hSpecAt :
      lichnerowiczRHSInFrame (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀)
        (roughLapRicInFrame (M := M) gInv nabla2Ric)
        (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀))
        (raisedRicciCompInFrame (I := I) S gInv (coordinateFrameAt (I := I) x₀))
        (t : Real) x₀ i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀)
        (roughLapRicInFrame (M := M) gInv nabla2Ric)
        (t : Real) x₀ i j := by
    simp [lichnerowiczRHSInFrame,
      ricciEvolutionRHSInFrame, rmRicciContractionCompInFrame,
      hLeft, hRight]
    ring
  exact hRicci.congr_deriv hSpecAt.symm




omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciLichAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) (i j : Idx)
    (hRicci : HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x i j) D.carrier (t : Real))
    (hInv : forall a b : Idx,
      gInv (t : Real) x a b = gInv (t : Real) x b a)
    (hRic : forall a b : Idx,
      ricciCompInFrame (I := I) S frame (t : Real) x a b =
        ricciCompInFrame (I := I) S frame (t : Real) x b a) :
    HasDerivWithinAt
      (fun s : Real => ricciCompInFrame (I := I) S frame s x i j)
      (lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (ricciCompInFrame (I := I) S frame)
        (raisedRicciCompInFrame (I := I) S gInv frame)
        (t : Real) x i j) D.carrier (t : Real) := by
  have hLeft :=
    ricciLeftActionCompInFrame_eq_quadratic
      (I := I) S gInv frame (t : Real) x i j
  have hRight :=
    ricciRightActionCompInFrame_eq_quadratic_at
      (I := I) S gInv frame (t : Real) x i j hInv hRic
  have hSpec :
      lichnerowiczRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (ricciCompInFrame (I := I) S frame)
          (raisedRicciCompInFrame (I := I) S gInv frame)
          (t : Real) x i j =
        ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
          (t : Real) x i j := by
    simp [lichnerowiczRHSInFrame, ricciEvolutionRHSInFrame,
      rmRicciContractionCompInFrame, hLeft, hRight]
    ring
  exact hRicci.congr_deriv hSpec.symm



theorem coordRicciLich
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j)
      (lichnerowiczRHSInFrame (I := I) S S.base.rm04
        (coordInv (I := I) S x₀) (coordinateFrameAt (I := I) x₀)
        (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀))
        (ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀))
        (raisedRicciCompInFrame (I := I) S (coordInv (I := I) S x₀)
          (coordinateFrameAt (I := I) x₀))
        (t : Real) x₀ i j) D.carrier (t : Real) := by
  apply ricciLichAt (I := I) S S.base.rm04
    (coordInv (I := I) S x₀) (coordinateFrameAt (I := I) x₀)
    (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀)) t x₀ i j
    (coordRicciEvol (I := I) S hS x₀ t i j)
  · intro a b
    exact coordInvSymmOn (I := I) S x₀ (t : Real)
      (coordinateFrameAt_mem (I := I) x₀) a b
  · intro a b
    exact coordRicSymmOn (I := I) S x₀ (t : Real)
      (coordinateFrameAt_mem (I := I) x₀) a b



noncomputable def ricciPairRHS
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x₀ : M) (v w : TangentSpace I x₀) : Real :=
  ∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
    (coordinateFrameAt_toBasis (I := I) x₀).coord i v *
      (coordinateFrameAt_toBasis (I := I) x₀).coord j w *
        ricciEvolutionRHSInFrame (I := I) S S.base.rm04
          (coordInv (I := I) S x₀) (coordinateFrameAt (I := I) x₀)
          (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀))
          t x₀ i j



theorem ricciPairCoord
    [I.Boundaryless] [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (v w : TangentSpace I x₀) :
    HasDerivWithinAt
      (fun s : Real => S.ricci s x₀
        (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w))
      (ricciPairRHS (I := I) S (t : Real) x₀ v w)
      D.carrier (t : Real) := by
  classical
  let b := coordinateFrameAt_toBasis (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  let rhs : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j =>
      ricciEvolutionRHSInFrame (I := I) S S.base.rm04
        (coordInv (I := I) S x₀) frame
        (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀))
        (t : Real) x₀ i j
  have hsum_eval : ∀ s : Real,
      S.ricci s x₀ (DifferentialGeometry.Integral.Connection.vec2 (I := I) v w) =
        ∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          b.coord i v * b.coord j w *
            ricciCompInFrame (I := I) S frame s x₀ i j := by
    intro s
    have h :=
      tensor0S_two_eval_coordFrame_sum (I := I)
        (M := M) (x₀ := x₀) (Ax := S.ricci s x₀) v w
    simpa [b, frame, DifferentialGeometry.Integral.Connection.vec2,
      ricciCompInFrame, SolutionOn.ricci, SolutionOn.ricciAt] using h
  have hsum_deriv :
      HasDerivWithinAt
        (fun s : Real =>
          ∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j w *
              ricciCompInFrame (I := I) S frame s x₀ i j)
        (∑ i : CoordinateIdx (𝕜 := Real) E, ∑ j : CoordinateIdx (𝕜 := Real) E,
          b.coord i v * b.coord j w * rhs i j)
        D.carrier (t : Real) := by
    simpa [rhs, b, frame, mul_assoc] using
      (HasDerivWithinAt.fun_sum
        (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
        (A := fun i s =>
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j w *
              ricciCompInFrame (I := I) S frame s x₀ i j)
        (A' := fun i =>
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            b.coord i v * b.coord j w * rhs i j)
        (s := D.carrier) (x := (t : Real))
        (fun i _hi => by
          simpa [rhs, b, frame, mul_assoc] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)))
              (A := fun j s =>
                b.coord i v * b.coord j w *
                  ricciCompInFrame (I := I) S frame s x₀ i j)
              (A' := fun j => b.coord i v * b.coord j w * rhs i j)
              (s := D.carrier) (x := (t : Real))
              (fun j _hj => by
                simpa [rhs, b, frame, mul_assoc] using
                  ((coordRicciEvol (I := I) S hS x₀ t i j).const_mul
                    (b.coord i v * b.coord j w))))))
  have hderiv := hsum_deriv.congr_of_eventuallyEq
    (by
      filter_upwards with s
      exact hsum_eval s)
    (hsum_eval (t : Real))
  simpa [ricciPairRHS, rhs, b, frame] using hderiv

end Components

end DifferentialGeometry.PDE.RicciFlow
