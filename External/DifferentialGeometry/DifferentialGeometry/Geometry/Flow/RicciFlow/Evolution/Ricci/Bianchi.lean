import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.GammaCoord

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


def roughLapRicInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ a : Idx, ∑ b : Idx,
    gInv t x a b * nabla2Ric t x a b i j





def Nabla2RicciTensorComponentsInFrameOn
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2RicTensor : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x d a i j,
    nabla2Ric t x d a i j =
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (nabla2RicTensor t) frame x d a i j



def Nab2RicLoc
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2RicTensor : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x, x ∈ u -> forall d a i j,
    nabla2Ric t x d a i j =
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (nabla2RicTensor t) frame x d a i j







def ricciVariationExpandedRHSInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  (∑ k : Idx, ∑ l : Idx,
    gInv t x k l *
      (-nabla2Ric t x k i j l -
        nabla2Ric t x k j i l +
        nabla2Ric t x k l i j)) -
    (∑ k : Idx, ∑ l : Idx,
      gInv t x k l *
        (-nabla2Ric t x i k j l -
          nabla2Ric t x i j k l +
          nabla2Ric t x i l k j))



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciVariationFromConnectionRHSInFrame (M := M)
        (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric)
        t x i j =
      ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric t x i j := by
  simp [ricciVariationFromConnectionRHSInFrame,
    nablaGammaDtFromNabla2RicInFrame, ricciVariationExpandedRHSInFrame]








def RicciVariationExpandedRHS_eq_evolutionRHS
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame
        (roughLapRicInFrame (M := M) gInv nabla2Ric)
        (t : Real) x i j


def contractedNabla2RicLeftInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x k i j l


def contractedNabla2RicRightInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x k j i l



def scalarHessianFromNabla2RicInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i j k l


def contractedNabla2RicTraceAInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i k j l


def contractedNabla2RicTraceBInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x i l k j



def contractedNabla2RicTraceRightNaturalInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) : Real :=
  ∑ k : Idx, ∑ l : Idx,
    gInv t x k l * nabla2Ric t x j k i l







def ContractedBianchiTraceInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall j : Idx,
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x k j l) =
        (1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x j k l) ∧
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x l k j) =
        (1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x j k l)





def DifferentiatedContractedBianchiInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      (1 / 2 : Real) *
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j ∧
    contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j




def ScalarHessianFromNabla2RicSymmetricInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
        (t : Real) x j i




omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem contractedNabla2RicTraceRightNatural_eq_traceB
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx) :
    contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j := by
  have hA := (hbianchi t x j i).1
  have hB := (hbianchi t x i j).2
  calc
    contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j
        = contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
            (t : Real) x j i := rfl
    _ = (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x j i := hA
    _ = (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j := by rw [← hHessSymm t x i j]
    _ = contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j := hB.symm


def DifferentiatedContractedBianchiInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall (i j : Idx),
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j ∧
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j


def HessSymmLoc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (u : Set M) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall (i j : Idx),
      scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x j i



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem traceRightNatLoc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (u : Set M)
    (hbianchi : DifferentiatedContractedBianchiInFrameOnLocal
      (D := D) (M := M) gInv nabla2Ric u)
    (hHess : HessSymmLoc (D := D) (M := M) gInv nabla2Ric u)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j : Idx) :
    contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j := by
  have hA := (hbianchi t x hx j i).1
  have hB := (hbianchi t x hx i j).2
  calc
    contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j
        = contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
            (t : Real) x j i := rfl
    _ = (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x j i := hA
    _ = (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j := by rw [← hHess t x hx i j]
    _ = contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j := hB.symm

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
@[deprecated "use DifferentiatedContractedBianchiInFrameOnLocal or a pointwise producer" (since := "2026-05-22")]
theorem DifferentiatedContractedBianchiInFrame.of_local_cover
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hcover : forall x : M, x ∈ u)
    (h :
      DifferentiatedContractedBianchiInFrameOnLocal
        (D := D) (M := M) gInv nabla2Ric u) :
    DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric := by
  intro t x i j
  exact h t x (hcover x) i j

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem differentiatedContractedBianchiInFrameOnLocal_of_regular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {u : Set M}
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hginv_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D, ∀ x : M, x ∈ u ->
        ∀ a b : Idx,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => gInv (t : Real) y a b) x)
    (hN_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D, ∀ x : M, x ∈ u ->
        ∀ a b c : Idx,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => nablaRic (t : Real) y a b c) x)
    (hginv_zero :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D, ∀ x : M, x ∈ u ->
        ∀ d k l : Idx,
          inverseMetricCovDerivCompInFrame (I := I) gInv
            (S.family.connection (t : Real)) frame hframe
            (t : Real) x d k l = 0)
    (hnabla2_at :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D, ∀ x : M, x ∈ u ->
        ∀ d a i j : Idx,
          nabla2Ric (t : Real) x d a i j =
            ricciSecondCovDerivCompInFrame
              (I := I) S frame hframe nablaRic (t : Real) x d a i j)
    (hbianchi :
      ContractedBianchiTraceInFrameOnLocal
        (D := D) (M := M) gInv nablaRic u) :
    DifferentiatedContractedBianchiInFrameOnLocal
      (D := D) (M := M) gInv nabla2Ric u := by
  classical
  intro t x hx i j
  let scalarTrace : M -> Real := fun y =>
    ∑ k : Idx, ∑ l : Idx,
      gInv (t : Real) y k l * nablaRic (t : Real) y j k l
  let traceA : M -> Real := fun y =>
    ∑ k : Idx, ∑ l : Idx,
      gInv (t : Real) y k l * nablaRic (t : Real) y k j l
  let traceB : M -> Real := fun y =>
    ∑ k : Idx, ∑ l : Idx,
      gInv (t : Real) y k l * nablaRic (t : Real) y l k j
  let Γj : Idx -> Real := fun a =>
    DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
      (S.family.connection (t : Real)) frame hframe x i j a
  have hginv_mdiff :
      ∀ a b : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => gInv (t : Real) y a b) x := by
    intro a b
    exact hginv_mdiff t x hx a b
  have hN_mdiff :
      ∀ a b c : Idx,
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => nablaRic (t : Real) y a b c) x := by
    intro a b c
    exact hN_mdiff t x hx a b c
  have hginv_zero :
      ∀ k l : Idx,
        inverseMetricCovDerivCompInFrame (I := I) gInv
          (S.family.connection (t : Real)) frame hframe
          (t : Real) x i k l = 0 := by
    intro k l
    exact hginv_zero t x hx i k l
  have hnabla2_at := hnabla2_at t x hx
  have hscalar_mdiff :
      MDifferentiableAt I 𝓘(Real, Real) scalarTrace x := by
    dsimp [scalarTrace]
    exact contractedTrace23_mdiffAt
      (I := I) gInv nablaRic (t : Real) (x := x) j hginv_mdiff hN_mdiff
  have hhalf_deriv :
      extDerivFun (I := I) (fun y : M => (1 / 2 : Real) * scalarTrace y)
          x (frame i x) =
        (1 / 2 : Real) * extDerivFun (I := I) scalarTrace x (frame i x) := by
    rw [ricci_extDerivFun_mul (I := I) (v := frame i x)
      (f := fun _ : M => (1 / 2 : Real)) (g := scalarTrace)
      (mdifferentiableAt_const
        (I := I) (I' := 𝓘(Real, Real)) (c := (1 / 2 : Real)) (x := x))
      hscalar_mdiff]
    simp
  have hscalar_cov :=
    contractedTrace23CovDeriv_eq_nabla2RicTrace
      (I := I) S gInv frame hframe nablaRic (t : Real) x i j
      hginv_mdiff hN_mdiff hginv_zero
  have htraceA_cov :=
    contractedTrace13CovDeriv_eq_nabla2RicTrace
      (I := I) S gInv frame hframe nablaRic (t : Real) x i j
      hginv_mdiff hN_mdiff hginv_zero
  have htraceB_cov :=
    contractedTraceBianchiCovDeriv_eq_nabla2RicTrace
      (I := I) S gInv frame hframe nablaRic (t : Real) x i j
      hginv_mdiff hN_mdiff hginv_zero
  have hscalar_eval :
      scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        extDerivFun (I := I) scalarTrace x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
    calc
      scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            ricciSecondCovDerivCompInFrame
              (I := I) S frame hframe nablaRic (t : Real) x i j k l := by
            unfold scalarHessianFromNabla2RicInFrame
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hnabla2_at i j k l]
      _ =
        extDerivFun (I := I) scalarTrace x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
            dsimp [scalarTrace, Γj] at hscalar_cov ⊢
            exact hscalar_cov.symm
  have htraceA_eval :
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        extDerivFun (I := I) traceA x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x k a l)) := by
    calc
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            ricciSecondCovDerivCompInFrame
              (I := I) S frame hframe nablaRic (t : Real) x i k j l := by
            unfold contractedNabla2RicTraceAInFrame
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hnabla2_at i k j l]
      _ =
        extDerivFun (I := I) traceA x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x k a l)) := by
            dsimp [traceA, Γj] at htraceA_cov ⊢
            exact htraceA_cov.symm
  have htraceB_eval :
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        extDerivFun (I := I) traceB x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x l k a)) := by
    calc
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            ricciSecondCovDerivCompInFrame
              (I := I) S frame hframe nablaRic (t : Real) x i l k j := by
            unfold contractedNabla2RicTraceBInFrame
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hnabla2_at i l k j]
      _ =
        extDerivFun (I := I) traceB x (frame i x) -
          (∑ a : Idx, Γj a *
            (∑ k : Idx, ∑ l : Idx,
              gInv (t : Real) x k l * nablaRic (t : Real) x l k a)) := by
            dsimp [traceB, Γj] at htraceB_cov ⊢
            exact htraceB_cov.symm
  have hA_event :
      traceA =ᶠ[nhds x] (fun y : M => (1 / 2 : Real) * scalarTrace y) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact (hbianchi t y hy j).1
  have hB_event :
      traceB =ᶠ[nhds x] (fun y : M => (1 / 2 : Real) * scalarTrace y) := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact (hbianchi t y hy j).2
  have hA_deriv :=
    ricci_extDerivFun_congr_eventually (I := I) (x := x)
      (v := frame i x) hA_event
  have hB_deriv :=
    ricci_extDerivFun_congr_eventually (I := I) (x := x)
      (v := frame i x) hB_event
  have hA_corr :
      (∑ a : Idx, Γj a *
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x k a l)) =
        ∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hbianchi t x hx a).1]
  have hB_corr :
      (∑ a : Idx, Γj a *
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nablaRic (t : Real) x l k a)) =
        ∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hbianchi t x hx a).2]
  have hA :
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j := by
    rw [htraceA_eval, hscalar_eval]
    rw [hA_deriv, hA_corr, hhalf_deriv]
    have hsum_scale :
        (∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l))) =
          (1 / 2 : Real) *
            (∑ a : Idx, Γj a *
              (∑ k : Idx, ∑ l : Idx,
                gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hsum_scale]
    ring
  have hB :
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j := by
    rw [htraceB_eval, hscalar_eval]
    rw [hB_deriv, hB_corr, hhalf_deriv]
    have hsum_scale :
        (∑ a : Idx, Γj a * ((1 / 2 : Real) *
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nablaRic (t : Real) x a k l))) =
          (1 / 2 : Real) *
            (∑ a : Idx, Γj a *
              (∑ k : Idx, ∑ l : Idx,
                gInv (t : Real) x k l * nablaRic (t : Real) x a k l)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hsum_scale]
    ring
  exact ⟨hA, hB⟩



def RicciSecondDerivativeCommutatorsInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric (t : Real) x i j =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j



def RicciSecCommLoc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall (i j : Idx),
      contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric (t : Real) x i j =
          contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j +
          rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
            (t : Real) x i j +
          ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
        contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j =
          contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j +
          rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
            (t : Real) x i j +
          ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j



def RicciCurvatureCommutatorsInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx),
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (1 / 2 : Real) *
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j




omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem RicciCurvatureCommutatorsInFrame_of_differentiatedBianchi_and_secondCommutators
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hsecond : RicciSecondDerivativeCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciCurvatureCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  have hleft := (hsecond t x i j).1
  have hright := (hsecond t x i j).2
  have hA := (hbianchi t x i j).1
  have hB := contractedNabla2RicTraceRightNatural_eq_traceB
    (M := M) gInv nabla2Ric hbianchi hHessSymm t x i j
  have hB' := (hbianchi t x i j).2
  constructor
  · rw [hleft, hA]
  · rw [hright, hB, hB']

end Components

end DifferentialGeometry.PDE.RicciFlow
