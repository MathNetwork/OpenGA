import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Bianchi

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

omit [IsManifold I 1 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem curvatureAction0SAt_vec2_eq
    (Rm13 : DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (X Y U V : TangentSpace I x) :
    DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) Rm13 Ric X Y
        (DifferentialGeometry.Integral.Connection.vec2 U V) =
      - (Rm13 x
            (DifferentialGeometry.Integral.Connection.oneFormAtSlot0S (I := I) Ric (DifferentialGeometry.Integral.Connection.vec2 U V) 0)
            (DifferentialGeometry.Integral.Connection.vec3 X Y U) +
          Rm13 x
            (DifferentialGeometry.Integral.Connection.oneFormAtSlot0S (I := I) Ric (DifferentialGeometry.Integral.Connection.vec2 U V) 1)
            (DifferentialGeometry.Integral.Connection.vec3 X Y V)) := by
  rw [DifferentialGeometry.Integral.Connection.curvatureAction0SAt]
  simp [Fin.sum_univ_two, DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]





omit [SigmaCompactSpace M] in
private theorem contractedCurvatureAction_left_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) g x basis gInvAt)
    (t : Real) (i j : Idx)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x (Rm13 t x) (Rm04 t x))
    (hTraceAt : DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
      (S.ricci t x) (Rm04 t x) gInvAt basis)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 t x (DifferentialGeometry.Integral.Connection.vec4 W X Y Z) =
        Rm04 t x (DifferentialGeometry.Integral.Connection.vec4 Y Z W X))
    (hOutput : DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 t x))
    (hFirst : DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 t x))
    (hRic : forall i j : Idx,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hgInvAt : forall a b : Idx, gInvAt a b = gInv t x a b)
    (hbasis : forall a : Idx, basis a = frame a x) :
    (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 t)
            (S.ricci t x) (frame k x) (frame i x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) =
      rmRicciContractionCompInFrame (I := I) S
        Rm04 gInv frame t x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  have hRicAt :
      forall a b : Idx,
        (S.ricci t x) (DifferentialGeometry.Integral.Connection.vec2 (basis a) (basis b)) =
          (S.ricci t x) (DifferentialGeometry.Integral.Connection.vec2 (basis b) (basis a)) := by
    intro a b
    simpa [hbasis] using hRic a b
  have hInvAt : forall a b : Idx, gInvAt a b = gInvAt b a := by
    exact Tensor0SBundle.invMetric_symm (I := I) (M := M) g x basis gInvAt hinvAt
  have hmain :=
    DifferentialGeometry.Integral.Connection.contracted_curvatureAction0SAt_vec2_eq
      (I := I) g basis gInvAt hinvAt (Rm13 t) (Rm04 t x) (S.ricci t x)
      hLower hTraceAt hPair hOutput hFirst hRicAt hInvAt i j
  simpa [DifferentialGeometry.Integral.Connection.rm04RicciContractionAt, DifferentialGeometry.Integral.Connection.raised02CompAt,
    DifferentialGeometry.Integral.Connection.ricciQuadraticAt, DifferentialGeometry.Integral.Connection.oneUp02CompAt,
    rmRicciContractionCompInFrame, raisedRicciCompInFrame, ricciOneUpCompInFrame,
    ricciQuadraticCompInFrame, DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp,
    hgInvAt, hbasis] using hmain



omit [SigmaCompactSpace M] in
private theorem contractedCurvatureAction_right_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    {g : SmoothRiemannianMetric I M} {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInvAt : Idx -> Idx -> Real)
    (hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) g x basis gInvAt)
    (t : Real) (i j : Idx)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x (Rm13 t x) (Rm04 t x))
    (hTraceAt : DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
      (S.ricci t x) (Rm04 t x) gInvAt basis)
    (hPair : forall W X Y Z : TangentSpace I x,
      Rm04 t x (DifferentialGeometry.Integral.Connection.vec4 W X Y Z) =
        Rm04 t x (DifferentialGeometry.Integral.Connection.vec4 Y Z W X))
    (hOutput : DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 t x))
    (hFirst : DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 t x))
    (hRic : forall i j : Idx,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hgInvAt : forall a b : Idx, gInvAt a b = gInv t x a b)
    (hbasis : forall a : Idx, basis a = frame a x) :
    (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 t)
            (S.ricci t x) (frame k x) (frame j x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) =
      rmRicciContractionCompInFrame (I := I) S
        Rm04 gInv frame t x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
  have hRicAt :
      forall a b : Idx,
        (S.ricci t x) (DifferentialGeometry.Integral.Connection.vec2 (basis a) (basis b)) =
          (S.ricci t x) (DifferentialGeometry.Integral.Connection.vec2 (basis b) (basis a)) := by
    intro a b
    simpa [hbasis] using hRic a b
  have hInvAt : forall a b : Idx, gInvAt a b = gInvAt b a := by
    exact Tensor0SBundle.invMetric_symm (I := I) (M := M) g x basis gInvAt hinvAt
  have hmain :=
    DifferentialGeometry.Integral.Connection.contracted_curvatureAction0SAt_vec2_eq
      (I := I) g basis gInvAt hinvAt (Rm13 t) (Rm04 t x) (S.ricci t x)
      hLower hTraceAt hPair hOutput hFirst hRicAt hInvAt j i
  have hsym :=
    DifferentialGeometry.Integral.Connection.curvature_ricci_rhs_symm
      (I := I) basis (Rm04 t x) gInvAt (S.ricci t x)
      hPair hRicAt hInvAt j i
  calc
    (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 t)
            (S.ricci t x) (frame k x) (frame j x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x)))
        =
          DifferentialGeometry.Integral.Connection.rm04RicciContractionAt (I := I) basis (Rm04 t x) gInvAt
              (S.ricci t x) j i +
            DifferentialGeometry.Integral.Connection.ricciQuadraticAt (I := I) basis gInvAt
              (S.ricci t x) j i := by
          simpa [hgInvAt, hbasis] using hmain
    _ =
          DifferentialGeometry.Integral.Connection.rm04RicciContractionAt (I := I) basis (Rm04 t x) gInvAt
              (S.ricci t x) i j +
            DifferentialGeometry.Integral.Connection.ricciQuadraticAt (I := I) basis gInvAt
              (S.ricci t x) i j := hsym
    _ =
      rmRicciContractionCompInFrame (I := I) S
        Rm04 gInv frame t x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j := by
          simp [DifferentialGeometry.Integral.Connection.rm04RicciContractionAt, DifferentialGeometry.Integral.Connection.raised02CompAt,
            DifferentialGeometry.Integral.Connection.ricciQuadraticAt, DifferentialGeometry.Integral.Connection.oneUp02CompAt,
            rmRicciContractionCompInFrame, raisedRicciCompInFrame, ricciOneUpCompInFrame,
            ricciQuadraticCompInFrame, DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp,
            hgInvAt, hbasis]





omit [SigmaCompactSpace M] in
@[deprecated "use a local or pointwise commutator producer instead" (since := "2026-05-22")]
theorem ricciSecondDerivativeCommutatorsInFrame_of_tensor0S_ricciIdentity
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (nabla2RicTensor : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hNabla2 : Nabla2RicciTensorComponentsInFrameOn
      (I := I) frame nabla2RicTensor nabla2Ric)
    (hRicciId : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I) (Rm13 (t : Real))
        (S.ricci (t : Real) x) (nabla2RicTensor (t : Real) x))
    (hRicTrace13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (hPair : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 W X Y Z) =
          Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y Z W X))
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hRic : RicciSymmetricInFrameOnRegular (I := I) S frame)
    :
    RicciSecondDerivativeCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  classical
  intro t x i j
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt (hcover x))
        (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_local
      (I := I) S gInv frame hframe hinv (t : Real) (hcover x)
  have hTraceReg :
      RicciTensorRealizesRm04FirstTraceInFrameOnRegular
        (I := I) S Rm04 gInv frame :=
    ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace
      (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv hRicTrace13 hLower
  have hTraceFrame := hTraceReg t
  have hTraceAt :
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (fun a b : Idx => gInv (t : Real) x a b)
        (hframe.toBasisAt (hcover x)) := by
    intro a b
    have h := hTraceFrame x a b
    simpa [DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm04FirstTraceInFrame,
      IsLocalFrameOn.toBasisAt_coe] using h
  have hIdComp :
      forall k l : Idx,
        nabla2Ric (t : Real) x k i j l -
            nabla2Ric (t : Real) x i k j l =
          DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
            (S.ricci (t : Real) x)
            (frame k x) (frame i x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x)) := by
    intro k l
    have h := hRicciId t x (frame k x) (frame i x)
      (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))
    have hinput₁ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame k x) (frame i x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame k x) (frame i x) (frame j x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    have hinput₂ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame i x) (frame k x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame i x) (frame k x) (frame j x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput₁, hinput₂] at h
    rw [hNabla2 (t : Real) x k i j l, hNabla2 (t : Real) x i k j l]
    simpa [DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp] using h
  have hIdCompRight :
      forall k l : Idx,
        nabla2Ric (t : Real) x k j i l -
            nabla2Ric (t : Real) x j k i l =
          DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
            (S.ricci (t : Real) x)
            (frame k x) (frame j x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x)) := by
    intro k l
    have h := hRicciId t x (frame k x) (frame j x)
      (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))
    have hinput₁ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame k x) (frame j x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame k x) (frame j x) (frame i x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    have hinput₂ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame j x) (frame k x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame j x) (frame k x) (frame i x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput₁, hinput₂] at h
    rw [hNabla2 (t : Real) x k j i l, hNabla2 (t : Real) x j k i l]
    simpa [DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp] using h
  have hleftCurv :
      contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame i x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := by
    unfold contractedNabla2RicLeftInFrame contractedNabla2RicTraceAInFrame
    calc
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x k i j l)
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            (nabla2Ric (t : Real) x i k j l +
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame i x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            have h := hIdComp k l
            rw [sub_eq_iff_eq_add] at h
            rw [h]
            ring
      _ =
        (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nabla2Ric (t : Real) x i k j l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l *
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame i x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := by
            simp [mul_add, Finset.sum_add_distrib]
  have hrightCurvNatural :
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x j k i l) +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame j x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := by
    unfold contractedNabla2RicRightInFrame
    calc
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x k j i l)
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            (nabla2Ric (t : Real) x j k i l +
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame j x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            have h := hIdCompRight k l
            rw [sub_eq_iff_eq_add] at h
            rw [h]
            ring
      _ =
        (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nabla2Ric (t : Real) x j k i l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l *
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame j x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := by
            simp [mul_add, Finset.sum_add_distrib]
  have hgInvAt :
      forall a b : Idx,
        (fun a b : Idx => gInv (t : Real) x a b) a b =
          gInv (t : Real) x a b := by
    intro a b
    rfl
  have hbasis :
      forall a : Idx,
        hframe.toBasisAt (hcover x) a =
          frame a x := by
    intro a
    simp [IsLocalFrameOn.toBasisAt_coe]
  have hleftAction :=
    contractedCurvatureAction_left_eq
      (I := I) S Rm13 Rm04 gInv frame
      (hframe.toBasisAt (hcover x))
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (t : Real) i j
      (hLower t x) hTraceAt (hPair t x) (hOutput t x) (hFirst t x) (hRic t x)
      hgInvAt hbasis
  have hrightAction :=
    contractedCurvatureAction_right_eq
      (I := I) S Rm13 Rm04 gInv frame
      (hframe.toBasisAt (hcover x))
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (t : Real) i j
      (hLower t x) hTraceAt (hPair t x) (hOutput t x) (hFirst t x) (hRic t x)
      hgInvAt hbasis
  constructor
  · calc
      contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame i x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := hleftCurv
      _ =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j := by
            rw [hleftAction]
            ring
  · calc
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame j x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := hrightCurvNatural
      _ =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j := by
            rw [hrightAction]
            ring






omit [SigmaCompactSpace M] in
theorem ricciSecCommLocId
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (nabla2RicTensor : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hNabla2 : Nab2RicLoc
      (I := I) frame u nabla2RicTensor nabla2Ric)
    (hRicciId : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I) (Rm13 (t : Real))
        (S.ricci (t : Real) x) (nabla2RicTensor (t : Real) x))
    (hRicTrace13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (hPair : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 W X Y Z) =
          Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y Z W X))
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hRic : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      x ∈ u -> forall i j : Idx,
        ricciCompInFrame (I := I) S frame (t : Real) x i j =
          ricciCompInFrame (I := I) S frame (t : Real) x j i) :
    RicciSecCommLoc (I := I) S Rm04 gInv frame u nabla2Ric := by
  classical
  intro t x hx i j
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt hx)
        (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_local
      (I := I) S gInv frame hframe hinv (t : Real) hx
  have hTraceAt :
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (fun a b : Idx => gInv (t : Real) x a b)
        (hframe.toBasisAt hx) := by
    exact
      DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13_section
        (I := I) (S.family.metric (t : Real)) (hframe.toBasisAt hx)
        (fun a b : Idx => gInv (t : Real) x a b) hinvAt
        (S.ricci (t : Real)) (Rm13 (t : Real)) (Rm04 (t : Real))
        (hRicTrace13 t) (hLower t x)
        (Tensor0SBundle.invMetric_symm
          (I := I) (M := M) (S.family.metric (t : Real)) x
          (hframe.toBasisAt hx) (fun a b : Idx => gInv (t : Real) x a b) hinvAt)
  have hIdComp :
      forall k l : Idx,
        nabla2Ric (t : Real) x k i j l -
            nabla2Ric (t : Real) x i k j l =
          DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
            (S.ricci (t : Real) x)
            (frame k x) (frame i x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x)) := by
    intro k l
    have h := hRicciId t x (frame k x) (frame i x)
      (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))
    have hinput₁ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame k x) (frame i x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame k x) (frame i x) (frame j x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    have hinput₂ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame i x) (frame k x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame i x) (frame k x) (frame j x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput₁, hinput₂] at h
    rw [hNabla2 (t : Real) x hx k i j l, hNabla2 (t : Real) x hx i k j l]
    simpa [DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp] using h
  have hIdCompRight :
      forall k l : Idx,
        nabla2Ric (t : Real) x k j i l -
            nabla2Ric (t : Real) x j k i l =
          DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
            (S.ricci (t : Real) x)
            (frame k x) (frame j x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x)) := by
    intro k l
    have h := hRicciId t x (frame k x) (frame j x)
      (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))
    have hinput₁ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame k x) (frame j x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame k x) (frame j x) (frame i x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    have hinput₂ :
        DifferentialGeometry.Integral.Connection.metricTraceInput (I := I) (frame j x) (frame k x)
            (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x)) =
          DifferentialGeometry.Integral.Connection.vec4 (frame j x) (frame k x) (frame i x) (frame l x) := by
      funext q
      fin_cases q <;> rfl
    rw [hinput₁, hinput₂] at h
    rw [hNabla2 (t : Real) x hx k j i l, hNabla2 (t : Real) x hx j k i l]
    simpa [DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp] using h
  have hleftCurv :
      contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame i x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := by
    unfold contractedNabla2RicLeftInFrame contractedNabla2RicTraceAInFrame
    calc
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x k i j l)
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            (nabla2Ric (t : Real) x i k j l +
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame i x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            have h := hIdComp k l
            rw [sub_eq_iff_eq_add] at h
            rw [h]
            ring
      _ =
        (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nabla2Ric (t : Real) x i k j l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l *
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame i x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := by
            simp [mul_add, Finset.sum_add_distrib]
  have hrightCurvNatural :
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x j k i l) +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame j x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := by
    unfold contractedNabla2RicRightInFrame
    calc
      (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l * nabla2Ric (t : Real) x k j i l)
          =
        ∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            (nabla2Ric (t : Real) x j k i l +
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame j x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            have h := hIdCompRight k l
            rw [sub_eq_iff_eq_add] at h
            rw [h]
            ring
      _ =
        (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l * nabla2Ric (t : Real) x j k i l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv (t : Real) x k l *
              DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
                (S.ricci (t : Real) x)
                (frame k x) (frame j x)
                (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := by
            simp [mul_add, Finset.sum_add_distrib]
  have hgInvAt :
      forall a b : Idx,
        (fun a b : Idx => gInv (t : Real) x a b) a b =
          gInv (t : Real) x a b := by
    intro a b
    rfl
  have hbasis :
      forall a : Idx,
        hframe.toBasisAt hx a =
          frame a x := by
    intro a
    simp [IsLocalFrameOn.toBasisAt_coe]
  have hleftAction :=
    contractedCurvatureAction_left_eq
      (I := I) S Rm13 Rm04 gInv frame
      (hframe.toBasisAt hx)
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (t : Real) i j
      (hLower t x) hTraceAt (hPair t x) (hOutput t x) (hFirst t x) (hRic t x hx)
      hgInvAt hbasis
  have hrightAction :=
    contractedCurvatureAction_right_eq
      (I := I) S Rm13 Rm04 gInv frame
      (hframe.toBasisAt hx)
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (t : Real) i j
      (hLower t x) hTraceAt (hPair t x) (hOutput t x) (hFirst t x) (hRic t x hx)
      hgInvAt hbasis
  constructor
  · calc
      contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame i x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame j x) (frame l x))) := hleftCurv
      _ =
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j := by
            rw [hleftAction]
            ring
  · calc
      contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j
          =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        (∑ k : Idx, ∑ l : Idx,
          gInv (t : Real) x k l *
            DifferentialGeometry.Integral.Connection.curvatureAction0SAt (I := I) (Rm13 (t : Real))
              (S.ricci (t : Real) x)
              (frame k x) (frame j x)
              (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame l x))) := hrightCurvNatural
      _ =
        contractedNabla2RicTraceRightNaturalInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j +
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j +
        ricciQuadraticCompInFrame (I := I) S gInv frame
          (t : Real) x i j := by
            rw [hrightAction]
            ring





def RicciContractedCommutatorsInFrame
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
        ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
      contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j


def RicciContractedCommutatorsInFrameOnLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M), x ∈ u ->
    forall i j : Idx,
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
          ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j ∧
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j =
          contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
            (t : Real) x i j

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem RicciContractedCommutatorsInFrame.toLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciContractedCommutatorsInFrameOnLocal
      (I := I) S Rm04 gInv frame u nabla2Ric := by
  intro t x _hx i j
  exact hcomm t x i j

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem ricci_trace_terms_eq_of_differentiatedBianchi
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (i j : Idx) :
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j := by
  have hA := (hbianchi t x i j).1
  have hB := (hbianchi t x i j).2
  rw [hA, hB]



omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
theorem traceTermsEqLoc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (u : Set M)
    (hbianchi : DifferentiatedContractedBianchiInFrameOnLocal
      (D := D) (M := M) gInv nabla2Ric u)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) (hx : x ∈ u)
    (i j : Idx) :
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j =
      contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric
        (t : Real) x i j := by
  have hA := (hbianchi t x hx i j).1
  have hB := (hbianchi t x hx i j).2
  rw [hA, hB]



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciCommLoc
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrameOnLocal
      (D := D) (M := M) gInv nabla2Ric u)
    (hHess : HessSymmLoc (D := D) (M := M) gInv nabla2Ric u)
    (hsecond : RicciSecCommLoc (I := I) S Rm04 gInv frame u nabla2Ric) :
    RicciContractedCommutatorsInFrameOnLocal
      (I := I) S Rm04 gInv frame u nabla2Ric := by
  intro t x hx i j
  have hleft := (hsecond t x hx i j).1
  have hright := (hsecond t x hx i j).2
  have hA := (hbianchi t x hx i j).1
  have hB := traceRightNatLoc
    (M := M) gInv nabla2Ric u hbianchi hHess t x hx i j
  have hB' := (hbianchi t x hx i j).2
  exact ⟨by rw [hleft, hA], by rw [hright, hB, hB'],
    traceTermsEqLoc (M := M) gInv nabla2Ric u hbianchi t x hx i j⟩

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_commutators
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hcurv : RicciCurvatureCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  exact ⟨(hcurv t x i j).1, (hcurv t x i j).2,
    ricci_trace_terms_eq_of_differentiatedBianchi
      (M := M) gInv nabla2Ric hbianchi t x i j⟩



omit [SigmaCompactSpace M] in
@[deprecated "use the local contracted-commutator route instead" (since := "2026-05-22")]
theorem RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_tensor0S_ricciIdentity
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (nabla2RicTensor : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hNabla2 : Nabla2RicciTensorComponentsInFrameOn
      (I := I) frame nabla2RicTensor nabla2Ric)
    (hRicciId : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I) (Rm13 (t : Real))
        (S.ricci (t : Real) x) (nabla2RicTensor (t : Real) x))
    (hRicTrace13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (hPair : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 W X Y Z) =
          Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y Z W X))
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hRic : RicciSymmetricInFrameOnRegular (I := I) S frame)
    :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric :=
  RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_commutators
    (I := I) S Rm04 gInv frame nabla2Ric hbianchi
    (RicciCurvatureCommutatorsInFrame_of_differentiatedBianchi_and_secondCommutators
      (I := I) S Rm04 gInv frame nabla2Ric hbianchi hHessSymm
      (ricciSecondDerivativeCommutatorsInFrame_of_tensor0S_ricciIdentity
        (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv
        nabla2RicTensor nabla2Ric
        hNabla2 hRicciId hRicTrace13 hLower hPair hOutput hFirst hRic))



@[deprecated "use the local contracted-commutator route instead" (since := "2026-05-22")]
theorem RicciContractedCommutatorsInFrame_of_tensor0S_ricciIdentity_lc
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (nabla2RicTensor : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hbianchi : DifferentiatedContractedBianchiInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hHessSymm : ScalarHessianFromNabla2RicSymmetricInFrame
      (D := D) (M := M) gInv nabla2Ric)
    (hNabla2 : Nabla2RicciTensorComponentsInFrameOn
      (I := I) frame nabla2RicTensor nabla2Ric)
    (hRicciId : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I) (Rm13 (t : Real))
        (S.ricci (t : Real) x) (nabla2RicTensor (t : Real) x))
    (hRicTrace13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric := by
  have hOutput :=
    rm04OutputSkew_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hFirst :=
    rm04FirstBianchi_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hPair :=
    rm04PairSymm_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hInput :=
    rm04InputSkew_regular (I := I) S Rm13 Rm04 hRm13 hLower
  have hTrace : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)) := by
    have hTraceReg :
      RicciTensorRealizesRm04FirstTraceInFrameOnRegular
        (I := I) S Rm04 gInv frame :=
    ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace
        (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv hRicTrace13 hLower
    intro t x i j
    have h := hTraceReg t x i j
    simpa [DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm04FirstTraceInFrame,
      IsLocalFrameOn.toBasisAt_coe] using h
  have hRic : RicciSymmetricInFrameOnRegular (I := I) S frame :=
    ricciSymm_regular (I := I) S Rm04 gInv frame hframe
      hcover hinv
      hTrace hPair hOutput hInput
  exact
    RicciContractedCommutatorsInFrame_of_differentiatedBianchi_and_tensor0S_ricciIdentity
      (I := I) S Rm13 Rm04 gInv frame hframe hcover hinv nabla2RicTensor nabla2Ric
      hbianchi hHessSymm hNabla2 hRicciId hRicTrace13 hLower
      hPair hOutput hFirst hRic

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [DecidableEq Idx] in
private theorem ricciVariationExpandedRHSInFrame_eq_decomposed
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (i j : Idx) :
    ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric t x i j =
      roughLapRicInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric t x i j +
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j +
        contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric t x i j -
        contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric t x i j := by
  let left : Real :=
    contractedNabla2RicLeftInFrame (M := M) gInv nabla2Ric t x i j
  let right : Real :=
    contractedNabla2RicRightInFrame (M := M) gInv nabla2Ric t x i j
  let rough : Real :=
    roughLapRicInFrame (M := M) gInv nabla2Ric t x i j
  let hess : Real :=
    scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j
  let traceA : Real :=
    contractedNabla2RicTraceAInFrame (M := M) gInv nabla2Ric t x i j
  let traceB : Real :=
    contractedNabla2RicTraceBInFrame (M := M) gInv nabla2Ric t x i j
  have hfirst :
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x k i j l -
            nabla2Ric t x k j i l +
            nabla2Ric t x k l i j)) =
        -left - right + rough := by
    dsimp [left, right, rough, contractedNabla2RicLeftInFrame,
      contractedNabla2RicRightInFrame, roughLapRicInFrame]
    calc
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x k i j l -
            nabla2Ric t x k j i l +
            nabla2Ric t x k l i j))
          =
        ∑ k : Idx, ∑ l : Idx,
          (-(gInv t x k l * nabla2Ric t x k i j l) -
            gInv t x k l * nabla2Ric t x k j i l +
            gInv t x k l * nabla2Ric t x k l i j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = - (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k i j l) -
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k j i l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x k l i j) := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib,
              Finset.sum_neg_distrib]
  have hsecond :
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x i k j l -
            nabla2Ric t x i j k l +
            nabla2Ric t x i l k j)) =
        -traceA - hess + traceB := by
    dsimp [hess, traceA, traceB, scalarHessianFromNabla2RicInFrame,
      contractedNabla2RicTraceAInFrame, contractedNabla2RicTraceBInFrame]
    calc
      (∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          (-nabla2Ric t x i k j l -
            nabla2Ric t x i j k l +
            nabla2Ric t x i l k j))
          =
        ∑ k : Idx, ∑ l : Idx,
          (-(gInv t x k l * nabla2Ric t x i k j l) -
            gInv t x k l * nabla2Ric t x i j k l +
            gInv t x k l * nabla2Ric t x i l k j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
      _ = - (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i k j l) -
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i j k l) +
          (∑ k : Idx, ∑ l : Idx,
            gInv t x k l * nabla2Ric t x i l k j) := by
            simp [sub_eq_add_neg, Finset.sum_add_distrib,
              Finset.sum_neg_distrib]
  unfold ricciVariationExpandedRHSInFrame
  rw [hfirst, hsecond]
  dsimp [left, right, rough, hess, traceA, traceB]
  ring



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric := by
  intro t x i j
  have hleft := (hcomm t x i j).1
  have hright := (hcomm t x i j).2.1
  have htrace := (hcomm t x i j).2.2
  rw [ricciVariationExpandedRHSInFrame_eq_decomposed
    (M := M) gInv nabla2Ric (t : Real) x i j]
  rw [hleft, hright, htrace]
  simp [ricciEvolutionRHSInFrame]
  ring



def contractedBianchiInFrame
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (gradScalar : Real -> M -> Idx -> Real) : Prop :=
  forall t x i,
    (∑ k : Idx, ∑ l : Idx, gInv t x k l * nablaRic t x l i k) =
      (1 / 2 : Real) * gradScalar t x i



def ricciSecondDerivativeCommute
    (secondDerivRic commutedSecondDerivRic :
      Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall t x a b i j,
    secondDerivRic t x a b i j = commutedSecondDerivRic t x a b i j



def ricciVariationGaugeTerms_cancel
    (gaugeTerms : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall t x i j, gaugeTerms t x i j = 0





def ricciCurvatureTerms_eq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (curvatureTerms : Real -> M -> Idx -> Idx -> Real) : Prop :=
  forall t x i j,
    curvatureTerms t x i j =
      2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame t x i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv frame t x i j




omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolutionEquationInFrame_of_variation_expanded
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (h_reduce : RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv nabla2Ric) := by
  intro t x i j
  exact (h_var t x i j).congr_deriv
    ((ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
        (M := M) gInv nabla2Ric (t : Real) x i j).trans
      (h_reduce t x i j))



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolutionEquationInFrameOnLocal_of_variation_expanded
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (h_reduce : RicciVariationExpandedRHS_eq_evolutionRHS
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) := by
  intro t x hx i j
  exact (h_var t x hx i j).congr_deriv
    ((ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
        (M := M) gInv nabla2Ric (t : Real) x i j).trans
      (h_reduce t x i j))



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolution_of_variation_commutators
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOn (I := I) S frame
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrame_of_variation_expanded
    (I := I) S Rm04 gInv frame nabla2Ric h_var
    (ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
      (I := I) S Rm04 gInv frame nabla2Ric hcomm)



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolutionEquationInFrameOnLocal_of_variation_commutators
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrame
      (I := I) S Rm04 gInv frame nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrameOnLocal_of_variation_expanded
    (I := I) S Rm04 gInv frame u nabla2Ric h_var
    (ricciVariationExpandedRHS_eq_evolutionRHS_of_commutators
      (I := I) S Rm04 gInv frame nabla2Ric hcomm)



omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] [T2Space M] in
theorem ricciEvolLocal
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (u : Set M)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (h_var : RicciVariationFormulaInFrameOnLocal (I := I) S frame u
      (nablaGammaDtFromNabla2RicInFrame (M := M) gInv nabla2Ric))
    (hcomm : RicciContractedCommutatorsInFrameOnLocal
      (I := I) S Rm04 gInv frame u nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal
      (I := I) S Rm04 gInv frame u
      (roughLapRicInFrame (M := M) gInv nabla2Ric) := by
  intro t x hx i j
  have hleft := (hcomm t x hx i j).1
  have hright := (hcomm t x hx i j).2.1
  have htrace := (hcomm t x hx i j).2.2
  have hreduce :
      ricciVariationExpandedRHSInFrame (M := M) gInv nabla2Ric
          (t : Real) x i j =
        ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame
          (roughLapRicInFrame (M := M) gInv nabla2Ric)
          (t : Real) x i j := by
    rw [ricciVariationExpandedRHSInFrame_eq_decomposed
      (M := M) gInv nabla2Ric (t : Real) x i j]
    rw [hleft, hright, htrace]
    simp [ricciEvolutionRHSInFrame]
    ring
  exact (h_var t x hx i j).congr_deriv
    ((ricciVariationFromConnectionRHSInFrame_nablaGammaDtFromNabla2Ric
        (M := M) gInv nabla2Ric (t : Real) x i j).trans hreduce)

end Components

end DifferentialGeometry.PDE.RicciFlow
