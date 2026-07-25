import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TraceAlgebra

set_option autoImplicit false
set_option linter.style.longLine false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section TraceRoute

variable {Idx : Type*} [Fintype Idx]



def ScalarRmRicciTraceInFrame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
    (∑ i : Idx, ∑ j : Idx,
      gInv (t : Real) x i j *
        rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
          (t : Real) x i j) =
      -ricciNormSqInFrame (I := I) S gInv frame (t : Real) x



omit [SigmaCompactSpace M] in
@[deprecated "use a local or pointwise frame statement instead" (since := "2026-05-22")]
theorem scalarRmRicciTraceInFrame_of_rm04_first_trace
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hTrace : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame := by
  classical
  intro t x
  let basis := hframe.toBasisAt (hcover x)
  have hRicAt : forall i j : Idx,
      (S.ricci (t : Real) x) (DifferentialGeometry.Integral.Connection.vec2 (basis i) (basis j)) =
        (S.ricci (t : Real) x) (DifferentialGeometry.Integral.Connection.vec2 (basis j) (basis i)) := by
    intro i j
    simpa [basis, ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciComp,
      DifferentialGeometry.Integral.Connection.ricciComp, IsLocalFrameOn.toBasisAt_coe] using
      hRicSym (t : Real) x i j
  have hinvAt :
      MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x
        basis (fun i j : Idx => gInv (t : Real) x i j) :=
    scalar_metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv (t : Real)
      (hcover x)
  have hmain :=
    DifferentialGeometry.Integral.Connection.metricTrace_rm04RicciContractionAt_eq_neg_inner
      (I := I) basis (Rm04 (t : Real) x) (gInv (t : Real) x)
      (S.ricci (t : Real) x) (hTrace t x) (hOutput t x) (hFirst t x)
      hRicAt (invMetric_symm (I := I) (M := M)
        (S.family.metric (t : Real)) x basis
        (fun i j : Idx => gInv (t : Real) x i j) hinvAt)
  simpa [basis, DifferentialGeometry.Integral.Connection.rm04RicciContractionAt, DifferentialGeometry.Integral.Connection.raised02CompAt,
    rmRicciContractionCompInFrame, raisedRicciCompInFrame,
    ricciNormSqInFrame, DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp,
    ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciComp, DifferentialGeometry.Integral.Connection.ricciComp,
    IsLocalFrameOn.toBasisAt_coe] using hmain




omit [SigmaCompactSpace M] in
@[deprecated "use a local or pointwise frame statement instead" (since := "2026-05-22")]
theorem scalarRmRicciTraceInFrame_of_rm04_first_trace_regular
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hTrace : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hRicSym : RicciSymmetricInFrameOnRegular (I := I) S frame) :
    ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame := by
  classical
  intro t x
  let basis := hframe.toBasisAt (hcover x)
  have hRicAt : forall i j : Idx,
      (S.ricci (t : Real) x) (DifferentialGeometry.Integral.Connection.vec2 (basis i) (basis j)) =
        (S.ricci (t : Real) x) (DifferentialGeometry.Integral.Connection.vec2 (basis j) (basis i)) := by
    intro i j
    simpa [basis, ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciComp,
      DifferentialGeometry.Integral.Connection.ricciComp, IsLocalFrameOn.toBasisAt_coe] using
      hRicSym t x i j
  have hinvAt :
      MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x
        basis (fun i j : Idx => gInv (t : Real) x i j) :=
    scalar_metricInverseInBasis_of_solution_frame
      (I := I) S gInv frame hframe hinv (t : Real)
      (hcover x)
  have hmain :=
    DifferentialGeometry.Integral.Connection.metricTrace_rm04RicciContractionAt_eq_neg_inner
      (I := I) basis (Rm04 (t : Real) x) (gInv (t : Real) x)
      (S.ricci (t : Real) x) (hTrace t x) (hOutput t x) (hFirst t x)
      hRicAt (invMetric_symm (I := I) (M := M)
        (S.family.metric (t : Real)) x basis
        (fun i j : Idx => gInv (t : Real) x i j) hinvAt)
  simpa [basis, DifferentialGeometry.Integral.Connection.rm04RicciContractionAt, DifferentialGeometry.Integral.Connection.raised02CompAt,
    rmRicciContractionCompInFrame, raisedRicciCompInFrame,
    ricciNormSqInFrame, DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp,
    ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciComp, DifferentialGeometry.Integral.Connection.ricciComp,
    IsLocalFrameOn.toBasisAt_coe] using hmain



omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j) =
      2 * ricciNormSqInFrame (I := I) S gInv frame t x := by
  unfold inverseMetricEvolutionRHSInFrame ricciNormSqInFrame
  calc
    (∑ i : Idx, ∑ j : Idx,
      2 * raisedRicciCompInFrame (I := I) S gInv frame t x i j *
        ricciCompInFrame (I := I) S frame t x i j)
        =
      ∑ i : Idx, ∑ j : Idx,
        2 * (ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
    _ =
      2 * (∑ i : Idx, ∑ j : Idx,
        ricciCompInFrame (I := I) S frame t x i j *
          raisedRicciCompInFrame (I := I) S gInv frame t x i j) := by
          simp [Finset.mul_sum]



omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_of_symm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j) =
      ricciNormSqInFrame (I := I) S gInv frame t x := by
  classical
  unfold ricciQuadraticCompInFrame ricciOneUpCompInFrame
    ricciNormSqInFrame DifferentialGeometry.Integral.Connection.ricciNormSqInFrame
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame ricciTwoTensorField
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx,
          (∑ a : Idx,
            gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            (∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
              gInv t x i j * gInv t x k a *
                ricciCompInFrame (I := I) S frame t x i a *
                ricciCompInFrame (I := I) S frame t x k j)
                =
              ∑ j : Idx, ∑ a : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          gInv t x i j * gInv t x a k *
          ricciCompInFrame (I := I) S frame t x j k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInvSym t x k a, hRicSym t x k j]
          ring
    _ =
      ∑ i : Idx, ∑ a : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          (∑ j : Idx, ∑ k : Idx,
            gInv t x i j * gInv t x a k *
              ricciCompInFrame (I := I) S frame t x j k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]




omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (hInvSym : forall i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        ricciQuadraticCompInFrame (I := I) S gInv frame t x i j) =
      ricciNormSqInFrame (I := I) S gInv frame t x := by
  classical
  unfold ricciQuadraticCompInFrame ricciOneUpCompInFrame
    ricciNormSqInFrame DifferentialGeometry.Integral.Connection.ricciNormSqInFrame
    DifferentialGeometry.Integral.Connection.raisedRicciComponentsInFrame ricciTwoTensorField
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx,
          (∑ a : Idx,
            gInv t x k a * ricciCompInFrame (I := I) S frame t x i a) *
          ricciCompInFrame (I := I) S frame t x k j))
        =
      ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        gInv t x i j * gInv t x k a *
          ricciCompInFrame (I := I) S frame t x i a *
          ricciCompInFrame (I := I) S frame t x k j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            (∑ j : Idx, ∑ k : Idx, ∑ a : Idx,
              gInv t x i j * gInv t x k a *
                ricciCompInFrame (I := I) S frame t x i a *
                ricciCompInFrame (I := I) S frame t x k j)
                =
              ∑ j : Idx, ∑ a : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_comm]
            _ =
              ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
                gInv t x i j * gInv t x k a *
                  ricciCompInFrame (I := I) S frame t x i a *
                  ricciCompInFrame (I := I) S frame t x k j := by
                  rw [Finset.sum_comm]
    _ =
      ∑ i : Idx, ∑ a : Idx, ∑ j : Idx, ∑ k : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          gInv t x i j * gInv t x a k *
          ricciCompInFrame (I := I) S frame t x j k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hInvSym k a, hRicSym k j]
          ring
    _ =
      ∑ i : Idx, ∑ a : Idx,
        ricciCompInFrame (I := I) S frame t x i a *
          (∑ j : Idx, ∑ k : Idx,
            gInv t x i j * gInv t x a k *
              ricciCompInFrame (I := I) S frame t x j k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]



omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) :
    scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      scalarLap (t : Real) x +
        2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x := by
  have hdt :=
    scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
      (I := I) S gInv frame (t : Real) x
  have hrm := hRmTrace t x
  have hquad :=
    scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_of_symm
      (I := I) S gInv frame hInvSym hRicSym (t : Real) x
  unfold scalarTraceDerivRHSInFrame
  rw [h_lap (t : Real) x]
  have hsplit :
      (∑ i : Idx, ∑ j : Idx,
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j +
          gInv (t : Real) x i j *
            ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
              (t : Real) x i j)) =
        (∑ i : Idx, ∑ j : Idx,
          inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j) +
        (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j * roughLapRic (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
              (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) := by
    simp [ricciEvolutionRHSInFrame, sub_eq_add_neg, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
      Finset.sum_mul]
    ring_nf
  rw [hsplit, hdt, hrm, hquad]
  ring



omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS_regular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (scalarLap : Real -> M -> Real)
    (h_lap : ScalarLaplacianTraceInFrame (M := M) gInv roughLapRic scalarLap)
    (hInvSym : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x i j,
      gInv (t : Real) x i j = gInv (t : Real) x j i)
    (hRicSym : RicciSymmetricInFrameOnRegular (I := I) S frame)
    (hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M) :
    scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x =
      scalarLap (t : Real) x +
        2 * ricciNormSqInFrame (I := I) S gInv frame (t : Real) x := by
  have hdt :=
    scalarTrace_inverseMetricEvolutionTerm_eq_two_ricciNormSq
      (I := I) S gInv frame (t : Real) x
  have hrm := hRmTrace t x
  have hquad :=
    scalarTrace_ricciQuadraticTerm_eq_ricciNormSq_at
      (I := I) S gInv frame (t : Real) x (hInvSym t x) (hRicSym t x)
  unfold scalarTraceDerivRHSInFrame
  rw [h_lap (t : Real) x]
  have hsplit :
      (∑ i : Idx, ∑ j : Idx,
        (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j +
          gInv (t : Real) x i j *
            ricciEvolutionRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
              (t : Real) x i j)) =
        (∑ i : Idx, ∑ j : Idx,
          inverseMetricEvolutionRHSInFrame (I := I) S gInv frame (t : Real) x i j *
            ricciCompInFrame (I := I) S frame (t : Real) x i j) +
        (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j * roughLapRic (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            rmRicciContractionCompInFrame (I := I) S Rm04 gInv frame
              (t : Real) x i j) -
        2 * (∑ i : Idx, ∑ j : Idx,
          gInv (t : Real) x i j *
            ricciQuadraticCompInFrame (I := I) S gInv frame (t : Real) x i j) := by
    simp [ricciEvolutionRHSInFrame, sub_eq_add_neg, mul_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum,
      Finset.sum_mul]
    ring_nf
  rw [hsplit, hdt, hrm, hquad]
  ring

end TraceRoute

end DifferentialGeometry.PDE.RicciFlow
