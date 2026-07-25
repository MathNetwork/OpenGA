import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.RmTrace

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


omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarTraceInFrame_hasDerivWithinAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M) :
    HasDerivWithinAt
      (fun s : Real => scalarTraceInFrame (I := I) S gInv frame s x)
      (scalarTraceDerivRHSInFrame (I := I) S Rm04 gInv frame roughLapRic
        (t : Real) x)
      D.carrier
      (t : Real) := by
  simpa [scalarTraceInFrame, scalarTraceDerivRHSInFrame, Finset.sum_apply] using
    (HasDerivWithinAt.fun_sum
      (u := (Finset.univ : Finset Idx))
      (A := fun i s =>
        ∑ j : Idx,
          gInv s x i j * ricciCompInFrame (I := I) S frame s x i j)
      (A' := fun i =>
        ∑ j : Idx,
          (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                (t : Real) x i j *
              ricciCompInFrame (I := I) S frame (t : Real) x i j +
            gInv (t : Real) x i j *
              ricciEvolutionRHSInFrame
                (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
      (s := D.carrier) (x := (t : Real))
      (fun i _hi =>
        by
          simpa [Finset.sum_apply] using
            (HasDerivWithinAt.fun_sum
              (u := (Finset.univ : Finset Idx))
              (A := fun j s =>
                gInv s x i j * ricciCompInFrame (I := I) S frame s x i j)
              (A' := fun j =>
                (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame
                      (t : Real) x i j *
                    ricciCompInFrame (I := I) S frame (t : Real) x i j +
                  gInv (t : Real) x i j *
                    ricciEvolutionRHSInFrame
                      (I := I) S Rm04 gInv frame roughLapRic (t : Real) x i j))
              (s := D.carrier) (x := (t : Real))
              (fun j _hj =>
                by
                  have hInv := h_inv t x (by simp) i j
                  have hRic := h_ricci t x i j
                  exact hInv.mul hRic))))


omit [SigmaCompactSpace M] in
@[deprecated "use a local or intrinsic scalar-evolution route instead" (since := "2026-05-22")]
theorem scalarEvolutionEquationOn_of_ricciEvolution
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
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
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ScalarEvolutionEquationOn (D := D)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame) := by
  intro t x
  have htrace :=
    scalarTraceInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x
  have hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame :=
    scalarRmRicciTraceInFrame_of_rm04_first_trace
      (I := I) S Rm04 gInv frame hframe hcover hTrace hOutput hFirst hinv hRicSym
  have hInvSym : forall s y i j, gInv s y i j = gInv s y j i := by
    intro s y i j
    have hy : y ∈ u := hcover y
    have hinvAt :=
      scalar_metricInverseInBasis_of_solution_frame
        (I := I) S gInv frame hframe hinv s hy
    simpa using
      invMetric_symm (I := I) (M := M) (S.family.metric s) y
        (hframe.toBasisAt hy) (fun i j : Idx => gInv s y i j) hinvAt i j
  exact htrace.congr_deriv
    (scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS
      (I := I) S Rm04 gInv frame roughLapRic
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (scalarLaplacianTraceInFrame_realizes (M := M) gInv roughLapRic)
      hInvSym hRicSym hRmTrace t x)



omit [SigmaCompactSpace M] in
@[deprecated "use a local or intrinsic scalar-evolution route instead" (since := "2026-05-22")]
theorem scalarEvolutionEquationOn_of_ricciEvolution_regular
    [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
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
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hFirst : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hRicSym : RicciSymmetricInFrameOnRegular (I := I) S frame) :
    ScalarEvolutionEquationOn (D := D)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame) := by
  intro t x
  have htrace :=
    scalarTraceInFrame_hasDerivWithinAt
      (I := I) S Rm04 gInv frame roughLapRic h_inv h_ricci t x
  have hRmTrace : ScalarRmRicciTraceInFrame (I := I) S Rm04 gInv frame :=
    scalarRmRicciTraceInFrame_of_rm04_first_trace_regular
      (I := I) S Rm04 gInv frame hframe hcover hTrace hOutput hFirst hinv hRicSym
  have hInvSym : forall (τ : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y i j,
      gInv (τ : Real) y i j = gInv (τ : Real) y j i := by
    intro τ y i j
    have hy : y ∈ u := hcover y
    have hinvAt :=
      scalar_metricInverseInBasis_of_solution_frame
        (I := I) S gInv frame hframe hinv (τ : Real) hy
    simpa using
      invMetric_symm (I := I) (M := M) (S.family.metric (τ : Real)) y
        (hframe.toBasisAt hy) (fun i j : Idx => gInv (τ : Real) y i j) hinvAt i j
  exact htrace.congr_deriv
    (scalarTraceDerivRHSInFrame_eq_scalarEvolutionRHS_regular
      (I := I) S Rm04 gInv frame roughLapRic
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (scalarLaplacianTraceInFrame_realizes (M := M) gInv roughLapRic)
      hInvSym hRicSym hRmTrace t x)



@[deprecated "use a local or intrinsic scalar-evolution route instead" (since := "2026-05-22")]
theorem scalarEvolutionEquationOn_of_ricciEvolution_lc
    [DecidableEq Idx]
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
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame (I := I) S Rm04 gInv frame roughLapRic)
    (hinv : InvMetricLocal (I := I) S gInv frame u) :
    ScalarEvolutionEquationOn (D := D)
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv roughLapRic)
      (ricciNormSqInFrame (I := I) S gInv frame) := by
  have hOutput :=
    rm04OutputSkew_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hFirst :=
    rm04FirstBianchi_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hPair :=
    rm04PairSymm_regular (I := I) S hS Rm13 Rm04 hRm13 hLower
  have hInput :=
    rm04InputSkew_regular (I := I) S Rm13 Rm04 hRm13 hLower
  have hRicSym : RicciSymmetricInFrameOnRegular (I := I) S frame :=
    ricciSymm_regular (I := I) S Rm04 gInv frame hframe hcover hinv
      hTrace hPair hOutput hInput
  exact scalarEvolutionEquationOn_of_ricciEvolution_regular
    (I := I) S Rm04 gInv frame roughLapRic hframe hcover hTrace hOutput hFirst
    h_inv h_ricci hinv hRicSym


end TraceRoute

end DifferentialGeometry.PDE.RicciFlow
