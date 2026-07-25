import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Geometry.Curvature.Contractions
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.LeviCivita
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Realized
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import Mathlib.Tactic.Ring

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



def RicciTensorRealizesRm04TraceInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Real,
    DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm04TraceInFrame
      (I := I) (S.ricci t) (Rm04 t) (gInv t) frame




def RicciTensorRealizesRm04FirstTraceInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Real,
    DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm04FirstTraceInFrame
      (I := I) (S.ricci t) (Rm04 t) (gInv t) frame




def RicciTensorRealizesRm04FirstTraceInFrameOnRegular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
    DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm04FirstTraceInFrame
      (I := I) (S.ricci (t : Real)) (Rm04 (t : Real)) (gInv (t : Real)) frame

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem ricciCompInFrame_eq_rm04_trace
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (htrace : RicciTensorRealizesRm04TraceInFrameOn
      (I := I) S Rm04 gInv frame)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x k i j l := by
  simpa [ricciCompInFrame] using
    DifferentialGeometry.Integral.Connection.ricciComp_eq_trace (I := I)
      (S.ricci t) (Rm04 t) (gInv t) frame (htrace t) x i j



omit [SigmaCompactSpace M] [T2Space M] in
private theorem metricInverseInBasis_of_solution_frame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u) :
    Tensor0SBundle.MetricInverseInBasis_gen
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).1
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).2


omit [SigmaCompactSpace M] [T2Space M] in
theorem metricInverseInBasis_of_local
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u) :
    Tensor0SBundle.MetricInverseInBasis_gen
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).1
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).2






omit [SigmaCompactSpace M] in
@[deprecated "use a local or pointwise frame statement instead" (since := "2026-05-22")]
theorem ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace
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
    (hRicTrace13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    :
    RicciTensorRealizesRm04FirstTraceInFrameOnRegular
      (I := I) S Rm04 gInv frame := by
  intro t x i j
  have hx : x ∈ u := hcover x
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt hx)
        (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_local
      (I := I) S gInv frame hframe hinv (t : Real) hx
  have hAt :=
    DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13_section
      (I := I) (S.family.metric (t : Real)) (hframe.toBasisAt hx)
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (S.ricci (t : Real)) (Rm13 (t : Real)) (Rm04 (t : Real))
      (hRicTrace13 t) (hLower t x)
      (Tensor0SBundle.invMetric_symm
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt hx) (fun a b : Idx => gInv (t : Real) x a b) hinvAt)
  simpa [DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm04FirstTraceInFrame,
    IsLocalFrameOn.toBasisAt_coe] using hAt i j



def ConnectionLocallySmoothOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection (t : Real)) (1 : WithTop ℕ∞)



omit [SigmaCompactSpace M] in
theorem connSmoothOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S) :
    ∀ s : Real, s ∈ D.carrier ->
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection s) (1 : WithTop ℕ∞) := by
  intro s _hs
  simpa [SolutionFamily.connection, metricCov] using
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric s)



omit [SigmaCompactSpace M] in
theorem connCurvOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSolutionOn (I := I) S)
    (x₀ : M) :
    ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.ConnectionCurvatureCoordAt (I := I) (S.family.connection s) x₀ := by
  intro s hs
  have htop :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) (S.family.connection s) ∞ := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric s)
  exact DifferentialGeometry.Integral.Connection.connection_curvature_coord_of_christoffel
    (I := I) (S.family.connection s) htop x₀


omit [SigmaCompactSpace M] in
theorem rm13OfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection s) (S.base.rm13 s) := by
  intro s _hs
  simpa [SolutionFamily.connection,
    SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric s)).h_rm13


omit [SigmaCompactSpace M] in
theorem ricciTraceOfSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    ∀ s : Real, s ∈ D.carrier ->
      DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I)
        (S.ricci s) (S.base.rm13 s) := by
  intro s _hs
  simpa [SolutionOn.ricci_eq, SolutionFamily.ricci, SolutionFamily.rm13] using
    (metricCurvData (I := I) (M := M) (S.base.metric s)).h_ricci13


def RicciSymmetricInFrameOnRegular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x i j,
    ricciCompInFrame (I := I) S frame (t : Real) x i j =
      ricciCompInFrame (I := I) S frame (t : Real) x j i

omit [SigmaCompactSpace M] in
theorem lcAt_regular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    DifferentialGeometry.Integral.Connection.IsLeviCivita (I := I)
      (S.family.connection (t : Real)) (S.family.metric (t : Real)) := by
  constructor
  · simpa [DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt,
      DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.metricAt] using
      hS.leviCivita.1 (DifferentialGeometry.Integral.Connection.RealTimeInterval.regularToFlow t)
  · simpa [DifferentialGeometry.Integral.Connection.RealizedMetricFamilyOn.connectionAt] using
      hS.leviCivita.2 (DifferentialGeometry.Integral.Connection.RealTimeInterval.regularToFlow t)

private theorem rm04Realizes_regular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) :
    DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I) (S.family.metric (t : Real))
      (S.family.connection (t : Real)) (Rm04 (t : Real)) :=
  DifferentialGeometry.Integral.Connection.rm04RealizesLower (I := I) (S.family.metric (t : Real))
    (S.family.connection (t : Real)) (Rm13 (t : Real)) (Rm04 (t : Real))
    (hRm13 t) (hLower t)


theorem rm04OutputSkew_regular
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x) := by
  intro t x
  exact DifferentialGeometry.Integral.Connection.rm04OutputSkew_ofMC
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2))
    (DifferentialGeometry.Integral.Connection.metricCompatible_of_isLeviCivita
      (I := I) (lcAt_regular (I := I) S hS t))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)


theorem rm04FirstBianchi_regular
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.FirstBianchiAt (I := I) (Rm04 (t : Real) x) := by
  intro t x
  exact DifferentialGeometry.Integral.Connection.firstBianchi_ofTF
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2))
    (DifferentialGeometry.Integral.Connection.torsionFree_of_isLeviCivita
      (I := I) (lcAt_regular (I := I) S hS t))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)


theorem rm04PairSymm_regular
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 W X Y Z) =
          Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y Z W X) := by
  intro t x
  exact DifferentialGeometry.Integral.Connection.rm04PairSymm_ofLC
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2))
    (lcAt_regular (I := I) S hS t) (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)


theorem rm04InputSkew_regular_first_two
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall X Y Z W : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y X Z W) =
          -Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 X Y Z W) := by
  intro t x
  exact DifferentialGeometry.Integral.Connection.rm04InputSkew_ofRealizes
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)





theorem rm04InputSkew_regular
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall X Y Z W : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y X Z W) =
          -Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 X Y Z W) :=
  rm04InputSkew_regular_first_two
    (I := I) S Rm13 Rm04 hRm13 hLower



omit [SigmaCompactSpace M] in
@[deprecated "use a local or pointwise frame statement instead" (since := "2026-05-22")]
theorem ricciSymm_regular
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hTrace : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hPair : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 W X Y Z) =
          Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y Z W X))
    (hOutput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hInput : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      forall X Y Z W : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 Y X Z W) =
          -Rm04 (t : Real) x (DifferentialGeometry.Integral.Connection.vec4 X Y Z W)) :
    RicciSymmetricInFrameOnRegular (I := I) S frame := by
  intro t x i j
  let basis := hframe.toBasisAt (hcover x)
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric (t : Real)) x
        basis (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_local
      (I := I) S gInv frame hframe hinv (t : Real)
      (hcover x)
  have hsym :=
    DifferentialGeometry.Integral.Connection.ricciSymm_of_rm04 (I := I) basis
      (fun a b : Idx => gInv (t : Real) x a b)
      (S.ricci (t : Real) x) (Rm04 (t : Real) x)
      (hTrace t x) (hPair t x) (hOutput t x) (hInput t x)
      (Tensor0SBundle.invMetric_symm
        (I := I) (M := M) (S.family.metric (t : Real)) x basis
        (fun a b : Idx => gInv (t : Real) x a b) hinvAt)
      i j
  simpa [basis, ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciComp,
    DifferentialGeometry.Integral.Connection.ricciComp, IsLocalFrameOn.toBasisAt_coe] using hsym




def RiemannEvolutionEquationInFrameOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M)
    (a i j l : Idx),
    HasDerivWithinAt
      (fun s : Real => DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 s) frame x a i j l)
      (rm04Dt (t : Real) x a i j l)
      D.carrier
      (t : Real)

end Components

end DifferentialGeometry.PDE.RicciFlow
