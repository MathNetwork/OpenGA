import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.CoordinateRegularity

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

section CoordinateFrameRicciEvolution

theorem coordNab2Reg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) :
    Nabla2RicciComponentsRegularInFrameOnLocal
      (I := I) S (coordinateFrameAt (I := I) x₀)
      (coordinateFrameSet (I := I) x₀)
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
      (coordNab2Ric (I := I) S x₀) := by
  constructor
  · exact
      { realizes := coordNablaRealOn (I := I) S x₀
        mdiffAt := coordNablaRegOn (I := I) S x₀ }
  · exact coordNab2On (I := I) S x₀



theorem coordInvSymmOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M)
    (t : Real) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    coordInv (I := I) S x₀ t x i j =
      coordInv (I := I) S x₀ t x j i := by
  have hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx)
        (fun a b : CoordinateIdx (𝕜 := Real) E =>
          coordInv (I := I) S x₀ t x a b) :=
    metricInverseInBasis_of_local
      (I := I) S (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀) hframe
      (coordInvLocal (I := I) S x₀) t hx
  exact
    Tensor0SBundle.invMetric_symm
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx)
      (fun a b : CoordinateIdx (𝕜 := Real) E =>
        coordInv (I := I) S x₀ t x a b)
      hinvAt i j



theorem coordRicSymmOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M)
    (t : Real) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x i j =
      ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) t x j i := by
  have hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x
        (hframe.toBasisAt hx)
        (fun a b : CoordinateIdx (𝕜 := Real) E =>
          coordInv (I := I) S x₀ t x a b) :=
    metricInverseInBasis_of_local
      (I := I) S (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀) hframe
      (coordInvLocal (I := I) S x₀) t hx
  have hsym :=
    DifferentialGeometry.Integral.Connection.metricRicciSymm (I := I) (M := M) (S.family.metric t)
      (hframe.toBasisAt hx)
      (fun a b : CoordinateIdx (𝕜 := Real) E =>
        coordInv (I := I) S x₀ t x a b)
      hinvAt i j
  simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt,
    IsLocalFrameOn.toBasisAt_coe] using hsym



theorem canNablaSymmAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.NablaRicSymmAt (I := I)
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x) := by
  classical
  intro A B C
  obtain ⟨Xsec, hXsec⟩ :=
    ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x A
  have hRicSymm :
      ∀ y : M, ∀ U V : TangentSpace I y,
        S.ricci t y (fun q : Fin 2 => if q = 0 then U else V) =
          S.ricci t y (fun q : Fin 2 => if q = 0 then V else U) := by
    intro y U V
    let basis := coordinateFrameAt_toBasis (I := I) y
    have hcomp :
        ∀ p q : CoordinateIdx (𝕜 := Real) E,
          S.ricci t y
              (fun r : Fin 2 => if r = 0 then basis p else basis q) =
            S.ricci t y
              (fun r : Fin 2 => if r = 0 then basis q else basis p) := by
      intro p q
      have hinv := coordInvReal (I := I) S y t
      have h :=
        DifferentialGeometry.Integral.Connection.metricRicciSymm (I := I) (M := M) (S.family.metric t)
          basis (fun m n : CoordinateIdx (𝕜 := Real) E =>
            coordInv (I := I) S y t y m n)
          hinv p q
      simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, basis,
        coordinateFrameAt_toBasis_apply] using h
    exact
      DifferentialGeometry.Tensor.Coordinates.tensor0S_two_symm_of_coordFrame
        (I := I) basis (S.ricci t y) hcomp U V
  have hsymm :=
    DifferentialGeometry.Tensor.Coordinates.nabla0SFun_two_symm_of_symm
      (I := I) (S.family.connection t) Xsec (S.ricci t) x hRicSymm B C
  have hleft :=
    totalNabla0SFun_apply_section
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) Xsec (S.ricci t) x
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) B C)
  have hright :=
    totalNabla0SFun_apply_section
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection t) Xsec (S.ricci t) x
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) C B)
  rw [← hXsec]
  rw [show
      DifferentialGeometry.Integral.Connection.vec3 (I := I) (Xsec x) B C =
        Fin.cons (Xsec x) (DifferentialGeometry.Integral.Connection.vec2 (I := I) B C) by
        ext q
        fin_cases q <;> rfl]
  rw [show
      DifferentialGeometry.Integral.Connection.vec3 (I := I) (Xsec x) C B =
        Fin.cons (Xsec x) (DifferentialGeometry.Integral.Connection.vec2 (I := I) C B) by
        ext q
        fin_cases q <;> rfl]
  rw [hleft, hright]
  exact hsymm



theorem coordNablaSymmOn
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M)
    (t : Real) (x : M)
    (a i j : CoordinateIdx (𝕜 := Real) E) :
    nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t x a i j =
      nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀) t x a j i := by
  let frame := coordinateFrameAt (I := I) x₀
  simpa [nablaRicComp, frame] using
    canNablaSymmAt (I := I) S t x (frame a x) (frame i x) (frame j x)








theorem canBianchiAt
    [I.Boundaryless]
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
    let basis := hframe.toBasisAt hx
    let gInvAt : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
      fun a b => coordInv (I := I) S x₀ t x a b
    let nablaRicT :=
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (S.family.connection t) (S.ricci t) x
    let dScalar := DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (S.scalar t) x
    ∃ nablaRm04 :
        Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 5 x,
      DifferentialGeometry.Integral.Connection.SecondBianchiAt (I := I) nablaRm04 ∧
        DifferentialGeometry.Integral.Connection.NablaRmSymmAt (I := I) nablaRm04 ∧
          DifferentialGeometry.Integral.Connection.NablaRicTraceAt (I := I) basis gInvAt nablaRm04 nablaRicT ∧
            DifferentialGeometry.Integral.Connection.DScalarTraceAt (I := I) basis gInvAt nablaRicT dScalar := by
  classical
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let basis := hframe.toBasisAt hx
  let gInvAt : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b => coordInv (I := I) S x₀ t x a b
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x basis gInvAt := by
    have h :=
      DifferentialGeometry.Tensor.Coordinates.gInvBasisAt (I := I) (S.family.metric t) x₀ hx
    simpa [basis, hframe, gInvAt, coordInv,
      IsLocalFrameOn.toBasisAt_coe] using h
  have hmetric :=
    DifferentialGeometry.Integral.Connection.metricBianchiAt (I := I) (M := M)
      (g := S.family.metric t) basis gInvAt hinv
  simpa [SolutionOn.family, SolutionOn.ricci, SolutionOn.scalar,
    SolutionFamily.connection, SolutionFamily.rm04, SolutionFamily.ricci,
    SolutionFamily.scalar, metricCov, metricRm04, metricRicci, metricScalarAt,
    DifferentialGeometry.Integral.Connection.metricCov, DifferentialGeometry.Integral.Connection.metricRm04, DifferentialGeometry.Integral.Connection.metricRicci,
    DifferentialGeometry.Integral.Connection.metricScalarAt, basis, hframe, gInvAt] using hmetric







theorem coordBianchiTr
    [I.Boundaryless]
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) :
    ContractedBianchiTraceInFrameOnLocal
      (D := D) (M := M) (coordInv (I := I) S x₀)
      (nablaRicComp (I := I) S (coordinateFrameAt (I := I) x₀))
      (coordinateFrameSet (I := I) x₀) := by
  classical
  have _ := hS
  intro t x hx j
  let hframe := coordinateFrameAt_isLocalFrame_one (I := I) x₀
  let basis := hframe.toBasisAt hx
  let gInvAt : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b => coordInv (I := I) S x₀ (t : Real) x a b
  let nablaRicT :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 (S.family.connection (t : Real)) (S.ricci (t : Real)) x
  let dScalar := DifferentialGeometry.Integral.Connection.differential1FormFun (I := I) (S.scalar (t : Real)) x
  obtain ⟨nablaRm04, hsecond, hRmSymm, hRicTrace, hScalar⟩ :=
    canBianchiAt (I := I) S x₀ (t : Real) hx
  have hInv : ∀ a b : CoordinateIdx (𝕜 := Real) E, gInvAt a b = gInvAt b a := by
    intro a b
    simpa [gInvAt] using
      coordInvSymmOn (I := I) S x₀ (t : Real) hx a b
  have hNablaSymm : DifferentialGeometry.Integral.Connection.NablaRicSymmAt (I := I) nablaRicT := by
    simpa [nablaRicT] using canNablaSymmAt (I := I) S (t : Real) x
  have hcontract :
      DifferentialGeometry.Integral.Connection.ContractedBianchiOfSecondAt (I := I) basis gInvAt nablaRm04
        nablaRicT dScalar :=
    DifferentialGeometry.Integral.Connection.contractOfSecond (I := I) basis gInvAt nablaRm04
      nablaRicT dScalar hRmSymm hRicTrace hScalar hNablaSymm hInv
  have hBianchi :
      DifferentialGeometry.Integral.Connection.ContractedBianchiAt (I := I) basis gInvAt nablaRicT dScalar :=
    DifferentialGeometry.Integral.Connection.contracted_bianchi_of_second (I := I) basis gInvAt nablaRm04
      nablaRicT dScalar hcontract hsecond
  have htraces :=
    DifferentialGeometry.Integral.Connection.contractTracesAt (I := I) basis gInvAt nablaRicT dScalar
      hBianchi hScalar hNablaSymm hInv j
  simpa [basis, gInvAt, nablaRicT, nablaRicComp, hframe,
    IsLocalFrameOn.toBasisAt_coe] using htraces








theorem coordBianchiOn
    [I.Boundaryless]
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) :
    DifferentiatedContractedBianchiInFrameOnLocal
      (D := D) (M := M) (coordInv (I := I) S x₀)
      (coordNab2Ric (I := I) S x₀) (coordinateFrameSet (I := I) x₀) := by
  let u : Set M := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  let gInv := coordInv (I := I) S x₀
  let nablaRic := nablaRicComp (I := I) S frame
  let nabla2Ric := coordNab2Ric (I := I) S x₀
  have htrace :
      ContractedBianchiTraceInFrameOnLocal
        (D := D) (M := M) gInv nablaRic u := by
    simpa [gInv, nablaRic, frame, u] using
      coordBianchiTr (I := I) S hS x₀
  exact
    differentiatedContractedBianchiInFrameOnLocal_of_regular
      (I := I) S gInv frame
      (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
      (coordinateFrameSet_open (I := I) x₀)
      nablaRic nabla2Ric
      (by
        intro t x hx a b
        simpa [gInv] using
          coordInvMdiffOn (I := I) S x₀ (t : Real) x hx a b)
      (by
        intro t x hx a b c
        simpa [nablaRic, frame] using
          coordNablaRegOn (I := I) S x₀ (t : Real) x hx a b c)
      (by
        intro t x hx d k l
        simpa [gInv, frame] using
          coordInvCovZeroOn (I := I) S x₀ t x hx d k l)
      (by
        intro t x hx d a i j
        simpa [nabla2Ric, nablaRic, frame] using
          (coordNab2On (I := I) S x₀) (t : Real) x hx d a i j)
      htrace







theorem canHessAt
    [I.Boundaryless]
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (t : Real)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    scalarHessianFromNabla2RicInFrame (M := M)
        (coordInv (I := I) S x₀) (coordNab2Ric (I := I) S x₀)
        t x₀ i j =
      scalarHessianFromNabla2RicInFrame (M := M)
        (coordInv (I := I) S x₀) (coordNab2Ric (I := I) S x₀)
        t x₀ j i := by
  classical
  let basis := coordinateFrameAt_toBasis (I := I) x₀
  let gInvAt : CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    fun a b => coordInv (I := I) S x₀ t x₀ a b
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen
        (I := I) (M := M) (S.family.metric t) x₀ basis gInvAt := by
    simpa [basis, gInvAt] using coordInvReal (I := I) S x₀ t
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (S.family.connection t) (∞ : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric t)
  let derivs :=
    CanonicalSpatialDerivs0S.of_smooth_connection
      (E := E) (H := H) (I := I) (M := M)
      (S.family.connection t) hcov (S.ricci t)
  have hnabla : ∀ y a i j,
      (derivs.nablaA y)
          (DifferentialGeometry.Integral.Connection.vec3 (I := I)
            (coordinateFrameAt (I := I) x₀ a y)
            (coordinateFrameAt (I := I) x₀ i y)
            (coordinateFrameAt (I := I) x₀ j y)) =
        nablaRicComp (I := I) S
          (coordinateFrameAt (I := I) x₀) t y a i j := by
    intro y a i j
    simp [nablaRicComp, derivs, CanonicalSpatialDerivs0S.of_smooth_connection]
  have hcan := coordNab2Can (I := I) S t x₀
    derivs.nablaA derivs.nabla2A derivs.second hnabla
  have hmetric :=
    DifferentialGeometry.Integral.Connection.canScalHess (I := I) (M := M)
      (g := S.family.metric t) basis gInvAt hinv i j
  have hmetric' :
      (∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInvAt k l *
            derivs.nabla2A x₀
              (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                (coordinateFrameAt (I := I) x₀ i x₀)
                (coordinateFrameAt (I := I) x₀ j x₀)
                (coordinateFrameAt (I := I) x₀ k x₀)
                (coordinateFrameAt (I := I) x₀ l x₀))) =
      ∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInvAt k l *
            derivs.nabla2A x₀
              (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                (coordinateFrameAt (I := I) x₀ j x₀)
                (coordinateFrameAt (I := I) x₀ i x₀)
                (coordinateFrameAt (I := I) x₀ k x₀)
                (coordinateFrameAt (I := I) x₀ l x₀)) := by
    simpa [SolutionOn.family, SolutionOn.ricci, SolutionFamily.connection,
      SolutionFamily.ricci, metricCov, metricRicci, DifferentialGeometry.Integral.Connection.metricCov,
      DifferentialGeometry.Integral.Connection.metricRicci, basis, gInvAt, derivs,
      CanonicalSpatialDerivs0S.of_smooth_connection,
      coordinateFrameAt_toBasis_apply] using hmetric
  calc
    scalarHessianFromNabla2RicInFrame (M := M)
        (coordInv (I := I) S x₀) (coordNab2Ric (I := I) S x₀)
        t x₀ i j
        =
      ∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInvAt k l *
            derivs.nabla2A x₀
              (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                (coordinateFrameAt (I := I) x₀ i x₀)
                (coordinateFrameAt (I := I) x₀ j x₀)
                (coordinateFrameAt (I := I) x₀ k x₀)
                (coordinateFrameAt (I := I) x₀ l x₀)) := by
          unfold scalarHessianFromNabla2RicInFrame
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hcan i j k l]
    _ =
      ∑ k : CoordinateIdx (𝕜 := Real) E,
        ∑ l : CoordinateIdx (𝕜 := Real) E,
          gInvAt k l *
            derivs.nabla2A x₀
              (DifferentialGeometry.Integral.Connection.vec4 (I := I)
                (coordinateFrameAt (I := I) x₀ j x₀)
                (coordinateFrameAt (I := I) x₀ i x₀)
                (coordinateFrameAt (I := I) x₀ k x₀)
                (coordinateFrameAt (I := I) x₀ l x₀)) := hmetric'
    _ =
      scalarHessianFromNabla2RicInFrame (M := M)
        (coordInv (I := I) S x₀) (coordNab2Ric (I := I) S x₀)
        t x₀ j i := by
          unfold scalarHessianFromNabla2RicInFrame
          refine (Finset.sum_congr rfl fun k _ => ?_).symm
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hcan j i k l]






theorem coordHessOn
    [I.Boundaryless]
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) :
    HessSymmLoc
      (D := D) (M := M) (coordInv (I := I) S x₀)
      (coordNab2Ric (I := I) S x₀) ({x₀} : Set M) := by
  have _ := hS
  intro t x hx i j
  have hx' : x = x₀ := by simpa using hx
  subst x
  exact canHessAt (I := I) S x₀ (t : Real) i j






theorem coordCommAt
    [I.Boundaryless]
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M) :
    RicciContractedCommutatorsInFrameOnLocal
      (I := I) S S.base.rm04 (coordInv (I := I) S x₀)
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (coordNab2Ric (I := I) S x₀) := by
  classical
  let u : Set M := coordinateFrameSet (I := I) x₀
  let gInv := coordInv (I := I) S x₀
  let frame := coordinateFrameAt (I := I) x₀
  let nabla2Ric := coordNab2Ric (I := I) S x₀
  have hbianchiOn :
      DifferentiatedContractedBianchiInFrameOnLocal
        (D := D) (M := M) gInv nabla2Ric u := by
    simpa [gInv, nabla2Ric, u] using coordBianchiOn (I := I) S hS x₀
  have hHessOn :
      HessSymmLoc (D := D) (M := M) gInv nabla2Ric ({x₀} : Set M) := by
    simpa [gInv, nabla2Ric] using coordHessOn (I := I) S hS x₀
  have hbianchi :
      DifferentiatedContractedBianchiInFrameOnLocal
        (D := D) (M := M) gInv nabla2Ric ({x₀} : Set M) := by
    intro t x hx i j
    have hx' : x = x₀ := by simpa using hx
    subst x
    exact hbianchiOn t x₀ (coordinateFrameAt_mem (I := I) x₀) i j
  have hHess :
      HessSymmLoc (D := D) (M := M) gInv nabla2Ric ({x₀} : Set M) := by
    exact hHessOn
  have hsecond :
      RicciSecCommLoc (I := I) S S.base.rm04 gInv frame ({x₀} : Set M)
        nabla2Ric := by
    let derivs :
        (s : Real) ->
          CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
            (M := M) (S.family.connection s) (S.ricci s) :=
      fun s => by
        have hcov :
            CovariantDerivative.ContMDiffCovariantDerivativeLocally
              (S.family.connection s) (∞ : WithTop ℕ∞) := by
          simpa [SolutionFamily.connection, metricCov] using
            metricCov_smooth (I := I) (M := M) (S.base.metric s)
        exact
          CanonicalSpatialDerivs0S.of_smooth_connection
            (E := E) (H := H) (I := I) (M := M)
            (S.family.connection s) hcov (S.ricci s)
    let nabla2Tensor : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M) :=
      fun s => (derivs s).nabla2A
    have hframeSing :
        IsLocalFrameOn I E (1 : WithTop ℕ∞) frame ({x₀} : Set M) := by
      refine (coordinateFrameAt_isLocalFrame_one (I := I) x₀).mono ?_
      intro x hx
      have hx' : x = x₀ := by simpa using hx
      subst x
      exact coordinateFrameAt_mem (I := I) x₀
    have hinvSing :
        InvMetricLocal (I := I) S gInv frame ({x₀} : Set M) := by
      intro t x hx i j
      have hx' : x = x₀ := by simpa using hx
      subst x
      simpa [gInv, frame] using
        (coordInvLocal (I := I) S x₀) t x₀
          (coordinateFrameAt_mem (I := I) x₀) i j
    have hNabla2 :
        Nab2RicLoc (I := I) frame ({x₀} : Set M) nabla2Tensor nabla2Ric := by
      intro t x hx d a i j
      have hx' : x = x₀ := by simpa using hx
      subst x
      have hnabla : ∀ y a i j,
          (derivs t).nablaA y
              (DifferentialGeometry.Integral.Connection.vec3 (I := I)
                (coordinateFrameAt (I := I) x₀ a y)
                (coordinateFrameAt (I := I) x₀ i y)
                (coordinateFrameAt (I := I) x₀ j y)) =
            nablaRicComp (I := I) S
              (coordinateFrameAt (I := I) x₀) t y a i j := by
        intro y a i j
        simp [nablaRicComp, derivs, CanonicalSpatialDerivs0S.of_smooth_connection]
      have hcan :=
        coordNab2Can (I := I) S t x₀ (derivs t).nablaA
          (derivs t).nabla2A (derivs t).second hnabla d a i j
      simpa [nabla2Ric, nabla2Tensor, frame, DifferentialGeometry.Integral.Connection.rm04Comp,
        DifferentialGeometry.Integral.Connection.rm04Comp] using hcan.symm
    have hRicciId :
        ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
          DifferentialGeometry.Integral.Connection.Tensor0SRicciIdentityAt (I := I) (S.base.rm13 (t : Real))
            (S.ricci (t : Real) x) (nabla2Tensor (t : Real) x) := by
      intro t x
      have hcov :
          CovariantDerivative.ContMDiffCovariantDerivativeLocally
            (S.family.connection (t : Real)) (1 : WithTop ℕ∞) :=
        connSmoothOfSol (I := I) S hS (t : Real) (D.regular_subset t.2)
      have hfirst :
          DifferentialGeometry.Integral.Connection.Nabla0SSectionRealizes (I := I) 2
            (S.family.connection (t : Real)) (S.ricci (t : Real))
            (derivs (t : Real)).nablaA := by
        intro y X slots
        exact (derivs (t : Real)).first X y slots
      have h20 :
          DifferentialGeometry.Integral.Connection.Nabla20SRealizesAt (I := I) 2
            (S.family.connection (t : Real)) (S.ricci (t : Real))
            (derivs (t : Real)).nablaA x (nabla2Tensor (t : Real) x) := by
        constructor
        · exact hfirst
        · intro X slots
          exact (derivs (t : Real)).second X x slots
      refine
        DifferentialGeometry.Integral.Connection.tensor0S_ricciIdentity_of_torsionFree
          (I := I) (S.family.connection (t : Real)) hcov (S.base.rm13 (t : Real))
          (S.ricci (t : Real)) (derivs (t : Real)).nablaA
          (S.ricci (t : Real) x) ((derivs (t : Real)).nablaA x)
          (nabla2Tensor (t : Real) x)
          ?_ rfl rfl h20 ?_
      · exact rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)
      · have htf :=
          DifferentialGeometry.Integral.Connection.torsionFree_of_isLeviCivita
            (I := I) (lcAt_regular (I := I) S hS t)
        simpa [DifferentialGeometry.Integral.Connection.IsTorsionFreeAt] using htf x
    have hRicTrace13 :
        ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
          DifferentialGeometry.Integral.Connection.RicciTensorRealizesRm13Trace (I := I)
            (S.ricci (t : Real)) (S.base.rm13 (t : Real)) := by
      intro t
      exact ricciTraceOfSol (I := I) S (t : Real) (D.regular_subset t.2)
    have hRm13 :
        ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
          DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
            (S.family.connection (t : Real)) (S.base.rm13 (t : Real)) := by
      intro t
      exact rm13OfSol (I := I) S (t : Real) (D.regular_subset t.2)
    have hLower :
        ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
          DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.family.metric (t : Real)) x
            (S.base.rm13 (t : Real) x) (S.base.rm04 (t : Real) x) := by
      intro t x
      have h :=
        DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
          (I := I) (S.base.metric (t : Real)) (S.base.connection (t : Real))
          (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real))
          (metricCurvData (I := I) (M := M) (S.base.metric (t : Real))).h_rm13
          (metricCurvData (I := I) (M := M) (S.base.metric (t : Real))).h_rm04
          x
      simpa [SolutionOn.family, SolutionFamily.connection, SolutionFamily.rm13,
        SolutionFamily.rm04, metricCov] using h
    have hPair :=
      rm04PairSymm_regular (I := I) S hS S.base.rm13 S.base.rm04
        hRm13 hLower
    have hOutput :=
      rm04OutputSkew_regular (I := I) S hS S.base.rm13 S.base.rm04
        hRm13 hLower
    have hFirst :=
      rm04FirstBianchi_regular (I := I) S hS S.base.rm13 S.base.rm04
        hRm13 hLower
    have hRic :
        ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
          x ∈ ({x₀} : Set M) -> ∀ i j : CoordinateIdx (𝕜 := Real) E,
            ricciCompInFrame (I := I) S frame (t : Real) x i j =
              ricciCompInFrame (I := I) S frame (t : Real) x j i := by
      intro t x hx i j
      have hx' : x = x₀ := by simpa using hx
      subst x
      have hsym :=
        DifferentialGeometry.Integral.Connection.metricRicciSymm (I := I) (M := M) (S.family.metric (t : Real))
          (coordinateFrameAt_toBasis (I := I) x₀)
          (fun a b => gInv (t : Real) x₀ a b)
          (by simpa [gInv] using coordInvReal (I := I) S x₀ (t : Real)) i j
      simpa [ricciCompInFrame, SolutionOn.ricciAt, SolutionFamily.ricciAt, frame]
        using hsym
    exact
      ricciSecCommLocId (I := I) S S.base.rm13 S.base.rm04 gInv frame
        hframeSing hinvSing nabla2Tensor nabla2Ric hNabla2 hRicciId
        hRicTrace13 hLower hPair hOutput hFirst hRic
  exact
    ricciCommLoc (I := I) S S.base.rm04 gInv frame ({x₀} : Set M)
      nabla2Ric hbianchi hHess hsecond






omit [SigmaCompactSpace M] in
theorem ricciEvolCore
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv :
      Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E))
    (nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real)
    (nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (x₀ : M)
    (hGamma :
      ChristoffelEvolutionEquationInFrameOn (I := I) S gInv
        (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic)
    (hginv_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => gInv (t : Real) y a b) x₀)
    (hN_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => nablaRic (t : Real) y a b c) x₀)
    (hginv_zero :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ d k l : CoordinateIdx (𝕜 := Real) E,
          inverseMetricCovDerivCompInFrame (I := I) gInv
            (S.family.connection (t : Real)) (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            (t : Real) x₀ d k l = 0)
    (hnabla2_at :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c e : CoordinateIdx (𝕜 := Real) E,
          nabla2Ric (t : Real) x₀ a b c e =
            ricciSecondCovDerivCompInFrame
              (I := I) S (coordinateFrameAt (I := I) x₀)
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic
              (t : Real) x₀ a b c e)
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
    (hcomm : RicciContractedCommutatorsInFrameOnLocal
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀)
      ({x₀} : Set M) nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal (I := I) S Rm04 gInv
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolLocal
    (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
    nabla2Ric
    (ricciVarCore
      (I := I) S hS gInv nablaRic nabla2Ric Rm13 x₀ hGamma
      hginv_mdiff hN_mdiff hginv_zero hnabla2_at
      hRicTrace hRm hcurv hmix)
    hcomm








omit [SigmaCompactSpace M] in
theorem ricciEvolutionEquationInCoordFrameAt_of_christoffelEvolution_nabla2_commutators
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
      (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) nabla2Ric) :
    RicciEvolutionEquationInFrameOnLocal (I := I) S Rm04 gInv
      (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
      (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
  ricciEvolutionEquationInFrameOnLocal_of_variation_commutators
    (I := I) S Rm04 gInv (coordinateFrameAt (I := I) x₀) ({x₀} : Set M)
    nabla2Ric
    (ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution_nabla2
      (I := I) S hS gInv gInvDt nablaRic nabla2Ric Rm13 x₀ hmetricReg
      hnablaReg hRicTrace hRm hcurv hmix)
    hcomm



omit [SigmaCompactSpace M] in
theorem evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators
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
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j)
      (roughLapRicInFrame (M := M) gInv nabla2Ric (t : Real) x₀ i j -
        2 * rmRicciContractionCompInFrame (I := I) S Rm04 gInv
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀ i j -
        2 * ricciQuadraticCompInFrame (I := I) S gInv
          (coordinateFrameAt (I := I) x₀) (t : Real) x₀ i j)
      D.carrier
      (t : Real) := by
  have h :=
    ricciEvolutionEquationInCoordFrameAt_of_christoffelEvolution_nabla2_commutators
      (I := I) S hS Rm13 Rm04 gInv gInvDt nablaRic nabla2Ric x₀ hmetricReg
      hnablaReg hRicTrace hRm hcurv hmix hcomm
  have hAt := h t x₀ (by simp) i j
  simpa [ricciEvolutionRHSInFrame] using hAt








theorem coordRicciEvol
    [I.Boundaryless]
    [IsManifold I (∞ + 1) M]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (x₀ : M)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    HasDerivWithinAt
      (fun s : Real =>
        ricciCompInFrame (I := I) S (coordinateFrameAt (I := I) x₀) s x₀ i j)
      (ricciEvolutionRHSInFrame
        (I := I) S S.base.rm04 (coordInv (I := I) S x₀)
        (coordinateFrameAt (I := I) x₀)
        (coordRoughRic (I := I) S x₀ (coordNab2Ric (I := I) S x₀))
        (t : Real) x₀ i j)
      D.carrier
      t := by
  let frame : CoordinateIdx (𝕜 := Real) E -> (x : M) -> TangentSpace I x :=
    coordinateFrameAt (I := I) x₀
  let gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (CoordinateIdx (𝕜 := Real) E) :=
    coordInv (I := I) S x₀
  let nablaRic :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> Real :=
    nablaRicComp (I := I) S frame
  let nabla2Ric :
      Real -> M -> CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E ->
        CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real :=
    coordNab2Ric (I := I) S x₀
  have hmetric :
      MetricCovDerivDerivativeComponentsInFrameOnLocal
        (I := I) S frame (coordinateFrameSet (I := I) x₀)
        (fun t x d a b =>
          (-2 : Real) * nablaRic t x d a b) := by
    simpa [frame, nablaRic] using
      coordMetricMix (I := I) S hS x₀
        (coordMetricDeriv (I := I) S hS x₀)
  have hGamma :
      ChristoffelEvolutionEquationInFrameOn
        (I := I) S gInv frame
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic := by
    simpa [gInv, frame, nablaRic] using
      coordGammaEvol (I := I) S hS x₀ hmetric
  have hginv_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => gInv (t : Real) y a b) x₀ := by
    intro τ a b
    simpa [gInv] using coordInvMdiff (I := I) S x₀ (τ : Real) a b
  have hN_mdiff :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c : CoordinateIdx (𝕜 := Real) E,
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => nablaRic (t : Real) y a b c) x₀ := by
    intro τ a b c
    simpa [nablaRic, frame] using
      coordNablaReg (I := I) S x₀ (τ : Real) a b c
  have hginv_zero :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ d k l : CoordinateIdx (𝕜 := Real) E,
          inverseMetricCovDerivCompInFrame (I := I) gInv
            (S.family.connection (t : Real)) frame
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            (t : Real) x₀ d k l = 0 := by
    intro τ d k l
    simpa [gInv, frame] using coordInvCovZero (I := I) S x₀ τ d k l
  have hnabla2_at :
      ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
        ∀ a b c e : CoordinateIdx (𝕜 := Real) E,
          nabla2Ric (t : Real) x₀ a b c e =
            ricciSecondCovDerivCompInFrame
              (I := I) S frame
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) nablaRic
              (t : Real) x₀ a b c e := by
    intro τ a b c e
    simpa [nabla2Ric, nablaRic, frame] using
      coordNab2At (I := I) S x₀ (τ : Real) a b c e
  have hmix :
      ChristoffelVariationMixedDerivativeInFrameOnRegular
          (I := I) S frame
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          (christoffelEvolutionRHSInFrame (M := M) gInv nablaRic) := by
    simpa [gInv, frame, nablaRic] using
      coordGammaMix (I := I) S hS x₀ hGamma
  have hcomm :
      RicciContractedCommutatorsInFrameOnLocal
        (I := I) S S.base.rm04 gInv frame ({x₀} : Set M) nabla2Ric := by
    simpa [gInv, frame, nabla2Ric] using
      coordCommAt (I := I) S hS x₀
  have hEvol :
      RicciEvolutionEquationInFrameOnLocal
        (I := I) S S.base.rm04 gInv frame ({x₀} : Set M)
        (roughLapRicInFrame (M := M) gInv nabla2Ric) :=
    ricciEvolCore
      (I := I) S hS S.base.rm13 S.base.rm04 gInv nablaRic nabla2Ric x₀
      hGamma hginv_mdiff hN_mdiff hginv_zero hnabla2_at
      (ricciTraceOfSol (I := I) S)
      (rm13OfSol (I := I) S)
      (connCurvOfSol (I := I) S hS x₀)
      hmix hcomm
  have hAt := hEvol t x₀ (by simp) i j
  simpa [gInv, frame, nabla2Ric, coordRoughRic, ricciEvolutionRHSInFrame] using hAt

end CoordinateFrameRicciEvolution

end Components

end DifferentialGeometry.PDE.RicciFlow
