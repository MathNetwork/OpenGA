import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.TfHeatAssembly

set_option autoImplicit false
set_option linter.style.longLine false







noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff BigOperators
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]


def scalGradSq
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    (S.family.metric t).inner x
      (DifferentialGeometry.Integral.Connection.gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x)
      (DifferentialGeometry.Integral.Connection.gradientAt (I := I) (flowG (I := I) S) t (S.scalar t) x)


def tfLapBook
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  fun t x =>
    DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
      (fun y : M => tfRicNormSq S.scalar (ricciNorm (I := I) S) t y) x




noncomputable def ricciNablaSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 3 :=
  (CanonicalSpatialDerivs0S.of_smooth_connection
    (E := E) (H := H) (I := I) (M := M)
    (S.base.connection t)
    (by
      simpa [SolutionFamily.connection, metricCov] using
        metricCov_smooth (I := I) (M := M) (S.base.metric t))
    (S.ricci t)).nablaA



noncomputable def ricciNormDuSec
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  DifferentialGeometry.Integral.Connection.duSec (I := I)
    (fun y : M =>
      DifferentialGeometry.Integral.Connection.normSq02 (I := I) (S.base.metric t) y (S.ricci t y))
    (by
      exact DifferentialGeometry.Integral.Connection.norm02_smooth (I := I) (M := M)
        (S.base.metric t) (S.ricci t))


def pinchCoupleSol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) :
    Real -> M -> Real :=
  ricciGradCoupleSq (I := I)
    (fun t : Real => S.family.metric t) S.scalar
    (fun t y => S.ricci t y)
    (fun t y => ricciNablaSec (I := I) S t y)








omit [Module.Finite ℝ E] in
theorem pinchEvol_solSec
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (epsilon : Real)
    (hsetup : PinchEvolOn (I := I) (D := D) (flowG (I := I) S)
      S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon)
    (hscalar : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x)
    (htfDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) x)
    (hscalarDiff : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real) (S.scalar (t : Real)) x) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) (flowG (I := I) S)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchBookRHS (I := I) (flowG (I := I) S)
            S.scalar (ricciNorm (I := I) S) (scalGradSq (I := I) S)
            (pinchCoupleSol (I := I) S)
            (cubicQ S.scalar (ricciNorm (I := I) S)
              (ricciCube (I := I) S))
            epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  classical
  let Idx := DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E
  let basis :
      forall (_t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
        Module.Basis Idx Real (TangentSpace I x) :=
    fun _t x => DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      forall (_t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (_x : M),
        Idx -> Idx -> Real :=
    fun t x i j => coordInv (I := I) S x (t : Real) x i j
  refine pinchEvol_sec (I := I) (Idx := Idx) (G := flowG (I := I) S)
    S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
    (scalGradSq (I := I) S)
    (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
    (fun t => S.ricci t) (fun t => ricciNablaSec (I := I) S t)
    (fun t => ricciNormDuSec (I := I) S t)
    epsilon hsetup hscalar ?_ htfDiff hscalarDiff
    basis gInv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t x
    simp [scalGradSq, flowG]
  · intro t x
    simpa [basis, gInv, flowG] using coordInvReal (I := I) S x (t : Real)
  · intro t x
    simp [ricciGradSq, ricciNablaSec, flowG,
      CanonicalSpatialDerivs0S.of_smooth_connection]
  · intro t x
    simp [ricciNorm, flowG]
  · intro t
    exact (flowG (I := I) S).metricCompatible (t : Real)
  · intro t
    simpa [ricciNablaSec, flowG] using
      (CanonicalSpatialDerivs0S.of_smooth_connection
        (E := E) (H := H) (I := I) (M := M)
        (S.base.connection (t : Real))
        (by
          simpa [SolutionFamily.connection, metricCov] using
            metricCov_smooth (I := I) (M := M)
              (S.base.metric (t : Real)))
        (S.ricci (t : Real))).first
  · intro t
    simpa [ricciNormDuSec, flowG] using
      DifferentialGeometry.Integral.Connection.duSec_realizes (I := I)
        (fun y : M =>
          DifferentialGeometry.Integral.Connection.normSq02 (I := I)
            ((flowG (I := I) S).metric (t : Real)) y
            (S.ricci (t : Real) y))
        (by
          simpa [flowG] using
            DifferentialGeometry.Integral.Connection.norm02_smooth (I := I) (M := M)
              (S.base.metric (t : Real)) (S.ricci (t : Real)))
  · intro t y
    simp [ricciNorm, DifferentialGeometry.Integral.Connection.normSq02, DifferentialGeometry.Integral.Connection.inner02, flowG]
  · intro t x
    have hf :
        ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
          (fun y : M =>
            DifferentialGeometry.Integral.Connection.normSq02 (I := I)
              ((flowG (I := I) S).metric (t : Real)) y
              (S.ricci (t : Real) y)) := by
      simpa [flowG] using
        DifferentialGeometry.Integral.Connection.norm02_smooth (I := I) (M := M)
          (S.base.metric (t : Real)) (S.ricci (t : Real))
    exact hf.contMDiffAt.mdifferentiableAt (by simp)


omit [Module.Finite ℝ E] in
theorem ricciSym_can
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x) := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv :
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real := fun k l =>
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := I) (S.base.metric t) x k l (extChartAt I x x)
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis gInv := by
    simpa [basis, gInv] using
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
        (I := I) (S.base.metric t) x
  have hInvSym : ∀ i j, gInv i j = gInv j i :=
    invMetric_symm (I := I) (S.base.metric t) x basis gInv hinv
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 :
      DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 :
      S.ricciAt t x =
        DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hLowerAt :
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hTrace :
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
        (S.base.rm04 t x) gInv basis :=
    DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13 (I := I) (S.base.metric t)
      basis gInv hinv (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt hInvSym
  exact ricciSym_rm04 (I := I) basis gInv
    (S.ricciAt t x) (S.base.rm04 t x) hTrace
    (DifferentialGeometry.Integral.Connection.rm04PairSymmAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    (DifferentialGeometry.Integral.Connection.rm04OutputSkewAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    (DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04))
    hInvSym



omit [Module.Finite ℝ E] in
theorem traceData_can
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
      (I := I) (S.base.metric t) (-(S.ricciAt t x))
      (-(S.scalar t x)) (S.base.rm04 t x) basis := by
  have hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric t)
  have hRm13 :
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 :
      DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 :
      S.ricciAt t x =
        DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hLowerAt :
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (S.base.rm13 t x) (S.base.rm04 t x) :=
    DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
      hRm13 hRm04 x
  have hcurv :
      DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) basis (S.base.rm04 t x)) :=
    DifferentialGeometry.Integral.Connection.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
      (I := I) (g := S.base.metric t)
      (Rm04 := S.base.rm04 t) (hRm04 := hRm04) basis
  have hRicFirst :
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
        (S.base.rm04 t x) DifferentialGeometry.Integral.Connection.delta3 basis :=
    firstTrace_delta (I := I) (S.base.metric t) horth
      (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      hRic13 hLowerAt
  have hScalarTrace :
      DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I) (S.scalar t x)
        (S.ricciAt t x) DifferentialGeometry.Integral.Connection.delta3 basis := by
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr
  exact DifferentialGeometry.Integral.Connection.traceDataOfFirst (I := I) (M := M) horth
    hcurv hRicFirst hScalarTrace




omit [Module.Finite ℝ E] in
theorem tfReactSmooth
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    tfRicReactRel
      S.scalar (ricciNorm (I := I) S)
      (tfRicNormSq S.scalar (ricciNorm (I := I) S))
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      (ricciReact (I := I) S) := by
  classical
  intro t x hR
  rcases DifferentialGeometry.Integral.Connection.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (ricciSym_can (I := I) S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag0⟩
  have hScalarTrace :
      DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I) (S.scalar t x)
        (S.ricciAt t x) DifferentialGeometry.Integral.Connection.delta3 basis := by
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr
  have hscalar :
      S.scalar t x =
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 :=
    scalar_eq_diag (I := I) hScalarTrace hdiag0
  have hdiag :
      DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
        (S.scalar t x) l1 l2 l3 basis := by
    exact ⟨hscalar, hdiag0.2⟩
  have hcube :
      ricciCube (I := I) S t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3 :=
    ricciCubeInv_diag (I := I) (S.base.metric t) horth hdiag0
  have hrel := tfRel_trace (I := I) (g := S.base.metric t)
    (Ric := S.ricciAt t x) (Rm04 := S.base.rm04 t x)
    (basis := basis) (traceData_can (I := I) S horth) hdiag hcube hR
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
        DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) (S.base.metric t) basis horth
  have hnorm :
      ricciNormAt (I := I) (S.base.ricciAt t x) basis =
        ricciNorm (I := I) S t x := by
    simpa [ricciNorm, SolutionOn.ricci, SolutionOn.ricciAt] using
      (ricciNorm_inner (I := I) (S.base.metric t)
        (S.base.ricciAt t x) basis hinv)
  have hreact :
      reactAt (I := I) (S.base.ricciAt t x) (S.base.rm04 t x) basis =
        ricciReact (I := I) S t x := by
    simpa [SolutionOn.ricciAt] using
      (reactAt_eq_react (I := I) S horth)
  simpa [tfRicNormSq, cubicQ, SolutionOn.scalar_eq_metricTrace,
    hnorm, hreact] using hrel




omit [Module.Finite ℝ E] in
theorem ricciDataSmooth
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    RicciNormHeatEquationOn
      (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
      (ricciGradSq (I := I) S) (ricciReact (I := I) S) ∧
    (∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      tfLapBook (I := I) S (t : Real) x =
        tfLap S.scalar
          (fun t x =>
            DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x)
      (scalGradSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x) := by
  refine ⟨ricciHeatSmooth (I := I) S _hS, ?_⟩
  intro t x
  have h := tfLapCore (I := I) S _hS (t : Real) (D.regular_subset t.2) x
  simpa [tfLapBook, tfLap, scalarSqLap, scalGradSq, tfRicNormSq,
    tfRicNormSqAt, ricciNormLap, flowG] using h



omit [Module.Finite ℝ E] in
theorem tfLapBook_eq
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      tfLapBook (I := I) S (t : Real) x =
        tfLap S.scalar
          (fun t x =>
            DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
              (S.scalar t) x)
          (scalGradSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x :=
  (ricciDataSmooth (I := I) S hS hdim).2







omit [Module.Finite ℝ E] in
theorem tfDataSmooth
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∃ reaction : Real -> M -> Real,
      RicciNormHeatEquationOn
        (D := D) (ricciNorm (I := I) S) (ricciNormLap (I := I) S)
        (ricciGradSq (I := I) S) reaction ∧
      (∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
        tfLapBook (I := I) S (t : Real) x =
          tfLap S.scalar
            (fun t x =>
              DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
            (scalGradSq (I := I) S) (ricciNormLap (I := I) S) (t : Real) x) ∧
      tfRicReactRel
        S.scalar (ricciNorm (I := I) S)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S))
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
        reaction := by
  rcases ricciDataSmooth (I := I) S _hS _hdim with ⟨hRic, hLap⟩
  exact ⟨ricciReact (I := I) S, hRic, hLap, tfReactSmooth (I := I) S _hdim⟩





omit [Module.Finite ℝ E] in
theorem tfBookData
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (_hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (_hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    ∃ (ricciNormLap reaction : Real -> M -> Real),
      RicciNormHeatEquationOn
        (D := D) (ricciNorm (I := I) S) ricciNormLap
        (ricciGradSq (I := I) S) reaction ∧
      (∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
        tfLapBook (I := I) S (t : Real) x =
          tfLap S.scalar
            (fun t x =>
              DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
                (S.scalar t) x)
            (scalGradSq (I := I) S) ricciNormLap (t : Real) x) ∧
      tfRicReactRel
        S.scalar (ricciNorm (I := I) S)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S))
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
        reaction := by
  rcases tfDataSmooth (I := I) S _hS _hdim with ⟨reaction, hRic, hLap, hRel⟩
  exact ⟨ricciNormLap (I := I) S, reaction, hRic, hLap, hRel⟩








omit [Module.Finite ℝ E] in
theorem tfHeat_book
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq S.scalar (ricciNorm (I := I) S))
      (tfLapBook (I := I) S)
      (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      S.scalar
      (ricciNorm (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) := by
  let G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real := flowG (I := I) S
  let scalarLap : Real -> M -> Real :=
    fun t x => DifferentialGeometry.Integral.Connection.laplacianAt (I := I) G t (S.scalar t) x
  have hmetric : ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      G.metric (t : Real) = S.family.metric (t : Real) := by
    intro t
    rfl
  have hconnection : ∀ t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D,
      G.connection (t : Real) = S.family.connection (t : Real) := by
    intro t
    rfl
  have hscalar :
      ScalarEvolutionEquationOn (D := D) S.scalar scalarLap
        (ricciNorm (I := I) S) := by
    simpa [scalarLap, ricciNorm] using
      (scalarEvolOfSmooth (I := I) (M := M) S hS G hmetric hconnection)
  have hbridge :
      ∃ (ricciNormLap reaction : Real -> M -> Real),
        RicciNormHeatEquationOn
          (D := D) (ricciNorm (I := I) S) ricciNormLap
          (ricciGradSq (I := I) S) reaction ∧
        (∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
          tfLapBook (I := I) S (t : Real) x =
            tfLap S.scalar scalarLap (scalGradSq (I := I) S) ricciNormLap
              (t : Real) x) ∧
        tfRicReactRel
          S.scalar (ricciNorm (I := I) S)
          (tfRicNormSq S.scalar (ricciNorm (I := I) S))
          (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
          reaction := by
    simpa [scalarLap, G] using tfBookData (I := I) S hS hdim
  rcases hbridge with ⟨ricciNormLap, reaction, hRic, hLap, hRel⟩
  have hcore :
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S))
        (tfLap S.scalar scalarLap (scalGradSq (I := I) S) ricciNormLap)
        (ricciGradSq (I := I) S)
        (scalGradSq (I := I) S)
        S.scalar
        (ricciNorm (I := I) S)
        (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) :=
    tfHeat_base
      (D := D)
      S.scalar scalarLap
      (ricciNorm (I := I) S)
      ricciNormLap
      (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      reaction
      hscalar hRic hRel
  intro t x hR
  have hcore' := hcore t x hR
  simpa [hLap t x] using hcore'





omit [Module.Finite ℝ E] in
theorem tfHeat_sol
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq S.scalar (ricciNorm (I := I) S))
      (tfLapBook (I := I) S)
      (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      S.scalar
      (ricciNorm (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S)) := by
  exact tfHeat_book (I := I) S (smoothOfSol (I := I) S hS) hdim



omit [Module.Finite ℝ E] in
theorem tfNonneg_sol
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3) :
    forall t x,
      0 <= tfRicNormSq S.scalar (ricciNorm (I := I) S) t x := by
  classical
  intro t x
  rcases DifferentialGeometry.Integral.Connection.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (ricciSym_can (I := I) S t x) with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hscalarTrace :=
    scalarTrace_delta (I := I) (S.base.metric t) (S.ricciAt t x) horth
  have hscalar :
      S.scalar t x = DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 := by
    calc
      S.scalar t x =
          DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) (S.family.metric t)
            (S.ricciAt t x) := SolutionOn.scalar_eq_metricTrace (I := I) S t x
      _ = DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) (S.base.metric t)
            (S.ricciAt t x) := by rfl
      _ = DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 := by
            exact scalar_eq_diag (I := I) hscalarTrace hdiag
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
        DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) (S.base.metric t)
      basis horth
  have hnorm :
      ricciNorm (I := I) S t x =
        ricciNormAt (I := I) (S.ricciAt t x) basis := by
    calc
      ricciNorm (I := I) S t x =
          normSq0S (I := I) (S.base.metric t) x 2 (S.ricciAt t x) := by
            simp [ricciNorm, SolutionOn.family, SolutionOn.ricci,
              SolutionOn.ricciAt]
      _ = ricciNormAt (I := I) (S.ricciAt t x) basis := by
            exact (ricciNorm_inner (I := I) (S.base.metric t)
              (S.ricciAt t x) basis hinv).symm
  have htf :
      tfRicNormSq S.scalar (ricciNorm (I := I) S) t x =
        DifferentialGeometry.Integral.Connection.tracefreeRicciEigenNormSq3 l1 l2 l3 := by
    rw [tfRicNormSq, tracefreeRicciNormSqOf, tracefreeRicciNormSqAtOf,
      hscalar, hnorm, ricciNormAt_diag (I := I) hdiag]
    unfold DifferentialGeometry.Integral.Connection.tracefreeRicciEigenNormSq3
      DifferentialGeometry.Integral.Connection.ricciEigenPairwiseGapSq3
      DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 DifferentialGeometry.Integral.Connection.ricciEigenScalar3
    ring
  rw [htf]
  exact DifferentialGeometry.Integral.Connection.tracefreeRicciEigenNormSq3_nonneg l1 l2 l3


omit [Module.Finite ℝ E] in
theorem tfDiff_sol
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDifferentiableAt I 𝓘(Real, Real)
        (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) x := by
  intro t x
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  simpa [tfRicNormSq, tracefreeRicciNormSqOf, tracefreeRicciNormSqAtOf] using
    (hSmooth.ricciRegular.ricci_norm_space (t : Real) ht x).sub
      (hSmooth.scalarRegular.scalar_sq_div_space (t : Real) ht x)



omit [Module.Finite ℝ E] in
theorem tfGrad_sol
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) x := by
  intro t x
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  let f : M -> Real := ricciNorm (I := I) S (t : Real)
  let h : M -> Real := fun y : M => S.scalar (t : Real) y ^ 2 / 3
  have hgrad_eq :
      (fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) =
        fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f y -
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) h y := by
    funext y
    simpa [f, h, flowG, tfRicNormSq, tracefreeRicciNormSqOf,
      tracefreeRicciNormSqAtOf] using
      DifferentialGeometry.Integral.Connection.gradientFun_sub (I := I) ((flowG (I := I) S).metric (t : Real))
        (hSmooth.ricciRegular.ricci_norm_space (t : Real) ht y)
        (hSmooth.scalarRegular.scalar_sq_div_space (t : Real) ht y)
  have hnormGrad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y) x := by
    simpa [f, flowG, SolutionOn.family] using
      hSmooth.ricciRegular.ricci_norm_grad (t : Real) ht x
  have hthirdGrad : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y) x := by
    simpa [h, flowG, SolutionOn.family] using
      hSmooth.scalarRegular.scalar_sq_div_grad (t : Real) ht x
  have hcombined : MDiffAt (T% fun y : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f y -
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) h y) x := by
    exact mdifferentiableAt_sub_section hnormGrad hthirdGrad
  have hsection_eq :
      (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real)) y) =
        (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f y -
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) h y) := by
    funext y
    simpa using congrFun hgrad_eq y
  rw [hsection_eq]
  exact hcombined



omit [Module.Finite ℝ E] in
theorem scalarPowGrad_sol
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (epsilon : Real)
    (hscalar : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
      MDiffAt (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) y := by
  intro t y
  let hSmooth := smoothOfSol (I := I) S hS
  have ht : (t : Real) ∈ D.carrier := D.regular_subset t.2
  let p : Real := -(2 - epsilon)
  let f : M -> Real := S.scalar (t : Real)
  let coeff : M -> Real := fun z : M => p * f z ^ (p - 1)
  have hcoeff : MDifferentiableAt I 𝓘(Real, Real) coeff y := by
    have hp :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun z : M => f z ^ (p - 1)) y :=
      DifferentialGeometry.Integral.Connection.mdifferentiableAt_rpow (I := I) (p - 1)
        (hSmooth.scalarRegular.scalar_space (t : Real) ht y)
        (hscalar t y)
    simpa [coeff] using mdifferentiableAt_const.mul hp
  have hgrad_eq :
      (fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) =
        coeff • fun z : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f z := by
    funext z
    simpa [p, f, coeff] using
      DifferentialGeometry.Integral.Connection.gradientFun_rpow (I := I) ((flowG (I := I) S).metric (t : Real))
        (p := p)
        (hSmooth.scalarRegular.scalar_space (t : Real) ht z)
        (hscalar t z)
  have hscalarGrad : MDiffAt (T% fun z : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f z) y := by
    simpa [f, flowG, SolutionOn.family] using
      hSmooth.scalarRegular.scalar_grad (t : Real) ht y
  have hsmul : MDiffAt (T% (coeff • fun z : M =>
      DifferentialGeometry.Integral.Connection.gradientFun (I := I)
        ((flowG (I := I) S).metric (t : Real)) f z)) y := by
    exact hcoeff.smul_section hscalarGrad
  have hsection_eq :
      (T% fun z : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I)
          ((flowG (I := I) S).metric (t : Real))
          (fun w : M => S.scalar (t : Real) w ^ (-(2 - epsilon))) z) =
        (T% (coeff • fun z : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real)) f z)) := by
    funext z
    simpa using congrFun hgrad_eq z
  rw [hsection_eq]
  exact hsmul







omit [Module.Finite ℝ E] in
theorem pinchEvol_sol
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    [IsManifold I 2 M] [IsManifold I 3 M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (hdim : forall (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (epsilon : Real)
    (hscalar : forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
      0 < S.scalar (t : Real) x) :
    forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) (x : M),
      HasDerivWithinAt
        (fun s : Real =>
          quotField (M := M)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) s x)
        (quotLap (I := I) (flowG (I := I) S)
            (tfRicNormSq S.scalar (ricciNorm (I := I) S))
            S.scalar (1 : Real) (2 - epsilon) (t : Real) x +
          pinchBookRHS (I := I) (flowG (I := I) S)
            S.scalar (ricciNorm (I := I) S) (scalGradSq (I := I) S)
            (pinchCoupleSol (I := I) S)
            (cubicQ S.scalar (ricciNorm (I := I) S)
              (ricciCube (I := I) S))
            epsilon (t : Real) x)
        D.carrier
        (t : Real) := by
  classical
  let scalarLap : Real -> M -> Real :=
    fun t x =>
      DifferentialGeometry.Integral.Connection.laplacianAt (I := I) (flowG (I := I) S) t
        (S.scalar t) x
  have hscalarHeat :
      ScalarEvolutionEquationOn (D := D) S.scalar scalarLap
        (ricciNorm (I := I) S) := by
    intro t x
    have h := scalarEvolOfSol (I := I) S hS (flowG (I := I) S)
      (by intro t; rfl) (by intro t; rfl) t x
    simpa [scalarLap, ricciNorm, flowG] using h
  have hSmooth := smoothOfSol (I := I) S hS
  have htfDiff := tfDiff_sol (I := I) S hS
  have hscalarDiff :
      forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
        MDifferentiableAt I 𝓘(Real, Real) (S.scalar (t : Real)) x := by
    intro t x
    exact hSmooth.scalarRegular.scalar_space (t : Real)
      (D.regular_subset t.2) x
  have htfNonneg :
      forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) y,
        0 <= tfRicNormSq S.scalar (ricciNorm (I := I) S) (t : Real) y := by
    intro t y
    exact tfNonneg_sol (I := I) S hdim (t : Real) y
  have hgradTf := tfGrad_sol (I := I) S hS
  have hgradScalar :
      forall (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D) x,
        MDiffAt (T% fun y : M =>
          DifferentialGeometry.Integral.Connection.gradientFun (I := I)
            ((flowG (I := I) S).metric (t : Real))
            (S.scalar (t : Real)) y) x := by
    intro t x
    exact hSmooth.scalarRegular.scalar_grad (t : Real)
      (D.regular_subset t.2) x
  have hgradScalarPow := scalarPowGrad_sol (I := I) S hS epsilon hscalar
  have hsetup : PinchEvolOn (I := I) (D := D) (flowG (I := I) S)
      S.scalar (ricciNorm (I := I) S) (ricciGradSq (I := I) S)
      (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon := by
    refine pinchEvol_setup (I := I) (G := flowG (I := I) S)
      S.scalar scalarLap (ricciNorm (I := I) S) (tfLapBook (I := I) S)
      (ricciGradSq (I := I) S) (scalGradSq (I := I) S)
      (cubicQ S.scalar (ricciNorm (I := I) S) (ricciCube (I := I) S))
      epsilon (tfHeat_sol (I := I) S hS hdim) hscalarHeat ?_ ?_
      htfDiff hscalarDiff htfNonneg hscalar hgradTf hgradScalar
      hgradScalarPow
    · intro t x
      rfl
    · intro t x
      rfl
  exact pinchEvol_solSec (I := I) S epsilon hsetup hscalar htfDiff
    hscalarDiff

end DifferentialGeometry.PDE.RicciFlow
