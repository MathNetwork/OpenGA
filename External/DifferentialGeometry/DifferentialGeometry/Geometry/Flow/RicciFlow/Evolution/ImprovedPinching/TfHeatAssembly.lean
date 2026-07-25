import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.HamiltonRHS

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




omit [TopologicalSpace M] in
theorem tfHeat_eigen
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq ricciTraceCube reaction : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRicHeat : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq reaction)
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hreaction : ∀ t x,
      reaction t x = ricciReact3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq
      (cubicQ scalar ricciNormSq ricciTraceCube) := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap ricciNormSq ricciNormLap
    nablaRicNormSq gradScalarNormSq
    (cubicQ scalar ricciNormSq ricciTraceCube) reaction
    hscalarHeat hRicHeat
    (tfRel_from_eigen
      scalar ricciNormSq ricciTraceCube reaction
      l1 l2 l3 hscalar hnorm hcube hreaction)



omit [TopologicalSpace M] in
theorem tfHeat_diag
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (scalar scalarLap ricciNormSq ricciNormLap
      nablaRicNormSq gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap ricciNormSq)
    (hRicHeat : RicciNormHeatEquationOn
      (D := D) ricciNormSq ricciNormLap nablaRicNormSq
        (diagReact3 l1 l2 l3))
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar ricciNormSq)
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      nablaRicNormSq gradScalarNormSq scalar ricciNormSq
      (cubicQ scalar ricciNormSq ricciTraceCube) := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap ricciNormSq ricciNormLap
    nablaRicNormSq gradScalarNormSq
    (cubicQ scalar ricciNormSq ricciTraceCube)
    (diagReact3 l1 l2 l3)
    hscalarHeat hRicHeat
    (tfRel_from_diag
      (M := M)
      scalar ricciNormSq ricciTraceCube l1 l2 l3 hscalar hnorm hcube)




omit [Module.Finite ℝ E] in
theorem tfHeat_sec6
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (roughLapRic : Real -> M -> Idx -> Idx -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Idx -> Idx -> Idx -> Real)
    (scalar scalarLap gradScalarNormSq Q : Real -> M -> Real)
    (hscalar : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (hInvSym : forall t x i j, gInv t x i j = gInv t x j i)
    (hRicSym : forall t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hRel : tfRicReactRel
      scalar (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      Q (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame) Q := by
  exact tfHeat_base
    (D := D)
    scalar scalarLap
    (ricciNormSqInFrame (I := I) S gInv frame)
    ricciNormLap
    (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
    gradScalarNormSq Q
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    hscalar
    (ricciNormHeatEquationOn_of_solution_canonical_laplacian
      (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
      h_inv h_ricci hInvSym hRicSym h_lap)
    hRel



omit [Module.Finite ℝ E] in
theorem tfHeat_point
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (htrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube) := by
  classical
  have hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i := by
    intro t x i j
    rw [hInv t x i j, hInv t x j i]
    fin_cases i <;> fin_cases j <;> simp [DifferentialGeometry.Integral.Connection.delta3]
  have hRel :=
    tfRel_point_sec6 (I := I) S Rm04 gInv frame heatBasis eigBasis
      scalar ricciTraceCube l1 l2 l3 hheatBasis hheat heig htrace hdiag hcube hInv
  exact tfHeat_sec6
    (I := I) S Rm04 gInv frame roughLapRic ricciNormLap nablaRic
    scalar scalarLap gradScalarNormSq
    (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
      ricciTraceCube)
    hscalarHeat h_inv h_ricci hInvSym hRicSym h_lap hRel



omit [Module.Finite ℝ E] in
theorem tfHeat_pfirst
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (heig : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) (eigBasis t x) (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
        (Rm04 t x) DifferentialGeometry.Integral.Connection.delta3 (eigBasis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
        (S.ricciAt t x) DifferentialGeometry.Integral.Connection.delta3 (eigBasis t x))
    (hdiag : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    tfRicHeatOn
      (D := D)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      gradScalarNormSq scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube) := by
  refine tfHeat_point (I := I) S Rm04 gInv frame heatBasis eigBasis
    roughLapRic ricciNormLap nablaRic scalar scalarLap gradScalarNormSq
    ricciTraceCube l1 l2 l3 hscalarHeat h_inv h_ricci h_lap hheatBasis hheat heig
    ?_ hdiag hcube hInv hRicSym
  intro t x
  exact DifferentialGeometry.Integral.Connection.traceDataOfFirst (I := I) (M := M) (heig t x)
    (hcurv t x) (hRicFirst t x) (hScalarTrace t x)






omit [Module.Finite ℝ E] in
theorem tfHeat_eig
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
          (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DifferentialGeometry.Integral.Connection.delta3 basis)
    (hScalarTrace : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
          (S.ricciAt t x) DifferentialGeometry.Integral.Connection.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 ricciTraceCube : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      (∀ t x,
        ricciTraceCube t x =
          DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
          ricciTraceCube) := by
  classical
  have heigExists : ∀ t x,
      ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        ∃ l1 l2 l3 : Real,
          DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
            (I := I) (S.base.metric t) x basis ∧
          DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
            (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3) l1 l2 l3 basis := by
    intro t x
    exact DifferentialGeometry.Integral.Connection.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (hRicSymAt t x)
  choose eigBasis l1 l2 l3 heig using heigExists
  let cube : Real -> M -> Real := fun t x =>
    ricciCubeInvAt (I := I) (S.base.metric t) (S.ricciAt t x)
  have heigOn : ∀ t x,
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x) := by
    intro t x
    exact (heig t x).1
  have hdiag0 : ∀ t x,
      DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
        (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
        (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    exact (heig t x).2
  have hdiag : ∀ t x,
      DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    rcases hdiag0 t x with ⟨hscalar0, hric⟩
    have hscalar :
        scalar t x =
          DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x) :=
      scalar_eq_diag (I := I) (hScalarTrace t x (eigBasis t x) (heigOn t x))
        (hdiag0 t x)
    exact ⟨hscalar, hric⟩
  have hcube : ∀ t x,
      cube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x) := by
    intro t x
    exact ricciCubeInv_diag (I := I) (S.base.metric t)
      (heigOn t x) (hdiag0 t x)
  refine ⟨eigBasis, l1, l2, l3, cube, heigOn, hdiag, hcube, ?_⟩
  exact tfHeat_pfirst (I := I) S Rm04 gInv frame heatBasis eigBasis
    roughLapRic ricciNormLap nablaRic scalar scalarLap gradScalarNormSq
    cube l1 l2 l3 hscalarHeat h_inv h_ricci h_lap hheatBasis hheat heigOn
    (fun t x => hcurv t x (eigBasis t x) (heigOn t x))
    (fun t x => hRicFirst t x (eigBasis t x) (heigOn t x))
    (fun t x => hScalarTrace t x (eigBasis t x) (heigOn t x))
    hdiag hcube hInv hRicSym



omit [Module.Finite ℝ E] in
theorem tfHeat_can
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
          (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DifferentialGeometry.Integral.Connection.delta3 basis)
    (hScalarTrace : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
          (S.ricciAt t x) DifferentialGeometry.Integral.Connection.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  classical
  rcases tfHeat_eig (I := I) S Rm04 gInv frame heatBasis roughLapRic
      ricciNormLap nablaRic scalar scalarLap gradScalarNormSq hscalarHeat h_inv
      h_ricci h_lap hheatBasis hheat hdim hRicSymAt hcurv hRicFirst
      hScalarTrace hInv hRicSym with
    ⟨eigBasis, l1, l2, l3, cube, heig, hdiag, hcube, hheatEq⟩
  have hcubeEq : cube = ricciCube (I := I) S := by
    funext t x
    calc
      cube t x =
          DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x) :=
            hcube t x
      _ = ricciCube (I := I) S t x := by
            simpa [ricciCube] using
              (ricciCubeInv_diag (I := I) (S.base.metric t)
                (heig t x) (hdiag t x)).symm
  refine ⟨eigBasis, l1, l2, l3, heig, hdiag, ?_⟩
  simpa [hcubeEq] using hheatEq





omit [Module.Finite ℝ E] in
theorem tfHeat_canR
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalar scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hRicHeat : RicciNormHeatEquationOn
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame))
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
          (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DifferentialGeometry.Integral.Connection.delta3 basis)
    (hScalarTrace : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I) (scalar t x)
          (S.ricciAt t x) DifferentialGeometry.Integral.Connection.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  classical
  have heigExists : ∀ t x,
      ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
        ∃ l1 l2 l3 : Real,
          DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
            (I := I) (S.base.metric t) x basis ∧
          DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
            (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3) l1 l2 l3 basis := by
    intro t x
    exact DifferentialGeometry.Integral.Connection.ricciEigen3 (I := I) (S.base.metric t)
      (S.ricciAt t x) (hdim t x) (hRicSymAt t x)
  choose eigBasis l1 l2 l3 heig using heigExists
  have heigOn : ∀ t x,
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (eigBasis t x) := by
    intro t x
    exact (heig t x).1
  have hdiag0 : ∀ t x,
      DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
        (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
        (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    exact (heig t x).2
  have hdiag : ∀ t x,
      DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
        (scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x) := by
    intro t x
    rcases hdiag0 t x with ⟨_hscalar0, hric⟩
    have hscalar :
        scalar t x =
          DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x) :=
      scalar_eq_diag (I := I) (hScalarTrace t x (eigBasis t x) (heigOn t x))
        (hdiag0 t x)
    exact ⟨hscalar, hric⟩
  have hcube : ∀ t x,
      ricciCube (I := I) S t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x) := by
    intro t x
    exact ricciCubeInv_diag (I := I) (S.base.metric t)
      (heigOn t x) (hdiag0 t x)
  have hRel :
      tfRicReactRel
        scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S))
        (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) :=
    tfRel_pfirst (I := I) S Rm04 gInv frame heatBasis eigBasis
      scalar (ricciCube (I := I) S) l1 l2 l3 hheatBasis hheat heigOn
      (fun t x => hcurv t x (eigBasis t x) (heigOn t x))
      (fun t x => hRicFirst t x (eigBasis t x) (heigOn t x))
      (fun t x => hScalarTrace t x (eigBasis t x) (heigOn t x))
      hdiag hcube hInv
  refine ⟨eigBasis, l1, l2, l3, heigOn, hdiag, ?_⟩
  exact tfHeat_base
    (D := D)
    scalar scalarLap
    (ricciNormSqInFrame (I := I) S gInv frame)
    ricciNormLap
    (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
    gradScalarNormSq
    (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
      (ricciCube (I := I) S))
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    hscalarHeat hRicHeat hRel




omit [Module.Finite ℝ E] in
theorem tfHeat_scalar
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
          (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRicFirst : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DifferentialGeometry.Integral.Connection.delta3 basis)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_can (I := I) S Rm04 gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic S.scalar scalarLap gradScalarNormSq hscalarHeat
    h_inv h_ricci h_lap hheatBasis hheat hdim hRicSymAt hcurv hRicFirst ?_
    hInv hRicSym
  intro t x basis horth
  have htr := scalarTrace_delta (I := I) (S.base.metric t)
    (S.ricciAt t x) horth
  simpa [SolutionOn.scalar_eq_metricTrace] using htr



omit [Module.Finite ℝ E] in
theorem tfHeat_trace
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x))
    (hcurv : ∀ (t : Real) (x : M)
      (basis : Module.Basis (Fin 3) Real (TangentSpace I x)),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) (S.base.metric t) x basis ->
        DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
          (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) basis (Rm04 t x)))
    (hRic13 : ∀ t x,
      S.ricciAt t x =
        DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) (Rm13 t x))
    (hLower : ∀ t x,
      DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
        (Rm13 t x) (Rm04 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_scalar (I := I) S Rm04 gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat h_inv
    h_ricci h_lap hheatBasis hheat hdim hRicSymAt hcurv ?_ hInv ?_
  · intro t x basis horth
    exact firstTrace_delta (I := I) (S.base.metric t) horth
      (S.ricciAt t x) (Rm13 t x) (Rm04 t x) (hRic13 t x) (hLower t x)
  · intro t x i j
    simpa [ricciCompInFrame] using
      hRicSymAt t x (frame i x) (frame j x)



omit [Module.Finite ℝ E] in
theorem tfHeat_lc
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Integral.Connection.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S Rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hRm13 : ∀ t,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (Rm13 t))
    (hRm04 : ∀ t,
      DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (Rm04 t))
    (hRic13 : ∀ t x,
      S.ricciAt t x =
        DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) (Rm13 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  have hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x) := by
    intro t x
    have hLowerAt :
        DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (Rm13 t x) (Rm04 t x) :=
      DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := Rm13 t) (Rm04 := Rm04 t)
        (hRm13 t) (hRm04 t) x
    have hTrace :
        DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (Rm04 t x) DifferentialGeometry.Integral.Connection.delta3 (heatBasis t x) :=
      firstTrace_delta (I := I) (S.base.metric t) (hheat t x)
        (S.ricciAt t x) (Rm13 t x) (Rm04 t x) (hRic13 t x) hLowerAt
    exact ricciSym_rm04 (I := I) (heatBasis t x) DifferentialGeometry.Integral.Connection.delta3
      (S.ricciAt t x) (Rm04 t x) hTrace
      (DifferentialGeometry.Integral.Connection.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t))
      (DifferentialGeometry.Integral.Connection.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t))
      (DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t))
      delta3_symm
  refine tfHeat_trace (I := I) S Rm13 Rm04 gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat h_inv
    h_ricci h_lap hheatBasis hheat hdim hRicSymAt ?_ hRic13 ?_ hInv
  · intro t x basis _horth
    exact
      DifferentialGeometry.Integral.Connection.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := Rm04 t) (hRm04 := hRm04 t) basis
  · intro t x
    exact DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
      (I := I) (g := S.base.metric t)
      (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
        (S.base.metric t))
      (Rm13 := Rm13 t) (Rm04 := Rm04 t)
      (hRm13 t) (hRm04 t) x



omit [Module.Finite ℝ E] in
theorem tfHeat_metric
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S S.base.rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_lc (I := I) S S.base.rm13 S.base.rm04 gInv frame heatBasis
    roughLapRic ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat
    h_inv h_ricci h_lap hheatBasis hheat hdim ?_ ?_ ?_ hInv
  · intro t
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  · intro t
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  · intro t x
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x



omit [Module.Finite ℝ E] in
theorem tfHeat_metric_smooth
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S S.base.rm04 gInv frame roughLapRic)
    (h_lap : DifferentialGeometry.Integral.Connection.RicciNormScalarLaplacianExpansionInFrame
      (I := I) (M := M) (Time := Real) ricciNormLap roughLapRic
      (ricciTwoTensorField (I := I) S) gInv frame nablaRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  refine tfHeat_metric (I := I) S gInv frame heatBasis roughLapRic
    ricciNormLap nablaRic scalarLap gradScalarNormSq hscalarHeat h_inv
    h_ricci h_lap hheatBasis hheat hdim hInv




omit [Module.Finite ℝ E] in
theorem tfHeat_ricci
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (hRicHeat : RicciNormHeatEquationOn
      (D := D)
      (ricciNormSqInFrame (I := I) S gInv frame)
      ricciNormLap
      (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
      (ricciNormCurvatureReactionInFrame
        (I := I) S S.base.rm04 gInv frame))
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  have hcov : ∀ t,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) := by
    intro t
    exact
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  have hRm13 : ∀ t,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    intro t
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 : ∀ t,
      DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    intro t
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 : ∀ t x,
      S.ricciAt t x =
        DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    intro t x
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x) := by
    intro t x
    have hLowerAt :
        DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (S.base.rm13 t x) (S.base.rm04 t x) :=
      DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
        (hRm13 t) (hRm04 t) x
    have hTrace :
        DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (S.base.rm04 t x) DifferentialGeometry.Integral.Connection.delta3 (heatBasis t x) :=
      firstTrace_delta (I := I) (S.base.metric t) (hheat t x)
        (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
        (hRic13 t x) hLowerAt
    exact ricciSym_rm04 (I := I) (heatBasis t x) DifferentialGeometry.Integral.Connection.delta3
      (S.ricciAt t x) (S.base.rm04 t x) hTrace
      (DifferentialGeometry.Integral.Connection.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (DifferentialGeometry.Integral.Connection.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      delta3_symm
  refine tfHeat_canR (I := I) S S.base.rm04 gInv frame heatBasis
    ricciNormLap nablaRic S.scalar scalarLap gradScalarNormSq
    hscalarHeat hRicHeat hheatBasis hheat hdim hRicSymAt ?_ ?_ ?_ hInv
  · intro t x basis _horth
    exact
      DifferentialGeometry.Integral.Connection.algebraicCurvatureSymmetries3_standardRmCompAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t) basis
  · intro t x basis horth
    have hLowerAt :
        DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (S.base.rm13 t x) (S.base.rm04 t x) :=
      DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
        (hRm13 t) (hRm04 t) x
    exact firstTrace_delta (I := I) (S.base.metric t) horth
      (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
      (hRic13 t x) hLowerAt
  · intro t x basis horth
    have htr := scalarTrace_delta (I := I) (S.base.metric t)
      (S.ricciAt t x) horth
    simpa [SolutionOn.scalar_eq_metricTrace] using htr




omit [Module.Finite ℝ E] in
theorem tfHeat_mc
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 2 M] [IsManifold I 3 M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (roughLapRic : Real -> M -> Fin 3 -> Fin 3 -> Real)
    (ricciNormLap : Real -> M -> Real)
    (nablaRic : Real -> M -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (basis : (x : M) -> Module.Basis (Fin 3) Real (TangentSpace I x))
    (X : (x : M) -> Fin 3 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (roughA : Real -> (x : M) -> DifferentialGeometry.Integral.Connection.Tensor02At (I := I) x)
    (nablaA : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 3)
    (nabla2A : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 4)
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (scalarLap gradScalarNormSq : Real -> M -> Real)
    (hscalarHeat : ScalarEvolutionEquationOn
      (D := D) S.scalar scalarLap
      (ricciNormSqInFrame (I := I) S gInv frame))
    (h_inv : InverseMetricEvolutionEquationInFrame (I := I) S gInv frame Set.univ)
    (h_ricci : RicciEvolutionEquationInFrame
      (I := I) S S.base.rm04 gInv frame roughLapRic)
    (hheatBasis : ∀ (t : Real) (x : M) (i : Fin 3),
      heatBasis t x i = frame i x)
    (hheat : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (heatBasis t x))
    (hdim : ∀ (_t : Real) (x : M),
      Module.finrank Real (TangentSpace I x) = 3)
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hframe : ∀ x i, basis x i = frame i x)
    (hinv : ∀ t x,
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) (M := M)
        (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x,
      DifferentialGeometry.Integral.Connection.SmoothBasisFieldsAt (I := I) (basis x) (X x))
    (hlapTrace : ∀ t x,
      ricciNormLap t x =
        DifferentialGeometry.Integral.Connection.metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hA : ∀ t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 2 (S.base.connection t) (A t) (nablaA t))
    (h2 : ∀ t,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) 3 (S.base.connection t) (nablaA t) (nabla2A t))
    (hdu : ∀ t,
      DifferentialGeometry.Integral.Connection.DuFieldRealizes (I := I)
        (fun y : M => DifferentialGeometry.Integral.Connection.normSq02 (I := I) (S.base.metric t) y (A t y))
        (du t))
    (hHess : ∀ t x,
      DifferentialGeometry.Integral.Connection.HessianRealizesNablaDuAt (I := I) (S.base.connection t) (du t)
        (normSecond t) x)
    (hrough : ∀ t x,
      DifferentialGeometry.Integral.Connection.RoughLap0SRealizesMetricTraceInBasis (I := I)
        (basis x) (gInv t x) (s := 2) (roughA t x) (nabla2A t x))
    (hAComp : ∀ t x i j,
      A t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        ricciTwoTensorField (I := I) S t x (frame i x) (frame j x))
    (hroughComp : ∀ t x i j,
      roughA t x (DifferentialGeometry.Integral.Connection.vec2 (I := I) (frame i x) (frame j x)) =
        roughLapRic t x i j)
    (hnablaComp : ∀ t x a i j,
      nablaA t x (DifferentialGeometry.Integral.Connection.vec3 (I := I) (frame a x) (frame i x) (frame j x)) =
        nablaRic t x a i j) :
    ∃ (eigBasis : (t : Real) -> (x : M) ->
        Module.Basis (Fin 3) Real (TangentSpace I x))
      (l1 l2 l3 : Real -> M -> Real),
      (∀ t x,
        DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
          (I := I) (S.base.metric t) x (eigBasis t x)) ∧
      (∀ t x,
        DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (S.ricciAt t x)
          (S.scalar t x) (l1 t x) (l2 t x) (l3 t x) (eigBasis t x)) ∧
      tfRicHeatOn
        (D := D)
        (tfRicNormSq S.scalar (ricciNormSqInFrame (I := I) S gInv frame))
        (tfLap S.scalar scalarLap gradScalarNormSq ricciNormLap)
        (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        gradScalarNormSq S.scalar
        (ricciNormSqInFrame (I := I) S gInv frame)
        (cubicQ S.scalar (ricciNormSqInFrame (I := I) S gInv frame)
          (ricciCube (I := I) S)) := by
  classical
  have hInvSym : ∀ t x i j, gInv t x i j = gInv t x j i := by
    intro t x i j
    rw [hInv t x i j, hInv t x j i]
    exact delta3_symm i j
  have hcov : ∀ t,
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (1 : WithTop ℕ∞) := by
    intro t
    exact
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  have hRm13 : ∀ t,
      DifferentialGeometry.Integral.Connection.Rm13RealizesConnection (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm13 t) := by
    intro t
    simpa [SolutionFamily.rm13, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm13
  have hRm04 : ∀ t,
      DifferentialGeometry.Integral.Connection.Rm04RealizesConnection (I := I) (S.base.metric t)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t)) (S.base.rm04 t) := by
    intro t
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have hRic13 : ∀ t x,
      S.ricciAt t x =
        DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) (S.base.rm13 t x) := by
    intro t x
    simpa [SolutionOn.ricciAt, SolutionFamily.ricciAt, SolutionFamily.rm13]
      using (metricCurvData (I := I) (M := M) (S.base.metric t)).h_ricci13 x
  have hRicSymAt : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) (S.ricciAt t x) := by
    intro t x
    have hLowerAt :
        DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) (S.base.metric t) x
          (S.base.rm13 t x) (S.base.rm04 t x) :=
      DifferentialGeometry.Integral.Connection.rm04LowersRm13At_of_realizes
        (I := I) (g := S.base.metric t)
        (cov := DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I)
          (S.base.metric t))
        (Rm13 := S.base.rm13 t) (Rm04 := S.base.rm04 t)
        (hRm13 t) (hRm04 t) x
    have hTrace :
        DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) (S.ricciAt t x)
          (S.base.rm04 t x) DifferentialGeometry.Integral.Connection.delta3 (heatBasis t x) :=
      firstTrace_delta (I := I) (S.base.metric t) (hheat t x)
        (S.ricciAt t x) (S.base.rm13 t x) (S.base.rm04 t x)
        (hRic13 t x) hLowerAt
    exact ricciSym_rm04 (I := I) (heatBasis t x) DifferentialGeometry.Integral.Connection.delta3
      (S.ricciAt t x) (S.base.rm04 t x) hTrace
      (DifferentialGeometry.Integral.Connection.rm04PairSymmAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (DifferentialGeometry.Integral.Connection.rm04OutputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      (DifferentialGeometry.Integral.Connection.rm04InputSkewAt_of_leviCivita_realizes
        (I := I) (g := S.base.metric t)
        (Rm04 := S.base.rm04 t) (hRm04 := hRm04 t))
      delta3_symm
  have hRicSym : ∀ t x i j,
      ricciCompInFrame (I := I) S frame t x i j =
        ricciCompInFrame (I := I) S frame t x j i := by
    intro t x i j
    simpa [ricciCompInFrame] using hRicSymAt t x (frame i x) (frame j x)
  have hRicHeat :
      RicciNormHeatEquationOn
        (D := D) (ricciNormSqInFrame (I := I) S gInv frame)
        ricciNormLap (nablaRicciNormSqInFrame (M := M) nablaRic gInv)
        (ricciNormCurvatureReactionInFrame
          (I := I) S S.base.rm04 gInv frame) :=
    ricci_heat_mc (I := I) S S.base.rm04 gInv frame roughLapRic
      ricciNormLap nablaRic basis X A roughA nablaA nabla2A du normSecond
      h_inv h_ricci hInvSym hRicSym hframe hinv hfields hlapTrace
      hA h2 hdu hHess hrough hAComp hroughComp hnablaComp
  exact tfHeat_ricci (I := I) S gInv frame heatBasis ricciNormLap nablaRic
    scalarLap gradScalarNormSq hscalarHeat hRicHeat hheatBasis hheat hdim hInv

end DifferentialGeometry.PDE.RicciFlow
