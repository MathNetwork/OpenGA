import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFrameInvariant
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricDeriv
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SBochnerProduct

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false


































































noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]



private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := Real) (E := E) s

private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance





section Fields

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]


def nablaRm04NormSqIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.base.metric t) x 5 (nablaRm04Field (I := I) S t x)



def nabla2Rm04NormSqIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.base.metric t) x 6 (nabla2Rm04Field (I := I) S t x)









def nablaRm04ReactionIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 x) : Real -> M -> Real :=
  fun t x =>
    ricReactionContract (gInv t x) (ric t x)
        (fun I0 : Fin 5 -> Idx =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S t x)
            (fun i => basis x i) I0)
        (fun J0 : Fin 5 -> Idx =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S t x)
            (fun i => basis x i) J0) +
      2 * inner0S (I := I) (S.base.metric t) x 5
            (Tdot t x -
              metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
                (nabla3Rm04Field (I := I) S t x))
            (nablaRm04Field (I := I) S t x)

end Fields






section HeatEquation

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]



















omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04NormHeatEquationOn_intrinsic
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Xb : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nablaRmNormLap : Real -> M -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 x)
    (hinv : ∀ (t : Real) (x : M),
      MetricInverseInBasis (I := I) (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x : M, SmoothBasisFieldsAt (I := I) (basis x) (Xb x))
    (hdu : ∀ t : Real,
      DuFieldRealizes (I := I)
        (fun y : M => normSq0S (I := I) (S.base.metric t) y 5
          (nablaRm04Field (I := I) S t y)) (du t))
    (hHess : ∀ (t : Real) (x : M),
      HessianRealizesNablaDuAt (I := I) (S.family.connection t) (du t)
        (normSecond t) x)
    (hlapTrace : ∀ (t : Real) (x : M),
      nablaRmNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hT : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (I0 : Fin 5 -> Idx),
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S r x)
            (fun i => basis x i) I0)
        (tensor0SComponent (I := I) (Tdot (t : Real) x) (fun i => basis x i) I0)
        D.carrier (t : Real))
    (hgInvDt : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (i j : Idx),
      HasDerivWithinAt (fun r : Real => gInv r x i j)
        (2 * (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
        D.carrier (t : Real)) :
    NablaRm04NormHeatEquationOn (D := D)
      (nablaRm04NormSqIntrinsic (I := I) S)
      nablaRmNormLap
      (nabla2Rm04NormSqIntrinsic (I := I) S)
      (nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot) := by
  classical
  intro t x

  have hmc : IsMetricCompatible_gen (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real)) :=
    solution_isMetricCompatible (I := I) S (t : Real)



  have hdt :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I)
      (s := 5) (x := x) (u := D.carrier) (t := (t : Real))
      (g := fun r : Real => S.base.metric r)
      (gInv := fun r : Real => gInv r x)
      (gInvDt := fun i j => 2 * (∑ p : Idx, ∑ q : Idx,
        gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
      (ric := ric (t : Real) x)
      (T := fun r : Real => nablaRm04Field (I := I) S r x)
      (Tdt := fun I0 =>
        tensor0SComponent (I := I) (Tdot (t : Real) x) (fun i => basis x i) I0)
      (Tdot := Tdot (t : Real) x)
      (basis := basis x)
      (fun r => hinv r x)
      (hgInvDt t x)
      (hT t x)
      (fun I0 => rfl)
      (fun i j => rfl)


  have hsplit :=
    tensorNormBochnerSplit_mc (I := I) (s := 5)
      (cov := S.family.connection (t : Real))
      (g := S.base.metric (t : Real))
      hmc (basis := basis x) (gInv := gInv (t : Real) x) (hinv t x)
      (Xb := Xb x) (hfields x)
      (T := nablaRm04Field (I := I) S (t : Real))
      (nablaT := nabla2Rm04Field (I := I) S (t : Real))
      (nabla2T := nabla3Rm04Field (I := I) S (t : Real))
      (nabla2Rm04Field_realizes (I := I) S (t : Real))
      (nabla3Rm04Field_realizes (I := I) S (t : Real))
      (du := du (t : Real)) (normSecond := normSecond (t : Real))
      (hdu (t : Real)) (hHess (t : Real) x)

  refine hdt.congr_deriv ?_

  rw [hlapTrace (t : Real) x]

  set Rm := nablaRm04Field (I := I) S (t : Real) x with hRm
  set Rm2 := nabla2Rm04Field (I := I) S (t : Real) x with hRm2
  set roughT := metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
    (nabla3Rm04Field (I := I) S (t : Real) x) with hroughT

  rw [hsplit]

  rw [nablaRm04ReactionIntrinsic, nabla2Rm04NormSqIntrinsic]

  have hsub :
      inner0S (I := I) (S.base.metric (t : Real)) x 5 (Tdot (t : Real) x - roughT) Rm =
        inner0S (I := I) (S.base.metric (t : Real)) x 5 (Tdot (t : Real) x) Rm -
          inner0S (I := I) (S.base.metric (t : Real)) x 5 roughT Rm := by
    simp only [inner0S, MetricFiberData.inner, map_sub, LinearMap.sub_apply]
  rw [hsub]



  ring

end HeatEquation






section Producer

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]



omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nabla2Rm04NormSqIntrinsic_nonneg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    0 ≤ nabla2Rm04NormSqIntrinsic (I := I) S t x := by
  unfold nabla2Rm04NormSqIntrinsic
  rw [normSq0S_eq_inner]
  exact (tensor0SMetricData (I := I) (S.base.metric t) x 6).inner_nonneg
    (nabla2Rm04Field (I := I) S t x)




















omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaRm04NormHeatBoundOn_intrinsic
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Xb : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nablaRmNormLap : Real -> M -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 5 x)
    (cReact : Real)
    (hinv : ∀ (t : Real) (x : M),
      MetricInverseInBasis (I := I) (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x : M, SmoothBasisFieldsAt (I := I) (basis x) (Xb x))
    (hdu : ∀ t : Real,
      DuFieldRealizes (I := I)
        (fun y : M => normSq0S (I := I) (S.base.metric t) y 5
          (nablaRm04Field (I := I) S t y)) (du t))
    (hHess : ∀ (t : Real) (x : M),
      HessianRealizesNablaDuAt (I := I) (S.family.connection t) (du t)
        (normSecond t) x)
    (hlapTrace : ∀ (t : Real) (x : M),
      nablaRmNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hT : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (I0 : Fin 5 -> Idx),
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaRm04Field (I := I) S r x)
            (fun i => basis x i) I0)
        (tensor0SComponent (I := I) (Tdot (t : Real) x) (fun i => basis x i) I0)
        D.carrier (t : Real))
    (hgInvDt : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (i j : Idx),
      HasDerivWithinAt (fun r : Real => gInv r x i j)
        (2 * (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
        D.carrier (t : Real))
    (hreact_bound : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M),
      nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot (t : Real) x ≤
        cReact *
          Real.sqrt
            (normSq0S (I := I) (S.base.metric (t : Real)) x 4
              (S.base.rm04 (t : Real) x)) *
          nablaRm04NormSqIntrinsic (I := I) S (t : Real) x) :
    NablaRm04NormHeatBoundOn (D := D)
      (nablaRm04NormSqIntrinsic (I := I) S)
      nablaRmNormLap
      (fun t x => normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x))
      cReact := by
  have h_heat :
      NablaRm04NormHeatEquationOn (D := D)
        (nablaRm04NormSqIntrinsic (I := I) S)
        nablaRmNormLap
        (nabla2Rm04NormSqIntrinsic (I := I) S)
        (nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot) :=
    nablaRm04NormHeatEquationOn_intrinsic (I := I) S basis gInv ric Xb du normSecond
      nablaRmNormLap Tdot hinv hfields hdu hHess hlapTrace hT hgInvDt
  exact nablaRm04NormHeatBoundOn_scalar (D := D)
    (nablaRm04NormSqIntrinsic (I := I) S)
    nablaRmNormLap
    (nabla2Rm04NormSqIntrinsic (I := I) S)
    (nablaRm04ReactionIntrinsic (I := I) S basis gInv ric Tdot)
    (fun t x => normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x))
    cReact h_heat
    (fun t x => nabla2Rm04NormSqIntrinsic_nonneg (I := I) S (t : Real) x)
    hreact_bound

end Producer

end DifferentialGeometry.PDE.RicciFlow
