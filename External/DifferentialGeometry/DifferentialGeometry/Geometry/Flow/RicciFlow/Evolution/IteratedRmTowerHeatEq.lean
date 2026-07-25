import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannHeatFull
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedNablaRmTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.NablaRiemannTimeDeriv
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection

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



def nablaKRm04NormSqIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) : Real -> M -> Real :=
  fun t x => normSq0S (I := I) (S.base.metric t) x (4 + k)
    (nablaKRm04Field (I := I) S t k x)









def nablaKRm04ReactionIntrinsic
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (4 + k) x) : Real -> M -> Real :=
  fun t x =>
    ricReactionContract (gInv t x) (ric t x)
        (fun I0 : Fin (4 + k) -> Idx =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis x i) I0)
        (fun J0 : Fin (4 + k) -> Idx =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
            (fun i => basis x i) J0) +
      2 * inner0S (I := I) (S.base.metric t) x (4 + k)
            (Tdot t x -
              metricTrace0S2TensorInBasis (I := I) (basis x) (gInv t x)
                (nablaKRm04Field (I := I) S t (k + 2) x))
            (nablaKRm04Field (I := I) S t k x)



def nablaKReactionAt
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M)
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x) : Real :=
  ricReactionContract gInv ric
      (fun I0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
          (fun i => basis i) I0)
      (fun J0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S t k x)
          (fun i => basis i) J0) +
    2 * inner0S (I := I) (S.base.metric t) x (4 + k)
      (Tdot - metricTrace0S2TensorInBasis (I := I) basis gInv
        (nablaKRm04Field (I := I) S t (k + 2) x))
      (nablaKRm04Field (I := I) S t k x)

end Fields





omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKNorm_smooth
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (nablaKRm04NormSqIntrinsic (I := I) S k t) := by
  simpa [nablaKRm04NormSqIntrinsic] using
    (normSq0S_smooth (I := I) (S.base.metric t)
      (nablaKRm04Field (I := I) S t k))


noncomputable def nablaKNormDu
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 :=
  duSec (I := I) (nablaKRm04NormSqIntrinsic (I := I) S k t)
    (nablaKNorm_smooth (I := I) S t k)


noncomputable def nablaKNormHess
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
  hessianSec (I := I) (S.family.connection t) (connSmoothInf (I := I) S t)
    (nablaKRm04NormSqIntrinsic (I := I) S k t)
    (nablaKNorm_smooth (I := I) S t k)


noncomputable def nablaKNormLap
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) : Real → M → Real :=
  fun t x => laplacian (I := I) (S.family.connection t) (S.base.metric t)
    (nablaKRm04NormSqIntrinsic (I := I) S k t) x






section HeatEquation

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]





omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKNormHeatAt
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real → Idx → Idx → Real)
    (ric : Idx → Idx → Real)
    (Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x)
    (hinv : ∀ r : Real,
      MetricInverseInBasis (I := I) (S.base.metric r) x basis (gInv r))
    (hT : ∀ I0 : Fin (4 + k) → Idx,
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k x)
            (fun i => basis i) I0)
        (tensor0SComponent (I := I) Tdot (fun i => basis i) I0)
        D.carrier (t : Real))
    (hgInvDt : ∀ i j : Idx,
      HasDerivWithinAt (fun r : Real => gInv r i j)
        (2 * (∑ p : Idx, ∑ q : Idx,
          gInv (t : Real) i p * gInv (t : Real) j q * ric p q))
        D.carrier (t : Real)) :
    HasDerivWithinAt
      (fun r : Real => nablaKRm04NormSqIntrinsic (I := I) S k r x)
      (nablaKNormLap (I := I) S k (t : Real) x +
        (-2 * nablaKRm04NormSqIntrinsic (I := I) S (k + 1) (t : Real) x +
          nablaKReactionAt (I := I) S k (t : Real) x basis
            (gInv (t : Real)) ric Tdot))
      D.carrier (t : Real) := by
  classical
  have hmc : IsMetricCompatible_gen (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real)) :=
    solution_isMetricCompatible (I := I) S (t : Real)
  let X : Idx → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun i =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis i)).choose
  have hfields : SmoothBasisFieldsAt (I := I) basis X := by
    intro i
    dsimp [X]
    exact
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis i)).choose_spec
  have hf := nablaKNorm_smooth (I := I) S (t : Real) k
  have hdu : DuFieldRealizes (I := I)
      (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real))
      (nablaKNormDu (I := I) S (t : Real) k) := by
    simpa [nablaKNormDu] using
      (duSec_realizes (I := I)
        (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real)) hf)
  have hHess : HessianRealizesNablaDuAt (I := I)
      (S.family.connection (t : Real))
      (nablaKNormDu (I := I) S (t : Real) k)
      (nablaKNormHess (I := I) S (t : Real) k) x := by
    simpa [nablaKNormDu, nablaKNormHess] using
      (hessianSec_realizesAt (I := I)
        (S.family.connection (t : Real)) (connSmoothInf (I := I) S (t : Real))
        (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real)) hf x)
  have hlapReal :=
    scalarLap_smooth (I := I)
      (S.family.connection (t : Real)) (connSmoothInf (I := I) S (t : Real))
      (S.base.metric (t : Real)) hmc
      (x := x) (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real)) hf
  have hlapBasis :=
    ScalarLaplacianRealizesTraceAt.toInBasis (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real))
      basis (gInv (t : Real)) (hinv (t : Real))
      (nablaKRm04NormSqIntrinsic (I := I) S k (t : Real))
      (nablaKNormHess (I := I) S (t : Real) k x) hlapReal
  have hlap :
      nablaKNormLap (I := I) S k (t : Real) x =
        metricTrace0S2InBasis (I := I) basis (gInv (t : Real))
          (nablaKNormHess (I := I) S (t : Real) k x) Fin.elim0 := by
    simpa [nablaKNormLap] using hlapBasis
  have hdt :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I)
      (s := 4 + k) (x := x) (u := D.carrier) (t := (t : Real))
      (g := fun r : Real => S.base.metric r)
      (gInv := gInv)
      (gInvDt := fun i j => 2 * (∑ p : Idx, ∑ q : Idx,
        gInv (t : Real) i p * gInv (t : Real) j q * ric p q))
      (ric := ric)
      (T := fun r : Real => nablaKRm04Field (I := I) S r k x)
      (Tdt := fun I0 =>
        tensor0SComponent (I := I) Tdot (fun i => basis i) I0)
      (Tdot := Tdot)
      (basis := basis)
      hinv hgInvDt hT (fun I0 => rfl) (fun i j => rfl)
  have hsplit :=
    tensorNormBochnerSplit_mc (I := I) (s := 4 + k)
      (cov := S.family.connection (t : Real))
      (g := S.base.metric (t : Real))
      hmc (basis := basis) (gInv := gInv (t : Real)) (hinv (t : Real))
      (Xb := X) hfields
      (T := nablaKRm04Field (I := I) S (t : Real) k)
      (nablaT := nablaKRm04Field (I := I) S (t : Real) (k + 1))
      (nabla2T := nablaKRm04Field (I := I) S (t : Real) (k + 2))
      (nablaKRm04Field_realizes (I := I) S (t : Real) k)
      (nablaKRm04Field_realizes (I := I) S (t : Real) (k + 1))
      (du := nablaKNormDu (I := I) S (t : Real) k)
      (normSecond := nablaKNormHess (I := I) S (t : Real) k)
      hdu hHess
  refine hdt.congr_deriv ?_
  rw [hlap, nablaKReactionAt, nablaKRm04NormSqIntrinsic]
  set A := ricReactionContract (gInv (t : Real)) ric
      (fun I0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis i) I0)
      (fun J0 : Fin (4 + k) → Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis i) J0) with hA
  set Rm := nablaKRm04Field (I := I) S (t : Real) k x with hRm
  have hsub :
      inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
          (Tdot - metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
            (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm =
        inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) Tdot Rm -
          inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
            (metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm := by
    simp only [inner0S, MetricFiberData.inner, map_sub, LinearMap.sub_apply]
  rw [hsub]
  set B := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) Tdot Rm with hB
  set C := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
      (metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
        (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm with hC
  have hsplit' :
      metricTrace0S2InBasis (I := I) basis (gInv (t : Real))
          (nablaKNormHess (I := I) S (t : Real) k x) Fin.elim0 =
        2 * C +
          2 * normSq0S (I := I) (S.base.metric (t : Real)) x (4 + (k + 1))
            (nablaKRm04Field (I := I) S (t : Real) (k + 1) x) := hsplit
  rw [hsplit']
  ring























omit [Module.Finite ℝ E] in
omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04NormHeatEquationOn_intrinsic
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ)
    (basis : (x : M) -> Module.Basis Idx Real (TangentSpace I x))
    (gInv : Real -> M -> Idx -> Idx -> Real)
    (ric : Real -> M -> Idx -> Idx -> Real)
    (Xb : (x : M) -> Idx -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (du : Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (normSecond : Real -> (y : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 y)
    (nablaKRmNormLap : Real -> M -> Real)
    (Tdot : Real -> (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (4 + k) x)
    (hinv : ∀ (t : Real) (x : M),
      MetricInverseInBasis (I := I) (S.base.metric t) x (basis x) (gInv t x))
    (hfields : ∀ x : M, SmoothBasisFieldsAt (I := I) (basis x) (Xb x))
    (hdu : ∀ t : Real,
      DuFieldRealizes (I := I)
        (fun y : M => normSq0S (I := I) (S.base.metric t) y (4 + k)
          (nablaKRm04Field (I := I) S t k y)) (du t))
    (hHess : ∀ (t : Real) (x : M),
      HessianRealizesNablaDuAt (I := I) (S.family.connection t) (du t)
        (normSecond t) x)
    (hlapTrace : ∀ (t : Real) (x : M),
      nablaKRmNormLap t x =
        metricTrace0S2InBasis (I := I) (basis x) (gInv t x)
          (normSecond t x) Fin.elim0)
    (hT : ∀ (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
      (x : M) (I0 : Fin (4 + k) -> Idx),
      HasDerivWithinAt
        (fun r : Real =>
          tensor0SComponent (I := I) (nablaKRm04Field (I := I) S r k x)
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
      (nablaKRm04NormSqIntrinsic (I := I) S k)
      nablaKRmNormLap
      (nablaKRm04NormSqIntrinsic (I := I) S (k + 1))
      (nablaKRm04ReactionIntrinsic (I := I) S k basis gInv ric Tdot) := by
  classical
  intro t x

  have hmc : IsMetricCompatible_gen (I := I)
      (S.family.connection (t : Real)) (S.base.metric (t : Real)) :=
    solution_isMetricCompatible (I := I) S (t : Real)



  have hdt :=
    hasDerivWithinAt_normSq0S_ricciFlow (I := I)
      (s := 4 + k) (x := x) (u := D.carrier) (t := (t : Real))
      (g := fun r : Real => S.base.metric r)
      (gInv := fun r : Real => gInv r x)
      (gInvDt := fun i j => 2 * (∑ p : Idx, ∑ q : Idx,
        gInv (t : Real) x i p * gInv (t : Real) x j q * ric (t : Real) x p q))
      (ric := ric (t : Real) x)
      (T := fun r : Real => nablaKRm04Field (I := I) S r k x)
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
    tensorNormBochnerSplit_mc (I := I) (s := 4 + k)
      (cov := S.family.connection (t : Real))
      (g := S.base.metric (t : Real))
      hmc (basis := basis x) (gInv := gInv (t : Real) x) (hinv t x)
      (Xb := Xb x) (hfields x)
      (T := nablaKRm04Field (I := I) S (t : Real) k)
      (nablaT := nablaKRm04Field (I := I) S (t : Real) (k + 1))
      (nabla2T := nablaKRm04Field (I := I) S (t : Real) (k + 2))
      (nablaKRm04Field_realizes (I := I) S (t : Real) k)
      (nablaKRm04Field_realizes (I := I) S (t : Real) (k + 1))
      (du := du (t : Real)) (normSecond := normSecond (t : Real))
      (hdu (t : Real)) (hHess (t : Real) x)

  refine hdt.congr_deriv ?_

  rw [hlapTrace (t : Real) x, nablaKRm04ReactionIntrinsic, nablaKRm04NormSqIntrinsic]





  set A := ricReactionContract (gInv (t : Real) x) (ric (t : Real) x)
      (fun I0 : Fin (4 + k) -> Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis x i) I0)
      (fun J0 : Fin (4 + k) -> Idx =>
        tensor0SComponent (I := I) (nablaKRm04Field (I := I) S (t : Real) k x)
          (fun i => basis x i) J0) with hA
  set Rm := nablaKRm04Field (I := I) S (t : Real) k x with hRm

  have hsub :
      inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
          (Tdot (t : Real) x -
            metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm =
        inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) (Tdot (t : Real) x) Rm -
          inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
            (metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
              (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm := by
    simp only [inner0S, MetricFiberData.inner, map_sub, LinearMap.sub_apply]
  rw [hsub]



  set B := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k) (Tdot (t : Real) x) Rm
    with hB
  set C := inner0S (I := I) (S.base.metric (t : Real)) x (4 + k)
      (metricTrace0S2TensorInBasis (I := I) (basis x) (gInv (t : Real) x)
        (nablaKRm04Field (I := I) S (t : Real) (k + 2) x)) Rm with hC

  have hsplit' :
      metricTrace0S2InBasis (I := I) (basis x) (gInv (t : Real) x)
          (normSecond (t : Real) x) Fin.elim0 =
        2 * C +
          2 * normSq0S (I := I) (S.base.metric (t : Real)) x (4 + (k + 1))
            (nablaKRm04Field (I := I) S (t : Real) (k + 1) x) := hsplit
  rw [hsplit']
  ring

end HeatEquation























section IteratedTimeDeriv

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]











def iteratedRmCompDt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base : Real → M → (Fin 4 → Idx) → Real)
    (baseDt : Real → M → (Fin 4 → Idx) → Real) :
    (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real
  | 0 => baseDt
  | (k + 1) => fun t x =>
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iteratedRmCompDt frame chr chrDt base baseDt k t y) x)
        (chr t x)
        (iteratedRmCompDt frame chr chrDt base baseDt k t x) -
      covDerivStepDt (chrDt t x)
        (iteratedRmComp (I := I) frame chr base k t x)

omit [DecidableEq Idx] in
@[simp] theorem iteratedRmCompDt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base baseDt : Real → M → (Fin 4 → Idx) → Real) :
    iteratedRmCompDt (I := I) frame chr chrDt base baseDt 0 = baseDt := rfl

omit [DecidableEq Idx] in
theorem iteratedRmCompDt_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base baseDt : Real → M → (Fin 4 → Idx) → Real) (k : ℕ) (t : Real) (x : M) :
    iteratedRmCompDt (I := I) frame chr chrDt base baseDt (k + 1) t x =
      covDerivStepComp
        (frameExtData (I := I) frame
          (fun y : M => iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t y) x)
        (chr t x)
        (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t x) -
      covDerivStepDt (chrDt t x)
        (iteratedRmComp (I := I) frame chr base k t x) := rfl



























omit [DecidableEq Idx] in
theorem iteratedRmComp_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (chr chrDt : Real → M → Idx → Idx → Idx → Real)
    (base baseDt : Real → M → (Fin 4 → Idx) → Real)
    {D : Set Real} {t : Real} (x : M)
    (hrm : ∀ m : Fin 4 → Idx,
      HasDerivWithinAt (fun s : Real => base s x m) (baseDt t x m) D t)
    (hchr : ∀ i a p : Idx,
      HasDerivWithinAt (fun s : Real => chr s x i a p) (chrDt t x i a p) D t)
    (hswap : ∀ (k : ℕ) (d : Idx) (m : Fin (4 + k) → Idx),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun y : M => iteratedRmComp (I := I) frame chr base k s y m) x
            (frame d x))
        (extDerivFun (I := I)
          (fun y : M => iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t y m) x
          (frame d x))
        D t) :
    ∀ (k : ℕ) (n : Fin (4 + k) → Idx),
      HasDerivWithinAt
        (fun s : Real => iteratedRmComp (I := I) frame chr base k s x n)
        (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t x n)
        D t := by
  intro k
  induction k with
  | zero =>
      intro n
      simpa [iteratedRmComp_zero, iteratedRmCompDt_zero] using hrm n
  | succ k ih =>
      intro n


      rw [show
          (fun s : Real => iteratedRmComp (I := I) frame chr base (k + 1) s x n) =
            fun s : Real =>
              covDerivStepComp
                (frameExtData (I := I) frame
                  (fun y : M => iteratedRmComp (I := I) frame chr base k s y) x)
                (chr s x)
                (iteratedRmComp (I := I) frame chr base k s x) n from by
        funext s; rw [iteratedRmComp_succ]]
      rw [iteratedRmCompDt_succ]


      exact covDerivStepComp_hasDerivWithinAt
        (I := I) frame
        (iteratedRmComp (I := I) frame chr base k)
        (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k)
        chr chrDt x n
        (fun m => ih m)
        hchr
        (fun m => hswap k (n 0) m)

end IteratedTimeDeriv



section Nonneg



omit [InnerProductSpace ℝ E] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaKRm04NormSqIntrinsic_nonneg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (k : ℕ) (t : Real) (x : M) :
    0 ≤ nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  unfold nablaKRm04NormSqIntrinsic
  rw [normSq0S_eq_inner]
  exact (tensor0SMetricData (I := I) (S.base.metric t) x (4 + k)).inner_nonneg
    (nablaKRm04Field (I := I) S t k x)

end Nonneg

end DifferentialGeometry.PDE.RicciFlow
