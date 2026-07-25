import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ScalarGradient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Regularity
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerTensor
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Curvature.DimensionThree.PinchingAlgebra
import DifferentialGeometry.Tensor.RSTensor.Metric
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility

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


abbrev Tensor02Fam : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x


def metric02
    (G : Real -> SmoothRiemannianMetric I M) :
    Tensor02Fam (E := E) (H := H) (I := I) (M := M) :=
  fun t x => Tensor0SBundle.metricTensorField (I := I) (G t) x

@[simp]
theorem metric02_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (t : Real) (x : M) (v : Fin 2 -> TangentSpace I x) :
    metric02 (I := I) G t x v = (G t).inner x (v 0) (v 1) := by
  simp [metric02]


def tfRic
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : Tensor02Fam (E := E) (H := H) (I := I) (M := M))
    (scalar : Real -> M -> Real) :
    Tensor02Fam (E := E) (H := H) (I := I) (M := M) :=
  fun t x =>
    Ric t x -
      (((1 : Real) / 3) * scalar t x) •
        metric02 (I := I) G t x

@[simp]
theorem tfRic_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (Ric : Tensor02Fam (E := E) (H := H) (I := I) (M := M))
    (scalar : Real -> M -> Real)
    (t : Real) (x : M) (v : Fin 2 -> TangentSpace I x) :
    tfRic (I := I) G Ric scalar t x v =
      Ric t x v - (((1 : Real) / 3) * scalar t x) *
        (G t).inner x (v 0) (v 1) := by
  unfold tfRic
  calc
    (Ric t x - (((1 : Real) / 3) * scalar t x) • metric02 (I := I) G t x) v =
        Ric t x v -
          ((((1 : Real) / 3) * scalar t x) • metric02 (I := I) G t x) v :=
      Tensor0SSpace.sub_apply 2 x _ _ v
    _ = _ := by
      rw [Tensor0SSpace.smul_apply, metric02_apply]
      simp only [smul_eq_mul]



abbrev tfRicNormSqAt (scalar ricciNormSq : Real) : Real :=
  tracefreeRicciNormSqAtOf scalar ricciNormSq





abbrev tfRicNormSq
    (scalar ricciNormSq : Real -> M -> Real) : Real -> M -> Real :=
  tracefreeRicciNormSqOf scalar ricciNormSq


omit [TopologicalSpace M] in
theorem tfRicNormSq_compat
    (scalar ricciNormSq : Real -> M -> Real) (t : Real) (x : M) :
    tfRicNormSq scalar ricciNormSq t x =
      tracefreeRicciNormSqOf scalar ricciNormSq t x := rfl



def pinchP
    (scalar ricciNormSq : Real -> M -> Real) (epsilon : Real)
    (t : Real) (x : M) : Real :=
  tfRicNormSq scalar ricciNormSq t x / Real.rpow (scalar t x) (2 - epsilon)



def cubicQAt (scalar ricciNormSq ricciTraceCube : Real) : Real :=
  2 * ricciNormSq ^ 2 + scalar ^ 4 -
    5 * scalar ^ 2 * ricciNormSq + 4 * scalar * ricciTraceCube


def cubicQ
    (scalar ricciNormSq ricciTraceCube : Real -> M -> Real)
    (t : Real) (x : M) : Real :=
  cubicQAt (scalar t x) (ricciNormSq t x) (ricciTraceCube t x)



theorem cubicQ_eigen (l1 l2 l3 : Real) :
    cubicQAt
        (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3)
        (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3)
        (DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3) =
      DifferentialGeometry.Integral.Connection.hamiltonCubicQ3 l1 l2 l3 := by
  unfold cubicQAt DifferentialGeometry.Integral.Connection.hamiltonCubicQ3
  ring



theorem tfRic_eigen (l1 l2 l3 : Real) :
    tfRicNormSqAt
        (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3)
        (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3) =
      DifferentialGeometry.Integral.Connection.tracefreeRicciEigenNormSq3 l1 l2 l3 := by
  unfold tfRicNormSqAt tracefreeRicciNormSqAtOf
    DifferentialGeometry.Integral.Connection.tracefreeRicciEigenNormSq3
    DifferentialGeometry.Integral.Connection.ricciEigenPairwiseGapSq3
    DifferentialGeometry.Integral.Connection.ricciEigenScalar3
    DifferentialGeometry.Integral.Connection.ricciEigenNormSq3
  ring





def EigenPinchCtxOn
    (l1 l2 l3 : Real -> M -> Real) (delta : Real) : Prop :=
  forall t x, DifferentialGeometry.Integral.Connection.PinchEigen3 (l1 t x) (l2 t x) (l3 t x) delta



theorem cubicQ_pinch
    {l1 l2 l3 delta epsilon : Real}
    (hctx : DifferentialGeometry.Integral.Connection.PinchEigen3 l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    0 <=
      cubicQAt
          (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3)
          (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3)
          (DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3) -
        epsilon * DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3 *
          tfRicNormSqAt
            (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3)
            (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3) := by
  simpa [cubicQ_eigen, tfRic_eigen] using
    DifferentialGeometry.Integral.Connection.PinchEigen3.q_sub_nonneg hctx hepsilon



omit [TopologicalSpace M] in
theorem cubicQ_pinchOn
    (l1 l2 l3 : Real -> M -> Real) {delta epsilon : Real}
    (hctx : EigenPinchCtxOn (M := M) l1 l2 l3 delta)
    (hepsilon : epsilon <= 2 * delta ^ 2) :
    forall t x,
      0 <=
        cubicQAt
            (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
            (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
            (DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) -
          epsilon * DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x) *
            tfRicNormSqAt
              (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
              (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x)) := by
  intro t x
  exact cubicQ_pinch (hctx t x) hepsilon



def ricciReact3 (l1 l2 l3 : Real) : Real :=
  l1 * l2 * (l1 + l2 - l3) +
    l1 * l3 * (l1 + l3 - l2) +
      l2 * l3 * (l2 + l3 - l1)



theorem react3_diag (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Integral.Connection.stdRmDiag3 l1 l2 l3 i k j l *
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j *
          DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 k l) =
      ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DifferentialGeometry.Integral.Connection.stdRmDiag3 DifferentialGeometry.Integral.Connection.ricciDiag3
    DifferentialGeometry.Integral.Connection.ricciEigenScalar3 DifferentialGeometry.Integral.Connection.delta3
  simp [Fin.sum_univ_three]
  ring


theorem curv3_diag_eq (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Integral.Connection.stdRmDiag3 l1 l2 l3 i k j l *
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j *
          DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 k l) =
      ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DifferentialGeometry.Integral.Connection.stdRmDiag3 DifferentialGeometry.Integral.Connection.ricciDiag3
    DifferentialGeometry.Integral.Connection.ricciEigenScalar3 DifferentialGeometry.Integral.Connection.delta3
  simp [Fin.sum_univ_three]
  ring





theorem curv3_neg_eq (l1 l2 l3 : Real) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Integral.Connection.stdRmDiag3 (-l1) (-l2) (-l3) i k j l *
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j *
          DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 k l) =
      -ricciReact3 l1 l2 l3 := by
  unfold ricciReact3 DifferentialGeometry.Integral.Connection.stdRmDiag3 DifferentialGeometry.Integral.Connection.ricciDiag3
    DifferentialGeometry.Integral.Connection.ricciEigenScalar3 DifferentialGeometry.Integral.Connection.delta3
  simp [Fin.sum_univ_three]
  ring


def diagReact3
    (l1 l2 l3 : Real -> M -> Real) : Real -> M -> Real :=
  fun t x =>
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
      DifferentialGeometry.Integral.Connection.stdRmDiag3 (l1 t x) (l2 t x) (l3 t x) i k j l *
        DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j *
          DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) k l

omit [TopologicalSpace M] in
@[simp]
theorem diagReact3_apply
    (l1 l2 l3 : Real -> M -> Real) (t : Real) (x : M) :
    diagReact3 (M := M) l1 l2 l3 t x =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (l1 t x) (l2 t x) (l3 t x) i k j l *
          DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j *
            DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) k l := by
  rfl

omit [TopologicalSpace M] in
theorem diagReact3_eq
    (l1 l2 l3 : Real -> M -> Real) (t : Real) (x : M) :
    diagReact3 (M := M) l1 l2 l3 t x =
      ricciReact3 (l1 t x) (l2 t x) (l3 t x) := by
  exact react3_diag (l1 t x) (l2 t x) (l3 t x)


theorem tfRel_eigen (l1 l2 l3 : Real)
    (hR : DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 ≠ 0) :
    4 * ricciReact3 l1 l2 l3 -
        ((4 : Real) / 3) *
          DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 *
            DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3 =
      (4 * DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3 *
          tfRicNormSqAt
            (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3)
            (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3) -
        2 * cubicQAt
          (DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3)
          (DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3)
          (DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3)) /
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 := by
  unfold ricciReact3 tfRicNormSqAt tracefreeRicciNormSqAtOf cubicQAt
    DifferentialGeometry.Integral.Connection.ricciEigenScalar3 DifferentialGeometry.Integral.Connection.ricciEigenNormSq3
    DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3
  have hR' : l1 + l2 + l3 ≠ 0 := by
    simpa [DifferentialGeometry.Integral.Connection.ricciEigenScalar3] using hR
  field_simp [hR']
  ring_nf


def tfRicReactRel
    (scalar ricciNormSq tfNormSq Q reaction : Real -> M -> Real) : Prop :=
  ∀ t x, scalar t x ≠ 0 ->
    4 * reaction t x - ((4 : Real) / 3) * scalar t x * ricciNormSq t x =
      (4 * ricciNormSq t x * tfNormSq t x - 2 * Q t x) / scalar t x




omit [TopologicalSpace M] in
theorem tfRel_from_eigen
    (scalar ricciNormSq ricciTraceCube reaction : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
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
    tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq)
      (cubicQ scalar ricciNormSq ricciTraceCube) reaction := by
  intro t x hR
  have hR' :
      DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x) ≠ 0 := by
    simpa [hscalar t x] using hR
  rw [hreaction t x, hscalar t x, hnorm t x]
  rw [tfRicNormSq, tracefreeRicciNormSqOf, cubicQ, hscalar t x, hnorm t x,
    hcube t x]
  exact tfRel_eigen (l1 t x) (l2 t x) (l3 t x) hR'



omit [TopologicalSpace M] in
theorem tfRel_from_diag
    (scalar ricciNormSq ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hnorm : ∀ t x,
      ricciNormSq t x =
        DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x)) :
    tfRicReactRel
      scalar ricciNormSq (tfRicNormSq scalar ricciNormSq)
      (cubicQ scalar ricciNormSq ricciTraceCube) (diagReact3 l1 l2 l3) := by
  exact tfRel_from_eigen
    (M := M)
    scalar ricciNormSq ricciTraceCube (diagReact3 l1 l2 l3)
    l1 l2 l3 hscalar hnorm hcube
    (by intro t x; exact diagReact3_eq (M := M) l1 l2 l3 t x)



theorem curvReact3_frame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 l1 l2 l3 i k j l) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      ricciReact3 l1 l2 l3 := by
  classical
  have hRicEval : ∀ i j : Fin 3,
      S.base.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame j x)) =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompInFrame] using hRic i j
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    unfold raisedRicciCompInFrame
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three, hInv, hRicEval, DifferentialGeometry.Integral.Connection.delta3,
        DifferentialGeometry.Integral.Connection.ricciDiag3]
  unfold curvRicciRicciInFrame
  simp_rw [hraised]
  simp_rw [hRm]
  exact curv3_diag_eq l1 l2 l3




theorem canonReact3_frame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 l1 l2 l3 i k j l) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      -ricciReact3 l1 l2 l3 := by
  rw [ricciNormCurvatureReactionInFrame_apply,
    curvReact3_frame (I := I) S Rm04 gInv frame t x l1 l2 l3 hInv hRic hRm]




theorem curv3_frame_neg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    curvRicciRicciInFrame (I := I) S Rm04 gInv frame t x =
      -ricciReact3 l1 l2 l3 := by
  classical
  have hRicEval : ∀ i j : Fin 3,
      S.base.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame j x)) =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    simpa [ricciCompInFrame] using hRic i j
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j := by
    intro i j
    unfold raisedRicciCompInFrame
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_three, hInv, hRicEval, DifferentialGeometry.Integral.Connection.delta3,
        DifferentialGeometry.Integral.Connection.ricciDiag3]
  unfold curvRicciRicciInFrame
  simp_rw [hraised]
  simp_rw [hRm]
  exact curv3_neg_eq l1 l2 l3



theorem canon3_frame_neg
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (l1 l2 l3 : Real)
    (hInv : ∀ i j : Fin 3,
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRic : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 i j)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      ricciReact3 l1 l2 l3 := by
  rw [ricciNormCurvatureReactionInFrame_apply,
    curv3_frame_neg (I := I) S Rm04 gInv frame t x l1 l2 l3 hInv hRic hRm]
  ring


def ricciNormAt {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis Ric i j *
      DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis Ric i j



def curvRicAt {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
    DifferentialGeometry.Integral.Connection.rm04CompAt (I := I) basis Rm04 i k j l *
      DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis Ric i j *
        DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis Ric k l


def reactAt {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  -curvRicAt (I := I) Ric Rm04 basis


def ricciCubeAt {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) : Real :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis Ric i j *
      DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis Ric j k *
      DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis Ric k i

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciCubeAt_diag {x : M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    ricciCubeAt (I := I) Ric basis =
      DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3 := by
  classical
  unfold ricciCubeAt DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3
  simp_rw [hdiag.2]
  unfold DifferentialGeometry.Integral.Connection.ricciDiag3
  simp [Fin.sum_univ_three]
  ring

omit [IsManifold I 1 M] in
theorem ricciEnd_diagVec {x : M}
    (g : SmoothRiemannianMetric I M)
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis)
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis 0) = l1 • basis 0 /\
      DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis 1) = l2 • basis 1 /\
      DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric (basis 2) = l3 • basis 2 := by
  classical
  let T := DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric
  have hdiagComp := hdiag.2
  have h0 : T (basis 0) = l1 • basis 0 := by
    apply eq_of_inner_basis_eq_gen (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 0)) (basis j) =
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis 0) (basis j)) := by
            exact DifferentialGeometry.Integral.Connection.ricciEnd_inner (I := I) g Ric (basis 0) (basis j)
      _ = DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 0 j := by
            simpa [DifferentialGeometry.Integral.Connection.ricciCompAt_apply] using hdiagComp 0 j
      _ = g.inner x (l1 • basis 0) (basis j) := by
            fin_cases j <;> simp [DifferentialGeometry.Integral.Connection.ricciDiag3,
              DifferentialGeometry.Integral.Connection.delta3, horth 0 0, horth 0 1, horth 0 2]
  have h1 : T (basis 1) = l2 • basis 1 := by
    apply eq_of_inner_basis_eq_gen (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 1)) (basis j) =
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis 1) (basis j)) := by
            exact DifferentialGeometry.Integral.Connection.ricciEnd_inner (I := I) g Ric (basis 1) (basis j)
      _ = DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 1 j := by
            simpa [DifferentialGeometry.Integral.Connection.ricciCompAt_apply] using hdiagComp 1 j
      _ = g.inner x (l2 • basis 1) (basis j) := by
            fin_cases j <;> simp [DifferentialGeometry.Integral.Connection.ricciDiag3,
              DifferentialGeometry.Integral.Connection.delta3, horth 1 0, horth 1 1, horth 1 2]
  have h2 : T (basis 2) = l3 • basis 2 := by
    apply eq_of_inner_basis_eq_gen (I := I) g x basis
    intro j
    calc
      g.inner x (T (basis 2)) (basis j) =
          Ric (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis 2) (basis j)) := by
            exact DifferentialGeometry.Integral.Connection.ricciEnd_inner (I := I) g Ric (basis 2) (basis j)
      _ = DifferentialGeometry.Integral.Connection.ricciDiag3 l1 l2 l3 2 j := by
            simpa [DifferentialGeometry.Integral.Connection.ricciCompAt_apply] using hdiagComp 2 j
      _ = g.inner x (l3 • basis 2) (basis j) := by
            fin_cases j <;> simp [DifferentialGeometry.Integral.Connection.ricciDiag3,
              DifferentialGeometry.Integral.Connection.delta3, horth 2 0, horth 2 1, horth 2 2]
  exact ⟨h0, h1, h2⟩



def ricciCubeInvAt {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x) : Real :=
  let T := DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric
  LinearMap.trace Real (TangentSpace I x) (T.comp (T.comp T))

omit [IsManifold I 1 M] in
theorem ricciCubeInv_diag {x : M}
    (g : SmoothRiemannianMetric I M)
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis)
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt
      (I := I) Ric scalar l1 l2 l3 basis) :
    ricciCubeInvAt (I := I) g Ric =
      DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3 := by
  classical
  let T := DifferentialGeometry.Integral.Connection.ricciEndAt (I := I) g Ric
  rcases ricciEnd_diagVec (I := I) g horth hdiag with ⟨hT0, hT1, hT2⟩
  have hT0c : (T.comp (T.comp T)) (basis 0) = (l1 ^ 3) • basis 0 := by
    simp [T, LinearMap.comp_apply, hT0, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hT1c : (T.comp (T.comp T)) (basis 1) = (l2 ^ 3) • basis 1 := by
    simp [T, LinearMap.comp_apply, hT1, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hT2c : (T.comp (T.comp T)) (basis 2) = (l3 ^ 3) • basis 2 := by
    simp [T, LinearMap.comp_apply, hT2, map_smul, pow_three, smul_smul,
      mul_assoc]
  have hinv :
      MetricInverseInBasis_gen (I := I) g x basis DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) g basis horth
  unfold ricciCubeInvAt
  change LinearMap.trace Real (TangentSpace I x) (T.comp (T.comp T)) =
    DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3
  rw [linearMap_trace_eq_sum_inv_inner_apply (I := I) g x basis
    DifferentialGeometry.Integral.Connection.delta3 hinv]
  unfold DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3
  simp only [Fin.sum_univ_three, DifferentialGeometry.Integral.Connection.delta3, LinearMap.coe_comp,
    Function.comp_apply]
  rw [show T (T (T (basis 0))) = (l1 ^ 3) • basis 0 by
        simpa [LinearMap.comp_apply] using hT0c,
      show T (T (T (basis 1))) = (l2 ^ 3) • basis 1 by
        simpa [LinearMap.comp_apply] using hT1c,
      show T (T (T (basis 2))) = (l3 ^ 3) • basis 2 by
        simpa [LinearMap.comp_apply] using hT2c]
  simp [DifferentialGeometry.Integral.Connection.delta3, horth 0 0, horth 1 1, horth 2 2]


def ricciCube
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D) : Real -> M -> Real :=
  fun t x => ricciCubeInvAt (I := I) (S.base.metric t) (S.ricciAt t x)

private theorem prod_delta4
    (I0 J0 : Fin 4 -> Fin 3) :
    (∏ a : Fin 4, DifferentialGeometry.Integral.Connection.delta3 (I0 a) (J0 a)) =
      if I0 = J0 then 1 else 0 := by
  classical
  rw [Fin.prod_univ_four]
  by_cases h : I0 = J0
  · subst J0
    simp [DifferentialGeometry.Integral.Connection.delta3]
  · have hne :
        I0 0 ≠ J0 0 ∨ I0 1 ≠ J0 1 ∨ I0 2 ≠ J0 2 ∨ I0 3 ≠ J0 3 := by
      by_contra hslots
      push Not at hslots
      apply h
      funext a
      fin_cases a <;> simp [hslots]
    rcases hne with h0 | h1 | h2 | h3
    · simp [DifferentialGeometry.Integral.Connection.delta3, h, h0]
    · simp [DifferentialGeometry.Integral.Connection.delta3, h, h1]
    · simp [DifferentialGeometry.Integral.Connection.delta3, h, h2]
    · simp [DifferentialGeometry.Integral.Connection.delta3, h, h3]

private theorem sum_delta4
    (F G : (Fin 4 -> Fin 3) -> Real) :
    (∑ I0 : Fin 4 -> Fin 3, ∑ J0 : Fin 4 -> Fin 3,
        (∏ a : Fin 4, DifferentialGeometry.Integral.Connection.delta3 (I0 a) (J0 a)) * F I0 * G J0) =
      ∑ I0 : Fin 4 -> Fin 3, F I0 * G I0 := by
  classical
  apply Finset.sum_congr rfl
  intro I0 _
  simp [prod_delta4]

private def fin4ikjl :
    (Fin 4 -> Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 2), f 1), f 3)
  invFun p := DifferentialGeometry.Integral.Connection.slots4 p.1.1.1 p.1.2 p.1.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.slots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [DifferentialGeometry.Integral.Connection.slots4]

private theorem sum4ikjl {α : Type*} [AddCommMonoid α]
    (F : (Fin 4 -> Fin 3) -> α) :
    (∑ I0 : Fin 4 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        F (DifferentialGeometry.Integral.Connection.slots4 i k j l) := by
  classical
  rw [Fintype.sum_equiv fin4ikjl F
    (fun p : (((Fin 3 × Fin 3) × Fin 3) × Fin 3) =>
      F (DifferentialGeometry.Integral.Connection.slots4 p.1.1.1 p.1.2 p.1.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        DifferentialGeometry.Integral.Connection.slots4 (fin4ikjl I0).1.1.1 (fin4ikjl I0).1.2
            (fin4ikjl I0).1.1.2 (fin4ikjl I0).2 = I0 := by
      change fin4ikjl.symm (fin4ikjl I0) = I0
      exact fin4ikjl.left_inv I0
    rw [hslot]

omit [FiniteDimensional ℝ E] in
private theorem coordPair04 {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 4 DifferentialGeometry.Integral.Connection.delta3
        Rm04 (ricciPair04 (I := I) Ric) basis =
      curvRicAt (I := I) Ric Rm04 basis := by
  classical
  unfold coordInner0S curvRicAt
  rw [sum_delta4]
  rw [sum4ikjl]
  have hpair : ∀ (v : Fin 4 → TangentSpace I x),
      ricciPair04 (I := I) Ric v =
        Ric (fun q : Fin 2 => if q = 0 then v 0 else v 2) *
          Ric (fun q : Fin 2 => if q = 0 then v 1 else v 3) := by
    intro v
    rw [ricciPair04_apply]
    congr 2
  simp [tensor0SComponent, DifferentialGeometry.Integral.Connection.rm04CompAt,
    DifferentialGeometry.Integral.Connection.ricciCompAt,
    DifferentialGeometry.Integral.Connection.slots4,
    DifferentialGeometry.Integral.Connection.slots2,
    hpair, mul_assoc]

theorem curvRic_inner {x : M}
    (g : SmoothMetric_gen I M)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis DifferentialGeometry.Integral.Connection.delta3) :
    curvRicAt (I := I) Ric Rm04 basis =
      inner0S (I := I) g x 4 Rm04 (ricciPair04 (I := I) Ric) := by
  rw [inner0S_eq_coord (I := I) g x 4 basis DifferentialGeometry.Integral.Connection.delta3 hinv]
  exact (coordPair04 (I := I) Ric Rm04 basis).symm



theorem reactAt_eq_react
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
      (I := I) (S.base.metric t) x basis) :
    reactAt (I := I) (S.ricciAt t x) (S.base.rm04 t x) basis =
      ricciReact (I := I) S t x := by
  have hinv :
      MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
        DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) (S.base.metric t) basis horth
  unfold reactAt ricciReact
  rw [curvRic_inner (I := I) (S.base.metric t) (S.ricciAt t x)
    (S.base.rm04 t x) basis hinv]



theorem react_frame {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (h₁ : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis₁)
    (h₂ : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis₂) :
    reactAt (I := I) Ric Rm04 basis₁ =
      reactAt (I := I) Ric Rm04 basis₂ := by
  have hinv₁ : MetricInverseInBasis_gen (I := I) g x basis₁ DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) g basis₁ h₁
  have hinv₂ : MetricInverseInBasis_gen (I := I) g x basis₂ DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) g basis₂ h₂
  unfold reactAt
  rw [curvRic_inner (I := I) g Ric Rm04 basis₁ hinv₁,
    curvRic_inner (I := I) g Ric Rm04 basis₂ hinv₂]

private theorem prod_delta2
    (I0 J0 : Fin 2 -> Fin 3) :
    (∏ a : Fin 2, DifferentialGeometry.Integral.Connection.delta3 (I0 a) (J0 a)) =
      if I0 = J0 then 1 else 0 := by
  classical
  rw [Fin.prod_univ_two]
  by_cases h : I0 = J0
  · subst J0
    simp [DifferentialGeometry.Integral.Connection.delta3]
  · have hne : I0 0 ≠ J0 0 ∨ I0 1 ≠ J0 1 := by
      by_contra hslots
      push Not at hslots
      apply h
      funext a
      fin_cases a <;> simp [hslots]
    rcases hne with h0 | h1
    · simp [DifferentialGeometry.Integral.Connection.delta3, h, h0]
    · simp [DifferentialGeometry.Integral.Connection.delta3, h, h1]

private theorem sum_delta2
    (F G : (Fin 2 -> Fin 3) -> Real) :
    (∑ I0 : Fin 2 -> Fin 3, ∑ J0 : Fin 2 -> Fin 3,
        (∏ a : Fin 2, DifferentialGeometry.Integral.Connection.delta3 (I0 a) (J0 a)) * F I0 * G J0) =
      ∑ I0 : Fin 2 -> Fin 3, F I0 * G I0 := by
  classical
  apply Finset.sum_congr rfl
  intro I0 _
  calc
    (∑ J0 : Fin 2 -> Fin 3,
        (∏ a : Fin 2, DifferentialGeometry.Integral.Connection.delta3 (I0 a) (J0 a)) * F I0 * G J0) =
        ∑ J0 : Fin 2 -> Fin 3, (if I0 = J0 then 1 else 0) * F I0 * G J0 := by
          apply Finset.sum_congr rfl
          intro J0 _
          rw [prod_delta2]
    _ = F I0 * G I0 := by
          simp

private def fin2ij :
    (Fin 2 -> Fin 3) ≃ (Fin 3 × Fin 3) where
  toFun f := (f 0, f 1)
  invFun p := DifferentialGeometry.Integral.Connection.slots2 p.1 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.slots2]
  right_inv p := by
    rcases p with ⟨i, j⟩
    simp [DifferentialGeometry.Integral.Connection.slots2]

private theorem sum2ij {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Fin 3) -> α) :
    (∑ I0 : Fin 2 -> Fin 3, F I0) =
      ∑ i : Fin 3, ∑ j : Fin 3, F (DifferentialGeometry.Integral.Connection.slots2 i j) := by
  classical
  rw [Fintype.sum_equiv fin2ij F
    (fun p : Fin 3 × Fin 3 => F (DifferentialGeometry.Integral.Connection.slots2 p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    have hslot :
        DifferentialGeometry.Integral.Connection.slots2 (fin2ij I0).1 (fin2ij I0).2 = I0 := by
      change fin2ij.symm (fin2ij I0) = I0
      exact fin2ij.left_inv I0
    rw [hslot]

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
private theorem coordRic02 {x : M}
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 2 DifferentialGeometry.Integral.Connection.delta3 Ric Ric basis =
      ricciNormAt (I := I) Ric basis := by
  classical
  unfold coordInner0S ricciNormAt
  rw [sum_delta2]
  rw [sum2ij]
  simp [tensor0SComponent, DifferentialGeometry.Integral.Connection.ricciCompAt, DifferentialGeometry.Integral.Connection.slots2]

omit [IsManifold I 1 M] in
theorem ricciNorm_inner {x : M}
    (g : SmoothMetric_gen I M)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hinv : MetricInverseInBasis_gen (I := I) g x basis DifferentialGeometry.Integral.Connection.delta3) :
    ricciNormAt (I := I) Ric basis =
      normSq0S (I := I) g x 2 Ric := by
  rw [normSq0S_eq_coord (I := I) g x 2 basis DifferentialGeometry.Integral.Connection.delta3 hinv Ric]
  exact (coordRic02 (I := I) Ric basis).symm

omit [IsManifold I 1 M] in
theorem ricciNorm_frame {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (h₁ : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis₁)
    (h₂ : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis₂) :
    ricciNormAt (I := I) Ric basis₁ =
      ricciNormAt (I := I) Ric basis₂ := by
  have hinv₁ : MetricInverseInBasis_gen (I := I) g x basis₁ DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) g basis₁ h₁
  have hinv₂ : MetricInverseInBasis_gen (I := I) g x basis₂ DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) g basis₂ h₂
  rw [ricciNorm_inner (I := I) g Ric basis₁ hinv₁,
    ricciNorm_inner (I := I) g Ric basis₂ hinv₂]

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciNormAt_diag {x : M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis) :
    ricciNormAt (I := I) Ric basis =
      DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 l1 l2 l3 := by
  classical
  rcases hdiag with ⟨_, hric⟩
  unfold ricciNormAt DifferentialGeometry.Integral.Connection.ricciEigenNormSq3
  simp_rw [hric]
  unfold DifferentialGeometry.Integral.Connection.ricciDiag3
  simp [Fin.sum_univ_three]
  ring

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem reactAt_diag {x : M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x}
    {scalar l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04CompAt (I := I) basis Rm04 i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (-l1) (-l2) (-l3) i k j l) :
    reactAt (I := I) Ric Rm04 basis = ricciReact3 l1 l2 l3 := by
  classical
  rcases hdiag with ⟨_, hric⟩
  unfold reactAt curvRicAt
  simp_rw [hRm]
  simp_rw [hric]
  rw [curv3_neg_eq]
  ring




omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem tfRel_basis {x : M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (hcube :
      ricciTraceCube = DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3)
    (hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04CompAt (I := I) basis Rm04 i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (-l1) (-l2) (-l3) i k j l)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 basis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric basis =
      (4 * ricciNormAt (I := I) Ric basis *
          tfRicNormSqAt scalar (ricciNormAt (I := I) Ric basis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric basis)
          ricciTraceCube) / scalar := by
  have hscalar :
      scalar = DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 := hdiag.1
  have hR' :
      DifferentialGeometry.Integral.Connection.ricciEigenScalar3 l1 l2 l3 ≠ 0 := by
    simpa [hscalar] using hR
  rw [reactAt_diag (I := I) hdiag hRm, ricciNormAt_diag (I := I) hdiag,
    hscalar, hcube]
  exact tfRel_eigen l1 l2 l3 hR'



omit [IsManifold I 1 M] in
omit [FiniteDimensional ℝ E] in
theorem diag_neg {x : M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 : Real}
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis) :
    DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) (-Ric) (-scalar)
      (-l1) (-l2) (-l3) basis := by
  rcases hdiag with ⟨hscalar, hric⟩
  constructor
  · unfold DifferentialGeometry.Integral.Connection.ricciEigenScalar3 at hscalar ⊢
    linarith
  · intro i j
    have hij := hric i j
    fin_cases i <;> fin_cases j <;>
      simpa [DifferentialGeometry.Integral.Connection.ricciCompAt_apply, DifferentialGeometry.Integral.Connection.ricciDiag3] using
        congrArg Neg.neg hij



omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem tfRel_trace {x : M}
    {g : SmoothRiemannianMetric I M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (htrace :
      DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-scalar) Rm04 basis)
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) Ric scalar l1 l2 l3 basis)
    (hcube :
      ricciTraceCube = DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 basis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric basis =
      (4 * ricciNormAt (I := I) Ric basis *
          tfRicNormSqAt scalar (ricciNormAt (I := I) Ric basis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric basis)
          ricciTraceCube) / scalar := by
  have hneg := diag_neg (I := I) hdiag
  have hcomp :=
    DifferentialGeometry.Integral.Connection.stdRmComp_eq_diag (I := I) htrace hneg
  have hRm : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04CompAt (I := I) basis Rm04 i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (-l1) (-l2) (-l3) i k j l := by
    intro i j k l
    have h := hcomp i k j l
    simpa [DifferentialGeometry.Integral.Connection.standardRmCompAt_apply] using h
  exact tfRel_basis (I := I) (Ric := Ric) (Rm04 := Rm04)
    (basis := basis) hdiag hcube hRm hR




theorem tfRel_point {x : M}
    {g : SmoothRiemannianMetric I M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x}
    {heatBasis eigBasis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    {scalar l1 l2 l3 ricciTraceCube : Real}
    (hheat : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x heatBasis)
    (heig : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x eigBasis)
    (htrace :
      DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
        (I := I) g (-Ric) (-scalar) Rm04 eigBasis)
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I) Ric scalar l1 l2 l3 eigBasis)
    (hcube :
      ricciTraceCube = DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 l1 l2 l3)
    (hR : scalar ≠ 0) :
    4 * reactAt (I := I) Ric Rm04 heatBasis -
        ((4 : Real) / 3) * scalar * ricciNormAt (I := I) Ric heatBasis =
      (4 * ricciNormAt (I := I) Ric heatBasis *
          tfRicNormSqAt scalar (ricciNormAt (I := I) Ric heatBasis) -
        2 * cubicQAt scalar (ricciNormAt (I := I) Ric heatBasis)
          ricciTraceCube) / scalar := by
  have hrel :=
    tfRel_trace (I := I) (g := g) (Ric := Ric) (Rm04 := Rm04)
      (basis := eigBasis) htrace hdiag hcube hR
  have hreact :
      reactAt (I := I) Ric Rm04 heatBasis =
        reactAt (I := I) Ric Rm04 eigBasis :=
    react_frame (I := I) g Ric Rm04 heatBasis eigBasis hheat heig
  have hnorm :
      ricciNormAt (I := I) Ric heatBasis =
        ricciNormAt (I := I) Ric eigBasis :=
    ricciNorm_frame (I := I) g Ric heatBasis eigBasis hheat heig
  simpa [hreact, hnorm] using hrel

private theorem raiseRicci_delta
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (hInv : ∀ i j : Idx, gInv t x i j = if i = j then 1 else 0)
    (i j : Idx) :
    raisedRicciCompInFrame (I := I) S gInv frame t x i j =
      ricciCompInFrame (I := I) S frame t x i j := by
  classical
  unfold raisedRicciCompInFrame
  simp [hInv]

theorem sec6_norm_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hbasis : ∀ i : Fin 3, basis i = frame i x)
    (hInv : ∀ i j : Fin 3, gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ricciNormSqInFrame (I := I) S gInv frame t x =
      ricciNormAt (I := I) (S.ricciAt t x) basis := by
  classical
  have hRicAt : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    simp [ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciCompAt_apply, hbasis i, hbasis j]
  have hraisedFrame : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        ricciCompInFrame (I := I) S frame t x i j := by
    intro i j
    apply raiseRicci_delta (I := I) S gInv frame t x
    intro a b
    simpa [DifferentialGeometry.Integral.Connection.delta3] using hInv a b
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    rw [hraisedFrame i j, hRicAt i j]
  rw [ricciNormSqInFrame_apply]
  unfold ricciNormAt
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hRicAt i j, hraised i j]

theorem sec6_react_at
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (hbasis : ∀ i : Fin 3, basis i = frame i x)
    (hInv : ∀ i j : Fin 3, gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame t x =
      reactAt (I := I) (S.ricciAt t x) (Rm04 t x) basis := by
  classical
  have hRicAt : ∀ i j : Fin 3,
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    simp [ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciCompAt_apply, hbasis i, hbasis j]
  have hraisedFrame : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        ricciCompInFrame (I := I) S frame t x i j := by
    intro i j
    apply raiseRicci_delta (I := I) S gInv frame t x
    intro a b
    simpa [DifferentialGeometry.Integral.Connection.delta3] using hInv a b
  have hraised : ∀ i j : Fin 3,
      raisedRicciCompInFrame (I := I) S gInv frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciCompAt (I := I) basis (S.ricciAt t x) i j := by
    intro i j
    rw [hraisedFrame i j, hRicAt i j]
  have hRmAt : ∀ i j k l : Fin 3,
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Integral.Connection.rm04CompAt (I := I) basis (Rm04 t x) i k j l := by
    intro i j k l
    simp [DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04Comp,
      DifferentialGeometry.Integral.Connection.rm04CompAt_apply,
      hbasis i, hbasis k, hbasis j, hbasis l]
  unfold ricciNormCurvatureReactionInFrame reactAt
  congr 1
  unfold curvRicciRicciInFrame curvRicAt
  simp_rw [hraised, hRmAt]

theorem tfRel_point_sec6
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
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
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  intro t x hR
  have hnorm := sec6_norm_at (I := I) S gInv frame t x (heatBasis t x)
    (hheatBasis t x) (hInv t x)
  have hreact := sec6_react_at (I := I) S Rm04 gInv frame t x (heatBasis t x)
    (hheatBasis t x) (hInv t x)
  have hpoint := tfRel_point (I := I) (g := S.base.metric t)
    (Ric := S.ricciAt t x) (Rm04 := Rm04 t x)
    (heatBasis := heatBasis t x) (eigBasis := eigBasis t x)
    (scalar := scalar t x) (l1 := l1 t x) (l2 := l2 t x) (l3 := l3 t x)
    (ricciTraceCube := ricciTraceCube t x)
    (hheat t x) (heig t x) (htrace t x) (hdiag t x) (hcube t x) hR
  rw [hreact, hnorm]
  unfold tfRicNormSq tracefreeRicciNormSqOf cubicQ
  rw [hnorm]
  exact hpoint




theorem tfRel_pfirst
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (heatBasis eigBasis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
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
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  refine tfRel_point_sec6 (I := I) S Rm04 gInv frame heatBasis eigBasis
    scalar ricciTraceCube l1 l2 l3 hheatBasis hheat heig ?_ hdiag hcube hInv
  intro t x
  exact DifferentialGeometry.Integral.Connection.traceDataOfFirst (I := I) (M := M) (heig t x)
    (hcurv t x) (hRicFirst t x) (hScalarTrace t x)

omit [IsManifold I 1 M] in
omit [FiniteDimensional ℝ E] in
theorem scalar_eq_diag {x : M}
    {Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x}
    {scalar scalar0 l1 l2 l3 : Real}
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (hScalar : DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt
      (I := I) scalar Ric DifferentialGeometry.Integral.Connection.delta3 basis)
    (hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt
      (I := I) Ric scalar0 l1 l2 l3 basis) :
    scalar = scalar0 := by
  classical
  rcases hdiag with ⟨hscalar0, hric⟩
  have h00 :
      Ric (DifferentialGeometry.Integral.Connection.vec2 (basis 0) (basis 0)) = l1 := by
    simpa [DifferentialGeometry.Integral.Connection.ricciCompAt_apply, DifferentialGeometry.Integral.Connection.ricciDiag3] using hric 0 0
  have h11 :
      Ric (DifferentialGeometry.Integral.Connection.vec2 (basis 1) (basis 1)) = l2 := by
    simpa [DifferentialGeometry.Integral.Connection.ricciCompAt_apply, DifferentialGeometry.Integral.Connection.ricciDiag3] using hric 1 1
  have h22 :
      Ric (DifferentialGeometry.Integral.Connection.vec2 (basis 2) (basis 2)) = l3 := by
    simpa [DifferentialGeometry.Integral.Connection.ricciCompAt_apply, DifferentialGeometry.Integral.Connection.ricciDiag3] using hric 2 2
  rw [hScalar, hscalar0]
  rw [Fin.sum_univ_three]
  simp [DifferentialGeometry.Integral.Connection.delta3, h00, h11, h22,
    DifferentialGeometry.Integral.Connection.ricciEigenScalar3]



omit [IsManifold I 1 M] in
theorem scalarTrace_delta {x : M}
    (g : SmoothRiemannianMetric I M)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis) :
    DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt (I := I)
      (DifferentialGeometry.Integral.Connection.metricTracePair0SAt (I := I) g Ric)
      Ric DifferentialGeometry.Integral.Connection.delta3 basis := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
        DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) g basis horth
  unfold DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt
  rw [DifferentialGeometry.Integral.Connection.metricTracePair0SAt_eq_sum_basis
    (I := I) g basis DifferentialGeometry.Integral.Connection.delta3 hinv Ric]



omit [IsManifold I 1 M] in
theorem firstTrace_delta
    [SigmaCompactSpace M] [T2Space M]
    {x : M} (g : SmoothRiemannianMetric I M)
    {basis : Module.Basis (Fin 3) Real (TangentSpace I x)}
    (horth : DifferentialGeometry.Integral.Connection.OrthonormalBasisAt (I := I) g x basis)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm13 : DifferentialGeometry.Integral.Connection.Tensor13At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (hRic : Ric = DifferentialGeometry.Integral.Connection.ricciFromRm13At (I := I) (M := M) Rm13)
    (hLower : DifferentialGeometry.Integral.Connection.Rm04LowersRm13At (I := I) g x Rm13 Rm04) :
    DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04
      DifferentialGeometry.Integral.Connection.delta3 basis := by
  classical
  have hinv :
      Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
        DifferentialGeometry.Integral.Connection.delta3 :=
    DifferentialGeometry.Integral.Connection.orthonormal_invBasis3 (I := I) g basis horth
  have hInvSym :
      ∀ i j : Fin 3,
        DifferentialGeometry.Integral.Connection.delta3 i j = DifferentialGeometry.Integral.Connection.delta3 j i := by
    intro i j
    unfold DifferentialGeometry.Integral.Connection.delta3
    by_cases hij : i = j
    · subst j
      simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  exact DifferentialGeometry.Integral.Connection.ricciFirstTraceAt_of_rm13 (I := I) g basis
    DifferentialGeometry.Integral.Connection.delta3 hinv Ric Rm13 Rm04 hRic hLower hInvSym

theorem delta3_symm (i j : Fin 3) :
    DifferentialGeometry.Integral.Connection.delta3 i j = DifferentialGeometry.Integral.Connection.delta3 j i := by
  unfold DifferentialGeometry.Integral.Connection.delta3
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

private theorem sum_fin_two_fun_local {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α]
    (F : (Fin 2 -> Idx) -> α) :
    (∑ I0 : Fin 2 -> Idx, F I0) =
      ∑ i : Idx, ∑ j : Idx, F (fun a : Fin 2 => if a = 0 then i else j) := by
  classical
  rw [Fintype.sum_equiv (finTwoArrowEquiv Idx) F
    (fun p : Idx × Idx => F (fun a : Fin 2 => if a = 0 then p.1 else p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr
    funext a
    fin_cases a <;> simp [finTwoArrowEquiv]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] in
private theorem vec2_update_zero {x : M}
    (X Y X' : TangentSpace I x) :
    Function.update (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Y)
        (0 : Fin 2) X' =
      DifferentialGeometry.Integral.Connection.vec2 (I := I) X' Y := by
  funext a
  fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2, Function.update]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] in
private theorem vec2_update_one {x : M}
    (X Y Y' : TangentSpace I x) :
    Function.update (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Y)
        (1 : Fin 2) Y' =
      DifferentialGeometry.Integral.Connection.vec2 (I := I) X Y' := by
  funext a
  fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2, Function.update]



omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciSym_of_basis
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (A : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (hsym : ∀ i j : Idx,
      A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) =
        A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (basis i))) :
    DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) A := by
  classical
  intro X Y
  let cx : Idx -> Real := fun i => basis.repr X i
  let cy : Idx -> Real := fun i => basis.repr Y i
  have hX : X = ∑ i : Idx, cx i • basis i := by
    simp [cx]
  have hY : Y = ∑ i : Idx, cy i • basis i := by
    simp [cy]
  have hXY :
      A (DifferentialGeometry.Integral.Connection.vec2 (I := I) X Y) =
        ∑ r : Fin 2 -> Idx,
          A (fun a : Fin 2 =>
            (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        A (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cx j else cy j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            A (fun a : Fin 2 =>
              (if a = 0 then cx (r a) else cy (r a)) • basis (r a)) := by
      simpa using
        (ContinuousMultilinearMap.map_sum
          (f := A)
          (g := fun a j =>
            (if a = 0 then cx j else cy j) • basis j))
    simpa [DifferentialGeometry.Integral.Connection.vec2] using hsum
  have hYX :
      A (DifferentialGeometry.Integral.Connection.vec2 (I := I) Y X) =
        ∑ r : Fin 2 -> Idx,
          A (fun a : Fin 2 =>
            (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
    rw [hX, hY]
    have hsum :
        A (fun a : Fin 2 =>
            ∑ j : Idx,
              (if a = 0 then cy j else cx j) • basis j) =
          ∑ r : Fin 2 -> Idx,
            A (fun a : Fin 2 =>
              (if a = 0 then cy (r a) else cx (r a)) • basis (r a)) := by
      simpa using
        (ContinuousMultilinearMap.map_sum
          (f := A)
          (g := fun a j =>
            (if a = 0 then cy j else cx j) • basis j))
    simpa [DifferentialGeometry.Integral.Connection.vec2] using hsum
  rw [hXY, hYX]
  rw [sum_fin_two_fun_local, sum_fin_two_fun_local]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hleft :
      (fun a : Fin 2 =>
        (if a = 0
          then cx ((fun a : Fin 2 => if a = 0 then j else i) a)
          else cy ((fun a : Fin 2 => if a = 0 then j else i) a)) •
            basis ((fun a : Fin 2 => if a = 0 then j else i) a)) =
        DifferentialGeometry.Integral.Connection.vec2 (I := I) (cx j • basis j) (cy i • basis i) := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
  have hright :
      (fun a : Fin 2 =>
        (if a = 0
          then cy ((fun a : Fin 2 => if a = 0 then i else j) a)
          else cx ((fun a : Fin 2 => if a = 0 then i else j) a)) •
            basis ((fun a : Fin 2 => if a = 0 then i else j) a)) =
        DifferentialGeometry.Integral.Connection.vec2 (I := I) (cy i • basis i) (cx j • basis j) := by
    funext a
    fin_cases a <;> simp [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2]
  rw [hleft, hright]
  have hL :
      A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (cx j • basis j) (cy i • basis i)) =
        (cx j) * (cy i) *
          A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (basis i)) := by
    have h0 := A.map_update_smul
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (cy i • basis i))
      (0 : Fin 2) (cx j) (basis j)
    have h1 := A.map_update_smul
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (basis i))
      (1 : Fin 2) (cy i) (basis i)
    calc
      A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (cx j • basis j) (cy i • basis i))
          = (cx j) *
              A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (cy i • basis i)) := by
              simpa only [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2,
                vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cx j) * ((cy i) *
              A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (basis i))) := by
              congr 1
              simpa only [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2,
                vec2_update_one,
                smul_eq_mul] using h1
      _ = (cx j) * (cy i) *
              A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis j) (basis i)) := by ring
  have hR :
      A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (cy i • basis i) (cx j • basis j)) =
        (cy i) * (cx j) *
          A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) := by
    have h0 := A.map_update_smul
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (cx j • basis j))
      (0 : Fin 2) (cy i) (basis i)
    have h1 := A.map_update_smul
      (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j))
      (1 : Fin 2) (cx j) (basis j)
    calc
      A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (cy i • basis i) (cx j • basis j))
          = (cy i) *
              A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (cx j • basis j)) := by
              simpa only [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2,
                vec2_update_zero,
                smul_eq_mul] using h0
      _ = (cy i) * ((cx j) *
              A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j))) := by
              congr 1
              simpa only [DifferentialGeometry.Integral.Connection.vec2, DifferentialGeometry.Integral.Connection.vec2,
                vec2_update_one,
                smul_eq_mul] using h1
      _ = (cy i) * (cx j) *
              A (DifferentialGeometry.Integral.Connection.vec2 (I := I) (basis i) (basis j)) := by ring
  rw [hL, hR, hsym j i]
  ring



omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
theorem ricciSym_rm04
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (Ric : DifferentialGeometry.Integral.Connection.Tensor02At (I := I) (M := M) x)
    (Rm04 : DifferentialGeometry.Integral.Connection.Tensor04At (I := I) (M := M) x)
    (hTrace : DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt (I := I) Ric Rm04
      gInv basis)
    (hPair : ∀ W X Y Z : TangentSpace I x,
      Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) W X Y Z) =
        Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) Y Z W X))
    (hOutput : DifferentialGeometry.Integral.Connection.Rm04OutputSkewAt (I := I) Rm04)
    (hInput : ∀ X Y Z W : TangentSpace I x,
      Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) Y X Z W) =
        -Rm04 (DifferentialGeometry.Integral.Connection.vec4 (I := I) X Y Z W))
    (hInv : ∀ i j : Idx, gInv i j = gInv j i) :
    DifferentialGeometry.Integral.Connection.RicciSymAt (I := I) Ric := by
  exact ricciSym_of_basis (I := I) basis Ric
    (fun i j =>
      DifferentialGeometry.Integral.Connection.ricciSymm_of_rm04 (I := I) basis gInv Ric Rm04 hTrace
        hPair hOutput hInput hInv i j)





theorem tfRel_frame
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j)
    (hRm : ∀ (t : Real) (x : M) (i j k l : Fin 3),
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (-(l1 t x)) (-(l2 t x)) (-(l3 t x))
          i k j l) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  refine tfRel_from_eigen
    (M := M)
    scalar (ricciNormSqInFrame (I := I) S gInv frame) ricciTraceCube
    (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame)
    l1 l2 l3 hscalar ?_ hcube ?_
  · intro t x
    have hRicAt : ∀ i j : Fin 3,
        S.base.ricciAt t x (DifferentialGeometry.Integral.Connection.vec2 (frame i x) (frame j x)) =
          DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j := by
      intro i j
      simpa [ricciCompInFrame] using hRic t x i j
    have hraised : ∀ i j : Fin 3,
        raisedRicciCompInFrame (I := I) S gInv frame t x i j =
          DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j := by
      intro i j
      unfold raisedRicciCompInFrame
      fin_cases i <;> fin_cases j <;>
        simp [Fin.sum_univ_three, hInv t x, hRicAt, DifferentialGeometry.Integral.Connection.delta3,
          DifferentialGeometry.Integral.Connection.ricciDiag3]
    rw [ricciNormSqInFrame_apply]
    simp only [hraised]
    unfold DifferentialGeometry.Integral.Connection.ricciEigenNormSq3 DifferentialGeometry.Integral.Connection.ricciDiag3
    simp only [Fin.sum_univ_three]
    rw [hRic t x 0 0, hRic t x 1 1, hRic t x 2 2]
    simp [DifferentialGeometry.Integral.Connection.ricciDiag3]
    ring
  · intro t x
    exact canon3_frame_neg (I := I) S Rm04 gInv frame t x
      (l1 t x) (l2 t x) (l3 t x)
      (hInv t x) (hRic t x) (hRm t x)






theorem tfRel_data
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (htrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RiemannFromRicci3DTraceDataAt
        (I := I) (S.base.metric t) (-(S.ricciAt t x))
        (-(scalar t x)) (Rm04 t x) (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  classical
  have hRm : ∀ (t : Real) (x : M) (i j k l : Fin 3),
      DifferentialGeometry.Integral.Connection.rm04Comp (I := I) (Rm04 t) frame x i k j l =
        DifferentialGeometry.Integral.Connection.stdRmDiag3 (-(l1 t x)) (-(l2 t x)) (-(l3 t x))
          i k j l := by
    intro t x i j k l
    have hdiag : DifferentialGeometry.Integral.Connection.RicciDiagAt (I := I)
        (S.ricciAt t x) (scalar t x)
        (l1 t x) (l2 t x) (l3 t x) (basis t x) := by
      constructor
      · exact hscalar t x
      · intro a b
        have h := hRic t x a b
        simpa [ricciCompInFrame, DifferentialGeometry.Integral.Connection.ricciCompAt_apply,
          hbasis t x a, hbasis t x b] using h
    have hneg := diag_neg (I := I) hdiag
    have hcomp :=
      DifferentialGeometry.Integral.Connection.stdRmComp_eq_diag (I := I) (htrace t x) hneg
    have h := hcomp i k j l
    simpa [DifferentialGeometry.Integral.Connection.standardRmCompAt_apply, DifferentialGeometry.Integral.Connection.rm04Comp,
      DifferentialGeometry.Integral.Connection.rm04Comp, DifferentialGeometry.Integral.Connection.rm04CompAt_apply,
      hbasis t x i, hbasis t x k, hbasis t x j, hbasis t x l] using h
  exact tfRel_frame (I := I) S Rm04 gInv frame scalar ricciTraceCube
    l1 l2 l3 hscalar hcube hInv hRic hRm



theorem tfRel_first
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    [SigmaCompactSpace M] [T2Space M]
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Integral.Connection.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Integral.Connection.InverseMetricComponents M (Fin 3))
    (frame : Fin 3 -> (x : M) -> TangentSpace I x)
    (basis : (t : Real) -> (x : M) ->
      Module.Basis (Fin 3) Real (TangentSpace I x))
    (scalar ricciTraceCube : Real -> M -> Real)
    (l1 l2 l3 : Real -> M -> Real)
    (hbasis : ∀ (t : Real) (x : M) (i : Fin 3),
      basis t x i = frame i x)
    (horth : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.OrthonormalBasisAt
        (I := I) (S.base.metric t) x (basis t x))
    (hcurv : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.AlgebraicCurvatureSymmetries3
        (DifferentialGeometry.Integral.Connection.standardRmCompAt (I := I) (basis t x) (Rm04 t x)))
    (hRicTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.RicciRealizesRm04FirstTraceAt
        (I := I) (S.ricciAt t x) (Rm04 t x) DifferentialGeometry.Integral.Connection.delta3
        (basis t x))
    (hScalarTrace : ∀ (t : Real) (x : M),
      DifferentialGeometry.Integral.Connection.ScalarRealizesRicciTraceAt
        (I := I) (scalar t x) (S.ricciAt t x) DifferentialGeometry.Integral.Connection.delta3
        (basis t x))
    (hscalar : ∀ t x,
      scalar t x =
        DifferentialGeometry.Integral.Connection.ricciEigenScalar3 (l1 t x) (l2 t x) (l3 t x))
    (hcube : ∀ t x,
      ricciTraceCube t x =
        DifferentialGeometry.Integral.Connection.ricciEigenTraceCube3 (l1 t x) (l2 t x) (l3 t x))
    (hInv : ∀ (t : Real) (x : M) (i j : Fin 3),
      gInv t x i j = DifferentialGeometry.Integral.Connection.delta3 i j)
    (hRic : ∀ (t : Real) (x : M) (i j : Fin 3),
      ricciCompInFrame (I := I) S frame t x i j =
        DifferentialGeometry.Integral.Connection.ricciDiag3 (l1 t x) (l2 t x) (l3 t x) i j) :
    tfRicReactRel
      scalar
      (ricciNormSqInFrame (I := I) S gInv frame)
      (tfRicNormSq scalar (ricciNormSqInFrame (I := I) S gInv frame))
      (cubicQ scalar (ricciNormSqInFrame (I := I) S gInv frame)
        ricciTraceCube)
      (ricciNormCurvatureReactionInFrame (I := I) S Rm04 gInv frame) := by
  refine tfRel_data (I := I) S Rm04 gInv frame basis scalar
    ricciTraceCube l1 l2 l3 hbasis ?_ hscalar hcube hInv hRic
  intro t x
  exact DifferentialGeometry.Integral.Connection.traceDataOfFirst
    (I := I) (horth t x) (hcurv t x) (hRicTrace t x) (hScalarTrace t x)

end DifferentialGeometry.PDE.RicciFlow
