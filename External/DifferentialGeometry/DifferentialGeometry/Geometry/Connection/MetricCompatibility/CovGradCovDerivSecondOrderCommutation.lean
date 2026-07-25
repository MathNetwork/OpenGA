import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivCommutation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Geometry.Curvature.Order2Defect.GradientSlotLeibniz

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def nablaTensorCurvSec
    (g : SmoothRiemannianMetric I M) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {𝒱 : M → Type*} [∀ x, AddCommGroup (𝒱 x)] [∀ x, Module ℝ (𝒱 x)]
    [∀ x, TopologicalSpace (𝒱 x)] [TopologicalSpace (TotalSpace F 𝒱)]
    [∀ x, IsTopologicalAddGroup (𝒱 x)] [∀ x, ContinuousSMul ℝ (𝒱 x)]
    [FiberBundle F 𝒱] [VectorBundle ℝ F 𝒱]
    (cov : CovariantDerivative I F 𝒱)
    (X Y Z : Π b : M, TangentSpace I b) (V : Π b : M, 𝒱 b) (x : M) : 𝒱 x :=
  cov.toFun (fun b => riemannSec cov Y Z V b) x (X x)
    - riemannSec cov (covApply (LeviCivita (I := I) g) X Y) Z V x
    - riemannSec cov Y (covApply (LeviCivita (I := I) g) X Z) V x
    - riemannSec cov Y Z (covApply cov X V) x

def secondOrderChristoffelResidual
    (g : SmoothRiemannianMetric I M) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {𝒱 : M → Type*} [∀ x, AddCommGroup (𝒱 x)] [∀ x, Module ℝ (𝒱 x)]
    [∀ x, TopologicalSpace (𝒱 x)] [TopologicalSpace (TotalSpace F 𝒱)]
    [∀ x, IsTopologicalAddGroup (𝒱 x)] [∀ x, ContinuousSMul ℝ (𝒱 x)]
    [FiberBundle F 𝒱] [VectorBundle ℝ F 𝒱]
    (cov : CovariantDerivative I F 𝒱)
    (B w : Π b : M, TangentSpace I b) (V : Π b : M, 𝒱 b) (x : M) : 𝒱 x :=
  cov.toFun (covApply cov B V) x (VectorField.mlieBracket I B w x)
    + cov.toFun (covApply cov (VectorField.mlieBracket I B w) V) x (B x)
    - (2 : ℝ) • cov.toFun (covApply cov (covApply (LeviCivita (I := I) g) B w) V) x (B x)
    + cov.toFun V x ((covApply (LeviCivita (I := I) g) B
        (covApply (LeviCivita (I := I) g) B w)) x)
    - cov.toFun (covApply cov w V) x ((covApply (LeviCivita (I := I) g) B B) x)
    + cov.toFun V x ((covApply (LeviCivita (I := I) g)
        (covApply (LeviCivita (I := I) g) B B) w) x)
    + cov.toFun (covApply cov (covApply (LeviCivita (I := I) g) B B) V) x (w x)

omit [CompactSpace M] [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma secondOrderChristoffelResidual_def
    (g : SmoothRiemannianMetric I M) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {𝒱 : M → Type*} [∀ x, AddCommGroup (𝒱 x)] [∀ x, Module ℝ (𝒱 x)]
    [∀ x, TopologicalSpace (𝒱 x)] [TopologicalSpace (TotalSpace F 𝒱)]
    [∀ x, IsTopologicalAddGroup (𝒱 x)] [∀ x, ContinuousSMul ℝ (𝒱 x)]
    [FiberBundle F 𝒱] [VectorBundle ℝ F 𝒱]
    (cov : CovariantDerivative I F 𝒱)
    (B w : Π b : M, TangentSpace I b) (V : Π b : M, 𝒱 b) (x : M) :
    secondOrderChristoffelResidual (I := I) g cov B w V x =
      cov.toFun (covApply cov B V) x (VectorField.mlieBracket I B w x)
        + cov.toFun (covApply cov (VectorField.mlieBracket I B w) V) x (B x)
        - (2 : ℝ) • cov.toFun (covApply cov (covApply (LeviCivita (I := I) g) B w) V) x (B x)
        + cov.toFun V x ((covApply (LeviCivita (I := I) g) B
            (covApply (LeviCivita (I := I) g) B w)) x)
        - cov.toFun (covApply cov w V) x ((covApply (LeviCivita (I := I) g) B B) x)
        + cov.toFun V x ((covApply (LeviCivita (I := I) g)
            (covApply (LeviCivita (I := I) g) B B) w) x)
        + cov.toFun (covApply cov (covApply (LeviCivita (I := I) g) B B) V) x (w x) := rfl

omit [CompactSpace M] [I.Boundaryless] in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma nablaTensorCurvSec_def
    (g : SmoothRiemannianMetric I M) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {𝒱 : M → Type*} [∀ x, AddCommGroup (𝒱 x)] [∀ x, Module ℝ (𝒱 x)]
    [∀ x, TopologicalSpace (𝒱 x)] [TopologicalSpace (TotalSpace F 𝒱)]
    [∀ x, IsTopologicalAddGroup (𝒱 x)] [∀ x, ContinuousSMul ℝ (𝒱 x)]
    [FiberBundle F 𝒱] [VectorBundle ℝ F 𝒱]
    (cov : CovariantDerivative I F 𝒱)
    (X Y Z : Π b : M, TangentSpace I b) (V : Π b : M, 𝒱 b) (x : M) :
    nablaTensorCurvSec (I := I) g cov X Y Z V x =
      cov.toFun (fun b => riemannSec cov Y Z V b) x (X x)
        - riemannSec cov (covApply (LeviCivita (I := I) g) X Y) Z V x
        - riemannSec cov Y (covApply (LeviCivita (I := I) g) X Z) V x
        - riemannSec cov Y Z (covApply cov X V) x := rfl

section AbstractThirdOrder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {𝒱 : M → Type*} [∀ x, AddCommGroup (𝒱 x)] [∀ x, Module ℝ (𝒱 x)]
  [∀ x, TopologicalSpace (𝒱 x)] [TopologicalSpace (TotalSpace F 𝒱)]
  [∀ x, IsTopologicalAddGroup (𝒱 x)] [∀ x, ContinuousSMul ℝ (𝒱 x)]
  [FiberBundle F 𝒱] [VectorBundle ℝ F 𝒱] [ContMDiffVectorBundle ∞ F 𝒱 I]

omit [CompactSpace M] [I.Boundaryless] in

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F 𝒱 I] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
lemma thirdOrder_commutation_abstract
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F 𝒱)
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {B w : Π b : M, TangentSpace I b} {V : Π b : M, 𝒱 b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% V)) :
    (cov.toFun (covApply cov B (covApply cov w V)) x (B x)
        - (2 : ℝ) • cov.toFun (covApply cov (covApply (LeviCivita (I := I) g) B w) V) x (B x)
        + cov.toFun V x ((covApply (LeviCivita (I := I) g) B
            (covApply (LeviCivita (I := I) g) B w)) x)
        - cov.toFun (covApply cov w V) x ((covApply (LeviCivita (I := I) g) B B) x)
        + cov.toFun V x ((covApply (LeviCivita (I := I) g)
            (covApply (LeviCivita (I := I) g) B B) w) x))
      - (cov.toFun (covApply cov B (covApply cov B V)) x (w x)
          - cov.toFun (covApply cov (covApply (LeviCivita (I := I) g) B B) V) x (w x)) =
      nablaTensorCurvSec (I := I) g cov B B w V x
        + (riemannSec cov (covApply (LeviCivita (I := I) g) B B) w V x
            + riemannSec cov B (covApply (LeviCivita (I := I) g) B w) V x
            + (2 : ℝ) • riemannSec cov B w (covApply cov B V) x)
        + secondOrderChristoffelResidual (I := I) g cov B w V x := by
  classical

  have hwBV : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (covApply cov w (covApply cov B V))) :=
    covApply_covApply_contMDiff (cov := cov) hw hB hV
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I B w)) :=
    mlieBracket_contMDiff (I := I) hB hw
  have hbrV : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞
      (T% (covApply cov (VectorField.mlieBracket I B w) V)) :=
    covApply_contMDiff (cov := cov) hbr hV
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (fun b : M => riemannSec cov B w V b)) :=
    riemannSec_contMDiff (cov := cov) hB hw hV

  have hSW : covApply cov B (covApply cov w V) =
      covApply cov w (covApply cov B V)
        + covApply cov (VectorField.mlieBracket I B w) V
        + (fun b : M => riemannSec cov B w V b) := by
    funext y
    have := covApply_outer_swap_eq_riemannSec cov B w V y
    simp only [Pi.add_apply, covApply_apply]
    rw [this]

  have hsplit : cov.toFun (covApply cov B (covApply cov w V)) x (B x) =
      cov.toFun (covApply cov w (covApply cov B V)) x (B x)
        + cov.toFun (covApply cov (VectorField.mlieBracket I B w) V) x (B x)
        + cov.toFun (fun b : M => riemannSec cov B w V b) x (B x) := by
    have h1 : MDiffAt (T% (covApply cov w (covApply cov B V))) x :=
      (hwBV x).mdifferentiableAt (by simp)
    have h2 : MDiffAt (T% (covApply cov (VectorField.mlieBracket I B w) V)) x :=
      (hbrV x).mdifferentiableAt (by simp)
    have h3 : MDiffAt (T% (fun b : M => riemannSec cov B w V b)) x :=
      (hRsec x).mdifferentiableAt (by simp)
    have h12 : MDiffAt (T% (covApply cov w (covApply cov B V)
        + covApply cov (VectorField.mlieBracket I B w) V)) x :=
      mdifferentiableAt_add_section h1 h2
    rw [hSW]
    rw [cov.isCovariantDerivativeOnUniv.add h12 h3,
        cov.isCovariantDerivativeOnUniv.add h1 h2]
    simp only [ContinuousLinearMap.add_apply]

  have hswap2 := covApply_outer_swap_eq_riemannSec cov B w (covApply cov B V) x

  have hcurv : cov.toFun (fun b : M => riemannSec cov B w V b) x (B x) =
      nablaTensorCurvSec (I := I) g cov B B w V x
        + riemannSec cov (covApply (LeviCivita (I := I) g) B B) w V x
        + riemannSec cov B (covApply (LeviCivita (I := I) g) B w) V x
        + riemannSec cov B w (covApply cov B V) x := by
    rw [nablaTensorCurvSec_def]; abel
  rw [secondOrderChristoffelResidual_def, hsplit, hswap2, hcurv]
  simp only [two_smul]
  abel

end AbstractThirdOrder

section Reductions

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_covDeriv_innerSlot_secondOrder_eq_abstract
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B w : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s B B
                (fun z : M => S.toSection z) y) x))
          (unitZeroSec (I := I) (M := M) x)) (w x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B
              (unitEvalSection (I := I) (M := M) g s S))) x (w x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (covApply (LeviCivita (I := I) g) B B)
            (unitEvalSection (I := I) (M := M) g s S)) x (w x) := by
  classical
  set nab := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) with hnab
  set V := unitEvalSection (I := I) (M := M) g s S with hV

  rw [tensor0S_curry_covGradBundleEquiv_unit_genVal (I := I) (M := M) s x
    ((tensorCov (I := I) g 0 s).toFun
      (fun y : M => tensorSecondCovDeriv (I := I) g 0 s B B
        (fun z : M => S.toSection z) y) x) (w x)]

  have hSsec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (S.toSection y)) :=
    S.toSection.contMDiff
  have hBBsm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) B
          (covApply (tensorCov (I := I) g 0 s) B (fun z : M => S.toSection z)) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s
      (covApplyRS_contMDiff (I := I) g 0 s hSsec hB) hB
  have hDBsm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (covApply (LeviCivita (I := I) g) B B)
          (fun z : M => S.toSection z) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hSsec
      (covApply_contMDiff (cov := LeviCivita (I := I) g) hB hB)
  have hHsmooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (tensorSecondCovDeriv (I := I) g 0 s B B (fun z : M => S.toSection z) y)) := by
    have hsub := hBBsm.sub_section hDBsm
    refine hsub.congr ?_
    intro y
    rw [tensorSecondCovDeriv_def]
    rfl
  set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
    ContMDiffSection.mk
      (fun y : M => tensorSecondCovDeriv (I := I) g 0 s B B (fun z : M => S.toSection z) y)
      hHsmooth with hσ
  have hσapp : ∀ y : M, σ y =
      tensorSecondCovDeriv (I := I) g 0 s B B (fun z : M => S.toSection z) y := fun y => rfl

  rw [show (fun y : M => tensorSecondCovDeriv (I := I) g 0 s B B
        (fun z : M => S.toSection z) y) = (fun y : M => σ y) from
    funext (fun y => (hσapp y).symm)]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s σ x (w x)]

  rw [show (fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
        (unitZeroSec (I := I) (M := M) y)) =
      (fun y : M => nab.toFun (covApply nab B V) y (B y) - nab.toFun V y
        ((LeviCivita (I := I) g).toFun B y (B y))) from by
    funext y
    rw [hσapp y]
    exact tensorSecondCovDeriv_unit_eval_genVal (I := I) (M := M) g s S hB y]

  have hVsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y (V y)) :=
    contMDiff_unitEvalSection (I := I) (M := M) g s S
  have hDsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g) B B)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hB hB
  have h1 := (covApply_covApply_contMDiff (cov := nab) hB hB hVsm x).mdifferentiableAt (by simp)
  have h2 := (covApply_contMDiff (cov := nab) hDsm hVsm x).mdifferentiableAt (by simp)
  rw [show (fun y : M => nab.toFun (covApply nab B V) y (B y) - nab.toFun V y
        ((LeviCivita (I := I) g).toFun B y (B y))) =
      covApply nab B (covApply nab B V) - covApply nab (covApply (LeviCivita (I := I) g) B B) V from by
    funext y
    simp only [Pi.sub_apply, covApply_apply]]
  rw [cov_toFun_sub nab h1 h2]
  simp only [ContinuousLinearMap.sub_apply]

omit [NeZero (Module.finrank ℝ E)] in
lemma curry_covApply_unitGradFieldGen_eq_abstractHess
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B w : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (y : M) :
    Tensor0SNabla.curriedSection I M
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)) B
          (unitGradFieldGen (I := I) (M := M) g s S)) y (w y) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
            (unitEvalSection (I := I) (M := M) g s S)) y (B y) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (unitEvalSection (I := I) (M := M) g s S) y
          ((covApply (LeviCivita (I := I) g) B w) y) := by
  classical
  set nab1 := Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) with hn1
  set nab := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) with hn
  set U := unitGradFieldGen (I := I) (M := M) g s S with hU
  set V := unitEvalSection (I := I) (M := M) g s S with hV

  have hcov : Tensor0SNabla.curriedSection I M (covApply nab1 B U) y (w y) =
      tensor0S_curry (I := I) (M := M) s y (nab1.toFun U y (B y)) (w y) := by
    rw [Tensor0SNabla.curriedSection_apply]; rfl
  rw [hcov]

  rw [curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g s U (Vfield := B) (Y := w) (x := y)
    ((contMDiff_curried_unitGradFieldGen (I := I) (M := M) g s S y).mdifferentiableAt (by simp))
    ((hB y).mdifferentiableAt (by simp)) ((hw y).mdifferentiableAt (by simp))]

  rw [curriedSection_unitGradFieldGen_eq_covApply_abstract (I := I) (M := M) g s S w]
  rw [curriedSection_unitGradFieldGen_apply (I := I) (M := M) g s S y
    ((LeviCivita (I := I) g).toFun w y (B y))]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_covDeriv_leadingSlot_secondOrder_eq_abstract
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B w : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorSecondCovDeriv (I := I) g 0 (s + 1) B B
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) (w x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
              (unitEvalSection (I := I) (M := M) g s S))) x (B x)
        - (2 : ℝ) • (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (covApply (LeviCivita (I := I) g) B w)
              (unitEvalSection (I := I) (M := M) g s S)) x (B x)
        + (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (unitEvalSection (I := I) (M := M) g s S) x
            ((covApply (LeviCivita (I := I) g) B (covApply (LeviCivita (I := I) g) B w)) x)
        - (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
              (unitEvalSection (I := I) (M := M) g s S)) x
            ((covApply (LeviCivita (I := I) g) B B) x)
        + (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (unitEvalSection (I := I) (M := M) g s S) x
            ((covApply (LeviCivita (I := I) g) (covApply (LeviCivita (I := I) g) B B) w) x) := by
  classical

  have hCwsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g) B w)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) hB hw
  have hUsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        (unitGradFieldGen (I := I) (M := M) g s S y)) :=
    contMDiff_unitGradFieldGen (I := I) (M := M) g s S
  have hBUsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g)) B (unitGradFieldGen (I := I) (M := M) g s S) y)) :=
    covApply_contMDiff
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
      hB hUsm
  have hcurBU : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
            (LeviCivita (I := I) g)) B (unitGradFieldGen (I := I) (M := M) g s S)) y)) :=
    (Tensor0SNabla.contMDiff_curriedSection_iff_section (I := I) (M := M)
      (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
        (LeviCivita (I := I) g)) B (unitGradFieldGen (I := I) (M := M) g s S))).mp hBUsm

  rw [tensorSecondCovDeriv_covGrad_unit_eval_genVal (I := I) (M := M) g s S hB x]

  rw [map_sub, ContinuousLinearMap.sub_apply]

  rw [curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g s
    (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g)) B (unitGradFieldGen (I := I) (M := M) g s S))
    (Vfield := B) (Y := w) (x := x)
    ((hcurBU x).mdifferentiableAt (by simp))
    ((hB x).mdifferentiableAt (by simp)) ((hw x).mdifferentiableAt (by simp))]

  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x
        ((LeviCivita (I := I) g).toFun B x (B x)) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x
        ((covApply (LeviCivita (I := I) g) B B) x) from rfl]
  rw [curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g s
    (unitGradFieldGen (I := I) (M := M) g s S)
    (Vfield := covApply (LeviCivita (I := I) g) B B) (Y := w) (x := x)
    ((contMDiff_curried_unitGradFieldGen (I := I) (M := M) g s S x).mdifferentiableAt (by simp))
    ((covApply_contMDiff (cov := LeviCivita (I := I) g) hB hB x).mdifferentiableAt (by simp))
    ((hw x).mdifferentiableAt (by simp))]

  rw [show (fun y : M => Tensor0SNabla.curriedSection I M
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g)) B (unitGradFieldGen (I := I) (M := M) g s S)) y (w y)) =
      (fun y : M =>
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
              (unitEvalSection (I := I) (M := M) g s S)) y (B y) -
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
            (unitEvalSection (I := I) (M := M) g s S) y
            ((covApply (LeviCivita (I := I) g) B w) y)) from
    funext (fun y => curry_covApply_unitGradFieldGen_eq_abstractHess (I := I) (M := M) g s S hB hw y)]

  rw [show ((LeviCivita (I := I) g).toFun w x (B x)) = (covApply (LeviCivita (I := I) g) B w x)
    from rfl]
  rw [curry_covApply_unitGradFieldGen_eq_abstractHess (I := I) (M := M) g s S
    (w := covApply (LeviCivita (I := I) g) B w) hB hCwsm x]

  rw [curriedSection_unitGradFieldGen_eq_covApply_abstract (I := I) (M := M) g s S w]
  rw [curriedSection_unitGradFieldGen_apply (I := I) (M := M) g s S x
    ((LeviCivita (I := I) g).toFun w x ((covApply (LeviCivita (I := I) g) B B) x))]

  have hVsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y (unitEvalSection (I := I) (M := M) g s S y)) :=
    contMDiff_unitEvalSection (I := I) (M := M) g s S
  have hwVsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
          (unitEvalSection (I := I) (M := M) g s S) y)) :=
    covApply_contMDiff
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) hw hVsm
  have hCwVsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) y
        (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (covApply (LeviCivita (I := I) g) B w)
          (unitEvalSection (I := I) (M := M) g s S) y)) :=
    covApply_contMDiff
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) hCwsm hVsm
  have hsplitB : (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
        (fun y : M =>
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
                (unitEvalSection (I := I) (M := M) g s S)) y (B y) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
              (unitEvalSection (I := I) (M := M) g s S) y
              ((covApply (LeviCivita (I := I) g) B w) y)) x (B x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
              (unitEvalSection (I := I) (M := M) g s S))) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (covApply (LeviCivita (I := I) g) B w)
            (unitEvalSection (I := I) (M := M) g s S)) x (B x) := by
    have h1 := (covApply_covApply_contMDiff
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      hB hw hVsm x).mdifferentiableAt (by simp)
    have h2 := (covApply_contMDiff
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      hCwsm hVsm x).mdifferentiableAt (by simp)
    rw [show (fun y : M =>
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
                (unitEvalSection (I := I) (M := M) g s S)) y (B y) -
            (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
              (unitEvalSection (I := I) (M := M) g s S) y
              ((covApply (LeviCivita (I := I) g) B w) y)) =
        covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B
            (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) w
              (unitEvalSection (I := I) (M := M) g s S)) -
          covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (covApply (LeviCivita (I := I) g) B w)
            (unitEvalSection (I := I) (M := M) g s S) from by
      funext y; simp only [Pi.sub_apply, covApply_apply]]
    rw [cov_toFun_sub
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) h1 h2]
    simp only [ContinuousLinearMap.sub_apply]
  rw [hsplitB]

  rw [show ((LeviCivita (I := I) g).toFun w x ((covApply (LeviCivita (I := I) g) B B) x)) =
      (covApply (LeviCivita (I := I) g) (covApply (LeviCivita (I := I) g) B B) w x) from rfl]
  simp only [two_smul]
  abel

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_covDeriv_leadingSlot_secondOrder_commutation
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B w : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          tensorSecondCovDeriv (I := I) g 0 (s + 1) B B
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
          (unitZeroSec (I := I) (M := M) x)) (w x) -
      tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 s x
            ((tensorCov (I := I) g 0 s).toFun
              (fun y : M => tensorSecondCovDeriv (I := I) g 0 s B B
                (fun z : M => S.toSection z) y) x))
          (unitZeroSec (I := I) (M := M) x)) (w x) =
      nablaTensorCurvSec (I := I) g
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B B w
          (unitEvalSection (I := I) (M := M) g s S) x
        + (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (covApply (LeviCivita (I := I) g) B B) w
              (unitEvalSection (I := I) (M := M) g s S) x
            + riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              B (covApply (LeviCivita (I := I) g) B w)
              (unitEvalSection (I := I) (M := M) g s S) x
            + (2 : ℝ) • riemannSec
              (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B w
              (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B
                (unitEvalSection (I := I) (M := M) g s S)) x)
        + secondOrderChristoffelResidual (I := I) g
            (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) B w
            (unitEvalSection (I := I) (M := M) g s S) x := by
  classical
  rw [covGrad_covDeriv_leadingSlot_secondOrder_eq_abstract (I := I) (M := M) g s S hB hw x]
  rw [covGrad_covDeriv_innerSlot_secondOrder_eq_abstract (I := I) (M := M) g s S hB x]
  exact thirdOrder_commutation_abstract (I := I) (M := M) g
    (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)) hB hw
    (contMDiff_unitEvalSection (I := I) (M := M) g s S)

end Reductions

end Connection
end Integral
end DifferentialGeometry

end
