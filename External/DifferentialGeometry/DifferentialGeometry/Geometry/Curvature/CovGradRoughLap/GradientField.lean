import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradParallelNaturality


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
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

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_contMDiff_mk'
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 3 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 3 ℝ E)
        (E := fun z : M => TensorRSSpace 0 3 I z) b
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection b)) :=
  (covGrad (I := I) (M := M) g 0 2 T₀).toSection.contMDiff

omit [NeZero (Module.finrank ℝ E)] in
lemma rawTensorConnLap_covGrad_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    rawTensorConnLap (I := I) g 0 3
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 3
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x :=
  rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 3
    (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_apply_unit_eval_generic
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2 S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2 S x (v 0))
          (unitZeroSec (I := I) (M := M) x))
        (Matrix.vecTail v) :=
  covGrad_toSection_apply_eval (I := I) (M := M) g 0 2 S x
    (unitZeroSec (I := I) (M := M) x) v

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_apply_unit_eval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s S x (v 0))
          (unitZeroSec (I := I) (M := M) x))
        (Matrix.vecTail v) :=
  covGrad_toSection_apply_eval (I := I) (M := M) g 0 s S x
    (unitZeroSec (I := I) (M := M) x) v

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma curry_covGrad_unit_eval_general
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (w : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x w)
        (unitZeroSec (I := I) (M := M) x) := by
  classical
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  change Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x w)
        (unitZeroSec (I := I) (M := M) x)) m
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) (v0 := w) (vs := m)]
  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g s S x (Fin.cons w m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons w m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDeriv_unit_eval_eq
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 3
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDeriv_unit_eval_eq_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
          (fun y : M => σ y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s
    (LeviCivita (I := I) g) σ (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covApply_unit_eval_eq
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        covApply (tensorCov (I := I) g 0 3) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq (I := I) (M := M) g σ y (X y)

noncomputable def covApplyCovGradSection
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun y : M => TensorRSSpace 0 3 I y)⟯ :=
  ContMDiffSection.mk
    (fun y : M =>
      covApply (tensorCov (I := I) g 0 3) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 3
      (covGrad_contMDiff_mk' (I := I) (M := M) g T₀) hX)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covApplyCovGradSection_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyCovGradSection (I := I) (M := M) g T₀ hX y =
      covApply (tensorCov (I := I) g 0 3) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y := rfl

noncomputable def unitGradField
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    Π y : M, Tensor0SSpace 3 I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
      (unitZeroSec (I := I) (M := M) y)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma unitGradField_apply
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (y : M) :
    unitGradField (I := I) (M := M) g T₀ y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
        (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSecondCovDeriv_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorSecondCovDeriv (I := I) g 0 3 B B
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)) B
            (unitGradField (I := I) (M := M) g T₀)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)).toFun
          (unitGradField (I := I) (M := M) g T₀) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [ContinuousLinearMap.sub_apply]
  congr 1
  · have hσ : (fun y : M => covApplyCovGradSection (I := I) (M := M) g T₀ hB y) =
        (fun y : M => covApply (tensorCov (I := I) g 0 3) B
          (fun z : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection z) y) := by
      funext y; exact covApplyCovGradSection_apply (I := I) (M := M) g T₀ hB y
    have h1 := covDeriv_unit_eval_eq (I := I) (M := M) g
      (covApplyCovGradSection (I := I) (M := M) g T₀ hB) x (B x)
    simp only [covApplyCovGradSection_apply] at h1
    rw [h1]
    rw [covApply_unit_eval_eq (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection B]
    rfl
  · exact covDeriv_unit_eval_eq (I := I) (M := M) g
      (covGrad (I := I) (M := M) g 0 2 T₀).toSection x ((LeviCivita (I := I) g).toFun B x (B x))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π y : M, Tensor0SSpace (s + 1) I y)
    {Vfield Y : Π b : M, TangentSpace I b} {x : M}
    (hC : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E))
      (fun y => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M W y)) x)
    (hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x)
    (hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x) :
    (tensor0S_curry (I := I) (M := M) s x
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          W x (Vfield x))) (Y x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x (Vfield x) -
        Tensor0SNabla.curriedSection I M W x
          ((LeviCivita (I := I) g).toFun Y x (Vfield x)) := by
  classical
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (F := Tensor0SModel s ℝ E)
    (V := fun z : M => Tensor0SSpace s I z)
    (cov_TM := LeviCivita (I := I) g)
    (cov_V := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (τ := Tensor0SNabla.curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  have hsucc : tensor0S_curry (I := I) (M := M) s x
      ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        W x (Vfield x)) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M)
        (F := Tensor0SModel s ℝ E)
        (V := fun z : M => Tensor0SSpace s I z)
        (cov_TM := LeviCivita (I := I) g)
        (cov_V := Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (τ := Tensor0SNabla.curriedSection I M W) x (Vfield x) := by
    rw [show
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          W x (Vfield x) =
        (Tensor0SNabla.tensor0SCovariantDerivative_succ I M (LeviCivita (I := I) g)
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))).toFun
          W x (Vfield x) from by
      rw [Tensor0SNabla.tensor0SCovariantDerivative_succ_eq]]
    rw [Tensor0SNabla.tensor0SCovariantDerivative_succ_apply]
    exact (tensor0S_curry (I := I) (M := M) s x).apply_symm_apply _
  rw [hsucc]
  exact hHom

noncomputable def unitGradFieldGen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    Π y : M, Tensor0SSpace (s + 1) I y :=
  fun y : M =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
      (covGrad (I := I) (M := M) g 0 s S).toSection y)
      (unitZeroSec (I := I) (M := M) y)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma unitGradFieldGen_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (y : M) :
    unitGradFieldGen (I := I) (M := M) g s S y =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        (covGrad (I := I) (M := M) g 0 s S).toSection y)
        (unitZeroSec (I := I) (M := M) y) := rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_unitGradFieldGen (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        (unitGradFieldGen (I := I) (M := M) g s S y)) := by
  classical
  have hϕ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => (Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (s + 1) I z)) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          (covGrad (I := I) (M := M) g 0 s S).toSection y))) :=
    (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff
  have hv : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun z : M => Tensor0SSpace 0 I z) y
        (unitZeroSec (I := I) (M := M) y)) :=
    contMDiff_unitZeroSection (I := I) (M := M)
  exact ContMDiff.clm_bundle_apply (b := fun y : M => y)
    (E₁ := fun z : M => Tensor0SSpace 0 I z) (E₂ := fun z : M => Tensor0SSpace (s + 1) I z)
    (F₁ := Tensor0SModel 0 ℝ E) (F₂ := Tensor0SModel (s + 1) ℝ E) hϕ hv

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_curried_unitGradFieldGen (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => (TangentSpace I z →L[ℝ] Tensor0SSpace s I z)) y
        (Tensor0SNabla.curriedSection I M (unitGradFieldGen (I := I) (M := M) g s S) y)) :=
  (Tensor0SNabla.contMDiff_curriedSection_iff_section (I := I) (M := M)
    (unitGradFieldGen (I := I) (M := M) g s S)).mp
    (contMDiff_unitGradFieldGen (I := I) (M := M) g s S)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma curry_unitGradFieldGen_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (y : M) (w : TangentSpace I y) :
    Tensor0SNabla.curriedSection I M (unitGradFieldGen (I := I) (M := M) g s S) y w =
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
        tensorCovDerivAt (I := I) (M := M) g 0 s S y w)
        (unitZeroSec (I := I) (M := M) y) := by
  rw [Tensor0SNabla.curriedSection_apply, unitGradFieldGen_apply]
  exact curry_covGrad_unit_eval_general (I := I) (M := M) g s S y w

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covGrad_contMDiff_mk'_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b
        ((covGrad (I := I) (M := M) g 0 s S).toSection b)) :=
  (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff

noncomputable def covApplyCovGradSection_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) :
    @ContMDiffSection ℝ _ E _ _ H _ I M _ _ (TensorRSModel 0 (s + 1) ℝ E) _ _ ∞
      (fun y : M => TensorRSSpace 0 (s + 1) I y)
      (Tensor0SBundle.tensorRSBundle_topology 0 (s + 1)) (fun _ => inferInstance)
      (Tensor0SBundle.tensorRSBundle_fiber 0 (s + 1)) :=
  @ContMDiffSection.mk ℝ _ E _ _ H _ I M _ _ (TensorRSModel 0 (s + 1) ℝ E) _ _ ∞
    (fun y : M => TensorRSSpace 0 (s + 1) I y)
    (Tensor0SBundle.tensorRSBundle_topology 0 (s + 1)) (fun _ => inferInstance)
    (Tensor0SBundle.tensorRSBundle_fiber 0 (s + 1))
    (fun y : M =>
      covApply (tensorCov (I := I) g 0 (s + 1)) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y)
    (covApplyRS_contMDiff (I := I) g 0 (s + 1)
      (covGrad_contMDiff_mk'_genVal (I := I) (M := M) g s S) hX)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covApplyCovGradSection_genVal_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) (y : M) :
    covApplyCovGradSection_genVal (I := I) (M := M) g s S hX y =
      covApply (tensorCov (I := I) g 0 (s + 1)) X
        (fun z : M => (covGrad (I := I) (M := M) g 0 s S).toSection z) y := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covApply_unit_eval_eq_genVal
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 t ℝ E, (fun y : M => TensorRSSpace 0 t I y)⟯)
    (X : Π b : M, TangentSpace I b) :
    (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from
        covApply (tensorCov (I := I) g 0 t) X (fun z : M => σ z) y)
        (unitZeroSec (I := I) (M := M) y)) =
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M t (LeviCivita (I := I) g)) X
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace t I y from σ y)
            (unitZeroSec (I := I) (M := M) y)) := by
  funext y
  rw [covApply_apply, covApply_apply]
  exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g t σ y (X y)

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorSecondCovDeriv_covGrad_unit_eval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {B : Π b : M, TangentSpace I b}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B)) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) B B
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (covApply (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
              (LeviCivita (I := I) g)) B
            (unitGradFieldGen (I := I) (M := M) g s S)) x (B x) -
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (unitGradFieldGen (I := I) (M := M) g s S) x
          ((LeviCivita (I := I) g).toFun B x (B x)) := by
  classical
  rw [tensorSecondCovDeriv_def]
  rw [ContinuousLinearMap.sub_apply]
  congr 1
  · have h1 := covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covApplyCovGradSection_genVal (I := I) (M := M) g s S hB) x (B x)
    simp only [covApplyCovGradSection_genVal_apply] at h1
    rw [h1]
    rw [covApply_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection B]
    rfl
  · exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1)
      (covGrad (I := I) (M := M) g 0 s S).toSection x ((LeviCivita (I := I) g).toFun B x (B x))

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorSecondCovDeriv_eq_covGrad_succ_twoSlotEval_genVal
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (x : M)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          (covGrad (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s S)).toSection x)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons (X x) (Fin.cons (Y x) m)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorSecondCovDeriv (I := I) g 0 s X Y (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x))
        m := by
  classical

  set GS : SmoothCcTensor g 0 (s + 1) := covGrad (I := I) (M := M) g 0 s S with hGS

  rw [covGrad_apply_unit_eval_genVal (I := I) (M := M) g (s + 1) GS x
    (Fin.cons (X x) (Fin.cons (Y x) m))]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons (X x) (Fin.cons (Y x) m) ∘ Fin.succ) = Fin.cons (Y x) m from
    funext (fun j => by simp [Fin.cons_succ])]

  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g 0 (s + 1) GS x (X x))
        (unitZeroSec (I := I) (M := M) x) =
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x (X x) from by
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 (s + 1) GS x (X x)]
    exact covDeriv_unit_eval_eq_genVal (I := I) (M := M) g (s + 1) GS.toSection x (X x)]

  rw [show Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
          (unitGradFieldGen (I := I) (M := M) g s S) x (X x))
        (Fin.cons (Y x) m) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
            (unitGradFieldGen (I := I) (M := M) g s S) x (X x)) (Y x)) m from
    (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)).toFun
        (unitGradFieldGen (I := I) (M := M) g s S) x (X x)) (v0 := Y x) (vs := m)).symm]

  rw [curry_covDeriv_succ_eq_covDeriv_curriedSection_sub_connCorrection (I := I) (M := M) g s
    (unitGradFieldGen (I := I) (M := M) g s S) (Vfield := X) (Y := Y) (x := x)
    ((contMDiff_curried_unitGradFieldGen (I := I) (M := M) g s S x).mdifferentiableAt (by simp))
    ((hX x).mdifferentiableAt (by simp)) ((hY x).mdifferentiableAt (by simp))]

  rw [show (fun y : M => Tensor0SNabla.curriedSection I M
        (unitGradFieldGen (I := I) (M := M) g s S) y (Y y)) =
      (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
          tensorCovDerivAt (I := I) (M := M) g 0 s S y (Y y))
          (unitZeroSec (I := I) (M := M) y)) from
    funext (fun y => curry_unitGradFieldGen_eq (I := I) (M := M) g s S y (Y y))]
  rw [curry_unitGradFieldGen_eq (I := I) (M := M) g s S x
    ((LeviCivita (I := I) g).toFun Y x (X x))]

  rw [tensorSecondCovDeriv_def (I := I) g 0 s X Y (fun y : M => S.toSection y) x]

  refine congrArg (fun T : Tensor0SSpace s I x => Tensor0SSpace.toModel T m) ?_

  rw [ContinuousLinearMap.sub_apply]

  have houter :
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun y : M =>
            (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
              tensorCovDerivAt (I := I) (M := M) g 0 s S y (Y y))
              (unitZeroSec (I := I) (M := M) y)) x (X x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) Y (fun y : M => S.toSection y)) x (X x))
          (unitZeroSec (I := I) (M := M) x) := by
    set σ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
      ContMDiffSection.mk
        (fun y : M => covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y)
        (covApplyRS_contMDiff (I := I) g 0 s
          (T := fun z : M => S.toSection z) S.toSection.contMDiff (X := Y) hY) with hσ
    have hσapp : ∀ y : M, σ y =
        covApply (tensorCov (I := I) g 0 s) Y (fun z : M => S.toSection z) y := fun y => rfl
    rw [show (covApply (tensorCov (I := I) g 0 s) Y (fun y : M => S.toSection y)) =
        (fun y : M => σ y) from funext (fun y => (hσapp y).symm)]
    rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s σ x (X x)]
    refine congrArg (fun F : Π z : M, Tensor0SSpace s I z =>
      (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun F x (X x)) ?_
    funext y
    rw [hσapp y, covApply_apply, ← tensorCovDerivAt_def (I := I) (M := M) g 0 s S y (Y y)]

  have hchr :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s S x ((LeviCivita (I := I) g).toFun Y x (X x)))
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          ((LeviCivita (I := I) g).toFun Y x (X x)))
        (unitZeroSec (I := I) (M := M) x) := by
    rw [tensorCovDerivAt_def (I := I) (M := M) g 0 s S x ((LeviCivita (I := I) g).toFun Y x (X x))]
  rw [houter, hchr]

end Connection
end Integral
end DifferentialGeometry

end
