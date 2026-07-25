import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldDifferentiatedTowerNormalForm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open TensorMultilinear
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in

def appCcRSFib (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (x : M) :
    TensorRSSpace a c I x :=
  (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCcRSFib_contMDiff (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel a c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel a c ℝ E)
        (E := fun z : M => TensorRSSpace a c I z) x
        (appCcRSFib (I := I) (M := M) g a b c Φ W x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun x => appCcRSFib (I := I) (M := M) g a b c Φ W x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel c ℝ E)
      (E := fun z : M => Tensor0SSpace c I z) x
      (appCcRSFib (I := I) (M := M) g a b c Φ W x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel c ℝ E)
      (E := fun z : M => Tensor0SSpace c I z) x
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) (Y x)))) := by
    funext x; rfl
  rw [heq]
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel b ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel b ℝ E)
        (E := fun z : M => Tensor0SSpace b I z) x
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff Y.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hWY

set_option backward.isDefEq.respectTransparency false in

def ccOperatorFieldComp (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) : SmoothCcTensor g a c where
  toSection :=
    { toFun := fun x : M => appCcRSFib (I := I) (M := M) g a b c Φ W x
      contMDiff_toFun := appCcRSFib_contMDiff (I := I) (M := M) g a b c Φ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma appCcRS_toSection (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (x : M) :
    (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x =
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCcRS_zero_eq_appCc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    ccOperatorFieldComp (I := I) (M := M) g 0 r s Φ W = operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, appCc_toSection]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApply_assoc (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (C : SmoothCcTensor g a b)
    (W : SmoothCcTensor g 0 a) :
    operatorFieldApply (I := I) (M := M) g b c Φ
        (operatorFieldApply (I := I) (M := M) g a b C W) =
      operatorFieldApply (I := I) (M := M) g a c
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ C) W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection, appCc_toSection, appCcRS_toSection,
    ContinuousLinearMap.comp_assoc]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCcRS_add_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ + W₂) =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ + ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ + ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x) =
      (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁).toSection x +
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂).toSection x from rfl]
  rw [appCcRS_toSection, appCcRS_toSection, appCcRS_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace a b I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.comp_add]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCcRS_smul_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (k : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (k • W) =
      k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x) =
      k • (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x from rfl]
  rw [appCcRS_toSection, appCcRS_toSection]
  rw [show ((k • W).toSection x : TensorRSSpace a b I x) = k • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.comp_smul]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem ccOperatorFieldComp_sub_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂) =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
  calc
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂) =
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ + (-W₂)) := by
      rw [sub_eq_add_neg]
    _ = ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ +
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ (-W₂) :=
      appCcRS_add_right (I := I) (M := M) g a b c Φ W₁ (-W₂)
    _ = ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ +
        -ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
      rw [show -W₂ = (-1 : ℝ) • W₂ by rw [neg_one_smul],
        appCcRS_smul_right, neg_one_smul]
    _ = ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
      rw [sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCcRS_add_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (Φ₁ + Φ₂) W =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ₁ W + ccOperatorFieldComp (I := I) (M := M) g a b c Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ₁ W + ccOperatorFieldComp (I := I) (M := M) g a b c Φ₂ W).toSection x) =
      (ccOperatorFieldComp (I := I) (M := M) g a b c Φ₁ W).toSection x +
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ₂ W).toSection x from rfl]
  rw [appCcRS_toSection, appCcRS_toSection, appCcRS_toSection]
  rw [show ((Φ₁ + Φ₂).toSection x : TensorRSSpace b c I x) = Φ₁.toSection x + Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_comp]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem appCcRS_zero_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W = 0 := by
  have h := appCcRS_add_left (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) 0 W
  rw [add_zero] at h
  have h2 : ccOperatorFieldComp (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W -
      ccOperatorFieldComp (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W =
      ccOperatorFieldComp (I := I) (M := M) g a b c (0 : SmoothCcTensor g b c) W := by
    nth_rewrite 1 [h]; abel
  rwa [sub_self] at h2

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem appCcRS_neg_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (-Φ) W = -ccOperatorFieldComp (I := I) (M := M) g a b c Φ W := by
  have h := appCcRS_add_left (I := I) (M := M) g a b c Φ (-Φ) W
  rw [add_neg_cancel, appCcRS_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem appCcRS_sub_left (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (Φ₁ - Φ₂) W =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ₁ W - ccOperatorFieldComp (I := I) (M := M) g a b c Φ₂ W := by
  rw [sub_eq_add_neg, appCcRS_add_left, appCcRS_neg_left, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_appCcRS_eq (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) (x : M) (v : E) :
    (show TensorRSSpace a c I x from
        tensorCovDerivAt (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) x v) =
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g b c Φ x v).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) +
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
            tensorCovDerivAt (I := I) (M := M) g a b W x v) := by
  apply ContinuousLinearMap.ext
  intro d
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel a ℝ E) (V := fun y : M => Tensor0SSpace a I y) (n := (⊤ : ℕ∞)) x d
  have hWd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel b ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel b ℝ E)
        (E := fun z : M => Tensor0SSpace b I z) y
        ((show Tensor0SSpace a I y →L[ℝ] Tensor0SSpace b I y from W.toSection y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff dSec.contMDiff
  let Wd : Cₛ^∞⟮I; Tensor0SModel b ℝ E, (fun y : M => Tensor0SSpace b I y)⟯ :=
    ⟨fun y : M => (show Tensor0SSpace a I y →L[ℝ] Tensor0SSpace b I y from W.toSection y) (dSec y),
      hWd_smooth⟩

  have hLHS :
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) x v) d =
        (Tensor0SNabla.tensor0SCovariantDerivative I M c (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace b I y →L[ℝ] Tensor0SSpace c I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
            ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M a (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    have hval : (fun y : M =>
          (show Tensor0SSpace a I y →L[ℝ] Tensor0SSpace c I y from
            (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection y) (dSec y)) =
        (fun y : M =>
          (show Tensor0SSpace b I y →L[ℝ] Tensor0SSpace c I y from Φ.toSection y) (Wd y)) := by
      funext y
      rw [appCcRS_toSection (I := I) (M := M) g a b c Φ W y]
      rfl
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) a c (LeviCivita (I := I) g)
        (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection dSec x v, hval,
      appCcRS_toSection (I := I) (M := M) g a b c Φ W x, ContinuousLinearMap.comp_apply]

  have hT1 :
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g b c Φ x v)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) d) =
        (Tensor0SNabla.tensor0SCovariantDerivative I M c (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace b I y →L[ℝ] Tensor0SSpace c I y from Φ.toSection y) (Wd y)) x v) -
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M b (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) := by
    rw [show (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) d = Wd x from by
      rw [show d = dSec x from hdSec.symm]; rfl,
      tensorCovDerivAt_def (I := I) (M := M) g b c Φ x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) b c (LeviCivita (I := I) g)
        Φ.toSection Wd x v]

  have hT2 :
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
          tensorCovDerivAt (I := I) (M := M) g a b W x v) d) =
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M b (LeviCivita (I := I) g)
              (fun y : M => Wd y) x v) -
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
            ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M a (LeviCivita (I := I) g)
                (fun y : M => dSec y) x v)) := by
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g a b W x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) a b (LeviCivita (I := I) g)
        W.toSection dSec x v]
    rw [map_sub (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)]
    rfl
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hLHS, hT1, hT2]
  abel

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor0S_curry_covGrad_appCcRS_eq (g : SmoothRiemannianMetric I M) (a b : ℕ)
    (W : SmoothCcTensor g a b) (x : M) (d : Tensor0SSpace a I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) b x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (b + 1) I x from
          (covGrad (I := I) (M := M) g a b W).toSection x) d) v0 =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
        tensorCovDerivAt (I := I) (M := M) g a b W x v0) d := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (b + 1) I x from
      (covGrad (I := I) (M := M) g a b W).toSection x) d) (v0 := v0) (vs := m)]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g a b W x d (Fin.cons v0 m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons v0 m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_appCcRS_eq (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    covGrad (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W +
        ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W +
        ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b W)).toSection x) =
      (ccOperatorFieldComp (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W).toSection x +
        (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
          (covGrad (I := I) (M := M) g a b W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

  rw [covGrad_toSection_apply_eval (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) x d v]

  rw [appCcRS_toSection (I := I) (M := M) g a b (c + 1) (covGrad (I := I) (M := M) g b c Φ) W x,
    ContinuousLinearMap.comp_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g b c Φ x
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) d) v]

  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (ccOperatorFieldComp (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
            (covGrad (I := I) (M := M) g a b W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
          ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
            tensorCovDerivAt (I := I) (M := M) g a b W x (v 0)) d))
        (Matrix.vecTail v) := by
    rw [appCcRS_toSection (I := I) (M := M) g a (b + 1) (c + 1) (slotExtend (I := I) (M := M) g b c Φ)
        (covGrad (I := I) (M := M) g a b W) x, ContinuousLinearMap.comp_apply,
      slotExtend_toSection (I := I) (M := M) g b c Φ x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g b c x
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace (b + 1) I x from
        (covGrad (I := I) (M := M) g a b W).toSection x) d) (v 0) (Matrix.vecTail v)]
    rw [tensor0S_curry_covGrad_appCcRS_eq (I := I) (M := M) g a b W x d (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]

  rw [show (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x from
        tensorCovDerivAt (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) x (v 0)) =
      (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
          tensorCovDerivAt (I := I) (M := M) g b c Φ x (v 0)).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) +
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
          (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
            tensorCovDerivAt (I := I) (M := M) g a b W x (v 0)) from
    tensorCovDerivAt_appCcRS_eq (I := I) (M := M) g a b c Φ W x (v 0)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma exists_orthoFrame_repr_anyRank
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      (∀ i : Fin n, bse i = e i) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (p q : ℕ) (S : TensorRSSpace p q I x),
        riemannianFiberNormSq (I := I) (M := M) g p q x S =
          ∑ K : Fin p → Fin n, ∑ J : Fin q → Fin n,
            fiberNormSqSummand (I := I) (M := M) g x p q S n e K J := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, eob.toBasis, ?_, ?_, ?_⟩
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
  · intro i j
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth i j
    rw [← hinner_eq (eob i) (eob j)]
    exact hite
  · intro p q S
    rfl


omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
private lemma fiberNormSqComponent_comp_anyRank_eq
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (x : M)
    (Φx : TensorRSSpace b c I x) (Wx : TensorRSSpace a b I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin a → Fin n) (J : Fin c → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x a c
        (show TensorRSSpace a c I x from
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
            (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) n e K J =
      ∑ P : Fin b → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
          fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := by
  classical
  change (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K k)))))
      (fun k => e (J k)) = _
  set wval : Tensor0SSpace b I x :=
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin a) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K k)))) with hwval
  have hexp := tensorS_coframe_expansion (I := I) (M := M) g x b e bse hbse horth wval
  conv_lhs => rw [hexp]
  rw [map_sum]
  rw [show (∑ P : Fin b → Fin n,
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          ((wval (fun k : Fin b => e (P k))) • coframeS (I := I) (M := M) g x b e P)) =
      ∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P) from by
    refine Finset.sum_congr rfl (fun P _ => ?_); rw [map_smul]]
  rw [show ((∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) : ℝ) =
      Tensor0SSpace.toModel (∑ P : Fin b → Fin n, (wval (fun k : Fin b => e (P k))) •
        (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
          (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) from rfl]
  rw [← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply]
  have hΦcomp : Tensor0SSpace.toModel
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx)
        (coframeS (I := I) (M := M) g x b e P)) (fun k => e (J k)) =
      fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J := rfl
  rw [hΦcomp]
  have hwcomp : wval (fun k : Fin b => e (P k)) =
      fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P := rfl
  rw [hwcomp, smul_eq_mul]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_compRS_le_mul
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (x : M)
    (Φx : TensorRSSpace b c I x) (Wx : TensorRSSpace a b I x) :
    riemannianFiberNormSq (I := I) (M := M) g a c x
        (show TensorRSSpace a c I x from
          (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
            (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) ≤
      riemannianFiberNormSq (I := I) (M := M) g b c x Φx *
        riemannianFiberNormSq (I := I) (M := M) g a b x Wx := by
  classical
  obtain ⟨n, e, bse, hbse, horth, hrepr⟩ :=
    exists_orthoFrame_repr_anyRank (I := I) (M := M) g x

  have hreprAC : ∀ S : TensorRSSpace a c I x,
      riemannianFiberNormSq (I := I) (M := M) g a c x S =
        ∑ K : Fin a → Fin n, ∑ J : Fin c → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x a c S n e K J := hrepr a c
  have hreprAB : ∀ S : TensorRSSpace a b I x,
      riemannianFiberNormSq (I := I) (M := M) g a b x S =
        ∑ K : Fin a → Fin n, ∑ P : Fin b → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x a b S n e K P := hrepr a b
  have hreprBC : ∀ S : TensorRSSpace b c I x,
      riemannianFiberNormSq (I := I) (M := M) g b c x S =
        ∑ P : Fin b → Fin n, ∑ J : Fin c → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x b c S n e P J := hrepr b c
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x a c e hreprAC _]
  have hWrepr : (∑ K : Fin a → Fin n, ∑ P : Fin b → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g a b x Wx := by
    rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x a b e hreprAB Wx]
  have hΦrepr : (∑ P : Fin b → Fin n, ∑ J : Fin c → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J) ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g b c x Φx := by
    rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g x b c e hreprBC Φx]

  have hcomp_eq : ∀ (K : Fin a → Fin n) (J : Fin c → Fin n),
      fiberNormSqComponent (I := I) (M := M) g x a c
          (show TensorRSSpace a c I x from
            (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φx).comp
              (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Wx)) n e K J =
        ∑ P : Fin b → Fin n,
          fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
            fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J :=
    fun K J => fiberNormSqComponent_comp_anyRank_eq (I := I) (M := M) g a b c x Φx Wx e bse hbse horth K J
  rw [Finset.sum_congr rfl (fun K (_ : K ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun J (_ : J ∈ Finset.univ) => by rw [hcomp_eq K J]))]

  set rfnsΦ : ℝ := riemannianFiberNormSq (I := I) (M := M) g b c x Φx with hrfnsΦ_def
  have hrfnsΦ_nonneg : 0 ≤ rfnsΦ := riemannianFiberNormSq_nonneg (I := I) (M := M) g b c x Φx

  have hper_row : ∀ K : Fin a → Fin n,
      (∑ J : Fin c → Fin n,
          (∑ P : Fin b → Fin n,
            fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P *
              fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J) ^ 2) ≤
        (∑ P : Fin b → Fin n, (fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P) ^ 2) *
          rfnsΦ := by
    intro K
    refine le_trans (Finset.sum_le_sum (fun J (_ : J ∈ Finset.univ) =>
      Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
        (fun P : Fin b → Fin n => fiberNormSqComponent (I := I) (M := M) g x a b Wx n e K P)
        (fun P : Fin b → Fin n => fiberNormSqComponent (I := I) (M := M) g x b c Φx n e P J))) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun P _ => sq_nonneg _))
    rw [← hΦrepr]
    exact le_of_eq Finset.sum_comm

  refine le_trans (Finset.sum_le_sum (fun K (_ : K ∈ Finset.univ) => hper_row K)) ?_
  rw [← Finset.sum_mul, hWrepr, mul_comm]


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [CompleteSpace E] in
theorem exists_uniform_riemannianFiberNormSq_appCcRS_le
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (Φ : SmoothCcTensor g b c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : SmoothCcTensor g a b) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g a c x
          ((ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x) ≤
        C * riemannianFiberNormSq (I := I) (M := M) g a b x (W.toSection x) := by
  obtain ⟨K, hK_nn, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor g b c Φ
  refine ⟨K, hK_nn, fun W x => ?_⟩
  rw [appCcRS_toSection (I := I) (M := M) g a b c Φ W x]
  refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g a b c x
    (Φ.toSection x) (W.toSection x)) ?_
  exact mul_le_mul_of_nonneg_right (hK x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g a b x (W.toSection x))


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCcRS_castRankCc_db {a a' b b' : ℕ} (g : SmoothRiemannianMetric I M) (r : ℕ)
    (ha : a = a') (hb : b = b')
    (Φ : SmoothCcTensor g a b) (V : SmoothCcTensor g r a) :
    castCcTensorRank g r hb (ccOperatorFieldComp (I := I) (M := M) g r a b Φ V) =
      ccOperatorFieldComp (I := I) (M := M) g r a' b' (castCcTensorSourceRank g b' ha (castCcTensorRank g a hb Φ))
        (castCcTensorRank g r ha V) := by
  subst ha; subst hb; rfl

def NormalFormRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (p rr : ℕ) : Prop :=
  ∃ Ψ : (k : ℕ) → SmoothCcTensor g (rr + k) (rr + p),
    ∀ W : SmoothCcTensor g r rr,
      op p rr W =
        ∑ k ∈ Finset.range (p + 1),
          ccOperatorFieldComp (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k) (iteratedCovGrad g r rr k W)


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_normalFormRS_sum (g : SmoothRiemannianMetric I M) (r p rr : ℕ)
    (Ψ : (k : ℕ) → SmoothCcTensor g (rr + k) (rr + p)) (W : SmoothCcTensor g r rr) :
    covGrad (I := I) (M := M) g r (rr + p)
        (∑ k ∈ Finset.range (p + 1),
          ccOperatorFieldComp (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k) (iteratedCovGrad g r rr k W)) =
      ∑ k ∈ Finset.range (p + 1),
        (ccOperatorFieldComp (I := I) (M := M) g r (rr + k) (rr + (p + 1))
            (covGrad (I := I) (M := M) g (rr + k) (rr + p) (Ψ k)) (iteratedCovGrad g r rr k W) +
          ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
            (slotExtend (I := I) (M := M) g (rr + k) (rr + p) (Ψ k))
            (iteratedCovGrad g r rr (k + 1) W)) := by
  rw [covGrad_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covGrad_appCcRS_eq (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k) (iteratedCovGrad g r rr k W)]
  rw [show covGrad (I := I) (M := M) g r (rr + k) (iteratedCovGrad g r rr k W) =
      iteratedCovGrad g r rr (k + 1) W from (iteratedCovGrad_succ g r rr k W).symm]
  rfl


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem castRankCc_appCcRS_iteratedCovGrad_covGrad (g : SmoothRiemannianMetric I M) (r p rr k : ℕ)
    (Ψ : SmoothCcTensor g ((rr + 1) + k) ((rr + 1) + p)) (W : SmoothCcTensor g r rr) :
    castCcTensorRank g r (by omega : (rr + 1) + p = rr + (p + 1))
        (ccOperatorFieldComp (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + p) Ψ
          (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))) =
      ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
        (castCcTensorSourceRank g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
          (castCcTensorRank g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) Ψ))
        (iteratedCovGrad g r rr (k + 1) W) := by
  rw [appCcRS_castRankCc_db g r (by omega : (rr + 1) + k = rr + (k + 1))
    (by omega : (rr + 1) + p = rr + (p + 1)) Ψ (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))]
  congr 1
  apply eq_of_heq
  refine HEq.trans ?_ (iteratedCovGrad_covGrad_comm_heq' g r rr k W)
  exact castRankCc_db_heq g r (by omega : (rr + 1) + k = rr + (k + 1))
    (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W))


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalFormRS_succ (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + p) (op p rr W) =
        op (p + 1) rr W +
          castCcTensorRank g r (by omega : (rr + 1) + p = rr + (p + 1)) (op p (rr + 1) (covGrad g r rr W)))
    (p : ℕ) (hp : ∀ rr, NormalFormRS (I := I) (M := M) g r op p rr) (rr : ℕ) :
    NormalFormRS (I := I) (M := M) g r op (p + 1) rr := by
  classical
  obtain ⟨Ψr, hΨr⟩ := hp rr
  obtain ⟨Ψr1, hΨr1⟩ := hp (rr + 1)

  set Tk : (k : ℕ) → SmoothCcTensor g (rr + (k + 1)) (rr + (p + 1)) := fun k =>
    slotExtend (I := I) (M := M) g (rr + k) (rr + p) (Ψr k) -
      castCcTensorSourceRank g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
        (castCcTensorRank g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) (Ψr1 k))
    with hTk_def

  refine ⟨fun j => match j with
    | 0 => covGrad (I := I) (M := M) g (rr + 0) (rr + p) (Ψr 0)
    | (k + 1) =>
        (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1)) else 0)
          + Tk k, ?_⟩
  intro W

  have hrec : op (p + 1) rr W =
      covGrad g r (rr + p) (op p rr W) -
        castCcTensorRank g r (by omega : (rr + 1) + p = rr + (p + 1))
          (op p (rr + 1) (covGrad g r rr W)) := by
    rw [covGrad_op p rr W]; abel
  rw [hrec, hΨr W]

  rw [covGrad_normalFormRS_sum (I := I) (M := M) g r p rr Ψr W]

  rw [hΨr1 (covGrad g r rr W), castRankCc_db_finset_sum]
  rw [show (∑ k ∈ Finset.range (p + 1),
        castCcTensorRank g r (by omega : (rr + 1) + p = rr + (p + 1))
          (ccOperatorFieldComp (I := I) (M := M) g r ((rr + 1) + k) ((rr + 1) + p) (Ψr1 k)
            (iteratedCovGrad g r (rr + 1) k (covGrad g r rr W)))) =
      ∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (castCcTensorSourceRank g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castCcTensorRank g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g r rr (k + 1) W) from
    Finset.sum_congr rfl (fun k _ =>
      castRankCc_appCcRS_iteratedCovGrad_covGrad (I := I) (M := M) g r p rr k (Ψr1 k) W)]

  rw [Finset.sum_add_distrib]

  rw [Finset.sum_range_succ' (fun j =>
    ccOperatorFieldComp (I := I) (M := M) g r (rr + j) (rr + (p + 1))
      ((match j with
        | 0 => covGrad (I := I) (M := M) g (rr + 0) (rr + p) (Ψr 0)
        | (k + 1) =>
            (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
              else 0) + Tk k))
      (iteratedCovGrad g r rr j W)) (p + 1)]

  rw [show (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          ((if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
            else 0) + Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) +
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [appCcRS_add_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1)) (Tk k)
          (iteratedCovGrad g r rr (k + 1) W)) =
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (slotExtend (I := I) (M := M) g (rr + k) (rr + p) (Ψr k))
          (iteratedCovGrad g r rr (k + 1) W)) -
      (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (castCcTensorSourceRank g (rr + (p + 1)) (by omega : (rr + 1) + k = rr + (k + 1))
            (castCcTensorRank g ((rr + 1) + k) (by omega : (rr + 1) + p = rr + (p + 1)) (Ψr1 k)))
          (iteratedCovGrad g r rr (k + 1) W)) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hTk_def, appCcRS_sub_left]]

  rw [show (∑ k ∈ Finset.range (p + 1),
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (if k + 1 < p + 1 then covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1))
            else 0)
          (iteratedCovGrad g r rr (k + 1) W)) =
      ∑ k ∈ Finset.range p,
        ccOperatorFieldComp (I := I) (M := M) g r (rr + (k + 1)) (rr + (p + 1))
          (covGrad (I := I) (M := M) g (rr + (k + 1)) (rr + p) (Ψr (k + 1)))
          (iteratedCovGrad g r rr (k + 1) W) from by
    rw [Finset.sum_range_succ]
    rw [if_neg (by omega : ¬ (p + 1 < p + 1)), appCcRS_zero_left, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (by simp only [Finset.mem_range] at hk; omega : k + 1 < p + 1)]]

  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g r (rr + k) (rr + (p + 1))
      (covGrad (I := I) (M := M) g (rr + k) (rr + p) (Ψr k)) (iteratedCovGrad g r rr k W)) p]

  abel


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalForm_zeroRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (rr : ℕ) (Φ₀ : SmoothCcTensor g (rr + 0) (rr + 0))
    (hbase : ∀ W : SmoothCcTensor g r rr,
      op 0 rr W = ccOperatorFieldComp (I := I) (M := M) g r (rr + 0) (rr + 0) Φ₀ W) :
    NormalFormRS (I := I) (M := M) g r op 0 rr := by
  refine ⟨fun k => match k with | 0 => Φ₀ | (_ + 1) => 0, fun W => ?_⟩
  rw [hbase W, Finset.sum_range_one]
  rfl


omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem normalForm_of_baseRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (covGrad_op : ∀ (p rr : ℕ) (W : SmoothCcTensor g r rr),
      covGrad g r (rr + p) (op p rr W) =
        op (p + 1) rr W +
          castCcTensorRank g r (by omega : (rr + 1) + p = rr + (p + 1)) (op p (rr + 1) (covGrad g r rr W)))
    (Φ₀ : ∀ rr : ℕ, SmoothCcTensor g (rr + 0) (rr + 0))
    (hbase : ∀ (rr : ℕ) (W : SmoothCcTensor g r rr),
      op 0 rr W = ccOperatorFieldComp (I := I) (M := M) g r (rr + 0) (rr + 0) (Φ₀ rr) W)
    (p : ℕ) : ∀ rr : ℕ, NormalFormRS (I := I) (M := M) g r op p rr := by
  induction p with
  | zero => exact fun rr => normalForm_zeroRS (I := I) (M := M) g r op rr (Φ₀ rr) (hbase rr)
  | succ p ih => exact fun rr => normalFormRS_succ (I := I) (M := M) g r op covGrad_op p ih rr


omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_jet_bound_of_normalFormRS (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p rr : ℕ), SmoothCcTensor g r rr → SmoothCcTensor g r (rr + p))
    (p rr : ℕ) (hNF : NormalFormRS (I := I) (M := M) g r op p rr) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
      ∀ (W : SmoothCcTensor g r rr) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r (rr + p) x ((op p rr W).toSection x) ≤
          kappa * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g r (rr + q) x
              ((iteratedCovGrad g r rr q W).toSection x) := by
  classical
  obtain ⟨Ψ, hΨ⟩ := hNF

  choose C hC_nn hC using fun k =>
    exists_uniform_riemannianFiberNormSq_appCcRS_le (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k)
  refine ⟨(p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC_nn k), fun W x => ?_⟩

  set a : ℕ → ℝ := fun k => riemannianFiberNormSq (I := I) (M := M) g r (rr + k) x
    ((iteratedCovGrad g r rr k W).toSection x) with ha_def
  have ha_nn : ∀ k, 0 ≤ a k := fun k =>
    riemannianFiberNormSq_nonneg (I := I) (M := M) g r (rr + k) x _

  rw [hΨ W, SmoothCcTensor.toSection_sum_apply]

  refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g r (rr + p) x
    (Finset.range (p + 1))
    (fun k => (ccOperatorFieldComp (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k)
      (iteratedCovGrad g r rr k W)).toSection x)) ?_
  rw [Finset.card_range]

  have hsummand : ∀ k ∈ Finset.range (p + 1),
      riemannianFiberNormSq (I := I) (M := M) g r (rr + p) x
          ((ccOperatorFieldComp (I := I) (M := M) g r (rr + k) (rr + p) (Ψ k)
            (iteratedCovGrad g r rr k W)).toSection x) ≤ C k * a k := fun k _ => hC k _ x
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsummand) (by positivity)) ?_

  have hCa_le : (∑ k ∈ Finset.range (p + 1), C k * a k) ≤
      (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hC_nn k)
    exact Finset.single_le_sum (f := a) (fun j _ => ha_nn j) ‹k ∈ Finset.range (p + 1)›
  rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 from by push_cast; ring]
  calc (p + 1 : ℝ) * ∑ k ∈ Finset.range (p + 1), C k * a k
      ≤ (p + 1 : ℝ) * ((∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k) :=
        mul_le_mul_of_nonneg_left hCa_le (by positivity)
    _ = (p + 1 : ℝ) * (∑ k ∈ Finset.range (p + 1), C k) * ∑ k ∈ Finset.range (p + 1), a k := by ring
set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem appCc_assoc (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (C : SmoothCcTensor g a b)
    (W : SmoothCcTensor g 0 a) :
    operatorFieldApply (I := I) (M := M) g b c Φ (operatorFieldApply (I := I) (M := M) g a b C W) =
      operatorFieldApply (I := I) (M := M) g a c (ccOperatorFieldComp (I := I) (M := M) g a b c Φ C) W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection, appCc_toSection, appCc_toSection, appCcRS_toSection,
    ContinuousLinearMap.comp_assoc]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem appCcRS_sub_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂) =
      ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
  calc
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ - W₂) =
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ (W₁ + (-W₂)) := by
      rw [sub_eq_add_neg]
    _ = ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ +
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ (-W₂) :=
      appCcRS_add_right (I := I) (M := M) g a b c Φ W₁ (-W₂)
    _ = ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ +
        -ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
      rw [show -W₂ = (-1 : ℝ) • W₂ by rw [neg_one_smul],
        appCcRS_smul_right, neg_one_smul]
    _ = ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ W₂ := by
      rw [sub_eq_add_neg]


end Connection
end Integral
end DifferentialGeometry

end
