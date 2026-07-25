import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Gradient
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Green
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Laplacian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.GradientContinuity
import DifferentialGeometry.Geometry.Boundary.EuclideanHalfSpaceInstance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

structure FullSmoothScalar (g : SmoothRiemannianMetric (I_half n) M) where

  toFun : M → ℝ

  smooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ toFun

namespace FullSmoothScalar

variable {g : SmoothRiemannianMetric (I_half n) M}

@[ext] theorem ext {f h : FullSmoothScalar g} (hfh : f.toFun = h.toFun) : f = h := by
  cases f; cases h; congr

instance : Zero (FullSmoothScalar g) where
  zero :=
    { toFun := fun _ => 0
      smooth := contMDiff_const }

instance : Add (FullSmoothScalar g) where
  add f h :=
    { toFun := f.toFun + h.toFun
      smooth := f.smooth.add h.smooth }

instance : Neg (FullSmoothScalar g) where
  neg f :=
    { toFun := -f.toFun
      smooth := f.smooth.neg }

instance : Sub (FullSmoothScalar g) where
  sub f h :=
    { toFun := f.toFun - h.toFun
      smooth := f.smooth.sub h.smooth }

instance : SMul ℝ (FullSmoothScalar g) where
  smul c f :=
    { toFun := c • f.toFun
      smooth := by
        have h : (c • f.toFun) = (fun x : M => c * f.toFun x) := by
          funext x; rfl
        rw [h]
        exact contMDiff_const.mul f.smooth }

@[simp] lemma toFun_zero : (0 : FullSmoothScalar g).toFun = (fun _ : M => 0) := rfl

@[simp] lemma toFun_zero_apply (x : M) : (0 : FullSmoothScalar g).toFun x = 0 := rfl

@[simp] lemma toFun_add (f h : FullSmoothScalar g) :
    (f + h).toFun = f.toFun + h.toFun := rfl

@[simp] lemma toFun_add_apply (f h : FullSmoothScalar g) (x : M) :
    (f + h).toFun x = f.toFun x + h.toFun x := rfl

@[simp] lemma toFun_neg (f : FullSmoothScalar g) :
    (-f).toFun = -f.toFun := rfl

@[simp] lemma toFun_neg_apply (f : FullSmoothScalar g) (x : M) :
    (-f).toFun x = -f.toFun x := rfl

@[simp] lemma toFun_sub (f h : FullSmoothScalar g) :
    (f - h).toFun = f.toFun - h.toFun := rfl

@[simp] lemma toFun_sub_apply (f h : FullSmoothScalar g) (x : M) :
    (f - h).toFun x = f.toFun x - h.toFun x := rfl

@[simp] lemma toFun_smul (c : ℝ) (f : FullSmoothScalar g) :
    (c • f).toFun = c • f.toFun := rfl

@[simp] lemma toFun_smul_apply (c : ℝ) (f : FullSmoothScalar g) (x : M) :
    (c • f).toFun x = c * f.toFun x := rfl

lemma toFun_injective :
    Function.Injective (fun f : FullSmoothScalar g => f.toFun) := by
  intro f h hfh
  exact ext hfh

instance : SMul ℕ (FullSmoothScalar g) := ⟨nsmulRec⟩
instance : SMul ℤ (FullSmoothScalar g) := ⟨zsmulRec⟩

@[simp] lemma toFun_nsmul (f : FullSmoothScalar g) (k : ℕ) :
    (k • f).toFun = k • f.toFun := by
  induction k with
  | zero =>
    change (nsmulRec 0 f).toFun = (0 : ℕ) • f.toFun
    change (0 : FullSmoothScalar g).toFun = (0 : ℕ) • f.toFun
    rw [toFun_zero, zero_nsmul]
    rfl
  | succ k ih =>
    change (nsmulRec (k + 1) f).toFun = (k + 1) • f.toFun
    change (nsmulRec k f + f).toFun = (k + 1) • f.toFun
    have hk : (nsmulRec k f).toFun = k • f.toFun := ih
    rw [toFun_add, hk, succ_nsmul]

@[simp] lemma toFun_zsmul (f : FullSmoothScalar g) (z : ℤ) :
    (z • f).toFun = z • f.toFun := by
  rcases z with k | k
  · change (k • f).toFun = (Int.ofNat k) • f.toFun
    rw [toFun_nsmul]; simp
  · change (-((k + 1) • f)).toFun = (Int.negSucc k) • f.toFun
    rw [toFun_neg, toFun_nsmul]
    show -((k + 1) • f.toFun) = Int.negSucc k • f.toFun
    rw [show (Int.negSucc k : ℤ) = -((k + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (FullSmoothScalar g) :=
  toFun_injective.addCommGroup
    (fun f => f.toFun)
    toFun_zero
    toFun_add
    toFun_neg
    toFun_sub
    toFun_nsmul
    toFun_zsmul

def toFunAddHom : FullSmoothScalar g →+ (M → ℝ) where
  toFun := fun f => f.toFun
  map_zero' := toFun_zero
  map_add' := toFun_add

instance : Module ℝ (FullSmoothScalar g) :=
  toFun_injective.module ℝ toFunAddHom toFun_smul

end FullSmoothScalar

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [CompactSpace M] in
lemma FullSmoothScalar.continuous_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : FullSmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := I_half n) g f.toFun x)
        (gradFun (I := I_half n) g h.toFun x)) :=
  continuous_g_inner_gradFun_gradFun (n := n) (M := M) g f.smooth h.smooth

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma FullSmoothScalar.continuous_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : FullSmoothScalar g) :
    Continuous (fun x : M => f.toFun x * h.toFun x) :=
  f.smooth.continuous.mul h.smooth.continuous

lemma FullSmoothScalar.integrable_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : FullSmoothScalar g) :
    Integrable (fun x : M => f.toFun x * h.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  exact (f.continuous_mul h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma FullSmoothScalar.integrable_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : FullSmoothScalar g) :
    Integrable (fun x : M =>
        g.inner x (gradFun (I := I_half n) g f.toFun x)
          (gradFun (I := I_half n) g h.toFun x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  integrable_g_inner_gradFun_gradFun (n := n) (M := M) g f.smooth h.smooth

def fullSmoothScalarH1Inner
    {g : SmoothRiemannianMetric (I_half n) M}
    (f h : FullSmoothScalar g) : ℝ :=
  (∫ x, f.toFun x * h.toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
  (∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
        (gradFun (I := I_half n) g h.toFun x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g))

omit [CompactSpace M] in
lemma fullSmoothScalarH1Inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : FullSmoothScalar g) :
    fullSmoothScalarH1Inner f h =
      (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := rfl

omit [CompactSpace M] in
lemma fullSmoothScalarH1Inner_symm
    {g : SmoothRiemannianMetric (I_half n) M} (f h : FullSmoothScalar g) :
    fullSmoothScalarH1Inner f h = fullSmoothScalarH1Inner h f := by
  unfold fullSmoothScalarH1Inner
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact mul_comm _ _
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _

omit [CompactSpace M] in
lemma FullSmoothScalar.integral_mul_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    0 ≤ ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact mul_self_nonneg _

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma SmoothRiemannianMetric_inner_self_nonneg
    (g : SmoothRiemannianMetric (I_half n) M) (x : M)
    (v : TangentSpace (I_half n) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv; simp [map_zero]
  · exact (g.pos x v hv).le

omit [CompactSpace M] in
lemma FullSmoothScalar.integral_inner_grad_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    0 ≤ ∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
          (gradFun (I := I_half n) g f.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact SmoothRiemannianMetric_inner_self_nonneg g x _

omit [CompactSpace M] in
lemma fullSmoothScalarH1Inner_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    0 ≤ fullSmoothScalarH1Inner f f := by
  unfold fullSmoothScalarH1Inner
  exact add_nonneg f.integral_mul_self_nonneg f.integral_inner_grad_self_nonneg

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma FullSmoothScalar.gradFun_add_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ : FullSmoothScalar g) (x : M) :
    gradFun (I := I_half n) g (f₁ + f₂).toFun x =
      gradFun (I := I_half n) g f₁.toFun x +
        gradFun (I := I_half n) g f₂.toFun x := by
  have hfun : (f₁ + f₂).toFun = f₁.toFun + f₂.toFun := rfl
  rw [hfun]
  exact gradFun_add (I := I_half n) g
    (f₁.smooth.mdifferentiable (by simp) x)
    (f₂.smooth.mdifferentiable (by simp) x)

lemma fullSmoothScalar_integral_mul_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : FullSmoothScalar g) :
    (∫ x, (f₁ + f₂).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, f₁.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, f₂.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, (f₁ + f₂).toFun x * h.toFun x =
      f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x := by
    intro x
    rw [FullSmoothScalar.toFun_add_apply]
    ring
  rw [show (fun x : M => (f₁ + f₂).toFun x * h.toFun x) =
      (fun x : M => f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x) from
      funext hpt]
  exact integral_add (f₁.integrable_mul h) (f₂.integrable_mul h)

lemma fullSmoothScalar_integral_inner_grad_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : FullSmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I_half n) g (f₁ + f₂).toFun x)
          (gradFun (I := I_half n) g h.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I_half n) g f₁.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x (gradFun (I := I_half n) g f₂.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, g.inner x
      (gradFun (I := I_half n) g (f₁ + f₂).toFun x)
      (gradFun (I := I_half n) g h.toFun x) =
      g.inner x (gradFun (I := I_half n) g f₁.toFun x)
        (gradFun (I := I_half n) g h.toFun x) +
      g.inner x (gradFun (I := I_half n) g f₂.toFun x)
        (gradFun (I := I_half n) g h.toFun x) := by
    intro x
    rw [FullSmoothScalar.gradFun_add_apply f₁ f₂ x]
    rw [map_add, ContinuousLinearMap.add_apply]
  rw [show (fun x : M => g.inner x
      (gradFun (I := I_half n) g (f₁ + f₂).toFun x)
      (gradFun (I := I_half n) g h.toFun x)) =
      (fun x : M => g.inner x (gradFun (I := I_half n) g f₁.toFun x)
          (gradFun (I := I_half n) g h.toFun x) +
        g.inner x (gradFun (I := I_half n) g f₂.toFun x)
          (gradFun (I := I_half n) g h.toFun x)) from funext hpt]
  exact integral_add (f₁.integrable_inner_grad h) (f₂.integrable_inner_grad h)

lemma fullSmoothScalarH1Inner_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : FullSmoothScalar g) :
    fullSmoothScalarH1Inner (f₁ + f₂) h =
      fullSmoothScalarH1Inner f₁ h + fullSmoothScalarH1Inner f₂ h := by
  unfold fullSmoothScalarH1Inner
  rw [fullSmoothScalar_integral_mul_add_left,
    fullSmoothScalar_integral_inner_grad_add_left]
  ring

omit [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
lemma FullSmoothScalar.gradFun_smul_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f : FullSmoothScalar g) (x : M) :
    gradFun (I := I_half n) g (c • f).toFun x =
      c • gradFun (I := I_half n) g f.toFun x := by
  apply metricFlatLinear_injective (I := I_half n) g x
  ext v
  change g.inner x (gradFun (I := I_half n) g (c • f.toFun) x) v =
    g.inner x (c • gradFun (I := I_half n) g f.toFun x) v
  rw [inner_gradFun (I := I_half n) g (c • f.toFun) x v]
  rw [show g.inner x (c • gradFun (I := I_half n) g f.toFun x) v =
      c * g.inner x (gradFun (I := I_half n) g f.toFun x) v from ?_]
  swap
  · rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [inner_gradFun (I := I_half n) g f.toFun x v]
  set d_f : TangentSpace (I_half n) x →L[ℝ] ℝ :=
    mfderiv (I_half n) 𝓘(ℝ, ℝ) f.toFun x with hd_f_def
  have hHaf : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) f.toFun x d_f := by
    rw [hd_f_def]
    exact (f.smooth.mdifferentiable (by simp) x).hasMFDerivAt
  have hHa_smul : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x (c • d_f) :=
    hHaf.const_smul c
  have hd_smul : mfderiv (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x = c • d_f :=
    hHa_smul.mfderiv
  rw [hd_smul]
  change (c • d_f) v = c * d_f v
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

omit [CompactSpace M] in
lemma fullSmoothScalar_integral_mul_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : FullSmoothScalar g) :
    (∫ x, (c • f).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => (c • f).toFun x * h.toFun x) =
      (fun x : M => c * (f.toFun x * h.toFun x)) := by
    funext x; rw [FullSmoothScalar.toFun_smul_apply]; ring
  rw [hpt]
  rw [integral_const_mul]

omit [CompactSpace M] in
lemma fullSmoothScalar_integral_inner_grad_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : FullSmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I_half n) g (c • f).toFun x)
          (gradFun (I := I_half n) g h.toFun x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
            (gradFun (I := I_half n) g h.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => g.inner x
      (gradFun (I := I_half n) g (c • f).toFun x)
      (gradFun (I := I_half n) g h.toFun x)) =
      (fun x : M => c * g.inner x (gradFun (I := I_half n) g f.toFun x)
        (gradFun (I := I_half n) g h.toFun x)) := by
    funext x
    rw [FullSmoothScalar.gradFun_smul_apply c f x]
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hpt, integral_const_mul]

omit [CompactSpace M] in
lemma fullSmoothScalarH1Inner_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : FullSmoothScalar g) :
    fullSmoothScalarH1Inner (c • f) h =
      c * fullSmoothScalarH1Inner f h := by
  unfold fullSmoothScalarH1Inner
  rw [fullSmoothScalar_integral_mul_smul_left,
    fullSmoothScalar_integral_inner_grad_smul_left]
  ring

noncomputable instance instPreInnerProductSpaceCoreFullSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    PreInnerProductSpace.Core ℝ (FullSmoothScalar g) where
  inner f h := fullSmoothScalarH1Inner f h
  conj_inner_symm f h := by
    change (fullSmoothScalarH1Inner h f : ℝ) =
      fullSmoothScalarH1Inner f h
    exact fullSmoothScalarH1Inner_symm h f
  re_inner_nonneg f := by
    change (0 : ℝ) ≤ fullSmoothScalarH1Inner f f
    exact fullSmoothScalarH1Inner_nonneg f
  add_left f₁ f₂ h := by
    change fullSmoothScalarH1Inner (f₁ + f₂) h =
      fullSmoothScalarH1Inner f₁ h + fullSmoothScalarH1Inner f₂ h
    exact fullSmoothScalarH1Inner_add_left f₁ f₂ h
  smul_left f h c := by
    change fullSmoothScalarH1Inner (c • f) h =
      c * fullSmoothScalarH1Inner f h
    exact fullSmoothScalarH1Inner_smul_left c f h

noncomputable instance instSeminormedAddCommGroupFullSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup (FullSmoothScalar g) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

noncomputable instance instInnerProductSpaceFullSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    InnerProductSpace ℝ (FullSmoothScalar g) :=
  InnerProductSpace.ofCore _

@[simp] lemma FullSmoothScalar.inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : FullSmoothScalar g) :
    @inner ℝ _ _ f h = fullSmoothScalarH1Inner f h := rfl

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
