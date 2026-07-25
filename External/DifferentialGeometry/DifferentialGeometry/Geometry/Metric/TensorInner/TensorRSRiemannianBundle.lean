import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannianBundle
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SInnerSectionContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace TensorRSRiemannianBundle

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def innerModelBilinRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => tensorInnerPointwise (I := I) (M := M) g r s b T S)
    (fun T₁ T₂ S =>
      tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S)
    (fun c T S =>
      tensorInnerPointwise_smul_left (I := I) (M := M) g r s b c T S)
    (fun T S₁ S₂ =>
      tensorInnerPointwise_add_right (I := I) (M := M) g r s b T S₁ S₂)
    (fun c T S =>
      tensorInnerPointwise_smul_right (I := I) (M := M) g r s b c T S)

@[simp] private lemma innerModelBilinRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelBilinRS (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b T S := rfl

private def innerModelLinearOuterRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →ₗ[ℝ] (TensorRSModel r s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (innerModelBilinRS (I := I) (M := M) g r s b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise (I := I) (M := M) g r s b (T₁ + T₂) S =
      tensorInnerPointwise (I := I) (M := M) g r s b T₁ S +
        tensorInnerPointwise (I := I) (M := M) g r s b T₂ S
    exact tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change tensorInnerPointwise (I := I) (M := M) g r s b (c • T) S =
      c • tensorInnerPointwise (I := I) (M := M) g r s b T S
    rw [tensorInnerPointwise_smul_left]
    rfl

def innerModelCLMRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (innerModelLinearOuterRS (I := I) (M := M) g r s b)

@[simp] lemma innerModelCLMRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b T S := rfl

lemma innerModelCLMRS_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T S =
      innerModelCLMRS (I := I) (M := M) g r s b S T := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b _ _

lemma innerModelCLMRS_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) (hT : T ≠ 0) :
    0 < innerModelCLMRS (I := I) (M := M) g r s b T T := by
  rw [innerModelCLMRS_apply]
  have hnn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b T T :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b T
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hT
    exact (tensorInnerPointwise_eq_zero_iff
      (I := I) (M := M) g r s b T).mp heq.symm

lemma innerModelCLMRS_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) :
    0 ≤ innerModelCLMRS (I := I) (M := M) g r s b T T := by
  rw [innerModelCLMRS_apply]
  exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b T

lemma innerModelCLMRS_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T₁ T₂ S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b (T₁ + T₂) S =
      innerModelCLMRS (I := I) (M := M) g r s b T₁ S +
        innerModelCLMRS (I := I) (M := M) g r s b T₂ S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_add_left (I := I) (M := M) g r s b _ _ _

lemma innerModelCLMRS_add_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S₁ S₂ : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T (S₁ + S₂) =
      innerModelCLMRS (I := I) (M := M) g r s b T S₁ +
        innerModelCLMRS (I := I) (M := M) g r s b T S₂ := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_add_right (I := I) (M := M) g r s b _ _ _

lemma innerModelCLMRS_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b (c • T) S =
      c * innerModelCLMRS (I := I) (M := M) g r s b T S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_smul_left (I := I) (M := M) g r s b c _ _

lemma innerModelCLMRS_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    innerModelCLMRS (I := I) (M := M) g r s b T (c • S) =
      c * innerModelCLMRS (I := I) (M := M) g r s b T S := by
  rw [innerModelCLMRS_apply, innerModelCLMRS_apply]
  exact tensorInnerPointwise_smul_right (I := I) (M := M) g r s b c _ _

private def bundleCLERS (r s : ℕ) (b : M) :
    TensorRSSpace r s I b ≃L[ℝ] TensorRSModel r s ℝ E :=
  Tensor0SBundle.tensorRSSpace_continuousLinearEquiv
    (𝕜 := ℝ) (E := E) (I := I) (M := M) r s b

private def bundleToModelCLMRS (r s : ℕ) (b : M) :
    TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E :=
  (bundleCLERS (I := I) (M := M) (E := E) r s b).toContinuousLinearMap

private def precompBundleCLMRS (r s : ℕ) (b : M) :
    (TensorRSModel r s ℝ E →L[ℝ] ℝ) →L[ℝ]
      (TensorRSSpace r s I b →L[ℝ] ℝ) :=
  ((bundleCLERS (I := I) (M := M) (E := E) r s b).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousLinearMap

@[simp] private lemma precompBundleCLMRS_apply (r s : ℕ) (b : M)
    (f : TensorRSModel r s ℝ E →L[ℝ] ℝ) (T : TensorRSSpace r s I b) :
    precompBundleCLMRS (I := I) (M := M) (E := E) r s b f T =
      f (Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) :=
  rfl

def tensorRSRiemannianInnerCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    TensorRSSpace r s I b →L[ℝ] TensorRSSpace r s I b →L[ℝ] ℝ :=
  let stepA : TensorRSModel r s ℝ E →L[ℝ] (TensorRSSpace r s I b →L[ℝ] ℝ) :=
    (precompBundleCLMRS (I := I) (M := M) (E := E) r s b).comp
      (innerModelCLMRS (I := I) (M := M) g r s b)
  stepA.comp (bundleToModelCLMRS (I := I) (M := M) (E := E) r s b)

@[simp] lemma tensorRSRiemannianInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) S) := by
  rfl

theorem tensorRSRiemannianInnerCLM_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S =
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b S T := by
  rw [tensorRSRiemannianInnerCLM_apply, tensorRSRiemannianInnerCLM_apply]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b _ _

theorem tensorRSRiemannianInnerCLM_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) (hT : T ≠ 0) :
    0 < tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T T := by
  rw [tensorRSRiemannianInnerCLM_apply]
  have hTm :
      Tensor0SBundle.TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T ≠ 0 := by
    intro h
    apply hT
    have hinj :=
      Tensor0SBundle.TensorRSSpace.toModel_injective
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
    have hzero :
        Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (0 : TensorRSSpace r s I b) = 0 :=
      Tensor0SBundle.TensorRSSpace.toModel_zero
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
    exact hinj (h.trans hzero.symm)
  have hnn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hTm
    exact (tensorInnerPointwise_eq_zero_iff
      (I := I) (M := M) g r s b _).mp heq.symm

theorem tensorRSRiemannianInnerCLM_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b (c • T) S =
      c * tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S := by
  have h := ContinuousLinearMap.map_smul
    (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b) c T
  change tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b (c • T) S = _
  rw [h]
  rfl

theorem tensorRSRiemannianInnerCLM_smul_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T (c • S) =
      c * tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T S := by
  have h := ContinuousLinearMap.map_smul
    ((tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b) T) c S
  change (tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T) (c • S) = _
  rw [h]
  rfl

private lemma innerModelRS_quadratic_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Continuous (fun T : TensorRSModel r s ℝ E =>
      tensorInnerPointwise (I := I) (M := M) g r s b T T) := by
  classical

  let ι := Fin (Module.finrank ℝ (TensorRSModel r s ℝ E))
  let basis : Module.Basis ι ℝ (TensorRSModel r s ℝ E) :=
    Module.finBasis ℝ (TensorRSModel r s ℝ E)

  let φ : ι → (TensorRSModel r s ℝ E →ₗ[ℝ] ℝ) := fun i => basis.coord i
  have hφ_cont : ∀ i, Continuous (φ i) := fun i =>
    LinearMap.continuous_of_finiteDimensional (φ i)

  have hexpand : ∀ T : TensorRSModel r s ℝ E,
      T = ∑ i : ι, (φ i T) • basis i := by
    intro T
    have := basis.linearCombination_repr T

    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at this
    · exact this.symm
    · intros; rw [zero_smul]

  have hgen_left : ∀ (a : ι → ℝ) (S : TensorRSModel r s ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b
        (∑ i : ι, a i • basis i) S =
        ∑ i : ι, (a i) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) S := by
    intro a S
    let LL : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun T' => tensorInnerPointwise (I := I) (M := M) g r s b T' S
        map_add' := fun T₁ T₂ =>
          tensorInnerPointwise_add_left (I := I) (M := M) g r s b T₁ T₂ S
        map_smul' := fun c T' => by
          change tensorInnerPointwise (I := I) (M := M) g r s b (c • T') S = c • _
          rw [tensorInnerPointwise_smul_left]
          rfl }
    have hLL_sum : LL (∑ i : ι, a i • basis i) =
        ∑ i : ι, LL (a i • basis i) :=
      map_sum LL _ _
    change LL _ = _
    rw [hLL_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [LL.map_smul]
    rfl
  have hgen_right : ∀ (a : ι → ℝ) (i : ι),
      tensorInnerPointwise (I := I) (M := M) g r s b (basis i)
        (∑ j : ι, a j • basis j) =
        ∑ j : ι, (a j) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro a i
    let RR : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun S' => tensorInnerPointwise (I := I) (M := M) g r s b (basis i) S'
        map_add' := fun S₁ S₂ =>
          tensorInnerPointwise_add_right (I := I) (M := M) g r s b (basis i) S₁ S₂
        map_smul' := fun c S' => by
          change tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (c • S') = c • _
          rw [tensorInnerPointwise_smul_right]
          rfl }
    have hRR_sum : RR (∑ j : ι, a j • basis j) =
        ∑ j : ι, RR (a j • basis j) :=
      map_sum RR _ _
    change RR _ = _
    rw [hRR_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [RR.map_smul]
    rfl

  have hbilin_aux : ∀ (T : TensorRSModel r s ℝ E) (a : ι → ℝ),
      T = ∑ i : ι, a i • basis i →
      tensorInnerPointwise (I := I) (M := M) g r s b T T =
        ∑ i : ι, ∑ j : ι, (a i) * (a j) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro T a hT
    calc tensorInnerPointwise (I := I) (M := M) g r s b T T
        = tensorInnerPointwise (I := I) (M := M) g r s b
            (∑ i : ι, a i • basis i) (∑ j : ι, a j • basis j) := by rw [← hT]
      _ = ∑ i : ι, (a i) *
            tensorInnerPointwise (I := I) (M := M) g r s b (basis i)
              (∑ j : ι, a j • basis j) :=
            hgen_left a (∑ j : ι, a j • basis j)
      _ = ∑ i : ι, (a i) *
            ∑ j : ι, (a j) *
              tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hgen_right a i]
      _ = ∑ i : ι, ∑ j : ι, (a i) * (a j) *
            tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
  have hbilin_expand : ∀ T : TensorRSModel r s ℝ E,
      tensorInnerPointwise (I := I) (M := M) g r s b T T =
        ∑ i : ι, ∑ j : ι, (φ i T) * (φ j T) *
          tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j) := by
    intro T
    exact hbilin_aux T (fun i => φ i T) (hexpand T)

  have hcont : Continuous (fun T : TensorRSModel r s ℝ E =>
      ∑ i : ι, ∑ j : ι, (φ i T) * (φ j T) *
        tensorInnerPointwise (I := I) (M := M) g r s b (basis i) (basis j)) := by
    refine continuous_finset_sum _ (fun i _ => ?_)
    refine continuous_finset_sum _ (fun j _ => ?_)
    refine ((hφ_cont i).mul (hφ_cont j)).mul continuous_const

  refine hcont.congr ?_
  intro T
  exact (hbilin_expand T).symm

lemma tensorRSRiemannianInnerCLM_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Continuous (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) := by
  have heq : (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) =
      (fun v : TensorRSSpace r s I b =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) v)
          (Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) v)) := by
    funext v; rw [tensorRSRiemannianInnerCLM_apply]
  rw [heq]
  exact (innerModelRS_quadratic_continuous (I := I) (M := M) g r s b).comp
    (Tensor0SBundle.TensorRSSpace.toModel_continuous
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b))

theorem tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    ContinuousAt (fun v : TensorRSSpace r s I b =>
      tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v) 0 :=
  (tensorRSRiemannianInnerCLM_diagonal_continuous (I := I) (M := M) g r s b).continuousAt

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private lemma innerModelRS_diagonal_sublevel_isBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    Bornology.IsBounded
      {T : TensorRSModel r s ℝ E |
        innerModelCLMRS (I := I) (M := M) g r s b T T < 1} := by
  by_cases hNT : Nontrivial (TensorRSModel r s ℝ E)
  · haveI := hNT
    have hPD : ∀ v : TensorRSModel r s ℝ E,
        v ≠ 0 → 0 < innerModelCLMRS (I := I) (M := M) g r s b v v := by
      intro v hv
      change 0 < tensorInnerPointwise (I := I) (M := M) g r s b v v
      have hQpos := (tensorInnerPointwise_eq_zero_iff
        (I := I) (M := M) g r s b v).not.mpr hv
      have hnn := tensorInnerPointwise_nonneg (I := I) (M := M) g r s b v
      exact lt_of_le_of_ne hnn (Ne.symm hQpos)
    have hNN : ∀ v : TensorRSModel r s ℝ E,
        0 ≤ innerModelCLMRS (I := I) (M := M) g r s b v v := fun v =>
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b v
    have hSmulL : ∀ (c : ℝ) (v w : TensorRSModel r s ℝ E),
        innerModelCLMRS (I := I) (M := M) g r s b (c • v) w =
          c * innerModelCLMRS (I := I) (M := M) g r s b v w := by
      intro c v w
      exact innerModelCLMRS_smul_left (I := I) (M := M) g r s b c v w
    have hSmulR : ∀ (c : ℝ) (v w : TensorRSModel r s ℝ E),
        innerModelCLMRS (I := I) (M := M) g r s b v (c • w) =
          c * innerModelCLMRS (I := I) (M := M) g r s b v w := by
      intro c v w
      exact innerModelCLMRS_smul_right (I := I) (M := M) g r s b c v w
    exact Tensor0SRiemannian.posDef_bilin_unit_ball_isBounded
      (innerModelCLMRS (I := I) (M := M) g r s b) hPD hNN hSmulL hSmulR
  · have hSubsingleton : Subsingleton (TensorRSModel r s ℝ E) :=
      not_nontrivial_iff_subsingleton.mp hNT
    haveI := hSubsingleton
    refine (Metric.isBounded_iff_subset_ball 0).mpr ⟨1, ?_⟩
    intro v _
    rw [Metric.mem_ball, dist_zero_right]
    have hv0 : v = 0 := Subsingleton.elim v 0
    rw [hv0, norm_zero]; exact one_pos

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private lemma innerModelRS_diagonal_sublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {T : TensorRSModel r s ℝ E |
        innerModelCLMRS (I := I) (M := M) g r s b T T < 1} :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    (innerModelRS_diagonal_sublevel_isBounded (I := I) (M := M) g r s b)

private lemma tensorRSRiemannianInner_diagonal_clm_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b T T =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T)
        (Tensor0SBundle.TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b) T) := by
  rw [tensorRSRiemannianInnerCLM_apply]

set_option maxHeartbeats 800000 in
theorem tensorRSRiemannianInnerCLM_isVonNBounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {v : TensorRSSpace r s I b |
        tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v < 1} := by
  set e : TensorRSSpace r s I b ≃L[ℝ] TensorRSModel r s ℝ E :=
    Tensor0SBundle.tensorRSSpace_continuousLinearEquiv
      (𝕜 := ℝ) (E := E) (I := I) (M := M) r s b with he_def
  have hModel := innerModelRS_diagonal_sublevel_isVonNBounded
    (I := I) (M := M) g r s b
  have hImg :=
    hModel.image (e.symm.toContinuousLinearMap)
  have hSetEq :
      e.symm.toContinuousLinearMap ''
        {T : TensorRSModel r s ℝ E |
          innerModelCLMRS (I := I) (M := M) g r s b T T < 1} =
      {v : TensorRSSpace r s I b |
          tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b v v < 1} := by
    ext v
    refine ⟨?_, ?_⟩
    · rintro ⟨T, hT, rfl⟩
      rw [Set.mem_setOf_eq] at hT
      rw [Set.mem_setOf_eq, tensorRSRiemannianInner_diagonal_clm_apply]
      have hRound : (e (e.symm T) : _) = T := e.apply_symm_apply T
      have hToModel :
          Tensor0SBundle.TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            ((e.symm.toContinuousLinearMap :
              TensorRSModel r s ℝ E →L[ℝ] TensorRSSpace r s I b) T) = T := hRound
      rw [hToModel]
      change tensorInnerPointwise (I := I) (M := M) g r s b T T < 1
      rw [innerModelCLMRS_apply] at hT
      exact hT
    · intro hv
      refine ⟨e v, ?_, ?_⟩
      · rw [Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq, tensorRSRiemannianInner_diagonal_clm_apply] at hv
        rw [innerModelCLMRS_apply]
        exact hv
      · exact e.symm_apply_apply v
  rw [← hSetEq]
  exact hImg

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

noncomputable def tensorRSRiemannianMetric
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Bundle.RiemannianMetric (E := fun b : M => TensorRSSpace r s I b) where
  inner := fun b => tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b
  symm := fun b T S =>
    tensorRSRiemannianInnerCLM_symm (I := I) (M := M) g r s b T S
  pos := fun b T hT =>
    tensorRSRiemannianInnerCLM_pos (I := I) (M := M) g r s b T hT
  continuousAt := fun b =>
    tensorRSRiemannianInnerCLM_diagonal_continuousAt_zero
      (I := I) (M := M) g r s b
  isVonNBounded := fun b =>
    tensorRSRiemannianInnerCLM_isVonNBounded (I := I) (M := M) g r s b

end TensorRSRiemannianBundle
end Tensor
end DifferentialGeometry

namespace Tensor0SBundle

open DifferentialGeometry.Tensor.TensorRSRiemannianBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[reducible]
noncomputable def tensorRS_riemannianBundle
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
  ⟨tensorRSRiemannianMetric (I := I) (M := M) g r s⟩

end Tensor0SBundle
