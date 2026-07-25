import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance bundleDualTopologicalSpace (s : ℕ) (b : M) :
    TopologicalSpace (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace
    (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := Tensor0SSpace s I b) (F := ℝ)

private def innerModelBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun T S => covariantTensorInnerPointwise (I := I) (M := M) s g b T S)
    (fun T₁ T₂ S =>
      tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_left (I := I) (M := M) g b s c T S)
    (fun T S₁ S₂ =>
      tensorInnerPointwise_0s_add_right (I := I) (M := M) g b s T S₁ S₂)
    (fun c T S =>
      tensorInnerPointwise_0s_smul_right (I := I) (M := M) g b s c T S)

@[simp] private lemma innerModelBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelBilin (I := I) (M := M) g s b T S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b T S := rfl

private def innerModelLinearOuter
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ] (Tensor0SModel s ℝ E →L[ℝ] ℝ) where
  toFun := fun T =>
    LinearMap.toContinuousLinearMap
      (innerModelBilin (I := I) (M := M) g s b T)
  map_add' := fun T₁ T₂ => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change covariantTensorInnerPointwise (I := I) (M := M) s g b (T₁ + T₂) S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b T₁ S +
        covariantTensorInnerPointwise (I := I) (M := M) s g b T₂ S
    exact tensorInnerPointwise_0s_add_left (I := I) (M := M) g b s T₁ T₂ S
  map_smul' := fun c T => by
    refine ContinuousLinearMap.ext ?_
    intro S
    change covariantTensorInnerPointwise (I := I) (M := M) s g b (c • T) S =
      c • covariantTensorInnerPointwise (I := I) (M := M) s g b T S
    rw [tensorInnerPointwise_0s_smul_left]
    rfl

def innerModelCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (innerModelLinearOuter (I := I) (M := M) g s b)

@[simp] lemma innerModelCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SModel s ℝ E) :
    innerModelCLM (I := I) (M := M) g s b T S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b T S := rfl

private def bundleCLE (s : ℕ) (b : M) :
    Tensor0SSpace s I b ≃L[ℝ]
      Tensor0SModel s ℝ E :=
  Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (E := E) (I := I) (M := M) s b

private def bundleToModelCLM (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SModel s ℝ E :=
  (bundleCLE (I := I) (M := M) (E := E) s b).toContinuousLinearMap

@[simp] private lemma bundleToModelCLM_apply (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    bundleToModelCLM (I := I) (M := M) (E := E) s b T =
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T := rfl

private def modelToBundleCLM (s : ℕ) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SSpace s I b :=
  (bundleCLE (I := I) (M := M) (E := E) s b).symm.toContinuousLinearMap

private def precompBundleCLM (s : ℕ) (b : M) :
    (Tensor0SModel s ℝ E →L[ℝ] ℝ) →L[ℝ]
      (Tensor0SSpace s I b →L[ℝ] ℝ) :=

  ((bundleCLE (I := I) (M := M) (E := E) s b).symm.arrowCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousLinearMap

@[simp] private lemma precompBundleCLM_apply (s : ℕ) (b : M)
    (f : Tensor0SModel s ℝ E →L[ℝ] ℝ) (T : Tensor0SSpace s I b) :
    precompBundleCLM (I := I) (M := M) (E := E) s b f T =
      f (Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
  rfl

def innerBundleCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ]
      Tensor0SSpace s I b →L[ℝ] ℝ :=

  let stepA : Tensor0SModel s ℝ E →L[ℝ] (Tensor0SSpace s I b →L[ℝ] ℝ) :=
    (precompBundleCLM (I := I) (M := M) (E := E) s b).comp
      (innerModelCLM (I := I) (M := M) g s b)

  stepA.comp (bundleToModelCLM (I := I) (M := M) (E := E) s b)

@[simp] lemma innerBundleCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) T)
        (Tensor0SBundle.Tensor0SSpace.toModel (I := I) (M := M)
          (𝕜 := ℝ) (E := E) (s := s) (x := b) S) := by
  rfl

lemma innerBundleCLM_symm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    innerBundleCLM (I := I) (M := M) g s b T S =
      innerBundleCLM (I := I) (M := M) g s b S T := by
  rw [innerBundleCLM_apply, innerBundleCLM_apply]
  exact tensorInnerPointwise_0s_symm (I := I) (M := M) g b s _ _

lemma innerBundleCLM_pos
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) (hT : T ≠ 0) :
    0 < innerBundleCLM (I := I) (M := M) g s b T T := by
  rw [innerBundleCLM_apply]

  have hTm :
      Tensor0SBundle.Tensor0SSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T ≠ 0 := by
    intro h
    apply hT
    have hinj :=
      Tensor0SBundle.Tensor0SSpace.toModel_injective
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    have hzero :
        Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (0 : Tensor0SSpace s I b) = 0 :=
      Tensor0SBundle.Tensor0SSpace.toModel_zero
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
    exact hinj (h.trans hzero.symm)
  have hnn :
      0 ≤ covariantTensorInnerPointwise (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) :=
    tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s _
  rcases lt_or_eq_of_le hnn with hlt | heq
  · exact hlt
  · exfalso
    apply hTm
    exact (tensorInnerPointwise_0s_eq_zero_iff
      (I := I) (M := M) g b s _).mp heq.symm

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
