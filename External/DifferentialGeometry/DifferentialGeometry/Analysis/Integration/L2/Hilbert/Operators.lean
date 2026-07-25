import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.DenseSubset
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.SimpLemmas
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace SmoothCcTensor

section UniformInducing

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


omit [InnerProductSpace ℝ E] in
theorem isUniformInducing_toL2 :
    IsUniformInducing (toL2 (g := g) (r := r) (s := s)) := by
  have hcoe : (toL2 (g := g) (r := r) (s := s) :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) := by
    funext S
    exact toL2_apply (g := g) (r := r) (s := s) S
  rw [show (toL2 (g := g) (r := r) (s := s) :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from hcoe]
  exact UniformSpace.Completion.isUniformInducing_coe _

end UniformInducing

section ExtendL2

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


def extendL2 (T : SmoothCcTensor g r s →L[ℝ] F) :
    TensorL2 r s g →L[ℝ] F :=
  T.extend (toL2 (g := g) (r := r) (s := s))


omit [InnerProductSpace ℝ E] in
@[simp] theorem extendL2_apply_toL2 (T : SmoothCcTensor g r s →L[ℝ] F)
    (S : SmoothCcTensor g r s) :
    extendL2 T ((toL2 (g := g) (r := r) (s := s)) S) = T S :=
  ContinuousLinearMap.extend_eq T denseRange_toL2 isUniformInducing_toL2 S


omit [InnerProductSpace ℝ E] in
theorem extendL2_unique (T : SmoothCcTensor g r s →L[ℝ] F)
    (U : TensorL2 r s g →L[ℝ] F)
    (h : U.comp (toL2 (g := g) (r := r) (s := s)) = T) :
    extendL2 T = U :=
  ContinuousLinearMap.extend_unique T denseRange_toL2 isUniformInducing_toL2 U h

end ExtendL2

section MapL2

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r₁ s₁ r₂ s₂ : ℕ}


def mapL2
    (T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂) :
    TensorL2 r₁ s₁ g →L[ℝ] TensorL2 r₂ s₂ g :=
  T.completion


omit [InnerProductSpace ℝ E] in
@[simp] theorem mapL2_apply_toL2
    (T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂)
    (S : SmoothCcTensor g r₁ s₁) :
    mapL2 T ((toL2 (g := g) (r := r₁) (s := s₁)) S) =
      (toL2 (g := g) (r := r₂) (s := s₂)) (T S) := by
  have hS := toL2_apply (g := g) (r := r₁) (s := s₁) S
  have hTS := toL2_apply (g := g) (r := r₂) (s := s₂) (T S)
  rw [hS, hTS]
  change T.completion (S : UniformSpace.Completion (SmoothCcTensor g r₁ s₁)) =
    (T S : UniformSpace.Completion (SmoothCcTensor g r₂ s₂))
  exact T.completion_apply_coe S


omit [InnerProductSpace ℝ E] in
theorem mapL2_unique
    (T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂)
    (U : TensorL2 r₁ s₁ g →L[ℝ] TensorL2 r₂ s₂ g)
    (h : U.comp (toL2 (g := g) (r := r₁) (s := s₁)) =
      (toL2 (g := g) (r := r₂) (s := s₂)).comp T) :
    mapL2 T = U := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine UniformSpace.Completion.induction_on (α := SmoothCcTensor g r₁ s₁)
      (p := fun y => (mapL2 T) y = U y) x ?_ ?_
  · exact isClosed_eq (mapL2 T).continuous U.continuous
  · intro a
    have hcoe :
        (a : UniformSpace.Completion (SmoothCcTensor g r₁ s₁)) =
          (toL2 (g := g) (r := r₁) (s := s₁)) a :=
      (toL2_apply (g := g) (r := r₁) (s := s₁) a).symm
    have hU : U ((toL2 (g := g) (r := r₁) (s := s₁)) a) =
        (toL2 (g := g) (r := r₂) (s := s₂)) (T a) := by
      have := congrArg (fun (φ : _ →L[ℝ] _) => φ a) h
      simpa using this
    have hM : (mapL2 T) ((toL2 (g := g) (r := r₁) (s := s₁)) a) =
        (toL2 (g := g) (r := r₂) (s := s₂)) (T a) :=
      mapL2_apply_toL2 (g := g) (r₁ := r₁) (s₁ := s₁)
        (r₂ := r₂) (s₂ := s₂) T a
    rw [hcoe, hM, ← hU]

end MapL2

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
