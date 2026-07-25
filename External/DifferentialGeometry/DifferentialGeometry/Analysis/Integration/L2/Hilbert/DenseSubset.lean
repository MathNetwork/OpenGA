import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion


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

section DenseEmbedding

variable [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}


def toL2 : SmoothCcTensor g r s →L[ℝ] TensorL2 r s g :=
  UniformSpace.Completion.toComplL


@[simp] theorem toL2_apply (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s) S : TensorL2 r s g) =
      (S : UniformSpace.Completion (SmoothCcTensor g r s)) := by
  change (UniformSpace.Completion.toComplL S : TensorL2 r s g) =
    (S : UniformSpace.Completion (SmoothCcTensor g r s))
  rw [UniformSpace.Completion.coe_toComplL]


theorem denseRange_toL2 :
    DenseRange (toL2 (g := g) (r := r) (s := s)) := by
  have hcoe : (toL2 (g := g) (r := r) (s := s) :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) := by
    funext S
    exact toL2_apply (g := g) (r := r) (s := s) S
  rw [hcoe]
  exact UniformSpace.Completion.denseRange_coe


@[simp] theorem norm_toL2 (S : SmoothCcTensor g r s) :
    ‖toL2 (g := g) (r := r) (s := s) S‖ = ‖S‖ := by
  have h := toL2_apply (g := g) (r := r) (s := s) S
  rw [show ‖toL2 (g := g) (r := r) (s := s) S‖ =
        ‖(S : UniformSpace.Completion (SmoothCcTensor g r s))‖ from
      congrArg norm h]
  exact UniformSpace.Completion.norm_coe S


@[simp] theorem inner_toL2 (S T : SmoothCcTensor g r s) :
    ⟪toL2 (g := g) (r := r) (s := s) S,
        toL2 (g := g) (r := r) (s := s) T⟫_ℝ = ⟪S, T⟫_ℝ := by
  have hS := toL2_apply (g := g) (r := r) (s := s) S
  have hT := toL2_apply (g := g) (r := r) (s := s) T
  rw [show (⟪toL2 (g := g) (r := r) (s := s) S,
            toL2 (g := g) (r := r) (s := s) T⟫_ℝ : ℝ) =
        ⟪(S : UniformSpace.Completion (SmoothCcTensor g r s)),
          (T : UniformSpace.Completion (SmoothCcTensor g r s))⟫_ℝ from by
      rw [hS, hT]]
  exact UniformSpace.Completion.inner_coe S T


theorem smoothCcTensor_eq_of_toL2_eq (S T : SmoothCcTensor g r s)
    (h : toL2 (g := g) (r := r) (s := s) S =
      toL2 (g := g) (r := r) (s := s) T) : S = T := by
  have hsub : S - T = 0 := by
    have hnorm0 : ‖S - T‖ = 0 := by
      have hmap : toL2 (g := g) (r := r) (s := s) (S - T) = 0 := by
        rw [map_sub, h, sub_self]
      have := congrArg norm hmap
      rwa [norm_toL2 (g := g) (r := r) (s := s) (S - T), norm_zero] at this
    have hinner0 :
        tensorL2Inner (I := I) (M := M) g r s (S - T).toFun (S - T).toFun = 0 := by
      have hsqrt : tensorL2Norm (I := I) (M := M) g r s (S - T).toFun = 0 := by
        rw [← SmoothCcTensor.norm_def (I := I) (M := M) (S - T)]
        exact hnorm0
      rw [tensorL2Norm_def] at hsqrt
      exact (Real.sqrt_eq_zero
        (tensorL2Inner_nonneg (I := I) (M := M) g r s (S - T).toFun)).mp hsqrt
    have hae :
        (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
            ((S - T).toFun x) ((S - T).toFun x))
          =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg
        (fun x : M => tensorInnerPointwise_nonneg (I := I) (M := M) g r s x
          ((S - T).toFun x))
        (SmoothCcTensor.memL2_toFun (I := I) (M := M) (S - T))).mp hinner0
    haveI : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    have heq :
        (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
            ((S - T).toFun x) ((S - T).toFun x)) = 0 :=
      (Continuous.ae_eq_iff_eq (riemannianVolumeMeasure (I := I) (M := M) g)
        (SmoothCcTensor.continuous_inner_self (I := I) (M := M) (S - T))
        continuous_const).mp hae
    have hsection : (S - T).toSection = 0 := by
      refine ContMDiffSection.ext (fun x => ?_)
      have hx : tensorInnerPointwise (I := I) (M := M) g r s x
          ((S - T).toFun x) ((S - T).toFun x) = 0 := congrFun heq x
      have hfun : (S - T).toFun x = 0 :=
        (tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g r s x
          ((S - T).toFun x)).mp hx
      have hmodel : TensorRSSpace.toModel ((S - T).toSection x) = 0 := hfun
      have hzero : TensorRSSpace.toModel
          ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
            (fun x : M => TensorRSSpace r s I x)⟯) x) = 0 := by
        rw [ContMDiffSection.coe_zero, Pi.zero_apply, TensorRSSpace.toModel_zero]
      exact TensorRSSpace.toModel_injective (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (hmodel.trans hzero.symm)
    refine SmoothCcTensor.ext ?_
    rw [SmoothCcTensor.toSection_zero]
    exact hsection
  exact sub_eq_zero.mp hsub

end DenseEmbedding

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
