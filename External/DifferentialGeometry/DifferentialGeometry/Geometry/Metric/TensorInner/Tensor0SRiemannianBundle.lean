import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannianBundle

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Tensor0SRiemannian
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

noncomputable def tensor0SRiemannianInnerCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b →L[ℝ] ℝ :=
  innerBundleCLM (I := I) (M := M) g s b

@[simp] lemma tensor0SRiemannianInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S =
      innerBundleCLM (I := I) (M := M) g s b T S := rfl

theorem tensor0SRiemannianInner_symm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S =
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b S T :=
  innerBundleCLM_symm (I := I) (M := M) g s b T S

theorem tensor0SRiemannianInner_pos
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) (hT : T ≠ 0) :
    0 < tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T T :=
  innerBundleCLM_pos (I := I) (M := M) g s b T hT

theorem tensor0SRiemannianInner_smul_left
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (c : ℝ) (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b (c • T) S =
      c * tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S := by
  have h := ContinuousLinearMap.map_smul
    (innerBundleCLM (I := I) (M := M) g s b) c T

  change innerBundleCLM (I := I) (M := M) g s b (c • T) S = _
  rw [h]
  rfl

theorem tensor0SRiemannianInner_smul_right
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (c : ℝ) (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T (c • S) =
      c * tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S := by
  have h := ContinuousLinearMap.map_smul
    ((innerBundleCLM (I := I) (M := M) g s b) T) c S
  change (innerBundleCLM (I := I) (M := M) g s b T) (c • S) = _
  rw [h]
  rfl

private lemma innerModel_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Continuous (fun T : Tensor0SModel s ℝ E =>
      covariantTensorInnerPointwise (I := I) (M := M) s g b T T) := by
  have hModelCLM := (innerModelCLM (I := I) (M := M) g s b).continuous
  have : Continuous (fun T : Tensor0SModel s ℝ E =>
      innerModelCLM (I := I) (M := M) g s b T T) :=
    hModelCLM.clm_apply continuous_id
  simpa [innerModelCLM_apply] using this

theorem tensor0SRiemannianInner_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Continuous (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) := by

  have heq : (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) =
      (fun v : Tensor0SSpace s I b =>
        covariantTensorInnerPointwise (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v)) := by
    funext v
    rw [tensor0SRiemannianInnerCLM_apply, innerBundleCLM_apply]
  rw [heq]
  have htoM : Continuous
      (fun v : Tensor0SSpace s I b =>
        Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v) :=
    Tensor0SBundle.Tensor0SSpace.toModel_continuous
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
  exact (innerModel_diagonal_continuous (I := I) (M := M) g s b).comp htoM

theorem tensor0SRiemannianInner_diagonal_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    ContinuousAt (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) 0 :=
  (tensor0SRiemannianInner_diagonal_continuous (I := I) (M := M) g s b).continuousAt

private lemma tensor0SRiemannianInner_diagonal_clm_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T T =
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T)
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) := by
  rw [tensor0SRiemannianInnerCLM_apply, innerBundleCLM_apply]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private lemma innerModel_diagonal_sublevel_isBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Bornology.IsBounded
      {T : Tensor0SModel s ℝ E |
        innerModelCLM (I := I) (M := M) g s b T T < 1} := by

  by_cases hNT : Nontrivial (Tensor0SModel s ℝ E)
  · haveI := hNT
    have hPD : ∀ v : Tensor0SModel s ℝ E,
        v ≠ 0 → 0 < innerModelCLM (I := I) (M := M) g s b v v := by
      intro v hv
      change 0 < covariantTensorInnerPointwise (I := I) (M := M) s g b v v
      have hQpos := (tensorInnerPointwise_0s_eq_zero_iff
        (I := I) (M := M) g b s v).not.mpr hv
      have hnn := tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s v
      exact lt_of_le_of_ne hnn (Ne.symm hQpos)
    have hNN : ∀ v : Tensor0SModel s ℝ E,
        0 ≤ innerModelCLM (I := I) (M := M) g s b v v := fun v =>
      tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s v
    have hSmulL : ∀ (c : ℝ) (v w : Tensor0SModel s ℝ E),
        innerModelCLM (I := I) (M := M) g s b (c • v) w =
          c * innerModelCLM (I := I) (M := M) g s b v w := by
      intro c v w
      change covariantTensorInnerPointwise (I := I) (M := M) s g b (c • v) w =
        c * covariantTensorInnerPointwise (I := I) (M := M) s g b v w
      rw [tensorInnerPointwise_0s_smul_left]
    have hSmulR : ∀ (c : ℝ) (v w : Tensor0SModel s ℝ E),
        innerModelCLM (I := I) (M := M) g s b v (c • w) =
          c * innerModelCLM (I := I) (M := M) g s b v w := by
      intro c v w
      change covariantTensorInnerPointwise (I := I) (M := M) s g b v (c • w) =
        c * covariantTensorInnerPointwise (I := I) (M := M) s g b v w
      rw [tensorInnerPointwise_0s_smul_right]
    exact Tensor0SRiemannian.posDef_bilin_unit_ball_isBounded
      (innerModelCLM (I := I) (M := M) g s b) hPD hNN hSmulL hSmulR
  · have hSubsingleton : Subsingleton (Tensor0SModel s ℝ E) :=
      not_nontrivial_iff_subsingleton.mp hNT
    haveI := hSubsingleton
    refine (Metric.isBounded_iff_subset_ball 0).mpr ⟨1, ?_⟩
    intro v _
    rw [Metric.mem_ball, dist_zero_right]
    have hv0 : v = 0 := Subsingleton.elim v 0
    rw [hv0, norm_zero]; exact one_pos

private lemma innerModel_diagonal_sublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {T : Tensor0SModel s ℝ E |
        innerModelCLM (I := I) (M := M) g s b T T < 1} :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    (innerModel_diagonal_sublevel_isBounded (I := I) (M := M) g s b)

theorem tensor0SRiemannianInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {v : Tensor0SSpace s I b |
        tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v < 1} := by

  set e : Tensor0SSpace s I b ≃L[ℝ] Tensor0SModel s ℝ E :=
    Tensor0SBundle.tensor0SSpace_continuousLinearEquiv
      (𝕜 := ℝ) (E := E) (I := I) (M := M) s b with he_def
  have hModel := innerModel_diagonal_sublevel_isVonNBounded
    (I := I) (M := M) g s b

  have hImg :=
    hModel.image (e.symm.toContinuousLinearMap)

  have hSetEq :
      e.symm.toContinuousLinearMap ''
        {T : Tensor0SModel s ℝ E |
          innerModelCLM (I := I) (M := M) g s b T T < 1} =
      {v : Tensor0SSpace s I b |
          tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v < 1} := by
    ext v
    refine ⟨?_, ?_⟩
    · rintro ⟨T, hT, rfl⟩
      rw [Set.mem_setOf_eq] at hT
      rw [Set.mem_setOf_eq, tensor0SRiemannianInner_diagonal_clm_apply]
      have hRound : (e (e.symm T) : _) = T := e.apply_symm_apply T
      have hToModel :
          Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
            ((e.symm.toContinuousLinearMap :
              Tensor0SModel s ℝ E →L[ℝ] Tensor0SSpace s I b) T) = T := hRound
      rw [hToModel]
      change covariantTensorInnerPointwise (I := I) (M := M) s g b T T < 1
      exact hT
    · intro hv
      refine ⟨e v, ?_, ?_⟩
      · rw [Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq, tensor0SRiemannianInner_diagonal_clm_apply] at hv
        change covariantTensorInnerPointwise (I := I) (M := M) s g b _ _ < 1
        exact hv
      · exact e.symm_apply_apply v
  rw [← hSetEq]
  exact hImg

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace in

noncomputable def tensor0SRiemannianMetric
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Bundle.RiemannianMetric (E := fun b : M => Tensor0SSpace s I b) where
  inner := fun b => tensor0SRiemannianInnerCLM (I := I) (M := M) g s b
  symm := fun b T S =>
    tensor0SRiemannianInner_symm (I := I) (M := M) g s b T S
  pos := fun b T hT =>
    tensor0SRiemannianInner_pos (I := I) (M := M) g s b T hT
  continuousAt := fun b =>
    tensor0SRiemannianInner_diagonal_continuousAt_zero
      (I := I) (M := M) g s b
  isVonNBounded := fun b =>
    tensor0SRiemannianInner_isVonNBounded (I := I) (M := M) g s b

end Tensor0SRiemannianBundle
end Tensor
end DifferentialGeometry

namespace Tensor0SBundle

open DifferentialGeometry.Tensor.Tensor0SRiemannianBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[reducible]
noncomputable def tensor0S_riemannianBundle
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Bundle.RiemannianBundle (fun b : M => Tensor0SSpace s I b) :=
  ⟨tensor0SRiemannianMetric (I := I) (M := M) g s⟩

end Tensor0SBundle
