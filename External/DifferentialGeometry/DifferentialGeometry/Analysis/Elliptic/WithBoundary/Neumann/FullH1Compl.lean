import DifferentialGeometry.Analysis.Elliptic.WithBoundary.Neumann.FullSmoothScalarPreH1
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

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

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

abbrev H1ComplFullNeumann (g : SmoothRiemannianMetric (I_half n) M) : Type _ :=
  UniformSpace.Completion (FullSmoothScalar g)

noncomputable def smoothToH1ComplFullNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    FullSmoothScalar g →L[ℝ] H1ComplFullNeumann g :=
  UniformSpace.Completion.toComplL

@[simp] lemma smoothToH1ComplFullNeumann_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : FullSmoothScalar g) :
    smoothToH1ComplFullNeumann g f = (f : H1ComplFullNeumann g) := rfl

lemma FullSmoothScalar.memLp_two
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    MemLp f.toFun 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I_half n) (M := M) g
  exact f.smooth.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def smoothToLpLinFullNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    FullSmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) where
  toFun f := f.memLp_two.toLp f.toFun
  map_add' f h := by
    have h_lhs_rfl : (f + h).memLp_two.toLp (f + h).toFun =
        (f.memLp_two.add h.memLp_two).toLp (f.toFun + h.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_add]
  map_smul' c f := by
    have h_lhs_rfl : (c • f).memLp_two.toLp (c • f).toFun =
        (f.memLp_two.const_smul c).toLp (c • f.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_const_smul]
    rfl

@[simp] lemma smoothToLpLinFullNeumann_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : FullSmoothScalar g) :
    smoothToLpLinFullNeumann g f = f.memLp_two.toLp f.toFun := rfl

lemma FullSmoothScalar.norm_smoothToLp_sq
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    ‖smoothToLpLinFullNeumann g f‖ ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (smoothToLpLinFullNeumann g f)
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)] at h
  have hae : (fun a : M =>
        @inner ℝ _ _
          ((smoothToLpLinFullNeumann g f : Lp ℝ 2 _) a)
          ((smoothToLpLinFullNeumann g f : Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g]
      (fun a : M => f.toFun a * f.toFun a) := by
    have hae_coe : (smoothToLpLinFullNeumann g f : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I_half n) (M := M) g] f.toFun :=
      MemLp.coeFn_toLp f.memLp_two
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rfl
  rw [integral_congr_ae hae] at h
  exact h.symm

lemma FullSmoothScalar.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    ‖f‖ ^ 2 = fullSmoothScalarH1Inner f f := by
  have h := real_inner_self_eq_norm_sq f
  rw [FullSmoothScalar.inner_def] at h
  exact h.symm

lemma FullSmoothScalar.norm_smoothToLp_sq_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    ‖smoothToLpLinFullNeumann g f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [f.norm_smoothToLp_sq, f.norm_sq_eq_inner_self]
  unfold fullSmoothScalarH1Inner
  have h_grad_nonneg :
      0 ≤ ∫ x, g.inner x (gradFun (I := I_half n) g f.toFun x)
            (gradFun (I := I_half n) g f.toFun x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    f.integral_inner_grad_self_nonneg
  linarith

lemma FullSmoothScalar.norm_smoothToLp_le
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    ‖smoothToLpLinFullNeumann g f‖ ≤ ‖f‖ := by
  have h_sq := f.norm_smoothToLp_sq_le
  have h_lhs_nn : 0 ≤ ‖smoothToLpLinFullNeumann g f‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖f‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

lemma FullSmoothScalar.norm_smoothToLp_le_one_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f : FullSmoothScalar g) :
    ‖smoothToLpLinFullNeumann g f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]; exact f.norm_smoothToLp_le

noncomputable def smoothToLpFullNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    FullSmoothScalar g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  (smoothToLpLinFullNeumann g).mkContinuous 1
    (fun f => f.norm_smoothToLp_le_one_mul)

@[simp] lemma smoothToLpFullNeumann_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : FullSmoothScalar g) :
    smoothToLpFullNeumann g f = f.memLp_two.toLp f.toFun := rfl

private lemma denseRange_toComplL_fullSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (UniformSpace.Completion.toComplL :
      FullSmoothScalar g →L[ℝ] H1ComplFullNeumann g) := by
  rw [show (UniformSpace.Completion.toComplL :
      FullSmoothScalar g → H1ComplFullNeumann g) =
      ((↑) : FullSmoothScalar g →
        UniformSpace.Completion (FullSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

private lemma isUniformInducing_toComplL_fullSmoothScalar
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        FullSmoothScalar g →L[ℝ] H1ComplFullNeumann g) := by
  rw [show (UniformSpace.Completion.toComplL :
      FullSmoothScalar g → H1ComplFullNeumann g) =
      ((↑) : FullSmoothScalar g →
        UniformSpace.Completion (FullSmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (FullSmoothScalar g)

noncomputable def H1ComplFullNeumannToLp
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplFullNeumann g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  ContinuousLinearMap.extend (smoothToLpFullNeumann g)
    (UniformSpace.Completion.toComplL :
      FullSmoothScalar g →L[ℝ] H1ComplFullNeumann g)

@[simp] lemma H1ComplFullNeumannToLp_smoothToH1ComplFullNeumann
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : FullSmoothScalar g) :
    H1ComplFullNeumannToLp g (smoothToH1ComplFullNeumann g f) =
      smoothToLpFullNeumann g f := by
  unfold H1ComplFullNeumannToLp
  exact ContinuousLinearMap.extend_eq (smoothToLpFullNeumann g)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_fullSmoothScalar g)
    (isUniformInducing_toComplL_fullSmoothScalar g) f

noncomputable def H1ComplFullNeumannBilin
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplFullNeumann g →L[ℝ] H1ComplFullNeumann g →L[ℝ] ℝ :=
  innerSL ℝ

@[simp] lemma H1ComplFullNeumannBilin_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : H1ComplFullNeumann g) :
    H1ComplFullNeumannBilin g u v = ⟪u, v⟫_ℝ := rfl

lemma H1ComplFullNeumannBilin_isCoercive
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsCoercive (H1ComplFullNeumannBilin g) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show H1ComplFullNeumannBilin g u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

noncomputable def lpFunctionalCLMFullNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      (H1ComplFullNeumann g →L[ℝ] ℝ) :=
  let applyL :
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
      (H1ComplFullNeumann g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) →L[ℝ]
        (H1ComplFullNeumann g →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (H1ComplFullNeumann g)
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) ℝ
  ((applyL.flip) (H1ComplFullNeumannToLp g)).comp
    (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ)

@[simp] lemma lpFunctionalCLMFullNeumann_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplFullNeumann g) :
    lpFunctionalCLMFullNeumann g f v =
      ⟪H1ComplFullNeumannToLp g v, f⟫_ℝ := by
  change (innerSL ℝ f) (H1ComplFullNeumannToLp g v) =
    ⟪H1ComplFullNeumannToLp g v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (H1ComplFullNeumannToLp g v) f

noncomputable def H1ComplFullNeumannLaxMilgramEquiv
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplFullNeumann g ≃L[ℝ] H1ComplFullNeumann g :=
  IsCoercive.continuousLinearEquivOfBilin
    (H1ComplFullNeumannBilin_isCoercive g)

@[simp] lemma H1ComplFullNeumannLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u w : H1ComplFullNeumann g) :
    ⟪H1ComplFullNeumannLaxMilgramEquiv g u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

noncomputable def H1ComplFullNeumannRieszRepr
    (g : SmoothRiemannianMetric (I_half n) M) :
    (H1ComplFullNeumann g →L[ℝ] ℝ) →L[ℝ] H1ComplFullNeumann g :=
  LinearMap.mkContinuous
    { toFun := fun φ =>
        (InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm φ
      map_add' := fun φ ψ =>
        (InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm φ‖
        ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq
        ((InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm.norm_map φ))

lemma H1ComplFullNeumannRieszRepr_inner
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : H1ComplFullNeumann g →L[ℝ] ℝ) (w : H1ComplFullNeumann g) :
    ⟪H1ComplFullNeumannRieszRepr g φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (H1ComplFullNeumann g)).symm φ, w⟫_ℝ
    = φ w
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (E := H1ComplFullNeumann g) (x := w) (y := φ)

noncomputable def resolventFullNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplFullNeumann g :=
  (H1ComplFullNeumannRieszRepr g).comp (lpFunctionalCLMFullNeumann g)

theorem resolventFullNeumann_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplFullNeumann g) :
    ⟪resolventFullNeumann g f, v⟫_ℝ =
      ⟪H1ComplFullNeumannToLp g v, f⟫_ℝ := by
  unfold resolventFullNeumann
  rw [ContinuousLinearMap.comp_apply, H1ComplFullNeumannRieszRepr_inner,
    lpFunctionalCLMFullNeumann_apply]

example (g : SmoothRiemannianMetric (I_half n) M) : Type _ := H1ComplFullNeumann g

example (g : SmoothRiemannianMetric (I_half n) M) :
    NormedAddCommGroup (H1ComplFullNeumann g) := inferInstance

example (g : SmoothRiemannianMetric (I_half n) M) :
    InnerProductSpace ℝ (H1ComplFullNeumann g) := inferInstance

example (g : SmoothRiemannianMetric (I_half n) M) :
    CompleteSpace (H1ComplFullNeumann g) := inferInstance

example (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplFullNeumann g :=
  resolventFullNeumann g

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
