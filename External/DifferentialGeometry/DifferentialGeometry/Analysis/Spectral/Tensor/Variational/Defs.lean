import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

noncomputable def tensorH1ComplBilin (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorH1Compl g r s →L[ℝ] ℝ :=
  innerSL ℝ

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorH1ComplBilin_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u v : TensorH1Compl g r s) :
    tensorH1ComplBilin (I := I) (M := M) g r s u v = ⟪u, v⟫_ℝ := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorH1ComplBilin_isCoercive (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCoercive (tensorH1ComplBilin (I := I) (M := M) g r s) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show tensorH1ComplBilin (I := I) (M := M) g r s u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

noncomputable def tensorLpFunctionalCLM (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] (TensorH1Compl g r s →L[ℝ] ℝ) :=
  let applyL :
      (TensorL2 r s g →L[ℝ] ℝ) →L[ℝ]
        (TensorH1Compl g r s →L[ℝ] TensorL2 r s g) →L[ℝ]
        (TensorH1Compl g r s →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (TensorH1Compl g r s) (TensorL2 r s g) ℝ
  ((applyL.flip) (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)).comp
    (innerSL ℝ : TensorL2 r s g →L[ℝ] TensorL2 r s g →L[ℝ] ℝ)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorLpFunctionalCLM_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    tensorLpFunctionalCLM (I := I) (M := M) g r s f v =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  change (innerSL ℝ f) (TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) =
    ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) f

noncomputable def tensorH1ComplLaxMilgramEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s ≃L[ℝ] TensorH1Compl g r s :=
  IsCoercive.continuousLinearEquivOfBilin
    (tensorH1ComplBilin_isCoercive (I := I) (M := M) g r s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorH1ComplLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u w : TensorH1Compl g r s) :
    ⟪tensorH1ComplLaxMilgramEquiv (I := I) (M := M) g r s u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

noncomputable def tensorH1ComplRieszRepr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (TensorH1Compl g r s →L[ℝ] ℝ) →L[ℝ] TensorH1Compl g r s :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ
      map_add' := fun φ ψ => by
        exact (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq
        ((InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm.norm_map φ))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorH1ComplRieszRepr_inner (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : TensorH1Compl g r s →L[ℝ] ℝ) (w : TensorH1Compl g r s) :
    ⟪tensorH1ComplRieszRepr (I := I) (M := M) g r s φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply
    (𝕜 := ℝ) (E := TensorH1Compl g r s) (x := w) (y := φ)

noncomputable def tensorResolvent (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorH1Compl g r s :=
  (tensorH1ComplRieszRepr (I := I) (M := M) g r s).comp
    (tensorLpFunctionalCLM (I := I) (M := M) g r s)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolvent_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    ⟪tensorResolvent (I := I) (M := M) g r s f, v⟫_ℝ =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  unfold tensorResolvent
  rw [ContinuousLinearMap.comp_apply, tensorH1ComplRieszRepr_inner,
    tensorLpFunctionalCLM_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorResolvent_bilin_eq_lpFunctional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    tensorH1ComplBilin (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s f) v =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  rw [tensorH1ComplBilin_apply]
  exact tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s f v

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorH1Compl g r s :=
  tensorResolvent (I := I) (M := M) g r s

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
