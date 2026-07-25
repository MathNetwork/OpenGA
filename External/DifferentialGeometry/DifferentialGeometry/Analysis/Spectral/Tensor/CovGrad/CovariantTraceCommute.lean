import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import DifferentialGeometry.Tensor.RSTensor.Derivation.Contract
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldEvaluationLeibniz


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

noncomputable def contractCcTensor (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g (1 + r) (s + 1) → SmoothCcTensor g r s :=
  fun T =>
    { toSection :=
        Tensor0SBundle.contract_TensorRSField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
          (n := ∞) r s T.toSection
      hasCompactSupport := by
        refine HasCompactSupport.of_support_subset_isCompact T.hasCompactSupport ?_
        intro x hx
        rw [Function.mem_support] at hx
        by_contra hxnot
        apply hx
        have hTzero : TensorRSSpace.toModel (T.toSection x) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : M => TensorRSSpace.toModel (T.toSection y)) hxnot
        have hxz : T.toSection x = 0 := by
          have h0 := TensorRSSpace.toModel_zero (I := I) (r := 1 + r) (s := s + 1) (x := x)
          exact TensorRSSpace.toModel_injective (hTzero.trans h0.symm)
        change TensorRSSpace.toModel
            (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x
              (T.toSection x)) = 0
        rw [hxz, map_zero, TensorRSSpace.toModel_zero] }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem contractCcTensor_toSection_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g (1 + r) (s + 1)) (x : M) :
    (contractCcTensor (I := I) (M := M) g r s T).toSection x =
      Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x
        (T.toSection x) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
@[simp] theorem contractCcTensor_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    contractCcTensor (I := I) (M := M) g r s (0 : SmoothCcTensor g (1 + r) (s + 1)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [contractCcTensor_toSection_apply]
  rw [show ((0 : SmoothCcTensor g (1 + r) (s + 1)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  rw [map_zero]
  rw [show ((0 : SmoothCcTensor g r s).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem contractCcTensor_add (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₁ T₂ : SmoothCcTensor g (1 + r) (s + 1)) :
    contractCcTensor (I := I) (M := M) g r s (T₁ + T₂) =
      contractCcTensor (I := I) (M := M) g r s T₁ + contractCcTensor (I := I) (M := M) g r s T₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [contractCcTensor_toSection_apply]
  rw [show ((contractCcTensor (I := I) (M := M) g r s T₁ +
        contractCcTensor (I := I) (M := M) g r s T₂).toSection x) =
      (contractCcTensor (I := I) (M := M) g r s T₁).toSection x +
        (contractCcTensor (I := I) (M := M) g r s T₂).toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]; rfl]
  rw [contractCcTensor_toSection_apply, contractCcTensor_toSection_apply]
  rw [show ((T₁ + T₂).toSection x) = T₁.toSection x + T₂.toSection x from by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add]; rfl]
  rw [map_add]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem contractCcTensor_smul (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g (1 + r) (s + 1)) :
    contractCcTensor (I := I) (M := M) g r s (c • T) =
      c • contractCcTensor (I := I) (M := M) g r s T := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [contractCcTensor_toSection_apply]
  rw [show ((c • contractCcTensor (I := I) (M := M) g r s T).toSection x) =
      c • (contractCcTensor (I := I) (M := M) g r s T).toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl]
  rw [contractCcTensor_toSection_apply]
  rw [show ((c • T).toSection x) = c • T.toSection x from by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul]; rfl]
  rw [map_smul]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
private lemma riemannianFiberNormSq_eq_bundle_norm_sq_gen
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (z : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    riemannianFiberNormSq (I := I) (M := M) g r s x z = ‖z‖ ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have h_inner :
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s x z z : ℝ) =
        riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
    exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x z).symm
  have hself : (inner ℝ z z : ℝ) =
      riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [← h_inner]; rfl
  rw [← hself, real_inner_self_eq_norm_sq]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem riemannianFiberNormSq_tensorRS_clm_apply_le
    (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ : ℕ) (x : M)
    (φ : TensorRSSpace r₁ s₁ I x →L[ℝ] TensorRSSpace r₂ s₂ I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ v : TensorRSSpace r₁ s₁ I x,
      riemannianFiberNormSq (I := I) (M := M) g r₂ s₂ x (φ v) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g r₁ s₁ x v := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r₁ s₁ I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r₁ s₁
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r₂ s₂ I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r₂ s₂
  let φg : TensorRSSpace r₁ s₁ I x →L[ℝ] TensorRSSpace r₂ s₂ I x :=
    LinearMap.toContinuousLinearMap (φ.toLinearMap)
  have hφg_apply : ∀ v, φg v = φ v := fun v => by
    change (LinearMap.toContinuousLinearMap (φ.toLinearMap)) v = φ v
    rw [LinearMap.coe_toContinuousLinearMap']; rfl
  refine ⟨‖φg‖ ^ 2, sq_nonneg _, fun v => ?_⟩
  rw [riemannianFiberNormSq_eq_bundle_norm_sq_gen (I := I) (M := M) g r₂ s₂ x (φ v),
      riemannianFiberNormSq_eq_bundle_norm_sq_gen (I := I) (M := M) g r₁ s₁ x v, ← hφg_apply v]
  calc ‖φg v‖ ^ 2 ≤ (‖φg‖ * ‖v‖) ^ 2 := by
          apply sq_le_sq'
          · nlinarith [φg.le_opNorm v, norm_nonneg (φg v), norm_nonneg v, norm_nonneg φg]
          · exact φg.le_opNorm v
    _ = ‖φg‖ ^ 2 * ‖v‖ ^ 2 := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem riemannianFiberNormSq_contract_trace_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ T : TensorRSSpace (1 + r) (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g r s x
          (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x T) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g (1 + r) (s + 1) x T :=
  riemannianFiberNormSq_tensorRS_clm_apply_le (I := I) (M := M) g (1 + r) (s + 1) r s x
    (Tensor0SBundle.contract_trace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
omit [CompleteSpace E] in
theorem riemannianFiberNormSq_contractCcTensor_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ T : SmoothCcTensor g (1 + r) (s + 1),
      riemannianFiberNormSq (I := I) (M := M) g r s x
          ((contractCcTensor (I := I) (M := M) g r s T).toSection x) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g (1 + r) (s + 1) x (T.toSection x) := by
  obtain ⟨Cφ, hCφ, hbound⟩ := riemannianFiberNormSq_contract_trace_le (I := I) (M := M) g r s x
  refine ⟨Cφ, hCφ, fun T => ?_⟩
  rw [contractCcTensor_toSection_apply]
  exact hbound (T.toSection x)

end Connection
end Integral
end DifferentialGeometry

end
