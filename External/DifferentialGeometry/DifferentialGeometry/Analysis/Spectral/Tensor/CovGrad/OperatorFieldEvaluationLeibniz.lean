import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.TensorRSContRiemannianBundle


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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

structure IsPointwiseLinearLocalOperator (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)) : Prop where

  linear : ∀ (r : ℕ) (c₁ c₂ : ℝ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    (op 0 r (c₁ • W₁ + c₂ • W₂)).toSection x =
      c₁ • (op 0 r W₁).toSection x + c₂ • (op 0 r W₂).toSection x

  local' : ∀ (r : ℕ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M),
    W₁.toSection x = W₂.toSection x → (op 0 r W₁).toSection x = (op 0 r W₂).toSection x


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [CompleteSpace E] in
theorem order_zero_apply_smul_of_pointwise_smul
    (g : SmoothRiemannianMetric I M) (r : ℕ)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (hbase : IsPointwiseLinearLocalOperator (I := I) (M := M) g op)
    (c : ℝ) (W₁ W₂ : SmoothCcTensor g 0 r) (x : M)
    (hval : W₂.toSection x = c • W₁.toSection x) :
    (op 0 r W₂).toSection x = c • (op 0 r W₁).toSection x := by
  have hcW : (c • W₁).toSection x = c • W₁.toSection x := by
    rw [SmoothCcTensor.toSection_smul]; rfl
  rw [hbase.local' r W₂ (c • W₁) x (by rw [hval, hcW])]
  have hlin := hbase.linear r c 0 W₁ W₁ x
  rw [show (c • W₁) = c • W₁ + (0 : ℝ) • W₁ from by rw [zero_smul, add_zero]]
  rw [hlin]
  simp only [zero_smul, add_zero]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
private lemma riemannianFiberNormSq_eq_bundle_norm_sq
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

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem riemannianFiberNormSq_clm_apply_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ v : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g 0 r x v := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 r
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 s
  let φg : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap (φ.toLinearMap)
  have hφg_apply : ∀ v, φg v = φ v := fun v => by
    change (LinearMap.toContinuousLinearMap (φ.toLinearMap)) v = φ v
    rw [LinearMap.coe_toContinuousLinearMap']; rfl
  refine ⟨‖φg‖ ^ 2, sq_nonneg _, fun v => ?_⟩
  rw [riemannianFiberNormSq_eq_bundle_norm_sq (I := I) (M := M) g 0 s x (φ v),
      riemannianFiberNormSq_eq_bundle_norm_sq (I := I) (M := M) g 0 r x v, ← hφg_apply v]
  calc ‖φg v‖ ^ 2 ≤ (‖φg‖ * ‖v‖) ^ 2 := by
          apply sq_le_sq'
          · nlinarith [φg.le_opNorm v, norm_nonneg (φg v), norm_nonneg v, norm_nonneg φg]
          · exact φg.le_opNorm v
    _ = ‖φg‖ ^ 2 * ‖v‖ ^ 2 := by ring

end Connection
end Integral
end DifferentialGeometry

end
