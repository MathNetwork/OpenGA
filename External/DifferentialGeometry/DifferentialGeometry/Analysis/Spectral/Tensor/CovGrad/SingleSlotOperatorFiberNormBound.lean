import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldCovariantCalculus


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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
lemma riemannianFiberNormSq_eq_bundle_norm_sq'
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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem riemannianFiberNormSq_clm_apply_le_of_sqrt_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x) (μ : ℝ) (hμ : 0 ≤ μ)
    (hbound : ∀ v : TensorRSSpace 0 r I x,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v)) ≤
        μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v)) :
    ∀ v : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) ≤
        μ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 r x v := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 r
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 s
  intro v
  have hsrc_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 r x v :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 r x v
  have htgt_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x (φ v)
  have hb := hbound v

  have hrhs_nn : 0 ≤ μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v) :=
    mul_nonneg hμ (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v))) ^ 2 ≤
        (μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v)) ^ 2 := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  rw [Real.sq_sqrt htgt_nn] at hsq
  rw [mul_pow, Real.sq_sqrt hsrc_nn] at hsq
  exact hsq

end Connection
end Integral
end DifferentialGeometry

end
