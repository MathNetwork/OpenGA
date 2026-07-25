import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_covGrad_comm_heq (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr g r (by omega : (s + 1) + k = s + (k + 1)) ih

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem norm_toSection_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) (x : M) :
    ‖Y.toSection x‖ = ‖Z.toSection x‖ := by
  subst h
  rw [eq_of_heq hYZ]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_toSection_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (X : SmoothCcTensor g r s) (x : M) :
    ‖(iteratedCovGrad g r (s + 1) m (covGrad g r s X)).toSection x‖ =
      ‖(iteratedCovGrad g r s (m + 1) X).toSection x‖ :=
  norm_toSection_heq_congr g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq (g := g) (r := r) (s := s) (m := m) X) x

def castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (Y : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ Y

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_toSection_iteratedCovGrad_castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (Y : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    ‖(iteratedCovGrad g r b j (castRankCc g r h Y)).toSection x‖ =
      ‖(iteratedCovGrad g r a j Y).toSection x‖ := by
  subst h
  rfl

structure ParallelTensorProduct (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ r₀ s₀ : ℕ) where

  prod : ∀ {a b : ℕ}, SmoothCcTensor g r₁ (s₁ + a) → SmoothCcTensor g r₂ (s₂ + b) →
    SmoothCcTensor g r₀ (s₀ + a + b)

  opNorm : ℝ

  opNorm_nonneg : 0 ≤ opNorm

  rfns_prod_le : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b))
    (x : M),
    riemannianFiberNormSq (I := I) (M := M) g r₀ (s₀ + a + b) x ((prod S T).toSection x) ≤
      opNorm * riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + a) x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + b) x (T.toSection x)

  covGrad_prod : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)),
    covGrad g r₀ (s₀ + a + b) (prod S T) =
      castRankCc g r₀ (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
          (prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T) +
        prod (a := a) (b := b + 1) S (covGrad g r₂ (s₂ + b) T)

namespace ParallelTensorProduct

variable {g : SmoothRiemannianMetric I M} {r₁ s₁ r₂ s₂ r₀ s₀ : ℕ}

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem eq_zero_of_riemannianFiberNormSq_eq_zero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (z : Tensor0SBundle.TensorRSSpace r s I x)
    (hz : riemannianFiberNormSq (I := I) (M := M) g r s x z = 0) : z = 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hnorm_sq : ‖z‖ ^ 2 = 0 :=
    (riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g r s x z).symm.trans hz
  have hnorm : ‖z‖ = 0 := by nlinarith [norm_nonneg z, hnorm_sq]
  exact norm_eq_zero.mp hnorm

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem prod_zero_left (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (T : SmoothCcTensor g r₂ (s₂ + b)) :
    Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.rfns_prod_le (0 : SmoothCcTensor g r₁ (s₁ + a)) T x
  have hzero : ((0 : SmoothCcTensor g r₁ (s₁ + a)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, riemannianFiberNormSq_zero, mul_zero, zero_mul] at hle
  have hval : (Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T).toSection x = 0 :=
    eq_zero_of_riemannianFiberNormSq_eq_zero (I := I) g r₀ (s₀ + a + b) x _
      (le_antisymm hle (riemannianFiberNormSq_nonneg (I := I) (M := M) g r₀ (s₀ + a + b) x _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem prod_zero_right (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) :
    Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.rfns_prod_le S (0 : SmoothCcTensor g r₂ (s₂ + b)) x
  have hzero : ((0 : SmoothCcTensor g r₂ (s₂ + b)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, riemannianFiberNormSq_zero, mul_zero] at hle
  have hval : (Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b))).toSection x = 0 :=
    eq_zero_of_riemannianFiberNormSq_eq_zero (I := I) g r₀ (s₀ + a + b) x _
      (le_antisymm hle (riemannianFiberNormSq_nonneg (I := I) (M := M) g r₀ (s₀ + a + b) x _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval

end ParallelTensorProduct

end RicciFlow
end PDE
end DifferentialGeometry

end
