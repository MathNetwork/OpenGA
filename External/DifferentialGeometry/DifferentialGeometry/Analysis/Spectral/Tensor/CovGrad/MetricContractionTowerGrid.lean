import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldDifferentiatedTowerNormalForm

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def fixedCoeffTowerOp (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0)) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W =>
      operatorFieldApply (I := I) (M := M) g (r + 0) (r + 0) (Φ₀ r) W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (fixedCoeffTowerOp g Φ₀ p r W) -
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (fixedCoeffTowerOp g Φ₀ p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem fixedCoeffTower_covGrad_op (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0))
    (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p)
        (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p r W) =
      fixedCoeffTowerOp (I := I) (M := M) g Φ₀ (p + 1) r W +
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p)
      (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p r W) -
      castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
        (fixedCoeffTowerOp (I := I) (M := M) g Φ₀ p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

omit [BoundarylessManifold I M] [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem fixedCoeffTower_base_appCc (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0))
    (r : ℕ) (W : SmoothCcTensor g 0 r) :
    fixedCoeffTowerOp (I := I) (M := M) g Φ₀ 0 r W =
      operatorFieldApply (I := I) (M := M) g (r + 0) (r + 0) (Φ₀ r) W :=
  rfl

def fixedCoeffDiffOp (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0)) :
    DiffBilinOp (I := I) (M := M) g :=
  let op := fixedCoeffTowerOp (I := I) (M := M) g Φ₀
  let covGrad_op := fixedCoeffTower_covGrad_op (I := I) (M := M) g Φ₀
  let hNF : ∀ (p r : ℕ), IsIteratedCovGradNormalForm (I := I) (M := M) g op p r :=
    fun p => normalForm_of_base (I := I) (M := M) g op covGrad_op Φ₀
      (fun r W => fixedCoeffTower_base_appCc (I := I) (M := M) g Φ₀ r W) p
  { op := op
    covGrad_op := covGrad_op
    kappa := fun p r => Classical.choose
      (exists_jet_bound_of_normalForm (I := I) (M := M) g op p r (hNF p r))
    kappa_nonneg := fun p r =>
      (Classical.choose_spec
        (exists_jet_bound_of_normalForm (I := I) (M := M) g op p r (hNF p r))).1
    rfns_op_le := fun p r W x =>
      (Classical.choose_spec
        (exists_jet_bound_of_normalForm (I := I) (M := M) g op p r (hNF p r))).2 W x }


omit [CompleteSpace E] in
theorem fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (g : SmoothRiemannianMetric I M)
    (Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0))
    (x₀ : M) (r : ℕ) (W : SmoothCcTensor g 0 r) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (r + a) x₀
        ((iteratedCovGrad g 0 r a
          ((fixedCoeffDiffOp (I := I) (M := M) g Φ₀).op 0 r W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).kappa 0 r a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x₀
            ((iteratedCovGrad g 0 r q W).toSection x₀) :=
  DiffBilinOp.exists_rfns_iteratedCovGrad_singleSum_le_at
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).op
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).covGrad_op
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).kappa
    (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).kappa_nonneg x₀
    (fun p r W => (fixedCoeffDiffOp (I := I) (M := M) g Φ₀).rfns_op_le p r W x₀) r W a

end Connection
end Integral
end DifferentialGeometry

end
