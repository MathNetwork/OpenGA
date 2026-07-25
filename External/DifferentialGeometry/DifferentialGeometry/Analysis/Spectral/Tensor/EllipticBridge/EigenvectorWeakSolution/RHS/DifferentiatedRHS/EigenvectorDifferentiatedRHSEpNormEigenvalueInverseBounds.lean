import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] in
lemma eigen_inv_one_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    1 ≤ (i.fst.val)⁻¹ := by
  have h_norm :
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i‖ = 1 :=
    (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s)).norm_eq_one i
  have hμ_unit : i.fst.val ∈ Set.Ioc (0 : ℝ) 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  have hμ_pos : 0 < i.fst.val := hμ_unit.1
  have hμ_le_one : i.fst.val ≤ 1 := hμ_unit.2
  exact (one_le_inv₀ hμ_pos).mpr hμ_le_one

omit [CompleteSpace E] in
private lemma pow_eigen_inv_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {k e : ℕ} (hke : k ≤ e) :
    (i.fst.val)⁻¹ ^ k ≤ (i.fst.val)⁻¹ ^ e := by
  exact pow_le_pow_right₀
    (eigen_inv_one_le (I := I) (M := M) g r s i) hke

omit [CompleteSpace E] in
lemma ofReal_const_pow_eigen_inv_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {C : ℝ} (hC_nn : 0 ≤ C) {k e : ℕ} (hke : k ≤ e) :
    ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ k) ≤
      ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ e) := by
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_left
    (pow_eigen_inv_le (I := I) (M := M) g r s i hke) hC_nn

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
