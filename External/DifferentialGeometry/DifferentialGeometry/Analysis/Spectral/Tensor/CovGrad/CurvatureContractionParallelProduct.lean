import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureContractionCovariantLeibnizGrid

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

theorem exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (Z : SmoothCcTensor g 0 s) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((iteratedCovGrad g 0 s j (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection
              x) ≤
          C j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
              ((iteratedCovGrad g 0 s q Z).toSection x) := by
  obtain ⟨kappa, hkappa_nn, hbound⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le
      (I := I) (M := M) g s hX hY

  refine ⟨fun j => (4 : ℝ) ^ j * gridWindowSum kappa 0 s j,
    fun j => mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 s j), fun Z j x => ?_⟩
  exact hbound Z j x

theorem curvatureContraction_grid_const_nonneg
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (j : ℕ) :
    0 ≤ (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
        (I := I) (M := M) g s hX hY).choose j :=
  (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
    (I := I) (M := M) g s hX hY).choose_spec.1 j

theorem riemannianFiberNormSq_curvatureContraction_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (Z : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x) ≤
      (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
          (I := I) (M := M) g s hX hY).choose 0 *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (Z.toSection x) := by
  have hgrid :=
    (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
      (I := I) (M := M) g s hX hY).choose_spec.2 Z 0 x
  rw [iteratedCovGrad_zero] at hgrid
  rw [Finset.sum_range_one, iteratedCovGrad_zero] at hgrid
  exact hgrid

end Connection
end Integral
end DifferentialGeometry

end
