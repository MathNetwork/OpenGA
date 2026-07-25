import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.CompactChartJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.EigensectionSobolevDecay









noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (eigenvectorSmooth)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))




theorem scalarEig_jet_le
    (g : SmoothRiemannianMetric I M) (α : M) (m k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 0) (y : EuclN),
        y ∈ K →
          ‖iteratedFDerivWithin ℝ m
              (tensorComponentEuclideanChart (I := I) (M := M) g 0 0
                (eigenvectorSmooth (I := I) (M := M) g 0 0 i) α
                Fin.elim0 Fin.elim0)
              (chartTargetEuclid (I := I) (M := M) α) y‖ ≤
            C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
  classical
  obtain ⟨Cjet, hCjet_nn, hjet⟩ :=
    rawPullR_jet_le (I := I) (M := M) g 0 0 α
      Fin.elim0 Fin.elim0 m k h_super hK hK_sub
  obtain ⟨Ceig, hCeig_nn, heig⟩ :=
    eigen_toHs_le (I := I) (M := M) g 0 k
  refine ⟨Cjet * Ceig, mul_nonneg hCjet_nn hCeig_nn, ?_⟩
  intro i y hy
  have hy_open : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hy
  rw [iteratedFDerivWithin_of_isOpen m
    (chartTargetEuclid_isOpen (I := I) (M := M) α) hy_open]
  calc
    ‖iteratedFDeriv ℝ m
        (tensorComponentEuclideanChart (I := I) (M := M) g 0 0
          (eigenvectorSmooth (I := I) (M := M) g 0 0 i) α
          Fin.elim0 Fin.elim0) y‖
        ≤ Cjet *
            ‖IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g) (r := 0) (s := 0) (2 * k)
              (eigenvectorSmooth (I := I) (M := M) g 0 0 i)‖ :=
          hjet (eigenvectorSmooth (I := I) (M := M) g 0 0 i) y hy
    _ ≤ Cjet *
          (Ceig * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left (heig i) hCjet_nn
    _ = (Cjet * Ceig) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) := by
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
