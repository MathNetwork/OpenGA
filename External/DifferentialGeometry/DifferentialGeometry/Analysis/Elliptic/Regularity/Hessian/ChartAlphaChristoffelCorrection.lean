import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.ChartAlphaLp


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function FiberBundle
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaChristoffelDischarge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridge
open DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaFrobenius
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def christoffelDischargeSmoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Prop :=
  ∀ x : M,
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) = 0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] lemma christoffelDischargeSmoothCase_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    christoffelDischargeSmoothCase (I := I) (M := M) g φ v ↔
      ∀ x : M,
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            (chartAtlasPOU I M α : M → ℝ) x *
              smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
                ((toEuclidean (E := E)) (extChartAt I α x)) = 0 := Iff.rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (α : M) (x : M) :
    smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
        ((toEuclidean (E := E)) (extChartAt I α x)) =
      smoothTensorPairingChart (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) +
        smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) :=
  smoothEuclidHessianPairingChart_eq_tensor_plus_diff
    (I := I) (M := M) g α φ v ((toEuclidean (E := E)) (extChartAt I α x))

theorem pou_weighted_euclid_pairing_decompose
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x +
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) := by
  classical
  have h_per_term : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothTensorPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) +
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) := by
    intro α _
    rw [smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff
      (I := I) (M := M) g φ v α x]
    ring
  rw [Finset.sum_congr rfl h_per_term]
  rw [Finset.sum_add_distrib]
  rw [pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise
    (I := I) (M := M) g φ v x]

theorem pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  rw [pou_weighted_euclid_pairing_decompose (I := I) (M := M) g φ v x]
  rw [h_discharge x]
  rw [add_zero]

omit [NeZero (Module.finrank ℝ E)] in

theorem hessPairingMChartContribution_smoothCase_eq_weighted_chartLocal
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (α : M) (x : M) :
    hessPairingMChartContribution (I := I) (M := M) g φ α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocal (I := I) (M := M) g α φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          ((toEuclidean (E := E)) (extChartAt I α x)) := rfl

end HessianChartAlphaChristoffelDischarge
end Laplacian
end Analysis
end DifferentialGeometry

end
