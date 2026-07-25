import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingFromChartBridges
import DifferentialGeometry.Analysis.Heat.Smoothing.HeatSemigroupIteratedDomain
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.ChartH2kRegularity

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem chartSideH2kBridge_heat_unconditional
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (k : ℕ) :
    ChartSideH2kBridge (I := I) (M := M) g k
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all
      (I := I) (M := M) g ht u_0 k
  have h_bridge_lift :=
    chartSideH2kBridge_of_laplacianDomainPow_unconditional
      (I := I) (M := M) g k hu_h_mem
  have h_coe : ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe] at h_bridge_lift
  exact h_bridge_lift

theorem heatSemigroup_smooth_representative_of_closed
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth := by
  apply heatSemigroup_smooth_representative_of_chartSideBridges
    (I := I) (M := M) g ht u_0
  intro k
  exact chartSideH2kBridge_heat_unconditional
    (I := I) (M := M) g ht u_0 k

theorem heatSemigroup_smooth_in_space_and_time_unconditional
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (∀ t : ℝ, 0 < t →
      ∃ u_smooth_t : M → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth_t ∧
        ((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I) (M := M) g] u_smooth_t) ∧
    ContDiffOn ℝ ∞
      (fun t : ℝ =>
        (heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)))
      (Set.Ioi (0 : ℝ)) := by
  apply heatSemigroup_smooth_in_space_and_time_of_chartSideBridges
    (I := I) (M := M) g u_0
  intro t ht k
  exact chartSideH2kBridge_heat_unconditional
    (I := I) (M := M) g ht u_0 k

end HeatEquation
end Analysis
end DifferentialGeometry

end
