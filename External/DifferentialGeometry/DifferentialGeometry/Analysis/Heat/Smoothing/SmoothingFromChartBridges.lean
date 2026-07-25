import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothRepresentative
import DifferentialGeometry.Analysis.Heat.Smoothing.HeatSemigroupIteratedDomain
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH2kBridge

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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem chartSideH2kBridge_iff_memWkpChart_two_k
    (g : SmoothRiemannianMetric I M) (k : ℕ) (u : M → ℝ) :
    ChartSideH2kBridge (I := I) (M := M) g k u ↔
      MemWkpChart (I := I) (M := M) g (2 * k) 2 u := by
  refine ⟨fun h => memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g k h, fun h => ?_⟩
  intro α
  exact h α

theorem heatSemigroup_smooth_representative_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) g k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth := by
  have h_iterated_regularity : ∀ k : ℕ,
      MemWkpChart (I := I) (M := M) g (2 * k) 2
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
    intro k
    exact (chartSideH2kBridge_iff_memWkpChart_two_k
      (I := I) (M := M) g k _).mp (h_bridges k)
  exact heatSemigroup_smooth_representative (I := I) (M := M) g ht u_0
    h_iterated_regularity

theorem heatSemigroup_smooth_in_space_and_time_of_chartSideBridges
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges_uniform :
      ∀ t : ℝ, 0 < t → ∀ k : ℕ,
        ChartSideH2kBridge (I := I) (M := M) g k
          (((heatSemigroup (I := I) (M := M) g t u_0 :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
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
  refine ⟨?_, ?_⟩
  · intro t ht
    exact heatSemigroup_smooth_representative_of_chartSideBridges
      (I := I) (M := M) g ht u_0 (h_bridges_uniform t ht)
  · exact heatSemigroup_contMDiff_in_time (I := I) (M := M) g u_0

theorem chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) g k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 ∧
        ChartSideH2kBridge (I := I) (M := M) g k
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro k
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 k
  refine ⟨u_h, hu_h_mem, hu_h_eq, ?_⟩
  have h_coe : ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact h_bridges k

theorem laplacianDomainPow_memWkpChart_2k_of_chartSideBridges_heat
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_bridges : ∀ k : ℕ,
      ChartSideH2kBridge (I := I) (M := M) g k
        (((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 ∧
        MemWkpChart (I := I) (M := M) g (2 * k) 2
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) ∧
        wkpNormChart (I := I) (M := M) g (2 * k) 2
          (((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) < ⊤ := by
  intro k
  obtain ⟨u_h, hu_h_mem, hu_h_eq, h_bridge_lift⟩ :=
    chartSideH2kBridge_heat_implies_chartSideH2kBridge_lifts
      (I := I) (M := M) g ht u_0 h_bridges k
  refine ⟨u_h, hu_h_mem, hu_h_eq, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h_mem h_bridge_lift).1
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
      (I := I) (M := M) g k hu_h_mem h_bridge_lift).2

theorem chartSideH2kBridge_heat_zero
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ChartSideH2kBridge (I := I) (M := M) g 0
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, _hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 0
  have h_coe : ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact chartSideH2kBridge_zero (I := I) (M := M) g u_h

theorem chartSideH2kBridge_heat_one
    (g : SmoothRiemannianMetric I M)
    {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ChartSideH2kBridge (I := I) (M := M) g 1
      (((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  obtain ⟨u_h, hu_h_mem, hu_h_eq⟩ :=
    heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 1
  have h_coe : ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    rw [hu_h_eq]
  rw [h_coe]
  exact chartSideH2kBridge_one (I := I) (M := M) g hu_h_mem

end HeatEquation
end Analysis
end DifferentialGeometry

end
