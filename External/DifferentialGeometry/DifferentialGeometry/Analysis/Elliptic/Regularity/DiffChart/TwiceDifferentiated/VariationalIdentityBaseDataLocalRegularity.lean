import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedDataConstructor
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TwiceDifferentiatedVariationalIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.FChartResidualMemW1p
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma base_weak_partial_ae_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3.chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h i :=
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3.chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h i

private lemma base_weak_partial_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_memWkp_2 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair := laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h
    exact h_pair.1.1 α
  have h_chosen_memWkp_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_memWkp_2.chosenWeakPartial_mem i
  have h_chosen :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp
      h_chosen_memWkp_1
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (MemW1p_congr_ae hΩ_open
    (base_weak_partial_ae_eq_chartPushedChosenFirstPartial
      (I := I) (M := M) g α hu_h i)).mpr h_chosen

private lemma chosenWeakPartial'_base_weak_partial_ae_eq_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial l₁)
        (chartTargetEuclid (I := I) (M := M) α) =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ := by
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_aeEq :=
    base_weak_partial_ae_eq_chartPushedChosenFirstPartial
      (I := I) (M := M) g α hu_h l₁
  have h_congr :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_ae_congr
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_aeEq l₂
  exact h_congr

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma exists_smooth_global_extension_chart
    {φ : EuclN → ℝ} {α : M}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (φExt : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ K ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) φExt ∧
      (∀ y ∈ Metric.cthickening δ K, φExt y = φ y) :=
  exists_smooth_global_extension (I := I) (M := M) (φ := φ) α
    hφ_chart hK_compact hK_in

lemma base_u_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.u_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.u_chart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

lemma base_f_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.f_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.f_chart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

lemma base_weak_partial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).weak_partial i) 2
      ((volume : Measure EuclN).restrict K) :=
  (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
    ).weak_partial_locally_memLp i K hK_compact hK_in

private lemma chosenWeakPartial_base_wp_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial l₁)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_w1p := base_weak_partial_memW1p (I := I) (M := M) g α hu_h l₁
  have h_global :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_w1p l₂
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

private lemma integral_chosenWeakPartial_base_eq_integral_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (ψ : EuclN → ℝ) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l₂
          ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial l₁)
          (chartTargetEuclid (I := I) (M := M) α)) y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
      ∂(volume : Measure EuclN)) := by
  have h_aeEq := chosenWeakPartial'_base_weak_partial_ae_eq_chosenSecond
    (I := I) (M := M) g α hu_h l₁ l₂
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h_aeEq] with y hy
  rw [hy]

end TwiceDifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
