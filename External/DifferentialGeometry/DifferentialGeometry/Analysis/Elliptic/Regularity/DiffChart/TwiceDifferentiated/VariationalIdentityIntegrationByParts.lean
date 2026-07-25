import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedDataConstructor
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentityTestFunctionCalculus
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentityBaseDataLocalRegularity

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

lemma per_pair_ibp_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l₁ l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y * chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            chosenThirdMixedPartialChartPushedU
              (I := I) (M := M) g α u_h i l₁ l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ :=
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' => chosenThirdMixedPartialChartPushedU
      (I := I) (M := M) g α u_h i l₁ l₂' with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' =>
      chosenThirdMixedPartialChartPushedU_isWeakPartial
        (I := I) (M := M) g α hu_h i l₁ l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₁ hK'_compact hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    exact chosenThirdMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₁ l₂' hK'_compact hK'_in
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

lemma per_pair_ibp_base_weak_partial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial i y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial i y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ :=
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i l₂' with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω := by
    intro l₂'
    exact hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp
      (I := I) (M := M) g α hu_h i l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact base_weak_partial_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i hK'_compact hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    exact chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l₂' hK'_compact hK'_in
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
          ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

lemma per_pair_ibp_base_u_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).u_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  set v : EuclN → ℝ := D.u_chart with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun l₂' => D.weak_partial l₂'
    with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' => D.weak_partial_isWeakPartial l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact base_u_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) hK'_compact
      hK'_compact.isClosed.measurableSet hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    exact base_weak_partial_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) l₂' hK'_compact hK'_in
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

lemma per_pair_ibp_base_f_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₂ : Fin (Module.finrank ℝ E))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  have h_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  set v : EuclN → ℝ := D.f_chart with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' => chosenFChartDeriv (I := I) (M := M) g α hu_h l₂' with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' =>
      chosenFChartDeriv_isWeakPartial (I := I) (M := M) g α hu_h l₂' h_memW1p
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    exact base_f_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) hK'_compact
      hK'_compact.isClosed.measurableSet hK'_in
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_memW1p l₂'
    have h_K'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict h_K'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    have h_unfold :
        w l₂' = DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l₂' D.f_chart Ω := rfl
    rw [h_unfold]
    rw [← h_eq]
    exact h_global.restrict K'
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l₂ y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

lemma per_pair_ibp_chosenFChartDeriv
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          φ y *
            fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ := chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l₂' =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂' v Ω
    with hw_def
  have hw_isWeakPartial : ∀ l₂' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l₂' (w l₂') v Ω :=
    fun l₂' =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_chosenFChartDeriv_memW1p l₂'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension_chart (φ := φ) hφ_chart hK_compact hK_in
  have h_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  have h_v_global :
      MemLp v 2 ((volume : Measure EuclN).restrict Ω) := by
    change MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁) 2
        ((volume : Measure EuclN).restrict Ω)
    unfold chosenFChartDeriv
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_memW1p l₁
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have h_K'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict h_K'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact h_v_global.restrict K'
  have hw_locMemLp : ∀ (l₂' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l₂') 2 ((volume : Measure EuclN).restrict K') := by
    intro l₂' K' hK'_compact hK'_in
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_chosenFChartDeriv_memW1p l₂'
    have h_K'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict h_K'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact h_global.restrict K'
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l₂
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l₂ 1) = 0 := by
        rw [fderiv_zero_outside_tsupport ψ y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l₂ 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l₂ y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * (fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂) y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
      rfl
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

end TwiceDifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
