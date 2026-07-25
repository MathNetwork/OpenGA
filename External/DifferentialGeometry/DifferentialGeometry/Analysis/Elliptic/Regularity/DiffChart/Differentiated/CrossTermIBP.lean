import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplViaH3
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DifferentiatedCrossTermIBP

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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp
    (I := I) (M := M) g α hu_h i l

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma exists_smooth_global_extension
    {φ : EuclN → ℝ} (α : M)
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (φExt : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ K ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) φExt ∧
      (∀ y ∈ Metric.cthickening δ K, φExt y = φ y) := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_subset, hη_smooth, hη_cs, _hη_range, hη_one, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hK_in
  let φExt : EuclN → ℝ := fun y => η y * φ y
  refine ⟨δ, φExt, hδ_pos, hδ_subset, ?_, ?_⟩
  · have h_open_chart : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_open_compl : IsOpen ((tsupport η)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport η
    · have hy_chart : y ∈ chartTargetEuclid (I := I) (M := M) α := hη_tsupp hy_supp
      have hη_at : ContDiffAt ℝ (⊤ : ℕ∞) η y := hη_smooth.contDiffAt
      have hφ_at : ContDiffAt ℝ (⊤ : ℕ∞) φ y :=
        (hφ_chart y hy_chart).contDiffAt (h_open_chart.mem_nhds hy_chart)
      exact hη_at.mul hφ_at
    · have h_nbhd : (tsupport η)ᶜ ∈ 𝓝 y := h_open_compl.mem_nhds hy_supp
      have h_eq_zero : φExt =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_nbhd] with z hz
        have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
        change η z * φ z = 0
        rw [hηz, zero_mul]
      have h_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclN => (0 : ℝ)) y :=
        contDiffAt_const
      exact h_const.congr_of_eventuallyEq h_eq_zero
  · intro y hy
    change η y * φ y = φ y
    rw [hη_one y hy]
    ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma weightedInvGramDerivOnEuclid_contDiffOn_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
  exact h

private lemma cross_derivative_term_ibp_single
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
        (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ)) y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j direction) y)
            (EuclideanSpace.single j 1) *
          (((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
           ) : EuclN → ℝ)) y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i j y * ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set φ : EuclN → ℝ := weightedInvGramDerivOnEuclid (I := I) g α i j direction
    with hφ_def
  have hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ Ω :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j direction
  set v : EuclN → ℝ :=
    (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i j' with hw_def
  have hw_isWeakPartial : ∀ j' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j' (w j') v Ω :=
    fun j' =>
      chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
        (I := I) (M := M) g α hu_h i j'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := φ) α
      hφ_chart hK_compact hK_in
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have h := chartPushedWeakPartialLp_locally_memLp
      (I := I) (M := M) g α i u_h hK'_compact hK'_in
    exact h
  have hw_locMemLp : ∀ (j' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w j') 2 ((volume : Measure EuclN).restrict K') := by
    intro j' K' hK'_compact hK'_in
    have h := chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i j' hK'_compact hK'_in
    exact h
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial j
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hcthick_subset : Metric.cthickening δ K ⊆ Ω := hδ_subset
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_nbhd : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_nbhd] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [h_fderiv_zero_outside_K y hy_K]
      simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K, ∀ j' : Fin (Module.finrank ℝ E),
      (fderiv ℝ φExt y) (EuclideanSpace.single j' 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single j' 1) := by
    intro y hy_K j'
    have hy_thick : y ∈ Metric.cthickening δ K := hK_in_thickening hy_K
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy_K, ?_⟩
      simp [hδ_pos]
    have h_thick_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y := h_thick_open.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (h_thick_sub hz)
    have h_fderiv_eq : fderiv ℝ φExt y = fderiv ℝ φ y :=
      Filter.EventuallyEq.fderiv_eq h_eq_nbhd
    rw [h_fderiv_eq]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K j]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w j y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w j y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  rw [← hLHS_eq, ← hLeibniz1_eq, ← hLeibniz2_eq]
  exact h_ibp_ext

theorem cross_derivative_term_ibp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            (((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
             ) : EuclN → ℝ)) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                (EuclideanSpace.single j 1) *
              (((chartPushedWeakPartialLp (I := I) (M := M) g α i
                (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
               ) : EuclN → ℝ)) y * ψ y)
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i j y * ψ y)
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set v : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i =>
    (((chartPushedWeakPartialLp (I := I) (M := M) g α i
      (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
     ) : EuclN → ℝ)) with hv_def
  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j => weightedInvGramDerivOnEuclid (I := I) g α i j l with hA_def
  set dA : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j j' y => (fderiv ℝ (A i j) y) (EuclideanSpace.single j' 1) with hdA_def
  set u₂ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i j' with hu₂_def
  have h_pair : ∀ (i j : Fin (Module.finrank ℝ E)),
      ∫ y in Ω, A i j y * v i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) =
      -((∫ y in Ω, dA i j j y * v i y * ψ y ∂(volume : Measure EuclN))
        + (∫ y in Ω, A i j y * u₂ i j y * ψ y ∂(volume : Measure EuclN))) :=
    fun i j =>
      cross_derivative_term_ibp_single
        (I := I) (M := M) g α hu_h l i j hψ_smooth hψ_cs hψ_supp
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  have hvolK_finite : (volume : Measure EuclN) K < (⊤ : ℝ≥0∞) :=
    hK_compact.measure_lt_top
  have hvolK_finite' : (volume.restrict K : Measure EuclN) Set.univ < (⊤ : ℝ≥0∞) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvolK_finite
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := ⟨hvolK_finite'⟩
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_fderiv_j_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_nbhd : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_nbhd] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  have hψ_fderiv_supp : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (fun y => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) ⊆ K := by
    intro j
    refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
    by_contra hy_notin
    have : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
      rw [h_fderiv_zero_outside_K y hy_notin]; simp
    exact hy this
  have h_A_cont_on : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (A i j) Ω := fun i j =>
    weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l
  have h_A_cont_K : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (A i j) K := fun i j => (h_A_cont_on i j).mono hK_in
  have hv_locMemLp_K : ∀ i : Fin (Module.finrank ℝ E),
      MemLp (v i) 2 ((volume : Measure EuclN).restrict K) :=
    fun i => chartPushedWeakPartialLp_locally_memLp
      (I := I) (M := M) g α i u_h hK_compact hK_in
  have hv_int_K : ∀ i : Fin (Module.finrank ℝ E),
      IntegrableOn (v i) K (volume : Measure EuclN) :=
    fun i => (hv_locMemLp_K i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_dA_cont_on : ∀ i j j' : Fin (Module.finrank ℝ E),
      ContinuousOn (dA i j j') Ω := by
    intro i j j'
    have h_diffOn :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
    have h_fderiv_diff : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y) Ω :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j' 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j' (1 : ℝ))).contDiff
    have h := h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)
    exact h.continuousOn
  have h_dA_cont_K : ∀ i j j' : Fin (Module.finrank ℝ E),
      ContinuousOn (dA i j j') K := fun i j j' => (h_dA_cont_on i j j').mono hK_in
  have hu₂_locMemLp_K : ∀ (i j' : Fin (Module.finrank ℝ E)),
      MemLp (u₂ i j') 2 ((volume : Measure EuclN).restrict K) := fun i j' =>
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i j' hK_compact hK_in
  have hu₂_int_K : ∀ (i j' : Fin (Module.finrank ℝ E)),
      IntegrableOn (u₂ i j') K (volume : Measure EuclN) := fun i j' =>
    (hu₂_locMemLp_K i j').integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have integrable_mul_compact_v :
      ∀ {i : Fin (Module.finrank ℝ E)} {h₁ : EuclN → ℝ},
        Continuous h₁ → tsupport h₁ ⊆ K →
        Integrable (fun y => v i y * h₁ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro i h₁ hh₁_cont hh₁_supp
    have hh₁_contOn : ContinuousOn h₁ K := hh₁_cont.continuousOn
    have step_K : IntegrableOn (fun y => v i y * h₁ y) K (volume : Measure EuclN) :=
      (hv_int_K i).mul_continuousOn hh₁_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → v i y * h₁ y = 0 := by
      intro y hy
      have : h₁ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh₁_supp hy_supp))
      simp [this]
    have h_eq_ind :
        (fun y => v i y * h₁ y) = K.indicator (fun y => v i y * h₁ y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => v i y * h₁ y))
        (volume : Measure EuclN) :=
      (integrable_indicator_iff hK_meas).mpr step_K
    have full_int : Integrable (fun y => v i y * h₁ y) (volume : Measure EuclN) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have integrable_mul_compact_u₂ :
      ∀ {i j' : Fin (Module.finrank ℝ E)} {h₁ : EuclN → ℝ},
        Continuous h₁ → tsupport h₁ ⊆ K →
        Integrable (fun y => u₂ i j' y * h₁ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro i j' h₁ hh₁_cont hh₁_supp
    have hh₁_contOn : ContinuousOn h₁ K := hh₁_cont.continuousOn
    have step_K : IntegrableOn (fun y => u₂ i j' y * h₁ y) K (volume : Measure EuclN) :=
      (hu₂_int_K i j').mul_continuousOn hh₁_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → u₂ i j' y * h₁ y = 0 := by
      intro y hy
      have : h₁ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh₁_supp hy_supp))
      simp [this]
    have h_eq_ind :
        (fun y => u₂ i j' y * h₁ y) = K.indicator (fun y => u₂ i j' y * h₁ y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => u₂ i j' y * h₁ y))
        (volume : Measure EuclN) :=
      (integrable_indicator_iff hK_meas).mpr step_K
    have full_int : Integrable (fun y => u₂ i j' y * h₁ y) (volume : Measure EuclN) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have h_int_LHS_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => A i j y * v i y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := by
    intro i j
    set h₁ : EuclN → ℝ := fun y => A i j y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) with hh₁_def
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hψ_y : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
        rw [h_fderiv_zero_outside_K y hy_notin]; simp
      have : A i j y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
        rw [hψ_y, mul_zero]
      exact hy this
    have h_h₁_cont : Continuous h₁ := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · have h_A_cont_at : ContinuousAt (A i j) y :=
          ((h_A_cont_on i j).continuousAt (hΩ_open.mem_nhds (hK_in hy)))
        exact h_A_cont_at.mul (hψ_fderiv_j_cont j).continuousAt
      · have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h₁ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have : (fderiv ℝ ψ z) (EuclideanSpace.single j 1) = 0 := by
            rw [h_fderiv_zero_outside_K z hz]; simp
          change A i j z * (fderiv ℝ ψ z) (EuclideanSpace.single j 1) = 0
          rw [this, mul_zero]
        have h_y_eq : h₁ y = 0 := by
          have : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
            rw [h_fderiv_zero_outside_K y hy]; simp
          change A i j y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
          rw [this, mul_zero]
        rw [continuousAt_congr h_eq_zero]
        exact continuousAt_const
    have h_int := integrable_mul_compact_v
      (i := i) (h₁ := h₁) h_h₁_cont hh₁_supp
    have h_eq : (fun y => v i y * h₁ y) =
        (fun y => A i j y * v i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) := by
      funext y
      change v i y * (A i j y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
        A i j y * v i y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ring
    rw [← h_eq]
    exact h_int
  have h_int_RHS1_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => dA i j j y * v i y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := by
    intro i j
    set h₁ : EuclN → ℝ := fun y => dA i j j y * ψ y with hh₁_def
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_notin
      have : dA i j j y * ψ y = 0 := by rw [hψ_y, mul_zero]
      exact hy this
    have h_h₁_cont : Continuous h₁ := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · have h_dA_cont_at : ContinuousAt (dA i j j) y :=
          ((h_dA_cont_on i j j).continuousAt (hΩ_open.mem_nhds (hK_in hy)))
        exact h_dA_cont_at.mul hψ_cont.continuousAt
      · have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h₁ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
          change dA i j j z * ψ z = 0
          rw [this, mul_zero]
        have h_y_eq : h₁ y = 0 := by
          have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          change dA i j j y * ψ y = 0
          rw [this, mul_zero]
        rw [continuousAt_congr h_eq_zero]
        exact continuousAt_const
    have h_int := integrable_mul_compact_v
      (i := i) (h₁ := h₁) h_h₁_cont hh₁_supp
    have h_eq : (fun y => v i y * h₁ y) =
        (fun y => dA i j j y * v i y * ψ y) := by
      funext y
      change v i y * (dA i j j y * ψ y) = dA i j j y * v i y * ψ y
      ring
    rw [← h_eq]
    exact h_int
  have h_int_RHS2_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => A i j y * u₂ i j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := by
    intro i j
    set h₁ : EuclN → ℝ := fun y => A i j y * ψ y with hh₁_def
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_notin
      have : A i j y * ψ y = 0 := by rw [hψ_y, mul_zero]
      exact hy this
    have h_h₁_cont : Continuous h₁ := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · have h_A_cont_at : ContinuousAt (A i j) y :=
          ((h_A_cont_on i j).continuousAt (hΩ_open.mem_nhds (hK_in hy)))
        exact h_A_cont_at.mul hψ_cont.continuousAt
      · have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h₁ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
          change A i j z * ψ z = 0
          rw [this, mul_zero]
        have h_y_eq : h₁ y = 0 := by
          have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          change A i j y * ψ y = 0
          rw [this, mul_zero]
        rw [continuousAt_congr h_eq_zero]
        exact continuousAt_const
    have h_int := integrable_mul_compact_u₂
      (i := i) (j' := j) (h₁ := h₁) h_h₁_cont hh₁_supp
    have h_eq : (fun y => u₂ i j y * h₁ y) =
        (fun y => A i j y * u₂ i j y * ψ y) := by
      funext y
      change u₂ i j y * (A i j y * ψ y) = A i j y * u₂ i j y * ψ y
      ring
    rw [← h_eq]
    exact h_int
  have hLHS_sum_swap :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            A i j y * v i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, A i j y * v i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
              ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_LHS_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_LHS_pair i j)]
  have hRHS1_sum_swap :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            dA i j j y * v i y * ψ y)
        ∂(volume : Measure EuclN)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, dA i j j y * v i y * ψ y
              ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_RHS1_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_RHS1_pair i j)]
  have hRHS2_sum_swap :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            A i j y * u₂ i j y * ψ y)
        ∂(volume : Measure EuclN)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, A i j y * u₂ i j y * ψ y
              ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_RHS2_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_RHS2_pair i j)]
  rw [hLHS_sum_swap, hRHS1_sum_swap, hRHS2_sum_swap]
  have hLHS_neg :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, A i j y * v i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω, dA i j j y * v i y * ψ y
              ∂(volume : Measure EuclN))
            + (∫ y in Ω, A i j y * u₂ i j y * ψ y
              ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact h_pair i j
  set X : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => ∫ y in Ω, dA i j j y * v i y * ψ y ∂(volume : Measure EuclN)
    with hX_def
  set Y : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => ∫ y in Ω, A i j y * u₂ i j y * ψ y ∂(volume : Measure EuclN)
    with hY_def
  have h_distribute :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((X i j) + (Y i j))) =
      -((∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), X i j)
        + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), Y i j)) := by
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), (-((X i j) + (Y i j))) =
        -((∑ j : Fin (Module.finrank ℝ E), X i j)
          + (∑ j : Fin (Module.finrank ℝ E), Y i j)) := by
      intro i
      simp_rw [neg_add]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    have h_outer : ∀ i : Fin (Module.finrank ℝ E),
        -((∑ j : Fin (Module.finrank ℝ E), X i j)
          + (∑ j : Fin (Module.finrank ℝ E), Y i j)) =
        (-(∑ j : Fin (Module.finrank ℝ E), X i j))
          + (-(∑ j : Fin (Module.finrank ℝ E), Y i j)) := by
      intro i; rw [neg_add]
    rw [Finset.sum_congr rfl (fun i _ => h_outer i)]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_neg_distrib (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (f := fun i => ∑ j, X i j)]
    rw [Finset.sum_neg_distrib (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (f := fun i => ∑ j, Y i j)]
    rw [← neg_add]
  rw [hLHS_neg]
  exact h_distribute

end DifferentiatedCrossTermIBP
end Laplacian
end Analysis
end DifferentialGeometry

end
