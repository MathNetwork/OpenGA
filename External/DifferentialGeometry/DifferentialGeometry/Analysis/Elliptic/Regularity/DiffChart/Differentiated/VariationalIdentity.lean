import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import Mathlib.Analysis.Calculus.FDeriv.Symmetric


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DifferentiatedVariationalIdentity

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
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Laplacian.FChartResidualMemW1p
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contDiff_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => fderiv ℝ ψ y) :=
    (contDiff_infty_iff_fderiv.1 hψ).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.comp h_fderiv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma hasCompactSupport_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma tsupport_fderiv_apply_single_subset
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_apply_single_swap
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : EuclN)
    (j l : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
        (EuclideanSpace.single j 1) =
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l 1) := by
  classical
  have h_diff_fderiv : Differentiable ℝ (fderiv ℝ ψ) :=
    ((contDiff_infty_iff_fderiv.1 hψ).2).differentiable (by simp)
  have h_flip_eq : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single k 1)) y =
        (fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single k 1) := by
    intro k
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : EuclN => (EuclideanSpace.single k (1 : ℝ))) y :=
      differentiableAt_const _
    have h_step :=
      fderiv_clm_apply (𝕜 := ℝ)
        (c := fderiv ℝ ψ) (u := fun _ : EuclN => EuclideanSpace.single k (1 : ℝ))
        (x := y) (h_diff_fderiv y) h_const_diff
    have h_const_fderiv :
        fderiv ℝ (fun _ : EuclN => EuclideanSpace.single k (1 : ℝ)) y = 0 :=
      fderiv_const_apply (EuclideanSpace.single k (1 : ℝ))
    rw [h_step, h_const_fderiv]; simp
  rw [h_flip_eq l, h_flip_eq j]
  have h_symm : IsSymmSndFDerivAt ℝ ψ y := by
    have h_ge : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact hψ.contDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) h_ge
  change ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single l 1))
        (EuclideanSpace.single j 1) =
      ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single j 1))
        (EuclideanSpace.single l 1)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact h_symm (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)

private lemma base_weak_partial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).weak_partial i) 2
      ((volume : Measure EuclN).restrict K) :=
  (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
    hu_h).weak_partial_locally_memLp i K hK_compact hK_in

private lemma base_u_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D :=
    chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
    with hD_def
  have h_weighted := D.u_chart_memLp_weighted
  obtain ⟨c, hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.u_chart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

private lemma base_f_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D :=
    chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
    with hD_def
  have h_weighted := D.f_chart_memLp_weighted
  obtain ⟨c, hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.f_chart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

private lemma weightedInvGram_ibp_per_pair
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      weightedInvGramOnEuclid (I := I) g α i j y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial i y *
        (fderiv ℝ
          (fun z => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
          (EuclideanSpace.single j 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  set φ : EuclN → ℝ := weightedInvGramOnEuclid (I := I) g α i j with hφ_def
  have hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ Ω :=
    weightedInvGramOnEuclid_contDiffOn (I := I) g α i j
  set v : EuclN → ℝ := D_base.weak_partial i with hv_def
  have hv_eq : v = ((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) := rfl
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun l' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i l' with hw_def
  have hw_isWeakPartial : ∀ l' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l' (w l') v Ω := by
    intro l'
    rw [hv_eq]
    exact chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
      (I := I) (M := M) g α hu_h i l'
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := fun K' hK' hK'_in =>
    base_weak_partial_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i hK' hK'_in
  have hw_locMemLp : ∀ (l' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w l') 2 ((volume : Measure EuclN).restrict K') :=
    fun l' K' hK' hK'_in =>
      chosenSecondPartialChartPushedU_locally_memLp
        (I := I) (M := M) g α hu_h i l' hK' hK'_in
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := φ) α
      hφ_chart hK_compact hK_in
  set ψ_test : EuclN → ℝ := fun y => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
    with hψ_test_def
  have hψ_test_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_test :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth j
  have hψ_test_cs : HasCompactSupport ψ_test :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs j
  have hψ_test_supp : tsupport ψ_test ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset ψ j).trans hψ_supp
  have h_ibp_ext :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l
      (ψ := ψ_test) hψ_test_smooth hψ_test_cs hψ_test_supp
  have h_fderiv_zero_outside_K_ψ : ∀ x ∉ K, fderiv ℝ ψ x = 0 :=
    fun x hx => by
      have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
      have h_fderiv_eq : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [h_compl_open.mem_nhds hx] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      rw [h_fderiv_eq]; simp
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have h_fderiv_zero_outside_K_ψ_test : ∀ x ∉ K, fderiv ℝ ψ_test x = 0 :=
    fun x hx => by
      have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
      have h_fderiv_eq : fderiv ℝ ψ_test x =
          fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [h_compl_open.mem_nhds hx] with y hy
        change (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
        rw [h_fderiv_zero_outside_K_ψ y hy]; simp
      rw [h_fderiv_eq]; simp
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ_test y) (EuclideanSpace.single l 1)
          ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ
            (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
            (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
      have h_swap :
          (fderiv ℝ ψ_test y) (EuclideanSpace.single l 1) =
          (fderiv ℝ
            (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
            (EuclideanSpace.single j 1) := by
        change (fderiv ℝ (fun z : EuclN =>
            (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
            (EuclideanSpace.single l 1) = _
        exact (fderiv_apply_single_swap (ψ := ψ) hψ_smooth y j l).symm
      rw [h_swap]
    · have h1 : (fderiv ℝ ψ_test y) (EuclideanSpace.single l 1) = 0 := by
        rw [h_fderiv_zero_outside_K_ψ_test y hy_K]; simp
      have h2 :
          (fderiv ℝ
            (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
            (EuclideanSpace.single j 1) = 0 := by
        rw [← fderiv_apply_single_swap (ψ := ψ) hψ_smooth y l j]
        change (fderiv ℝ ψ_test y) (EuclideanSpace.single l 1) = 0
        exact h1
      rw [h1, h2]; ring
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K, ∀ l' : Fin (Module.finrank ℝ E),
      (fderiv ℝ φExt y) (EuclideanSpace.single l' 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l' 1) := fun y hy_K _ => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have h_fderiv_φ_eq_φ_deriv : ∀ y : EuclN,
      (fderiv ℝ φ y) (EuclideanSpace.single l 1) =
      weightedInvGramDerivOnEuclid (I := I) g α i j l y := fun _ => rfl
  have hψ_j_zero_outside_K : ∀ y, y ∉ K →
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 :=
    fun y hy => by rw [h_fderiv_zero_outside_K_ψ y hy]; simp
  have hψ_test_zero_outside_K : ∀ y, y ∉ K → ψ_test y = 0 := fun y hy => by
    change (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
    exact hψ_j_zero_outside_K y hy
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l 1) * v y * ψ_test y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω,
        weightedInvGramDerivOnEuclid (I := I) g α i j l y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K l, h_fderiv_φ_eq_φ_deriv y]
    · rw [hψ_test_zero_outside_K y hy_K, hψ_j_zero_outside_K y hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l y * ψ_test y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [hψ_test_zero_outside_K y hy_K, hψ_j_zero_outside_K y hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

private lemma weightedInvGram_ibp_double_sum
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
          weightedInvGramOnEuclid (I := I) g α i j y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial i y *
            (fderiv ℝ
              (fun z => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
              (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l y *
                (chartBilinearH1ComplData_of_laplacianDomain
                  (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j => weightedInvGramOnEuclid (I := I) g α i j with hA_def
  set dA : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j => weightedInvGramDerivOnEuclid (I := I) g α i j l with hdA_def
  set v : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i =>
    D_base.weak_partial i with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i =>
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l with hw_def
  set ψl : EuclN → ℝ := fun y =>
    (fderiv ℝ ψ y) (EuclideanSpace.single l 1) with hψl_def
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
  have hψl_smooth : ContDiff ℝ (⊤ : ℕ∞) ψl :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth l
  have hψl_cs : HasCompactSupport ψl :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs l
  have hψl_supp : tsupport ψl ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset ψ l).trans hψ_supp
  have hψ_fderiv_j_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψl_fderiv_j_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψl y) (EuclideanSpace.single j 1)) :=
    fun j => (hψl_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have h_fderiv_zero_outside_K_ψ : ∀ z ∉ K, fderiv ℝ ψ z = 0 :=
    fun z hz => by
      have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
      have h_fderiv_eq : fderiv ℝ ψ z = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) z := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [h_compl_open.mem_nhds hz] with w hw
        exact image_eq_zero_of_notMem_tsupport hw
      rw [h_fderiv_eq]; simp
  have h_fderiv_zero_outside_K_ψl : ∀ x ∉ K, fderiv ℝ ψl x = 0 :=
    fun x hx => by
      have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
      have h_fderiv_eq : fderiv ℝ ψl x =
          fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [h_compl_open.mem_nhds hx] with y hy
        change (fderiv ℝ ψ y) (EuclideanSpace.single l 1) = 0
        rw [h_fderiv_zero_outside_K_ψ y hy]; simp
      rw [h_fderiv_eq]; simp
  have h_A_cont_on : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (A i j) Ω := fun i j =>
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_dA_cont_on : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (dA i j) Ω := fun i j =>
    weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l
  have hv_locMemLp : ∀ i : Fin (Module.finrank ℝ E),
      MemLp (v i) 2 ((volume : Measure EuclN).restrict K) := fun i =>
    base_weak_partial_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i hK_compact hK_in
  have hw_locMemLp : ∀ i : Fin (Module.finrank ℝ E),
      MemLp (w i) 2 ((volume : Measure EuclN).restrict K) := fun i =>
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i l hK_compact hK_in
  have hv_int_K : ∀ i, IntegrableOn (v i) K (volume : Measure EuclN) :=
    fun i => (hv_locMemLp i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hw_int_K : ∀ i, IntegrableOn (w i) K (volume : Measure EuclN) :=
    fun i => (hw_locMemLp i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have integrable_mul_compact :
      ∀ {u h₁ : EuclN → ℝ}, IntegrableOn u K (volume : Measure EuclN) →
        Continuous h₁ → tsupport h₁ ⊆ K →
        Integrable (fun y => u y * h₁ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro u h₁ hu_int hh₁_cont hh₁_supp
    have hh₁_contOn : ContinuousOn h₁ K := hh₁_cont.continuousOn
    have step_K : IntegrableOn (fun y => u y * h₁ y) K (volume : Measure EuclN) :=
      hu_int.mul_continuousOn hh₁_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → u y * h₁ y = 0 := by
      intro y hy
      have : h₁ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh₁_supp hy_supp))
      simp [this]
    have h_eq_ind :
        (fun y => u y * h₁ y) = K.indicator (fun y => u y * h₁ y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => u y * h₁ y))
        (volume : Measure EuclN) :=
      (integrable_indicator_iff hK_meas).mpr step_K
    have full_int : Integrable (fun y => u y * h₁ y) (volume : Measure EuclN) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have integrable_triple :
      ∀ {a : EuclN → ℝ} (ha_cont_on : ContinuousOn a Ω)
        {u : EuclN → ℝ} (hu_int : IntegrableOn u K (volume : Measure EuclN))
        {ζ : EuclN → ℝ}
        (hζ_fderiv_zero : ∀ x ∉ K, fderiv ℝ ζ x = 0)
        (hζ_fderiv_cont : ∀ j' : Fin (Module.finrank ℝ E),
          Continuous (fun y : EuclN => (fderiv ℝ ζ y) (EuclideanSpace.single j' 1)))
        (j : Fin (Module.finrank ℝ E)),
        Integrable (fun y => a y * u y *
          (fderiv ℝ ζ y) (EuclideanSpace.single j 1))
          ((volume : Measure EuclN).restrict Ω) := by
    intro a ha_cont_on u hu_int ζ hζ_fderiv_zero hζ_fderiv_cont j
    set h₁ : EuclN → ℝ := fun y => a y * (fderiv ℝ ζ y) (EuclideanSpace.single j 1)
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hζy : (fderiv ℝ ζ y) (EuclideanSpace.single j 1) = 0 := by
        rw [hζ_fderiv_zero y hy_notin]; simp
      exact hy (by change a y * _ = 0; rw [hζy, mul_zero])
    have h_h₁_cont : Continuous h₁ := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · have h_a_cont_at : ContinuousAt a y :=
          (ha_cont_on.continuousAt (hΩ_open.mem_nhds (hK_in hy)))
        exact h_a_cont_at.mul (hζ_fderiv_cont j).continuousAt
      · have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h₁ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have hζz : (fderiv ℝ ζ z) (EuclideanSpace.single j 1) = 0 := by
            rw [hζ_fderiv_zero z hz]; simp
          change a z * (fderiv ℝ ζ z) (EuclideanSpace.single j 1) = 0
          rw [hζz, mul_zero]
        rw [continuousAt_congr h_eq_zero]; exact continuousAt_const
    have h_int := integrable_mul_compact (u := u) (h₁ := h₁) hu_int h_h₁_cont hh₁_supp
    have h_eq : (fun y => u y * h₁ y) =
        (fun y => a y * u y * (fderiv ℝ ζ y) (EuclideanSpace.single j 1)) := by
      funext y
      change u y * (a y * (fderiv ℝ ζ y) (EuclideanSpace.single j 1)) =
        a y * u y * (fderiv ℝ ζ y) (EuclideanSpace.single j 1)
      ring
    rw [← h_eq]; exact h_int
  have h_int_LHS_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => A i j y * v i y *
        (fderiv ℝ ψl y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple (h_A_cont_on i j) (hv_int_K i)
      h_fderiv_zero_outside_K_ψl hψl_fderiv_j_cont j
  have h_int_RHS1_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => dA i j y * v i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple (h_dA_cont_on i j) (hv_int_K i)
      h_fderiv_zero_outside_K_ψ hψ_fderiv_j_cont j
  have h_int_RHS2_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => A i j y * w i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple (h_A_cont_on i j) (hw_int_K i)
      h_fderiv_zero_outside_K_ψ hψ_fderiv_j_cont j
  have sum_swap :
      ∀ {F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ},
        (∀ i j, Integrable (F i j) ((volume : Measure EuclN).restrict Ω)) →
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E), F i j y)
          ∂(volume : Measure EuclN)
        = ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∫ y in Ω, F i j y ∂(volume : Measure EuclN) := by
    intro F hF_int
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => hF_int i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => hF_int i j)]
  have hLHS_sum_swap := sum_swap (F := fun i j y => A i j y * v i y *
    (fderiv ℝ ψl y) (EuclideanSpace.single j 1)) h_int_LHS_pair
  have hRHS1_sum_swap := sum_swap (F := fun i j y => dA i j y * v i y *
    (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) h_int_RHS1_pair
  have hRHS2_sum_swap := sum_swap (F := fun i j y => A i j y * w i y *
    (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) h_int_RHS2_pair
  have h_pair : ∀ (i j : Fin (Module.finrank ℝ E)),
      ∫ y in Ω, A i j y * v i y *
        (fderiv ℝ ψl y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) =
      -((∫ y in Ω, dA i j y * v i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
        + (∫ y in Ω, A i j y * w i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN))) := by
    intro i j
    exact weightedInvGram_ibp_per_pair (I := I) (M := M) g α hu_h l i j
      hψ_smooth hψ_cs hψ_supp
  rw [hLHS_sum_swap, hRHS1_sum_swap, hRHS2_sum_swap]
  have hLHS_neg :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, A i j y * v i y *
            (fderiv ℝ ψl y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω, dA i j y * v i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
              ∂(volume : Measure EuclN))
            + (∫ y in Ω, A i j y * w i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
                ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact h_pair i j
  set X : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => ∫ y in Ω, dA i j y * v i y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN)
  set Y : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => ∫ y in Ω, A i j y * w i y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN)
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma density_coef_ibp
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {v : EuclN → ℝ}
    {w : Fin (Module.finrank ℝ E) → EuclN → ℝ}
    (hw_isWeakPartial : ∀ l' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l' (w l') v
        (chartTargetEuclid (I := I) (M := M) α))
    (hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' →
      K' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp v 2 ((volume : Measure EuclN).restrict K'))
    (hw_locMemLp : ∀ (l' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp (w l') 2 ((volume : Measure EuclN).restrict K'))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * v y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l y * v y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * w l y * ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set φ : EuclN → ℝ := densityOnEuclid (I := I) g α with hφ_def
  have hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ Ω :=
    densityOnEuclid_contDiffOn (I := I) g α
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := φ) α
      hφ_chart hK_compact hK_in
  have h_ibp_ext :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial l
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 :=
    fun x hx => by
      have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
      have h_fderiv_eq : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
        apply Filter.EventuallyEq.fderiv_eq
        filter_upwards [h_compl_open.mem_nhds hx] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      rw [h_fderiv_eq]; simp
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have : (fderiv ℝ ψ y) (EuclideanSpace.single l 1) = 0 := by
        rw [h_fderiv_zero_outside_K y hy_K]; simp
      rw [this]; simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K,
      (fderiv ℝ φExt y) (EuclideanSpace.single l 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single l 1) := fun y hy_K => by
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]; exact ⟨y, hy_K, by simp [hδ_pos]⟩
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y :=
      Metric.isOpen_thickening.mem_nhds hy_thick_open
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (Metric.thickening_subset_cthickening _ _ hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_nbhd]
  have h_fderiv_φ_eq_φ_deriv : ∀ y : EuclN,
      (fderiv ℝ φ y) (EuclideanSpace.single l 1) =
      densityDerivOnEuclid (I := I) g α l y := fun _ => rfl
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K, h_fderiv_φ_eq_φ_deriv y]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y _ => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [image_eq_zero_of_notMem_tsupport hy_K]; ring
  rw [hLHS_eq] at h_ibp_ext
  rw [hLeibniz1_eq, hLeibniz2_eq] at h_ibp_ext
  exact h_ibp_ext

private lemma density_u_chart_ibp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).u_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l y *
          (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
          (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weak_partial l y * ψ y
          ∂(volume : Measure EuclN))) := by
  set D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  refine density_coef_ibp (I := I) (M := M) g α l (v := D_base.u_chart)
    (w := fun l' => D_base.weak_partial l')
    (fun l' => D_base.weak_partial_isWeakPartial l') ?_ ?_
    hψ_smooth hψ_cs hψ_supp
  · intro K' hK'_compact hK'_in
    exact base_u_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) hK'_compact hK'_compact.isClosed.measurableSet hK'_in
  · intro l' K' hK'_compact hK'_in
    exact base_weak_partial_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) l' hK'_compact hK'_in

private lemma density_f_chart_ibp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l y *
          (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y
          ∂(volume : Measure EuclN))) := by
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  have h_base_f_chart_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  refine density_coef_ibp (I := I) (M := M) g α l (v := D_base.f_chart)
    (w := fun l' => chosenFChartDeriv (I := I) (M := M) g α hu_h l')
    (fun l' => chosenFChartDeriv_isWeakPartial (I := I) (M := M) g α hu_h l'
      h_base_f_chart_memW1p) ?_ ?_ hψ_smooth hψ_cs hψ_supp
  · intro K' hK'_compact hK'_in
    exact base_f_chart_locally_memLp (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) hK'_compact hK'_compact.isClosed.measurableSet hK'_in
  · intro l' K' hK'_compact hK'_in
    have h_global :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_base_f_chart_memW1p l'
    have h_unfold : (fun l' => chosenFChartDeriv (I := I) (M := M) g α hu_h l') l' =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 l' D_base.f_chart Ω := rfl
    rw [h_unfold]
    have h_K'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict h_K'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact h_global.restrict K'

theorem differentiated_variational_identity_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i direction y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weak_partial direction y * ψ y
      ∂(volume : Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) -
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α direction y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityDerivOnEuclid (I := I) g α direction y *
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
      ∂(volume : Measure EuclN)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set l : Fin (Module.finrank ℝ E) := direction with hl_def
  set D_base := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
    g α (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h) with hD_def
  set ψl : EuclN → ℝ := fun y =>
    (fderiv ℝ ψ y) (EuclideanSpace.single l 1) with hψl_def
  have hψl_smooth : ContDiff ℝ (⊤ : ℕ∞) ψl :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth l
  have hψl_cs : HasCompactSupport ψl :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs l
  have hψl_supp : tsupport ψl ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset ψ l).trans hψ_supp
  have h_base_id := D_base.variational_identity ψl hψl_smooth hψl_cs hψl_supp
  have hT1 := weightedInvGram_ibp_double_sum (I := I) (M := M) g α hu_h l
    hψ_smooth hψ_cs hψ_supp
  have hT2 := density_u_chart_ibp (I := I) (M := M) g α hu_h l
    hψ_smooth hψ_cs hψ_supp
  have hT3 := density_f_chart_ibp (I := I) (M := M) g α hu_h l
    hψ_smooth hψ_cs hψ_supp
  set T1 : ℝ := ∫ y in Ω,
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          D_base.weak_partial i y *
          (fderiv ℝ ψl y) (EuclideanSpace.single j 1))
    ∂(volume : Measure EuclN) with hT1_def
  set T2 : ℝ := ∫ y in Ω,
    densityOnEuclid (I := I) g α y * D_base.u_chart y * ψl y
    ∂(volume : Measure EuclN) with hT2_def
  set T3 : ℝ := ∫ y in Ω,
    densityOnEuclid (I := I) g α y * D_base.f_chart y * ψl y
    ∂(volume : Measure EuclN) with hT3_def
  have h_base_TS : T1 + T2 = T3 := h_base_id
  set A1_principal : ℝ := ∫ y in Ω,
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          chosenSecondPartialChartPushedU
            (I := I) (M := M) g α u_h i l y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
    ∂(volume : Measure EuclN) with hA1_principal_def
  set A1_cross : ℝ := ∫ y in Ω,
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          D_base.weak_partial i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
    ∂(volume : Measure EuclN) with hA1_cross_def
  set A2_principal : ℝ := ∫ y in Ω,
    densityOnEuclid (I := I) g α y * D_base.weak_partial l y * ψ y
    ∂(volume : Measure EuclN) with hA2_principal_def
  set A2_cross : ℝ := ∫ y in Ω,
    densityDerivOnEuclid (I := I) g α l y * D_base.u_chart y * ψ y
    ∂(volume : Measure EuclN) with hA2_cross_def
  set B_principal : ℝ := ∫ y in Ω,
    densityOnEuclid (I := I) g α y *
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y * ψ y
    ∂(volume : Measure EuclN) with hB_principal_def
  set B_cross : ℝ := ∫ y in Ω,
    densityDerivOnEuclid (I := I) g α l y * D_base.f_chart y * ψ y
    ∂(volume : Measure EuclN) with hB_cross_def
  have hT1' : T1 = -(A1_cross + A1_principal) := hT1
  have hT2' : T2 = -(A2_cross + A2_principal) := hT2
  have hT3' : T3 = -(B_cross + B_principal) := hT3
  have h_combined : A1_principal + A2_principal =
      B_principal - A1_cross - A2_cross + B_cross := by
    have : T1 + T2 = T3 := h_base_TS
    rw [hT1', hT2', hT3'] at this
    linarith
  exact h_combined

end DifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
