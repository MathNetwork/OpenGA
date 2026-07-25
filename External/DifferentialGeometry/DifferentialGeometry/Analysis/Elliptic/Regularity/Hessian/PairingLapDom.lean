import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.LpClass
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.PairingChart
import DifferentialGeometry.Analysis.Elliptic.Regularity.Ricci.PairingCLM
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.MeasurablePullback
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianPairingLapDom

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
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chartHessianPhiOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartHessianTensor (I := I) g α (φ : M → ℝ) i j
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma chartHessianPhiOnEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y =
      chartHessianTensor (I := I) g α (φ : M → ℝ) i j
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

private noncomputable def cutoffHessianPhi
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartCutoffα (I := I) (M := M) α y *
    chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y

private lemma cutoffHessianPhi_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    cutoffHessianPhi (I := I) (M := M) g α φ i j y =
      chartCutoffα (I := I) (M := M) α y *
        chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y := rfl

noncomputable def hessPairingChartLocal
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          invGramOnEuclid (I := I) g α i k y *
            invGramOnEuclid (I := I) g α j l y *
            chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
            laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma hessPairingChartLocal_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) :
    hessPairingChartLocal (I := I) (M := M) g α φ hu_h y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := rfl

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartHessianPhiOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hrewrite : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y =
        chartIteratedPartialDeriv (I := I) α (φ : M → ℝ) i j
          ((toEuclidean (E := E)).symm y) -
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k ((toEuclidean (E := E)).symm y) *
            partialDeriv (E := E) k (scalarOnE (I := I) α (φ : M → ℝ))
              ((toEuclidean (E := E)).symm y) := by
    intro y hy
    have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy
    have h_inv : extChartAt I α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        (toEuclidean (E := E)).symm y :=
      (extChartAt I α).right_inv hy_target
    rw [chartHessianPhiOnEuclid_def, chartHessianTensor_def, h_inv]
  refine ContinuousOn.congr ?_ hrewrite
  refine ContinuousOn.sub ?_ ?_
  · have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.continuous
    have h_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α (φ : M → ℝ))
        (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α φ.contMDiff
    have h_int_eq_target : interior (extChartAt I α).target = (extChartAt I α).target :=
      (isOpen_extChartAt_target (I := I) α).interior_eq
    have h_smooth_iter : ContDiffOn ℝ ∞
        (chartIteratedPartialDeriv (I := I) α (φ : M → ℝ) i j)
        (extChartAt I α).target := by
      unfold chartIteratedPartialDeriv partialDeriv
      have h_fder1 : ContDiffOn ℝ ∞
          (fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)))
          (extChartAt I α).target :=
        h_smooth_target.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) α)
          (by rw [ENat.coe_top_add_one])
      have h_pd_j : ContDiffOn ℝ ∞
          (fun z : E => fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)) z
            ((chartModelBasis E) j))
          (extChartAt I α).target :=
        h_fder1.clm_apply contDiffOn_const
      have h_fder2 : ContDiffOn ℝ ∞
          (fderiv ℝ (fun z : E => fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)) z
            ((chartModelBasis E) j)))
          (extChartAt I α).target :=
        h_pd_j.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) α)
          (by rw [ENat.coe_top_add_one])
      exact h_fder2.clm_apply contDiffOn_const
    have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
      toEuclidean_symm_mem_target (I := I) hy
    exact h_smooth_iter.continuousOn.comp h_toE_cont.continuousOn h_maps
  · refine continuousOn_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun k _ => ?_)
    have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.continuous
    have h_int_eq_target : interior (extChartAt I α).target = (extChartAt I α).target :=
      (isOpen_extChartAt_target (I := I) α).interior_eq
    have h_chris_cont : ContinuousOn (chartChristoffel (I := I) g α i j k)
        (extChartAt I α).target := by
      rw [← h_int_eq_target]
      exact (chartChristoffel_contDiffOn_interior (I := I) g α i j k).continuousOn
    have h_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α (φ : M → ℝ))
        (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α φ.contMDiff
    have h_pd_cont : ContinuousOn
        (partialDeriv (E := E) k (scalarOnE (I := I) α (φ : M → ℝ)))
        (extChartAt I α).target := by
      unfold partialDeriv
      rw [← h_int_eq_target]
      have h_smooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α (φ : M → ℝ))
          (interior (extChartAt I α).target) := h_smooth_target.mono interior_subset
      have h_fder : ContDiffOn ℝ ∞
          (fderiv ℝ (scalarOnE (I := I) α (φ : M → ℝ)))
          (interior (extChartAt I α).target) :=
        h_smooth_int.fderiv_of_isOpen isOpen_interior
          (by rw [ENat.coe_top_add_one])
      exact (h_fder.clm_apply contDiffOn_const).continuousOn
    have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
      toEuclidean_symm_mem_target (I := I) hy
    have h_chris_comp : ContinuousOn
        (fun y : EuclN => chartChristoffel (I := I) g α i j k
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_chris_cont.comp h_toE_cont.continuousOn h_maps
    have h_pd_comp : ContinuousOn
        (fun y : EuclN => partialDeriv (E := E) k (scalarOnE (I := I) α (φ : M → ℝ))
          ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_pd_cont.comp h_toE_cont.continuousOn h_maps
    exact h_chris_comp.mul h_pd_comp

private lemma cutoffHessianPhi_continuous
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    Continuous (cutoffHessianPhi (I := I) (M := M) g α φ i j) := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hη_cont : Continuous η :=
    (chartCutoffα_smooth (I := I) (M := M) α).continuous
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffHessianPhi (I := I) (M := M) g α φ i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffHessianPhi
    rw [hη_zero, zero_mul]
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hyKη : y ∈ Kη
  · have hyΩ : y ∈ Ω := hKη_sub_Ω hyKη
    have hH_cont_at : ContinuousAt (chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j) y :=
      (chartHessianPhiOnEuclid_continuousOn (I := I) (M := M) g α φ i j).continuousAt
        (hΩ_open.mem_nhds hyΩ)
    have hη_cont_at : ContinuousAt η y := hη_cont.continuousAt
    exact hη_cont_at.mul hH_cont_at
  · have h_nbd : (Kη)ᶜ ∈ 𝓝 y :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hyKη
    have h_eventually_zero :
        cutoffHessianPhi (I := I) (M := M) g α φ i j =ᶠ[𝓝 y]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [h_nbd] with z hz
      exact h_zero_off z hz
    exact (continuousAt_const (y := (0 : ℝ))).congr h_eventually_zero.symm

private lemma cutoffHessianPhi_bounded
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN,
      |cutoffHessianPhi (I := I) (M := M) g α φ i j y| ≤ C := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have h_cont : Continuous (cutoffHessianPhi (I := I) (M := M) g α φ i j) :=
    cutoffHessianPhi_continuous (I := I) (M := M) g α φ i j
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffHessianPhi (I := I) (M := M) g α φ i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffHessianPhi
    rw [hη_zero, zero_mul]
  by_cases hKη_ne : Kη.Nonempty
  · have h_norm_cont : ContinuousOn
        (fun y : EuclN => ‖cutoffHessianPhi (I := I) (M := M) g α φ i j y‖) Kη :=
      h_cont.continuousOn.norm
    obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
      hKη_compact.exists_isMaxOn hKη_ne h_norm_cont
    set C := ‖cutoffHessianPhi (I := I) (M := M) g α φ i j y₀‖ with hC_def
    have hC_nn : 0 ≤ C := norm_nonneg _
    refine ⟨C, hC_nn, ?_⟩
    intro y
    by_cases hyK : y ∈ Kη
    · have h := hy₀_max hyK
      have h_eq : |cutoffHessianPhi (I := I) (M := M) g α φ i j y| =
          ‖cutoffHessianPhi (I := I) (M := M) g α φ i j y‖ := rfl
      rw [h_eq]; exact h
    · rw [h_zero_off y hyK, abs_zero]; exact hC_nn
  · refine ⟨0, le_refl 0, ?_⟩
    intro y
    have hy_notK : y ∉ Kη := fun hyK => hKη_ne ⟨y, hyK⟩
    rw [h_zero_off y hy_notK, abs_zero]

private lemma cutoffHessianPhi_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E))
    (μ : Measure EuclN) :
    AEStronglyMeasurable (cutoffHessianPhi (I := I) (M := M) g α φ i j) μ :=
  (cutoffHessianPhi_continuous (I := I) (M := M) g α φ i j).aestronglyMeasurable

private lemma hessPairingChartLocal_ae_eq_cutoff
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    hessPairingChartLocal (I := I) (M := M) g α φ hu_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              cutoffInvGram (I := I) (M := M) g α i k y *
                cutoffInvGram (I := I) (M := M) g α j l y *
                cutoffHessianPhi (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  set V : Set EuclN := Ω \ K with hV_def
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hV_meas : MeasurableSet V := hΩ_meas.diff hK_meas
  have h_pt_K : ∀ y ∈ K, ∀ i j k l : Fin (Module.finrank ℝ E),
      invGramOnEuclid (I := I) g α i k y *
          invGramOnEuclid (I := I) g α j l y *
          chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y =
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          cutoffHessianPhi (I := I) (M := M) g α φ i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y := by
    intro y hy i j k l
    have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
      chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
    unfold cutoffInvGram cutoffHessianPhi
    rw [hη_one]; ring
  have hae_zero_all : ∀ᵐ y ∂(volume : Measure EuclN),
      ∀ (k l : Fin (Module.finrank ℝ E)), y ∈ V →
        laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 := by
    have h_pair_ae : ∀ (p : Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E)),
        ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h p.1 p.2 y = 0 := by
      intro p
      have h := laplacianDomainHessianChart_ae_zero_off_support
        (I := I) (M := M) g α hu_h p.1 p.2
      have := (ae_restrict_iff' hV_meas).mp h
      filter_upwards [this] with y hy hyV
      exact hy hyV
    have h_all : ∀ᵐ y ∂(volume : Measure EuclN),
        ∀ (p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          y ∈ V →
            laplacianDomainHessianChart (I := I) (M := M) g α hu_h p.1 p.2 y = 0 :=
      ae_all_iff.mpr h_pair_ae
    filter_upwards [h_all] with y hy k l hyV
    exact hy ⟨k, l⟩ hyV
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  filter_upwards [hae_zero_all] with y hy_zeros hyΩ
  by_cases hyK : y ∈ K
  · rw [hessPairingChartLocal_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    exact h_pt_K y hyK i j k l
  · have hyV : y ∈ V := ⟨hyΩ, hyK⟩
    rw [hessPairingChartLocal_def]
    have h_LHS_zero : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro k _
      refine Finset.sum_eq_zero ?_
      intro l _
      have hH_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 :=
        hy_zeros k l hyV
      rw [hH_zero, mul_zero]
    have h_RHS_zero : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              cutoffInvGram (I := I) (M := M) g α i k y *
                cutoffInvGram (I := I) (M := M) g α j l y *
                cutoffHessianPhi (I := I) (M := M) g α φ i j y *
                laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro k _
      refine Finset.sum_eq_zero ?_
      intro l _
      have hH_zero : laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y = 0 :=
        hy_zeros k l hyV
      rw [hH_zero, mul_zero]
    rw [h_LHS_zero, h_RHS_zero]

private lemma cutoffSummand_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y : EuclN =>
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          cutoffHessianPhi (I := I) (M := M) g α φ i j y *
          laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨C_ik, hC_ik_nn, hC_ik_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α i k
  obtain ⟨C_jl, hC_jl_nn, hC_jl_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α j l
  obtain ⟨C_φ, hC_φ_nn, hC_φ_bd⟩ :=
    cutoffHessianPhi_bounded (I := I) (M := M) g α φ i j
  set Ctot := C_ik * C_jl * C_φ with hCtot_def
  have hCtot_nn : 0 ≤ Ctot := by
    rw [hCtot_def]
    exact mul_nonneg (mul_nonneg hC_ik_nn hC_jl_nn) hC_φ_nn
  have h_H_lp : MemLp (laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    laplacianDomainHessianChart_memLp_two (I := I) (M := M) g α hu_h k l
  set bdd_fn : EuclN → ℝ := fun y =>
    Ctot * |laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y|
    with hbdd_def
  have h_abs_H : MemLp (fun y => |laplacianDomainHessianChart
      (I := I) (M := M) g α hu_h k l y|) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := h_H_lp.abs
  have hbdd_memLp : MemLp bdd_fn 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := h_abs_H.const_mul Ctot
  refine MemLp.mono hbdd_memLp ?_ ?_
  · have h_aesm_ik : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α i k)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffInvGram_aestronglyMeasurable (I := I) (M := M) g α i k _
    have h_aesm_jl : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α j l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffInvGram_aestronglyMeasurable (I := I) (M := M) g α j l _
    have h_aesm_φ : AEStronglyMeasurable
        (cutoffHessianPhi (I := I) (M := M) g α φ i j)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffHessianPhi_aestronglyMeasurable (I := I) (M := M) g α φ i j _
    have h_aesm_H : AEStronglyMeasurable
        (laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_H_lp.aestronglyMeasurable
    exact ((h_aesm_ik.mul h_aesm_jl).mul h_aesm_φ).mul h_aesm_H
  · refine Filter.Eventually.of_forall ?_
    intro y
    simp only [Real.norm_eq_abs, hbdd_def]
    set H := laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y with hH_def
    set Gik := cutoffInvGram (I := I) (M := M) g α i k y with hGik_def
    set Gjl := cutoffInvGram (I := I) (M := M) g α j l y with hGjl_def
    set Hφ := cutoffHessianPhi (I := I) (M := M) g α φ i j y with hHφ_def
    have h_abs_prod : |Gik * Gjl * Hφ * H| = |Gik| * |Gjl| * |Hφ| * |H| := by
      rw [abs_mul, abs_mul, abs_mul]
    rw [h_abs_prod]
    have h_bd_ik := hC_ik_bd y
    have h_bd_jl := hC_jl_bd y
    have h_bd_φ := hC_φ_bd y
    have h_H_nn : (0 : ℝ) ≤ |H| := abs_nonneg _
    have h_step1 : |Gik| * |Gjl| ≤ C_ik * C_jl := by
      calc |Gik| * |Gjl|
          ≤ C_ik * |Gjl| := mul_le_mul_of_nonneg_right h_bd_ik (abs_nonneg _)
        _ ≤ C_ik * C_jl := mul_le_mul_of_nonneg_left h_bd_jl hC_ik_nn
    have h_step2 : |Gik| * |Gjl| * |Hφ| ≤ C_ik * C_jl * C_φ :=
      calc |Gik| * |Gjl| * |Hφ|
          ≤ (C_ik * C_jl) * |Hφ| := mul_le_mul_of_nonneg_right h_step1 (abs_nonneg _)
        _ ≤ (C_ik * C_jl) * C_φ := mul_le_mul_of_nonneg_left h_bd_φ
              (mul_nonneg hC_ik_nn hC_jl_nn)
    have h_step3 : |Gik| * |Gjl| * |Hφ| * |H| ≤ Ctot * |H| := by
      rw [hCtot_def]
      exact mul_le_mul_of_nonneg_right h_step2 h_H_nn
    have h_rhs_nn : (0 : ℝ) ≤ Ctot * |H| := mul_nonneg hCtot_nn h_H_nn
    have h_abs_rhs : abs (Ctot * |H|) = Ctot * |H| := abs_of_nonneg h_rhs_nn
    rw [h_abs_rhs]
    exact h_step3

theorem hessPairingChartLocal_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingChartLocal (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_ae := hessPairingChartLocal_ae_eq_cutoff
    (I := I) (M := M) g α φ hu_h
  have h_cutoff_memLp : MemLp (fun y : EuclN =>
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                cutoffInvGram (I := I) (M := M) g α i k y *
                  cutoffInvGram (I := I) (M := M) g α j l y *
                  cutoffHessianPhi (I := I) (M := M) g α φ i j y *
                  laplacianDomainHessianChart (I := I) (M := M) g α hu_h k l y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun j _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun k _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => ?_)
    exact cutoffSummand_memLp_two (I := I) (M := M) g α φ hu_h i j k l
  exact MemLp.ae_eq h_ae.symm h_cutoff_memLp

noncomputable def hessPairingChartLocalLp
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (hessPairingChartLocal_memLp_two (I := I) (M := M) g α φ hu_h).toLp _

@[simp] lemma hessPairingChartLocalLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (hessPairingChartLocalLp (I := I) (M := M) g α φ hu_h :
        Lp ℝ 2 ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h :=
  MemLp.coeFn_toLp _

private noncomputable def hessPairingChartLocalMExt
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  hessPairingChartLocal (I := I) (M := M) g α φ hu_h
    ((toEuclidean (E := E)) (extChartAt I α x))

omit [NeZero (Module.finrank ℝ E)] in
lemma hessPairingChartLocalMExt_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    hessPairingChartLocalMExt (I := I) (M := M) g φ α hu_h x =
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h
        ((toEuclidean (E := E)) (extChartAt I α x)) := rfl

noncomputable def hessPairingMChartContribution
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  (chartAtlasPOU I M α : M → ℝ) x *
    hessPairingChartLocalMExt (I := I) (M := M) g φ α hu_h x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma hessPairingMChartContribution_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocalMExt (I := I) (M := M) g φ α hu_h x := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma hessPairingMChartContribution_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ tsupport ((chartAtlasPOU I M α : M → ℝ))) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x = 0 := by
  unfold hessPairingMChartContribution
  have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  rw [hρ_zero, zero_mul]

noncomputable def hessPairingMOnLapDom
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma hessPairingMOnLapDom_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    hessPairingMOnLapDom (I := I) (M := M) g φ hu_h x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x := rfl

private noncomputable def hessPairingChartLocalRep
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) : EuclN → ℝ :=
  (hessPairingChartLocalLp (I := I) (M := M) g α φ hu_h :
    Lp ℝ 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)))

private lemma hessPairingChartLocalRep_stronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    StronglyMeasurable
      (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) :=
  Lp.stronglyMeasurable _

private lemma hessPairingChartLocalRep_measurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Measurable (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) :=
  (hessPairingChartLocalRep_stronglyMeasurable (I := I) (M := M) g α φ hu_h).measurable

private lemma hessPairingChartLocalRep_ae_eq
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h :=
  hessPairingChartLocalLp_coeFn (I := I) (M := M) g α φ hu_h

private lemma hessPairingChartLocalRep_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  Lp.memLp _

private noncomputable def chartContribSurrogate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  (chartAtlasPOU I M α : M → ℝ) x *
    DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold (I := I) α
      (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) x

private lemma chartContribSurrogate_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold (I := I) α
          (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartAtlasPOU_continuous (α : M) :
    Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartAtlasPOU_measurable (α : M) :
    Measurable fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
  (chartAtlasPOU_continuous (I := I) (M := M) α).measurable

private lemma chartContribSurrogate_measurable
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Measurable (chartContribSurrogate (I := I) (M := M) g φ α hu_h) := by
  classical
  refine Measurable.mul ?_ ?_
  · exact chartAtlasPOU_measurable (I := I) (M := M) α
  · exact DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_measurable
      (I := I) α (hessPairingChartLocalRep_measurable (I := I) (M := M) g α φ hu_h)

private lemma chartContribSurrogate_zero_off_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h x = 0 := by
  classical
  unfold chartContribSurrogate
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_apply_of_notMem
    (I := I) α _ hx]
  ring

private lemma chartContribSurrogate_tsupport_subset
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    tsupport (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
      (chartAt H α).source := by
  classical
  have h_supp_sub : Function.support
      (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        (chartAt H α).source := by
    intro x hx
    by_contra h_notin
    apply hx
    exact chartContribSurrogate_zero_off_source
      (I := I) (M := M) g φ α hu_h h_notin
  have h_supp_in_pou : Function.support
      (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        Function.support fun x : M => (chartAtlasPOU I M α : M → ℝ) x := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hρ_zero
    apply hx
    unfold chartContribSurrogate
    rw [hρ_zero]; ring
  have h_tsupp_in_pou : tsupport
      (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    closure_mono h_supp_in_pou
  exact h_tsupp_in_pou.trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

private lemma chartContribSurrogate_eq_on_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h
          ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  classical
  unfold chartContribSurrogate
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_apply_of_mem
    (I := I) α _ hx]

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingMChartContribution_eq_on_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (_hx : x ∈ (chartAt H α).source) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocal (I := I) (M := M) g α φ hu_h
          ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  unfold hessPairingMChartContribution hessPairingChartLocalMExt
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingMChartContribution_zero_off_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    hessPairingMChartContribution (I := I) (M := M) g φ α hu_h x = 0 := by
  classical
  unfold hessPairingMChartContribution
  have hsub :
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hx_notsupp : x ∉ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h =>
    hx (hsub h)
  have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx_notsupp
  rw [hρ_zero]
  ring

private lemma hessPairingChartLocalRep_exists_null_superset
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∃ N : Set EuclN, MeasurableSet N ∧
      (volume : Measure EuclN) (N ∩ chartTargetEuclid (I := I) (M := M) α) = 0 ∧
      ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, y ∉ N →
        hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y =
        hessPairingChartLocal (I := I) (M := M) g α φ hu_h y := by
  classical
  have h_ae := hessPairingChartLocalRep_ae_eq (I := I) (M := M) g α φ hu_h
  set badSet : Set EuclN := { y : EuclN |
      hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y ≠
      hessPairingChartLocal (I := I) (M := M) g α φ hu_h y } with hbadSet_def
  have h_bad_null : ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)) badSet = 0 := h_ae
  obtain ⟨N, h_bad_sub_N, hN_meas, hN_null⟩ :=
    exists_measurable_superset_of_null h_bad_null
  refine ⟨N, hN_meas, ?_, ?_⟩
  · rw [MeasureTheory.Measure.restrict_apply hN_meas] at hN_null
    exact hN_null
  · intro y hy_in_target hy_notN
    have hy_not_bad : y ∉ badSet := fun hyb => hy_notN (h_bad_sub_N hyb)
    by_contra h_ne
    exact hy_not_bad h_ne

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem riemannianVolumeMeasure_pullback_null
    (g : SmoothRiemannianMetric I M) (α : M)
    {N : Set EuclN} (hN_meas : MeasurableSet N)
    (hN_null : (volume : Measure EuclN)
      (N ∩ chartTargetEuclid (I := I) (M := M) α) = 0) :
    (riemannianVolumeMeasure (I := I) (M := M) g)
      ((chartAt H α).source ∩
        { x : M | (toEuclidean (E := E)) ((extChartAt I α) x) ∈ N }) = 0 := by
  classical
  set NM : Set M := (chartAt H α).source ∩
    { x : M | (toEuclidean (E := E)) ((extChartAt I α) x) ∈ N } with hNM_def
  have h_src_meas : MeasurableSet ((chartAt H α).source) :=
    ((chartAt H α).open_source).measurableSet
  have h_extChartExt_meas : Measurable
      (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt_measurable
      (I := I) α
  have h_toE_meas : Measurable (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).continuous.measurable
  have h_comp_meas : Measurable
      (fun x : M => (toEuclidean (E := E))
        (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α x)) :=
    h_toE_meas.comp h_extChartExt_meas
  have h_preim_meas : MeasurableSet
      { x : M | (toEuclidean (E := E))
        (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α x) ∈ N } :=
    h_comp_meas hN_meas
  have hNM_eq : NM = (chartAt H α).source ∩
      { x : M | (toEuclidean (E := E))
        (DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt (I := I) α x) ∈ N } := by
    apply Set.eq_of_subset_of_subset
    · intro x ⟨hx_src, hx_N⟩
      refine ⟨hx_src, ?_⟩
      simp only [Set.mem_setOf_eq]
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt_apply_of_mem
        (I := I) α hx_src]
      exact hx_N
    · intro x ⟨hx_src, hx_N⟩
      refine ⟨hx_src, ?_⟩
      simp only [Set.mem_setOf_eq]
      simp only [Set.mem_setOf_eq] at hx_N
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.extChartAtExt_apply_of_mem
        (I := I) α hx_src] at hx_N
      exact hx_N
  have hNM_meas : MeasurableSet NM := by
    rw [hNM_eq]; exact h_src_meas.inter h_preim_meas
  have h_meas_as_lint : (riemannianVolumeMeasure (I := I) (M := M) g) NM =
      ∫⁻ a, NM.indicator (fun _ : M => (1 : ℝ≥0∞)) a
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [MeasureTheory.lintegral_indicator_const hNM_meas (1 : ℝ≥0∞)]
    rw [one_mul]
  rw [h_meas_as_lint]
  have hF_supp : ∀ x : M, x ∉ (chartAt H α).source →
      NM.indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := by
    intro x hx
    have hx_notNM : x ∉ NM := fun hxNM => hx hxNM.1
    exact Set.indicator_of_notMem hx_notNM _
  have hF_meas : Measurable (NM.indicator (fun _ => (1 : ℝ≥0∞))) :=
    Measurable.indicator measurable_const hNM_meas
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Chart.riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hF_meas hF_supp
  change ∫⁻ x, NM.indicator (fun _ : M => (1 : ℝ≥0∞)) x
      ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) = 0
  rw [h_bridge]
  have h_via :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartLocalMeasure_lintegral_via_chartTargetEuclid
      (I := I) (M := M) g α hF_meas
  rw [h_via]
  have h_setLInt_eq :
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            NM.indicator (fun _ : M => (1 : ℝ≥0∞))
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(volume : Measure EuclN) =
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y
          ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) ?_
    intro y hy_target
    have hy_target' : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rcases hy_target with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [h_eq]; exact hw_target
    have hx_in_src :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H α).source := by
      have : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target'
      rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at this
    have h_toE_extChart_x :
        (toEuclidean (E := E)) ((extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
      have h_extChart_inv : (extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            (toEuclidean (E := E)).symm y :=
        (extChartAt I α).right_inv hy_target'
      rw [h_extChart_inv]
      exact (toEuclidean (E := E)).apply_symm_apply y
    have h_indic_eq : NM.indicator (fun _ : M => (1 : ℝ≥0∞))
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
          N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y := by
      by_cases hxNM : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ NM
      · rw [Set.indicator_of_mem hxNM]
        have hxN : (toEuclidean (E := E)) ((extChartAt I α)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ∈ N := hxNM.2
        rw [h_toE_extChart_x] at hxN
        rw [Set.indicator_of_mem hxN]
      · rw [Set.indicator_of_notMem hxNM]
        have h_not_in_preim : (toEuclidean (E := E)) ((extChartAt I α)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ∉ N := by
          intro h
          exact hxNM ⟨hx_in_src, h⟩
        rw [h_toE_extChart_x] at h_not_in_preim
        rw [Set.indicator_of_notMem h_not_in_preim]
    change ENNReal.ofReal _ * NM.indicator _ _ =
      ENNReal.ofReal _ * N.indicator _ _
    rw [h_indic_eq]
  rw [h_setLInt_eq]
  have h_factor_indicator : ∀ y : EuclN,
      ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y =
      N.indicator
        (fun y : EuclN => ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) y := by
    intro y
    by_cases hyN : y ∈ N
    · rw [Set.indicator_of_mem hyN, Set.indicator_of_mem hyN, mul_one]
    · rw [Set.indicator_of_notMem hyN, Set.indicator_of_notMem hyN, mul_zero]
  rw [show (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            N.indicator (fun _ : EuclN => (1 : ℝ≥0∞)) y
          ∂(volume : Measure EuclN)) =
    ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      N.indicator (fun y : EuclN => ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) y
          ∂(volume : Measure EuclN) from by
    refine MeasureTheory.lintegral_congr ?_
    intro y
    exact h_factor_indicator y]
  rw [show ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
      N.indicator (fun y : EuclN => ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) y
          ∂(volume : Measure EuclN) =
      ∫⁻ y in N ∩ chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
            (DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ∂(volume : Measure EuclN) from
    MeasureTheory.setLIntegral_indicator hN_meas _]
  rw [MeasureTheory.setLIntegral_measure_zero
    (N ∩ chartTargetEuclid (I := I) (M := M) α) _ hN_null, mul_zero]

private lemma chartContribSurrogate_ae_eq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    chartContribSurrogate (I := I) (M := M) g φ α hu_h =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      hessPairingMChartContribution (I := I) (M := M) g φ α hu_h := by
  classical
  obtain ⟨N, hN_meas, hN_null, hN_agree⟩ :=
    hessPairingChartLocalRep_exists_null_superset
      (I := I) (M := M) g α φ hu_h
  have hpre_null := riemannianVolumeMeasure_pullback_null
    (I := I) (M := M) g α hN_meas hN_null
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hpre_null
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_cases hx_src : x ∈ (chartAt H α).source
  · refine ⟨hx_src, ?_⟩
    simp only [Set.mem_setOf_eq]
    have h_y_in_target : (toEuclidean (E := E)) ((extChartAt I α) x) ∈
        chartTargetEuclid (I := I) (M := M) α := by
      refine ⟨(extChartAt I α) x, ?_, rfl⟩
      have : x ∈ (extChartAt I α).source := by
        rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
      exact (extChartAt I α).map_source this
    by_contra h_not_in_N
    have h_agree_at_y :=
      hN_agree _ h_y_in_target h_not_in_N
    apply hx
    rw [chartContribSurrogate_eq_on_source (I := I) (M := M) g φ α hu_h hx_src,
        hessPairingMChartContribution_eq_on_source (I := I) (M := M) g φ α hu_h hx_src,
        h_agree_at_y]
  · exfalso
    apply hx
    rw [chartContribSurrogate_zero_off_source (I := I) (M := M) g φ α hu_h hx_src,
        hessPairingMChartContribution_zero_off_source (I := I) (M := M) g φ α hu_h hx_src]

private lemma chartPushedRaw_chartContribSurrogate_le_rep
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (y : EuclN) :
    ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (chartContribSurrogate (I := I) (M := M) g φ α hu_h) y‖ₑ ≤
      ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy]
    have hy_target' : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rcases hy with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [h_eq]; exact hw_target
    have hx_src :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H α).source := by
      have : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target'
      rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at this
    rw [chartContribSurrogate_eq_on_source (I := I) (M := M) g φ α hu_h hx_src]
    have h_toE_extChart_x :
        (toEuclidean (E := E)) ((extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
      have h_extChart_inv : (extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            (toEuclidean (E := E)).symm y :=
        (extChartAt I α).right_inv hy_target'
      rw [h_extChart_inv]
      exact (toEuclidean (E := E)).apply_symm_apply y
    rw [h_toE_extChart_x]
    have h_nn : (0 : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
      (chartAtlasPOU I M).nonneg α _
    have h_le : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≤ 1 :=
      (chartAtlasPOU I M).le_one α _
    rw [enorm_mul]
    have h_abs_le_one : ‖(chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg h_nn]
      have : ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ≤
            ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_le
      rw [show ((1 : ℝ≥0∞)) = ENNReal.ofReal 1 by simp]
      exact this
    calc ‖(chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ *
            ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ
        ≤ 1 * ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := by
          gcongr
      _ = ‖hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := one_mul _
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy]
    simp

private lemma chartContribSurrogate_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (chartContribSurrogate (I := I) (M := M) g φ α hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_c_meas : Measurable (chartContribSurrogate (I := I) (M := M) g φ α hu_h) :=
    chartContribSurrogate_measurable (I := I) (M := M) g φ α hu_h
  have h_c_tsupp : tsupport (chartContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
      (chartAt H α).source :=
    chartContribSurrogate_tsupport_subset (I := I) (M := M) g φ α hu_h
  obtain ⟨C_α, hC_α_pos, hC_α_bnd⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw
      (I := I) (M := M) g α (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h_c_meas h_c_tsupp
  have h_chart_le : eLpNorm
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (chartContribSurrogate (I := I) (M := M) g φ α hu_h)) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) ≤
    eLpNorm (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    eLpNorm_mono_enorm
      (chartPushedRaw_chartContribSurrogate_le_rep
        (I := I) (M := M) g φ α hu_h)
  have h_rep_memLp := hessPairingChartLocalRep_memLp_two
    (I := I) (M := M) g α φ hu_h
  have h_rep_eLp_lt_top := h_rep_memLp.2
  refine ⟨h_c_meas.aestronglyMeasurable, ?_⟩
  calc eLpNorm (chartContribSurrogate (I := I) (M := M) g φ α hu_h) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ENNReal.ofReal C_α *
          eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (chartContribSurrogate (I := I) (M := M) g φ α hu_h)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hC_α_bnd
    _ ≤ ENNReal.ofReal C_α *
          eLpNorm (hessPairingChartLocalRep (I := I) (M := M) g α φ hu_h) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by gcongr
    _ < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_rep_eLp_lt_top

theorem hessPairingMChartContribution_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingMChartContribution (I := I) (M := M) g φ α hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_surr_memLp := chartContribSurrogate_memLp_two
    (I := I) (M := M) g φ α hu_h
  have h_ae_eq := chartContribSurrogate_ae_eq (I := I) (M := M) g φ α hu_h
  exact MemLp.ae_eq h_ae_eq h_surr_memLp

theorem hessPairingMOnLapDom_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (hessPairingMOnLapDom (I := I) (M := M) g φ hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  unfold hessPairingMOnLapDom
  refine memLp_finset_sum _ ?_
  intro α _
  exact hessPairingMChartContribution_memLp_two
    (I := I) (M := M) g φ α hu_h

noncomputable def hessPairingLpOnLapDom
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (hessPairingMOnLapDom_memLp_two (I := I) (M := M) g φ hu_h).toLp _

lemma hessPairingLpOnLapDom_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (hessPairingLpOnLapDom (I := I) (M := M) g φ hu_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      hessPairingMOnLapDom (I := I) (M := M) g φ hu_h :=
  MemLp.coeFn_toLp _

end HessianPairingLapDom
end Laplacian
end Analysis
end DifferentialGeometry

end
