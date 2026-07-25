import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedDataConstructor
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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

private abbrev K_α (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma K_α_compact (α : M) : IsCompact (K_α (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma K_α_meas (α : M) : MeasurableSet (K_α (I := I) (M := M) α) :=
  (K_α_compact (I := I) (M := M) α).isClosed.measurableSet

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma K_α_subset_target (α : M) :
    K_α (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTarget_diff_K_α_isOpen (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
  (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (K_α_compact (I := I) (M := M) α).isClosed

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma chartTarget_diff_K_α_subset_target (α : M) :
    chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := fun _ hy => hy.1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set EuclN}
    (_hΩ : IsOpen Ω) (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclN → ℝ}
    (hu : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω)
    (hu_ae_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hu_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u V := by
    refine ⟨?_, ?_⟩
    · exact hu.1.mono_measure
        (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub hg_weak
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V) u V :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hu_V i
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) u Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      hu i
  have h_partial_Ω_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub h_partial_Ω
  have h_chosen_V_zero :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V
        =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_ae_zero_of_ae_zero
      (d := Module.finrank ℝ E) hp hV hu_ae_zero_V i
  have hg_lp_Ω : MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hu i
  have hg_lp_Ω_V : MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
  have hg_loc_Ω_V : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω)
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V) p
      ((volume : Measure EuclN).restrict V) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      hu_V i
  have hgV_loc : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V)
      ((volume : Measure EuclN).restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) p i u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV h_partial_Ω_V h_partial_V
      hg_loc_Ω_V hgV_loc
  exact h_unique.trans h_chosen_V_zero

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_u_h_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  have h_diff_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy.1 hy.2

private lemma chosenWeakPartial_chartPushed_u_h_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  have h_w1p :=
    DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree.chartPushed_memW1p_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
  exact chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α)
    (chartTarget_diff_K_α_subset_target (I := I) (M := M) α)
    h_w1p (chartPushed_u_h_ae_zero_off_K_α (I := I) (M := M) g α u_h) i

private lemma chosenSecond_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E)) :
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set g_i : EuclN → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 i
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) with hg_i_def
  have h_pair := laplacianDomainPow_two_h2_plus_rhs_h2 (I := I) (M := M) g hu_h
  have h_memWkp_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) := h_pair.1.1 α
  have h_g_i_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 g_i
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_step := h_memWkp_2.chosenWeakPartial_mem i
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
      at h_step
    exact h_step
  have h_unfold : chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l g_i
        (chartTargetEuclid (I := I) (M := M) α) := rfl
  rw [h_unfold]
  have h_g_i_ae :=
    chosenWeakPartial_chartPushed_u_h_ae_zero_off_K_α
      (I := I) (M := M) g α hu_h i
  exact chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α)
    (chartTarget_diff_K_α_subset_target (I := I) (M := M) α)
    h_g_i_memW1p h_g_i_ae l

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma weakPartial_ae_zero_on_open_subset_of_ae_zero
    {Ω U : Set EuclN} (hΩ_open : IsOpen Ω) (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ω)
    {f w : EuclN → ℝ}
    (i : Fin (Module.finrank ℝ E))
    (hw_isWeak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i w f Ω)
    (hw_li : LocallyIntegrableOn w U (volume : Measure EuclN))
    (hf_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict U), f y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict U), w y = 0 := by
  classical
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hf_ae_zero_vol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → f y = 0 := by
    rw [← ae_restrict_iff' hU_meas]; exact hf_ae_zero
  have h_target : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → w y = 0 := by
    apply hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw_li
    intro ψ hψ_smooth hψ_cs hψ_supp
    have hψ_supp_Ω : tsupport ψ ⊆ Ω := hψ_supp.trans hU_sub
    have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
    have h_weak := hw_isWeak ψ hψ_smooth hψ_cs hψ_supp_Ω
    have h_f_supp_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1) = 0 := by
      refine (ae_restrict_iff' hΩ_meas).mpr ?_
      filter_upwards [hf_ae_zero_vol] with y hy _hyΩ
      by_cases hy_U : y ∈ U
      · rw [hy hy_U]; ring
      · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
          (isClosed_tsupport _).isOpen_compl
        have h_y_not_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp h)
        have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds h_y_not_supp] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
          have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
          rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
        rw [h_fderiv_zero]; simp
    have h_zero_lhs :
        ∫ y in Ω, f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
          ∂(volume : Measure EuclN) = 0 := by
      rw [MeasureTheory.integral_congr_ae h_f_supp_ae]; simp
    rw [h_zero_lhs] at h_weak
    have h_rhs_zero :
        ∫ y in Ω, w y * ψ y ∂(volume : Measure EuclN) = 0 := by linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • w x = 0 := fun x hx => by
      have hx_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_Ω h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_rhs_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target] with y hy hy_U
  exact hy hy_U

omit [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrableOn_of_locally_memLp_two_chart
    (_g : SmoothRiemannianMetric I M) (α : M)
    {f : EuclN → ℝ}
    (hf : ∀ K : Set EuclN, IsCompact K →
      K ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f 2 ((volume : Measure EuclN).restrict K)) :
    LocallyIntegrableOn f
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  intro x hx
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2)
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset : B ⊆ chartTargetEuclid (I := I) (M := M) α \
      K_α (I := I) (M := M) α := by
    intro y hy; apply hr_subset
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
  have hB_subset_Ω : B ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hB_subset hy).1
  have hf_K : MemLp f 2 ((volume : Measure EuclN).restrict B) :=
    hf B hB_compact hB_subset_Ω
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn f B (volume : Measure EuclN) :=
    hf_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x
    (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall

private lemma chosenThird_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l j : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l j y = 0 := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_isWeak :=
    chosenThirdMixedPartialChartPushedU_isWeakPartial
      (I := I) (M := M) g α hu_h i l j
  have hf_ae := chosenSecond_ae_zero_off_K_α (I := I) (M := M) g α hu_h i l
  have hw_li : LocallyIntegrableOn
      (chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l j)
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two_chart (I := I) (M := M) g α
      (fun K hK hK_in =>
        chosenThirdMixedPartialChartPushedU_locally_memLp
          (I := I) (M := M) g α hu_h i l j hK hK_in)
  refine weakPartial_ae_zero_on_open_subset_of_ae_zero
    hΩ_open hU_open hU_sub (i := j) h_isWeak hw_li ?_
  exact hf_ae

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma vol_restrict_chart_target_absCont_weighted (α : M)
    (g : SmoothRiemannianMetric I M) :
    (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  intro A hA
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
      (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
      (chartTargetEuclid (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_chart_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chart_meas))] at hA
  rw [Measure.restrict_apply' h_chart_meas]
  rw [Measure.restrict_apply' h_chart_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

private lemma base_u_chart_ae_eq_chartPushed_on_vol
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := by
  have h_coeFn :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm.chartPushedLpFromLp_coeFn
      (I := I) (M := M) g α (H1ComplToLp (I := I) (M := M) g u_h)
  have h_v_abs_w := vol_restrict_chart_target_absCont_weighted (I := I) (M := M)
    (α := α) g
  exact h_v_abs_w.ae_le h_coeFn

private lemma base_u_chart_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart y = 0 := by
  classical
  have h_aeEq := base_u_chart_ae_eq_chartPushed_on_vol (I := I) (M := M) g α hu_h
  have h_abs : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) :=
    MeasureTheory.Measure.absolutelyContinuous_of_le
      (MeasureTheory.Measure.restrict_mono
        (chartTarget_diff_K_α_subset_target (I := I) (M := M) α) le_rfl)
  have h_aeEq_restrict := h_abs.ae_le h_aeEq
  have h_diff_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  filter_upwards [(ae_restrict_iff' h_diff_meas).mp h_aeEq_restrict]
    with y hy hy_diff
  rw [hy hy_diff]
  exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy_diff.1 hy_diff.2

private lemma base_weak_partial_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).weak_partial i y = 0 := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_isWeak := D.weak_partial_isWeakPartial i
  have hw_li : LocallyIntegrableOn (D.weak_partial i)
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two_chart (I := I) (M := M) g α
      (fun K' hK' hK'_in => D.weak_partial_locally_memLp i K' hK' hK'_in)
  have hf_ae := base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
  exact weakPartial_ae_zero_on_open_subset_of_ae_zero
    hΩ_open hU_open hU_sub (i := i) h_isWeak hw_li hf_ae

private lemma base_f_chart_locally_memLp_helper
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart) 2
      ((volume : Measure EuclN).restrict K) :=
  base_f_chart_locally_memLp (I := I) (M := M) g α hu_h hK_compact
    hK_compact.isClosed.measurableSet hK_in

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma memLp_top_of_continuousOn_on_compact_chart
    (_g : SmoothRiemannianMetric I M) (α : M)
    {h : EuclN → ℝ}
    (hh_contOn : ContinuousOn h (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp h ∞ ((volume : Measure EuclN).restrict K) := by
  classical
  by_cases hK_empty : K = ∅
  · subst hK_empty
    rw [MeasureTheory.Measure.restrict_empty]
    refine ⟨?_, ?_⟩
    · exact aestronglyMeasurable_zero_measure h
    · simp
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_K_cont : ContinuousOn h K := hh_contOn.mono hK_in
  have h_abs_K : ContinuousOn (fun y => |h y|) K :=
    continuous_abs.comp_continuousOn h_K_cont
  obtain ⟨y_max, _hy_max_K, h_max⟩ :=
    hK_compact.exists_isMaxOn hK_ne h_abs_K
  set C : ℝ := |h y_max|
  have hC_bd : ∀ y ∈ K, |h y| ≤ C := fun y hy => h_max hy
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_meas : AEStronglyMeasurable h ((volume : Measure EuclN).restrict K) :=
    h_K_cont.aestronglyMeasurable hK_meas
  have h_ae_bd : ∀ᵐ y ∂((volume : Measure EuclN).restrict K), |h y| ≤ C := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact hC_bd y hy
  refine ⟨h_meas, ?_⟩
  rw [eLpNorm_exponent_top]
  refine lt_of_le_of_lt ?_
    (show (ENNReal.ofReal (max C 0) : ℝ≥0∞) < ⊤ from
      ENNReal.ofReal_lt_top)
  refine eLpNormEssSup_le_of_ae_enorm_bound (C := ENNReal.ofReal (max C 0)) ?_
  refine h_ae_bd.mono (fun y hy => ?_)
  rw [Real.enorm_eq_ofReal_abs]
  apply ENNReal.ofReal_le_ofReal
  exact hy.trans (le_max_left _ _)

private lemma base_f_chart_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).f_chart y = 0 := by
  classical
  set D := chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  set U : Set EuclN := Ω \ K_α (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have h_density_contOn : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_continuousOn (I := I) g α
  have h_prod_locInt : LocallyIntegrableOn
      (fun y => densityOnEuclid (I := I) g α y * D.f_chart y) U
      (volume : Measure EuclN) := by
    intro x hx
    obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
    set B : Set EuclN := Metric.closedBall x (r / 2)
    have hB_compact : IsCompact B := isCompact_closedBall _ _
    have hB_subset_U : B ⊆ U := by
      intro y hy; apply hr_subset
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
    have hB_subset_Ω : B ⊆ Ω := fun y hy => hU_sub (hB_subset_U hy)
    have h_fchart_K_memLp := base_f_chart_locally_memLp_helper
      (I := I) (M := M) g α hu_h hB_compact hB_subset_Ω
    have h_density_memLp_top := memLp_top_of_continuousOn_on_compact_chart
      (I := I) (M := M) g α h_density_contOn hB_compact hB_subset_Ω
    have h_prod_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
        D.f_chart y) 2 ((volume : Measure EuclN).restrict B) :=
      MemLp.mul' (p := ∞) (q := 2) (r := 2) h_fchart_K_memLp h_density_memLp_top
    have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
    haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hB_finite
    have h_int : IntegrableOn (fun y => densityOnEuclid (I := I) g α y *
        D.f_chart y) B (volume : Measure EuclN) :=
      h_prod_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    refine ⟨B, ?_, h_int⟩
    refine Filter.mem_inf_of_left ?_
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x
      (by linarith : 0 < r / 2))
    exact Metric.ball_subset_closedBall
  have h_zero_for_test : ∀ ψ : EuclN → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∫ y, ψ y • (densityOnEuclid (I := I) g α y * D.f_chart y)
        ∂(volume : Measure EuclN) = 0 := by
    intro ψ hψ_smooth hψ_cs hψ_supp_U
    have hψ_supp_chart : tsupport ψ ⊆ Ω := hψ_supp_U.trans hU_sub
    have h_var := D.variational_identity ψ hψ_smooth hψ_cs hψ_supp_chart
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
        ∂(volume : Measure EuclN) at h_var
    have h_principal_zero :
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_wp_each : ∀ i : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
              D.weak_partial i y = 0 := fun i =>
          base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α hu_h i
        have h_wp_all_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            ∀ i : Fin (Module.finrank ℝ E),
              y ∈ U → D.weak_partial i y = 0 := by
          rw [ae_all_iff]; intro i
          rw [← ae_restrict_iff' hU_meas]
          exact h_wp_each i
        filter_upwards [h_wp_all_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [hy i hy_U]; ring
        · have h_y_not_in_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp_U h)
          have h_compl_open : IsOpen (tsupport ψ)ᶜ :=
            (isClosed_tsupport _).isOpen_compl
          have h_zero_nbhd : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
            filter_upwards [h_compl_open.mem_nhds h_y_not_in_supp] with z hz
            exact image_eq_zero_of_notMem_tsupport hz
          have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
            have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_nbhd
            rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
          refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [h_fderiv_zero]; simp
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    have h_mass_zero :
        ∫ y in Ω, densityOnEuclid (I := I) g α y * D.u_chart y * ψ y
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => densityOnEuclid (I := I) g α y * D.u_chart y * ψ y) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_uc_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
            D.u_chart y = 0 :=
          base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
        have h_uc_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            y ∈ U → D.u_chart y = 0 := by
          rw [← ae_restrict_iff' hU_meas]; exact h_uc_ae
        filter_upwards [h_uc_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · rw [hy hy_U]; ring
        · have h_y_not_in_supp : y ∉ tsupport ψ := fun h => hy_U (hψ_supp_U h)
          have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_in_supp
          rw [hψ_y]; ring
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    rw [h_principal_zero, h_mass_zero] at h_var
    have h_fchart_int_zero :
        ∫ y in Ω, densityOnEuclid (I := I) g α y * D.f_chart y * ψ y
          ∂(volume : Measure EuclN) = 0 := by
      linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • (densityOnEuclid (I := I) g α x *
        D.f_chart x) = 0 := fun x hx => by
      have hx_supp : x ∉ tsupport ψ := fun h => hx (hψ_supp_chart h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_supp
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_fchart_int_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  have h_cf_vol : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ U → densityOnEuclid (I := I) g α y * D.f_chart y = 0 :=
    hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_prod_locInt h_zero_for_test
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_cf_vol] with y hy hy_U
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_U.1
  have h_eq : densityOnEuclid (I := I) g α y * D.f_chart y = 0 := hy hy_U
  have h_ne : densityOnEuclid (I := I) g α y ≠ 0 := ne_of_gt h_pos
  exact (mul_eq_zero.mp h_eq).resolve_left h_ne

private lemma chosenFChartDeriv_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y = 0 := by
  classical
  have hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_memW1p :=
    base_f_chart_memW1p_from_residual_memW1p (I := I) (M := M) g α hu_h
      (fChartResidual_memW1p_truly_unconditional (I := I) (M := M) g α hu_h)
  have h_base_fc_ae := base_f_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  exact chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
    (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hU_open hU_sub
    h_memW1p h_base_fc_ae l

private lemma fChartDeriv2_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y = 0 := by
  classical
  have hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_chosenFC_ae := chosenFChartDeriv_ae_zero_off_K_α
    (I := I) (M := M) g α hu_h l₁
  have h_chosen :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_on_open_subset_of_ae_zero
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hU_open hU_sub
      h_chosenFChartDeriv_memW1p h_chosenFC_ae l₂
  change ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 l₂
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α) y = 0
  exact h_chosen

private lemma fChartEffTwiceNumerator_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y = 0 := by
  classical
  have h_uc := base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  have h_fc := base_f_chart_ae_zero_off_K_α (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  have h_wp_each : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i y = 0 := fun i =>
    base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i
  have h_sec_each : ∀ i j : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y = 0 := by
    intro i j
    exact chosenSecond_ae_zero_off_K_α (I := I) (M := M) g α hu_h i j
  have h_third_each : ∀ i l j : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l j y = 0 := by
    intro i l j
    exact chosenThird_ae_zero_off_K_α (I := I) (M := M) g α hu_h i l j
  have h_fcDeriv : ∀ l : Fin (Module.finrank ℝ E),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y = 0 := fun l =>
    chosenFChartDeriv_ae_zero_off_K_α (I := I) (M := M) g α hu_h l
  have h_fcDeriv2 :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      fChartDeriv2 (I := I) (M := M) g α hu_h l₁ l₂ y = 0 :=
    fChartDeriv2_ae_zero_off_K_α (I := I) (M := M) g α hu_h l₁ l₂
      h_chosenFChartDeriv_memW1p
  have hU_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  have h_wp_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i, (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i y = 0 := by
    rw [ae_all_iff]; exact h_wp_each
  have h_sec_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i j, chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact h_sec_each i
  have h_third_l1_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i j, chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact h_third_each i l₁ j
  have h_third_l2_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      ∀ i j, chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y = 0 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact h_third_each i l₂ j
  filter_upwards [h_uc, h_fc, h_wp_all, h_sec_all, h_third_l1_all, h_third_l2_all,
    h_fcDeriv l₁, h_fcDeriv l₂, h_fcDeriv2]
    with y hy_uc hy_fc hy_wp hy_sec hy_third1 hy_third2 hy_fcD1 hy_fcD2 hy_fcD12
  unfold effectiveSourceChartSecondOrderNumerator
  have h_A1_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₂) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁ y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro _ _
    rw [hy_sec i l₁]; ring
  have h_A2_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₂ y *
            chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ j y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_third1 i j]; ring
  have h_C1_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂) y)
              (EuclideanSpace.single j 1) *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial i y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro _ _
    rw [hy_wp i]; ring
  have h_C2_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramSecondDerivOnEuclid (I := I) g α i j l₁ l₂ y *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_sec i j]; ring
  have h_C3_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l₁) y)
              (EuclideanSpace.single j 1) *
            chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₂ y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro _ _
    rw [hy_sec i l₂]; ring
  have h_C4_zero :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
            chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₂ j y) = 0 := by
    refine Finset.sum_eq_zero ?_; intro i _
    refine Finset.sum_eq_zero ?_; intro j _
    rw [hy_third2 i j]; ring
  rw [h_A1_zero, h_A2_zero, h_C1_zero, h_C2_zero, h_C3_zero, h_C4_zero,
      hy_wp l₁, hy_wp l₂, hy_fcD1, hy_fcD2, hy_fcD12, hy_uc, hy_fc]
  ring

lemma integral_fChartEffTwiceNumerator_eq_integral_density_fChartEffTwice
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (h_chosenFChartDeriv_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
        (chartTargetEuclid (I := I) (M := M) α))
    (ψ : EuclN → ℝ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y
        ∂(volume : Measure EuclN) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hU_meas : MeasurableSet (Ω \ K_α (I := I) (M := M) α) :=
    hΩ_meas.diff (K_α_meas (I := I) (M := M) α)
  have h_ae_eq : (fun y : EuclN =>
      effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y) =ᵐ[
      (volume : Measure EuclN).restrict Ω]
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
        effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y) := by
    have h_numer_off := fChartEffTwiceNumerator_ae_zero_off_K_α
      (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p
    refine (ae_restrict_iff' hΩ_meas).mpr ?_
    have h_off_vol : ∀ᵐ y ∂(volume : Measure EuclN),
        y ∈ Ω \ K_α (I := I) (M := M) α →
        effectiveSourceChartSecondOrderNumerator (I := I) (M := M) g α l₁ l₂ hu_h y = 0 := by
      rw [← ae_restrict_iff' hU_meas]; exact h_numer_off
    filter_upwards [h_off_vol] with y hy hy_Ω
    by_cases hy_K : y ∈ K_α (I := I) (M := M) α
    · have h_pt := density_mul_fChartEffTwice_eq_indicator_numerator
        (I := I) (M := M) g α l₁ l₂ hu_h y hy_Ω
      rw [Set.indicator_of_mem hy_K] at h_pt
      rw [h_pt]
    · have hy_diff : y ∈ Ω \ K_α (I := I) (M := M) α := ⟨hy_Ω, hy_K⟩
      have h_pt := density_mul_fChartEffTwice_eq_indicator_numerator
        (I := I) (M := M) g α l₁ l₂ hu_h y hy_Ω
      rw [Set.indicator_of_notMem hy_K] at h_pt
      rw [hy hy_diff]
      have h_rhs_zero :
          densityOnEuclid (I := I) g α y *
          effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y = 0 := by
        rw [show densityOnEuclid (I := I) g α y *
            effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y * ψ y =
            (densityOnEuclid (I := I) g α y *
              effectiveSourceChartSecondOrder (I := I) (M := M) g α l₁ l₂ hu_h y) * ψ y from rfl]
        rw [h_pt]; ring
      linarith
  exact MeasureTheory.integral_congr_ae h_ae_eq

end TwiceDifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
