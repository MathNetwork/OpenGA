import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedDataConstructor
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedH2Interior
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThree
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplViaH3
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK


noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedMemWkpThreeSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplDataCanonical
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH2Interior
open DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpThree
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem MemWkp_two_extend_via_cutoff
    (k : ℕ)
    {Ω Ω' K : Set EuclN}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hΩ'_in_Ω : Ω' ⊆ Ω)
    (hK_compact : IsCompact K) (hK_in_Ω' : K ⊆ Ω')
    {u : EuclN → ℝ}
    (hu_local : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω')
    (hu_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ K)),
      u y = 0) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 u Ω := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_in_Ω', hη_smooth, hη_compact_support, hη_range,
    hη_one_on_cthick, hη_tsupp_in_Ω'⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact hΩ'_open hK_in_Ω'
  obtain ⟨C, hC_nn, hη_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hη_smooth hη_compact_support k
  have h_eta_u_in_Ω' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω' :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ'_open hη_smooth
      (fun j _hj x _hx => hη_bound x j _hj) hu_local
  have h_tsupp_prod_in_tsupp_eta : tsupport (fun x => η x * u x) ⊆ tsupport η := by
    refine closure_mono ?_
    intro x hx
    have hx_ne : η x * u x ≠ 0 := hx
    intro hx_eta_zero
    apply hx_ne
    rw [hx_eta_zero]
    ring
  have h_tsupp_prod_in_Ω' : tsupport (fun x => η x * u x) ⊆ Ω' :=
    h_tsupp_prod_in_tsupp_eta.trans hη_tsupp_in_Ω'
  have h_compactSupport_prod : HasCompactSupport (fun x => η x * u x) :=
    hη_compact_support.of_isClosed_subset (isClosed_tsupport _)
      h_tsupp_prod_in_tsupp_eta
  have h_eta_u_in_Ω : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k 2 (fun x => η x * u x) Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hΩ'_open hΩ_open hΩ'_in_Ω h_eta_u_in_Ω' h_tsupp_prod_in_Ω'
      h_compactSupport_prod
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set U_K : Set EuclN := Metric.cthickening δ K with hU_K_def
  have hU_K_compact : IsCompact U_K := hK_compact.cthickening
  have hU_K_closed : IsClosed U_K := Metric.isClosed_cthickening
  have hU_K_meas : MeasurableSet U_K := hU_K_closed.measurableSet
  have hK_in_U_K : K ⊆ U_K := Metric.self_subset_cthickening _
  have hU_K_in_Ω' : U_K ⊆ Ω' := hδ_in_Ω'
  have hU_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω'.trans hΩ'_in_Ω
  have h_eta_u_ae_eq_u : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict Ω] u := by
    have h_eq_on_U_K : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict U_K] u := by
      refine (ae_restrict_iff' hU_K_meas).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      have hx_eta : η x = 1 := hη_one_on_cthick x hx
      change η x * u x = u x
      rw [hx_eta]; ring
    have h_diff_meas : MeasurableSet (Ω \ U_K) := hΩ_meas.diff hU_K_meas
    have h_K_in_U_K : Ω \ U_K ⊆ Ω \ K := by
      intro x hx
      exact ⟨hx.1, fun hxK => hx.2 (hK_in_U_K hxK)⟩
    have hu_ae_zero_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ U_K)),
        u y = 0 := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ U_K) ≪
          (volume : Measure EuclN).restrict (Ω \ K) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_K_in_U_K le_rfl)
      exact h_abs.ae_le hu_ae_zero
    have h_eq_on_diff : (fun x => η x * u x) =ᵐ[(volume : Measure EuclN).restrict (Ω \ U_K)] u := by
      filter_upwards [hu_ae_zero_diff] with x hx
      rw [hx]; ring
    have h_cover : Ω = U_K ∪ (Ω \ U_K) := by
      ext x; constructor
      · intro hx
        by_cases h : x ∈ U_K
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact hU_K_in_Ω hx
        · exact hx.1
    have h_U_K_in_Ω : U_K ⊆ Ω := hU_K_in_Ω
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict (U_K ∪ (Ω \ U_K)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq]
    rw [MeasureTheory.Measure.restrict_union (Set.disjoint_sdiff_right) h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_U_K, h_eq_on_diff⟩
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    h_eta_u_ae_eq_u).mp h_eta_u_in_Ω

theorem chartPushed_chosenFirstPartial_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set D : ChartBilinearH1ComplData (I := I) (M := M) g α :=
    derivedChartBilinearH1ComplDataUnconditional (I := I) (M := M) g α i hu_h
    with hD_def
  obtain ⟨Ω'', hΩ''_open, hΩ''_compact_closure, hΩ''_in_chart, hK_in_Ω'',
    h_D_uChart_memWkp22_Ω''⟩ :=
    derivedChartBilinear_memWkp_two_two_interior (I := I) (M := M) g α i hu_h
  set K_α : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_α_def
  have hK_α_compact : IsCompact K_α :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_α_in_chart : K_α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hΩ''_in_chart' : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    subset_trans subset_closure hΩ''_in_chart
  have h_D_uChart_eq_base : D.u_chart =
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1
          hu_h)).weak_partial i := by
    rfl
  have h_D_uChart_ae_zero_off_K_α :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K_α)),
        D.u_chart y = 0 := by
    rw [h_D_uChart_eq_base]
    exact base_weak_partial_ae_zero_off_K_α (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h) i
  have h_D_uChart_memWkp22_chart :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart
        (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_two_extend_via_cutoff (E := E) 2
      h_chart_open hΩ''_open hΩ''_in_chart' hK_α_compact hK_in_Ω''
      h_D_uChart_memWkp22_Ω'' h_D_uChart_ae_zero_off_K_α
  have h_D_uChart_ae_eq_chosen :
      D.u_chart =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
    have h_eq : D.u_chart = (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) := by
      rw [h_D_uChart_eq_base]
      exact DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartBilinearH1ComplData_of_laplacianDomain_weak_partial_def
        (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h) i
    rw [h_eq]
    exact chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
      (I := I) (M := M) g α hu_h i
  have h_chosenFirst_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i)
        (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open
      h_D_uChart_ae_eq_chosen).mp h_D_uChart_memWkp22_chart
  exact h_chosenFirst_memWkp22

theorem chartPushed_memWkp_three_two_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  refine chartPushed_memWkp_three_two_of_chosen_partials_memWkp_two_two
    (I := I) (M := M) g α hu_h ?_
  intro i
  exact chartPushed_chosenFirstPartial_memWkp_two_two
    (I := I) (M := M) g α hu_h i

theorem chartPushed_memWkp_three_two_of_laplacianDomainPow_two'
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 3 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_three_two_of_laplacianDomainPow_two
    (I := I) (M := M) g α hu_h

end ChartPushedMemWkpThreeSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
