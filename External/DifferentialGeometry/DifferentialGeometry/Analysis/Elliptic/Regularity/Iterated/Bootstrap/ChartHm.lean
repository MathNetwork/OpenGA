import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.MixedPartials
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.PowH2kBridge
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpFourSmooth
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem MemWkp_extend_via_cutoff_poly
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
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict (U_K ∪ (Ω \ U_K)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq]
    rw [MeasureTheory.Measure.restrict_union (Set.disjoint_sdiff_right) h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_U_K, h_eq_on_diff⟩
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    h_eta_u_ae_eq_u).mp h_eta_u_in_Ω

omit [NeZero (Module.finrank ℝ E)] in
private theorem chosenMthMixed_memWkp_of_chartH_at_all_multi_indices
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ (n_succ : ℕ),
    ∀ (m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E)),
      (∀ (idx_all : Fin m → Fin (Module.finrank ℝ E)),
        DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx_all)
          (chartTargetEuclid (I := I) (M := M) α)) →
      (∀ (idx_next : Fin (m + 1) → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (n_succ + 1) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) idx_next)
          (chartTargetEuclid (I := I) (M := M) α)) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (n_succ + 2) 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro n_succ m dirs h_w1p_m h_memWkp_succ
  refine ⟨h_w1p_m dirs, ?_⟩
  intro i
  have h_snoc_last : (Fin.snoc dirs i : Fin (m + 1) →
      Fin (Module.finrank ℝ E)) (Fin.last m) = i := Fin.snoc_last _ _
  have h_init_snoc : (Fin.init (Fin.snoc dirs i : Fin (m + 1) →
      Fin (Module.finrank ℝ E)) : Fin m → Fin (Module.finrank ℝ E)) = dirs :=
    Fin.init_snoc _ _
  have h_succ_eq :
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
        (Fin.snoc dirs i) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 i
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [chosenMthMixedPartialChartPushedU_succ, h_snoc_last, h_init_snoc]
  have h_next := h_memWkp_succ (Fin.snoc dirs i)
  rw [h_succ_eq] at h_next
  exact h_next

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  suffices h : ∀ s : ℕ, ∀ (j : ℕ), s + j = m → ∀ (dirs : Fin j → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (s + 2) 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j dirs)
        (chartTargetEuclid (I := I) (M := M) α) by
    have h_apply := h m 0 (by omega) (Fin.elim0)
    simpa [chosenMthMixedPartialChartPushedU_zero] using h_apply
  intro s
  induction s with
  | zero =>
      intro j hj dirs
      have hj_eq : j = m := by omega
      subst hj_eq
      exact h_top_memWkp_two dirs
  | succ s ih =>
      intro j hj dirs
      have hj_le_m : j ≤ m := by omega
      have hj_succ_in_m : s + (j + 1) = m := by omega
      have h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j dirs)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_intermediate_w1p j hj_le_m dirs
      have h_next : ∀ (idx : Fin (j + 1) → Fin (Module.finrank ℝ E)),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (s + 2) 2
            (chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (j + 1) idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        fun idx => ih (j + 1) hj_succ_in_m idx
      have h_w1p_at_all : ∀ idx_all : Fin j → Fin (Module.finrank ℝ E),
          DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
            (chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h j idx_all)
            (chartTargetEuclid (I := I) (M := M) α) :=
        h_intermediate_w1p j hj_le_m
      have h_aux := chosenMthMixed_memWkp_of_chartH_at_all_multi_indices
        (I := I) (M := M) g α u_h (s + 1) j dirs h_w1p_at_all h_next
      have h_eq : s + 1 + 2 = s + 1 + 2 := rfl
      exact h_aux

theorem chartPushed_memWkp_two_of_laplacianDomainPow_one
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1
  exact h α

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_m_plus_two_step
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_chart_H_m_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_intermediate_w1p : ∀ (j : ℕ), j ≤ m →
      ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h j idx)
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro j hj idx
    have h_parent_j_plus_1 :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (j + 1) 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
      have h_le : j + 1 ≤ m + 1 := by omega
      exact h_chart_H_m_plus_1.le_of_le h_le
    exact chosenMthMixedPartialChartPushedU_memW1p_two
      (I := I) (M := M) g α u_h j h_parent_j_plus_1 idx
  exact chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two
    (I := I) (M := M) g α u_h m h_intermediate_w1p h_top_memWkp_two

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_m_plus_two_of_chartPushed_memWkp_m_plus_two
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_chart_pushed_memWkp :
      ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 2) 2
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) g (m + 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact h_chart_pushed_memWkp α

end IteratedChartHmBootstrap
end Laplacian
end Analysis
end DifferentialGeometry

end
