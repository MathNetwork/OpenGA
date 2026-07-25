import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.EigenvectorChartComponentH2Quant
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartGradientEnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHSEnergyBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorArbitraryKRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem wkpNorm_le_of_memWkp_precompact_uniform
    {d : ℕ} [NeZero d] {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {Ω Ω' K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ_open : IsOpen Ω) (hΩ'_open : IsOpen Ω')
    (hK_compact : IsCompact K) (hKΩ' : K ⊆ Ω')
    (hΩ'_cl : closure Ω' ⊆ Ω) :
    ∃ K_prom : ℝ, 0 < K_prom ∧
      ∀ u : EuclideanSpace ℝ (Fin d) → ℝ,
        u =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)] 0 →
        MemWkp (d := d) k p u Ω' →
        iteratedWeakSobolevNorm (d := d) k p u Ω ≤
          ENNReal.ofReal K_prom * iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  have hΩ'Ω : Ω' ⊆ Ω := subset_closure.trans hΩ'_cl
  obtain ⟨δ, χ, hδ_pos, _hδ_sub, hχ_smooth, hχ_compact, _hχ_range,
      hχ_one, hχ_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := d) hK_compact hΩ'_open hKΩ'
  set N : Set (EuclideanSpace ℝ (Fin d)) := Metric.cthickening δ K with hN_def
  have hN_closed : IsClosed N := Metric.isClosed_cthickening
  have hN_meas : MeasurableSet N := hN_closed.measurableSet
  have hK_sub_N : K ⊆ N := Metric.self_subset_cthickening K
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := d) hχ_smooth hχ_compact k
  obtain ⟨K_prom, hK_prom_pos, hK_prom_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := d) k hp hp_top hΩ'_open hχ_smooth hCχ_nn
      (fun j hj x hx => hCχ_bound x j hj)
  refine ⟨K_prom, hK_prom_pos, fun u hu_ae_zero hu_precompact => ?_⟩
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => χ x * u x with hv_def
  have hv_memWkp_Ω' : MemWkp (d := d) k p v Ω' :=
    MemWkp.smul_smooth_bounded (d := d) k hp hΩ'_open hχ_smooth
      (fun j _hj x _hx => hCχ_bound x j _hj) hu_precompact
  have hv_tsupp : tsupport v ⊆ Ω' :=
    (tsupport_smul_subset_left χ u).trans hχ_supp
  have hv_compact : HasCompactSupport v := hχ_compact.mul_right
  have hv_ae_eq_u : v =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict Ω] u := by
    have h_split : Ω = (Ω ∩ N) ∪ (Ω \ N) := by rw [Set.inter_union_diff]
    have h_on_inter :
        v =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω ∩ N)] u := by
      refine (ae_restrict_iff' (hΩ_open.measurableSet.inter hN_meas)).mpr ?_
      refine Filter.Eventually.of_forall fun x hx => ?_
      simp only [hv_def, hχ_one x hx.2, one_mul]
    have h_on_diff :
        v =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ N)] u := by
      have h_sub : Ω \ N ⊆ Ω \ K := Set.diff_subset_diff_right hK_sub_N
      have hu_zero_diff :
          u =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ N)] 0 :=
        hu_ae_zero.filter_mono
          (ae_mono (Measure.restrict_mono_set volume h_sub))
      filter_upwards [hu_zero_diff] with x hx
      simp only [hv_def, hx, Pi.zero_apply, mul_zero]
    have h_union :
        v =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
            ((Ω ∩ N) ∪ (Ω \ N))] u := by
      rw [Filter.EventuallyEq, ae_restrict_union_eq]
      exact ⟨h_on_inter, h_on_diff⟩
    rwa [← h_split] at h_union
  calc
    iteratedWeakSobolevNorm (d := d) k p u Ω
        = iteratedWeakSobolevNorm (d := d) k p v Ω :=
          (wkpNorm_congr_ae (d := d) hp hΩ_open hv_ae_eq_u).symm
    _ = iteratedWeakSobolevNorm (d := d) k p v Ω' :=
          wkpNorm_extend_zero (d := d) hp hp_top hΩ'_open hΩ_open hΩ'Ω
            hv_memWkp_Ω' hv_tsupp hv_compact
    _ ≤ ENNReal.ofReal K_prom * iteratedWeakSobolevNorm (d := d) k p u Ω' :=
          hK_prom_bound hu_precompact

private lemma sqrt_energy_le_of_atoms_le
    {n : ℕ} {T : ℝ} (hT : 0 ≤ T) {a : Fin n → ℝ} {a_u a_f : ℝ}
    (ha : ∀ l, |a l| ≤ T) (ha_u : |a_u| ≤ T) (ha_f : |a_f| ≤ T) :
    Real.sqrt ((∑ l : Fin n, (a l) ^ 2) + a_u ^ 2 + a_f ^ 2) ≤
      Real.sqrt ((n : ℝ) + 2) * T := by
  classical
  have h_sq : ∀ l, (a l) ^ 2 ≤ T ^ 2 := fun l => by
    have := abs_le.mp (ha l)
    nlinarith [this.1, this.2, hT]
  have h_sq_u : a_u ^ 2 ≤ T ^ 2 := by
    have := abs_le.mp ha_u
    nlinarith [this.1, this.2, hT]
  have h_sq_f : a_f ^ 2 ≤ T ^ 2 := by
    have := abs_le.mp ha_f
    nlinarith [this.1, this.2, hT]
  have h_sum_le : (∑ l : Fin n, (a l) ^ 2) ≤ (n : ℝ) * T ^ 2 := by
    calc (∑ l : Fin n, (a l) ^ 2) ≤ ∑ _l : Fin n, T ^ 2 :=
          Finset.sum_le_sum (fun l _ => h_sq l)
      _ = (n : ℝ) * T ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_energy_le :
      (∑ l : Fin n, (a l) ^ 2) + a_u ^ 2 + a_f ^ 2 ≤ ((n : ℝ) + 2) * T ^ 2 := by
    nlinarith [h_sum_le, h_sq_u, h_sq_f]
  calc Real.sqrt ((∑ l : Fin n, (a l) ^ 2) + a_u ^ 2 + a_f ^ 2)
      ≤ Real.sqrt (((n : ℝ) + 2) * T ^ 2) := Real.sqrt_le_sqrt h_energy_le
    _ = Real.sqrt ((n : ℝ) + 2) * Real.sqrt (T ^ 2) := by
        rw [Real.sqrt_mul (by positivity)]
    _ = Real.sqrt ((n : ℝ) + 2) * T := by rw [Real.sqrt_sq hT]

set_option maxHeartbeats 3200000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvector_chartComponent_wkpNorm_two_energy_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2
            (eigenvectorTensorChartBilinearData (I := I) (M := M)
              g r s i α P₀).u_chart
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_compact.exists_cthickening_subset_open h_chart_open hK_in
  set Ω'' : Set EuclN := Metric.thickening (R_α / 2) K with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_half_pos : 0 < R_α / 2 := by positivity
  have hK_in_Ω'' : K ⊆ Ω'' := Metric.self_subset_thickening h_half_pos K
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (R_α / 2) K :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_half_in_chart : Metric.cthickening (R_α / 2) K ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (R_α / 2) ≤ R_α := by linarith
    exact (Metric.cthickening_mono hle K).trans hR_α_subset
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_half_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => h_closureΩ''_in_chart (subset_closure hy)
  set R₀ : ℝ := R_α / 4 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (R_α / 2) K) ⊆
        Metric.cthickening (R₀ + R_α / 2) K := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + R_α / 2) K ⊆
        Metric.cthickening R_α K := by
      have hle : R₀ + R_α / 2 ≤ R_α := by rw [hR₀_def]; linarith
      exact Metric.cthickening_mono hle K
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  set ε : ℝ := R₀ / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set Ω' : Set EuclN := Metric.thickening (8 * ε) (closure Ω'') with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) (closure Ω'') :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart :
      Metric.cthickening (8 * ε) (closure Ω'') ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R₀ := by rw [hε_def]; linarith
    exact (Metric.cthickening_mono hle (closure Ω'')).trans h_room
  have h_closureΩ'_in_chart :
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hΩ''_compact_closure.cthickening.of_isClosed_subset isClosed_closure
      h_closureΩ'_sub
  have h_closureΩ''_sub_Ω' : closure Ω'' ⊆ Ω' := by
    rw [hΩ'_def]
    exact Metric.self_subset_thickening (by positivity) (closure Ω'')
  have hΩ''_sub_closureΩ' : Ω'' ⊆ closure Ω' :=
    fun y hy => subset_closure (h_closureΩ''_sub_Ω' (subset_closure hy))
  set K_η : Set EuclN := Metric.cthickening (3 * ε) (closure Ω'') with hK_η_def
  have hK_η_compact : IsCompact K_η := hΩ''_compact_closure.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) (closure Ω'') with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η :=
    Metric.cthickening_subset_thickening' (by positivity) (by linarith)
      (closure Ω'')
  obtain ⟨_δ_η, η, _hδ_η_pos, _hδ_η_sub_Ωη, hη_smooth, hη_supp, hη_range,
      hη_one_on_cthick_K_η, hη_tsupp_in_Ω_η⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_η_compact hΩ_η_open hK_η_in_Ω_η
  obtain ⟨N, hN_pos, h_fderiv_eta⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.exists_grad_bound_of_compactSupport_smooth
      hη_smooth hη_supp
  have hN_nn : 0 ≤ N := hN_pos.le
  have hη_one_on_K_η : ∀ x ∈ K_η, η x = 1 := fun x hx =>
    hη_one_on_cthick_K_η x (Metric.self_subset_cthickening _ hx)
  have hΩ''_sub_K_η : Ω'' ⊆ K_η := by
    intro y hy
    exact Metric.self_subset_cthickening _ (subset_closure hy)
  have hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1 :=
    fun x hx => hη_one_on_K_η x (hΩ''_sub_K_η hx)
  have hη_in_Ω' : tsupport η ⊆ Ω' := by
    refine hη_tsupp_in_Ω_η.trans ?_
    rw [hΩ_η_def, hΩ'_def]
    intro y hy
    refine Metric.mem_thickening_iff_infEDist_lt.mpr ?_
    have h := Metric.mem_thickening_iff_infEDist_lt.mp hy
    exact lt_of_lt_of_le h (ENNReal.ofReal_le_ofReal (by linarith))
  have hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ ε →
      Metric.cthickening |h| (tsupport η) ⊆ Ω' := by
    intro h hh
    have h_tsupp_in_cthick_5ε :
        tsupport η ⊆ Metric.cthickening (5 * ε) (closure Ω'') := by
      refine hη_tsupp_in_Ω_η.trans ?_
      rw [hΩ_η_def]
      exact Metric.thickening_subset_cthickening _ _
    by_cases h_abs : |h| ≤ 0
    · have hh_zero : |h| = 0 := le_antisymm h_abs (abs_nonneg _)
      have hcth_zero : Metric.cthickening |h| (tsupport η) = tsupport η := by
        rw [hh_zero, Metric.cthickening_zero]
        exact (isClosed_tsupport η).closure_eq
      rw [hcth_zero]
      exact hη_in_Ω'
    · have h_abs_pos : 0 < |h| := not_le.mp h_abs
      have h1 : Metric.cthickening |h| (tsupport η) ⊆
          Metric.cthickening |h| (Metric.cthickening (5 * ε) (closure Ω'')) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 :
          Metric.cthickening |h| (Metric.cthickening (5 * ε) (closure Ω'')) ⊆
            Metric.cthickening (|h| + 5 * ε) (closure Ω'') :=
        Metric.cthickening_cthickening_subset h_abs_pos.le (by positivity)
          (closure Ω'')
      have h_le : |h| + 5 * ε < 8 * ε := by nlinarith [hε_pos]
      have h3 : Metric.cthickening (|h| + 5 * ε) (closure Ω'') ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le
          (closure Ω'')
      exact (h1.trans h2).trans h3
  have h_room_ε : Metric.cthickening ε (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    (Metric.cthickening_mono (by rw [hε_def]; linarith) (closure Ω'')).trans
      h_room
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    tensor_h2_chart_loc_of_data_quantitative (I := I) (M := M) (g := g)
      (α := α) (r := r) (s := s) (P₀ := P₀)
      hη_smooth hη_supp hη_range hN_nn h_fderiv_eta hΩ'_open
      h_closureΩ'_in_chart hΩ'_compact_closure hη_in_Ω' hε_pos hh_supp_in_Ω'
      hη_one_on_Ω'' hΩ''_open hΩ''_compact_closure h_room_ε
  set C_geom_max : ℝ :=
    ∑ i' : Fin (Module.finrank ℝ E), ∑ k' : Fin (Module.finrank ℝ E),
      C_geom i' k' with hC_geom_max_def
  have hC_geom_max_nn : 0 ≤ C_geom_max := by
    rw [hC_geom_max_def]
    exact Finset.sum_nonneg fun i' _ =>
      Finset.sum_nonneg fun k' _ => hC_geom_nn i' k'
  have hC_geom_le_max : ∀ i' k', C_geom i' k' ≤ C_geom_max := by
    intro i' k'
    rw [hC_geom_max_def]
    have h_inner : C_geom i' k' ≤
        ∑ k'' : Fin (Module.finrank ℝ E), C_geom i' k'' :=
      Finset.single_le_sum (fun k'' _ => hC_geom_nn i' k'')
        (Finset.mem_univ k')
    have h_outer : (∑ k'' : Fin (Module.finrank ℝ E), C_geom i' k'') ≤
        ∑ i'' : Fin (Module.finrank ℝ E),
          ∑ k'' : Fin (Module.finrank ℝ E), C_geom i'' k'' :=
      Finset.single_le_sum
        (fun i'' _ => Finset.sum_nonneg fun k'' _ => hC_geom_nn i'' k'')
        (Finset.mem_univ i')
    exact h_inner.trans h_outer
  choose Cwp hCwp_nn hCwp_bd using fun k : Fin (Module.finrank ℝ E) =>
    eigenvectorChartWeakPartial_eLpNorm_le (I := I) (M := M)
      g r s α P₀ k
  obtain ⟨Cf, hCf_nn, hCf_bd⟩ :=
    eigenvectorChartRHS_eLpNorm_le_energy (I := I) (M := M)
      g r s α P₀
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :=
    eLpNorm_tensorL2ChartComponent_le_uniform (I := I) (M := M) g r s α P₀
  obtain ⟨c_dom, _hc_dom_pos, h_dom_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) α hΩ'_compact_closure
      hΩ'_compact_closure.isClosed.measurableSet h_closureΩ'_in_chart
  set c_d : ℝ := ((ENNReal.ofReal c_dom) ^ ((1 / 2 : ℝ≥0∞).toReal)).toReal
    with hc_d_def
  have hc_d_nn : 0 ≤ c_d := ENNReal.toReal_nonneg
  have hc_d_enn_ne_top :
      (ENNReal.ofReal c_dom) ^ ((1 / 2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have h_fchart_density : ∀ f : EuclN → ℝ,
      eLpNorm f 2 ((volume : Measure EuclN).restrict (closure Ω')) ≤
        ENNReal.ofReal c_d *
          eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
    intro f
    have h_mono :
        eLpNorm f 2 ((volume : Measure EuclN).restrict (closure Ω')) ≤
          eLpNorm f 2 (ENNReal.ofReal c_dom •
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) :=
      eLpNorm_mono_measure f h_dom_le
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f
      (ENNReal.ofReal c_dom), smul_eq_mul,
      ← ENNReal.ofReal_toReal hc_d_enn_ne_top, ← hc_d_def] at h_mono
    exact h_mono
  obtain ⟨K_prom, hK_prom_pos, hK_prom_bd⟩ :=
    wkpNorm_le_of_memWkp_precompact_uniform
      (d := Module.finrank ℝ E) (k := 2) (p := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
  set Catom : ℝ :=
    Ccomp + Cf + ∑ k : Fin (Module.finrank ℝ E), Cwp k with hCatom_def
  have hCatom_nn : 0 ≤ Catom := by
    rw [hCatom_def]
    have h_sum : 0 ≤ ∑ k : Fin (Module.finrank ℝ E), Cwp k :=
      Finset.sum_nonneg (fun k _ => hCwp_nn k)
    positivity
  have hCcomp_le : Ccomp ≤ Catom := by
    rw [hCatom_def]
    have h_sum : 0 ≤ ∑ k : Fin (Module.finrank ℝ E), Cwp k :=
      Finset.sum_nonneg (fun k _ => hCwp_nn k)
    linarith
  have hCf_le : Cf ≤ Catom := by
    rw [hCatom_def]
    have h_sum : 0 ≤ ∑ k : Fin (Module.finrank ℝ E), Cwp k :=
      Finset.sum_nonneg (fun k _ => hCwp_nn k)
    linarith
  have hCwp_le : ∀ k, Cwp k ≤ Catom := by
    intro k
    rw [hCatom_def]
    have h_single : Cwp k ≤ ∑ k' : Fin (Module.finrank ℝ E), Cwp k' :=
      Finset.single_le_sum (fun k' _ => hCwp_nn k') (Finset.mem_univ k)
    linarith
  set Cdat : ℝ := (1 + c_d) * Catom with hCdat_def
  have hCdat_nn : 0 ≤ Cdat := by rw [hCdat_def]; positivity
  have hCatom_le_Cdat : Catom ≤ Cdat := by
    rw [hCdat_def]; nlinarith [hCatom_nn, hc_d_nn]
  set Cbig : ℝ := C_geom_max * Real.sqrt ((n : ℝ) + 2) + 1 with hCbig_def
  have hCbig_nn : 0 ≤ Cbig := by
    rw [hCbig_def]
    have := Real.sqrt_nonneg ((n : ℝ) + 2)
    positivity
  set Cint : ℝ :=
    (1 + (n : ℝ) + (n : ℝ) * (n : ℝ)) * Cbig * Cdat with hCint_def
  have hCint_nn : 0 ≤ Cint := by rw [hCint_def]; positivity
  set C : ℝ := K_prom * Cint + 1 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have : 0 ≤ K_prom * Cint := mul_nonneg hK_prom_pos.le hCint_nn
    linarith
  refine ⟨C, hC_nn, fun i => ?_⟩
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀
    with hD_def
  set vec :=
    tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i
    with hvec_def
  have hD_f_chart : D.f_chart =
      eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ := rfl
  have hD_weak_partial : ∀ k, D.weak_partial k =
      eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k :=
    fun _ => rfl
  have hD_u_chart : D.u_chart =
      ((tensorL2ChartComponent (I := I) (M := M) g r s vec α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) := rfl
  set φnorm : ℝ := ‖vec‖ with hφnorm_def
  have hφnorm_nn : 0 ≤ φnorm := norm_nonneg _
  have hφnorm_eq_one : φnorm = 1 := by
    rw [hφnorm_def, hvec_def]
    exact (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s)).norm_eq_one i
  have hμ_Ioc : 0 < i.fst.val ∧ i.fst.val ≤ 1 :=
    tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        have h_norm : φnorm = 1 := hφnorm_eq_one
        rw [hφnorm_def, hvec_def, h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)
  obtain ⟨hμ_pos, hμ_le_one⟩ := hμ_Ioc
  have hμinv_pos : 0 < (i.fst.val)⁻¹ := inv_pos.mpr hμ_pos
  have h_one_le_μinv : (1 : ℝ) ≤ (i.fst.val)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hμ_pos]; simpa using hμ_le_one
  have h_sqrt_μinv_le : Real.sqrt ((i.fst.val)⁻¹) ≤ (i.fst.val)⁻¹ := by
    have h := Real.sqrt_le_sqrt
      (show (i.fst.val)⁻¹ ≤ (i.fst.val)⁻¹ * (i.fst.val)⁻¹ from by
        nlinarith [h_one_le_μinv, hμinv_pos])
    calc Real.sqrt ((i.fst.val)⁻¹)
        ≤ Real.sqrt ((i.fst.val)⁻¹ * (i.fst.val)⁻¹) := h
      _ = (i.fst.val)⁻¹ := by
          rw [show (i.fst.val)⁻¹ * (i.fst.val)⁻¹ = ((i.fst.val)⁻¹) ^ 2 from by
            ring, Real.sqrt_sq hμinv_pos.le]
  have h_restrict_mono :
      (volume : Measure EuclN).restrict (closure Ω') ≤
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) :=
    Measure.restrict_mono h_closureΩ'_in_chart (le_refl (volume : Measure EuclN))
  set T_atom : ℝ := Cdat * (i.fst.val)⁻¹ * φnorm with hT_atom_def
  have hT_atom_nn : 0 ≤ T_atom := by rw [hT_atom_def]; positivity
  have h_wp_toReal_le : ∀ l : Fin (Module.finrank ℝ E),
      (eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ T_atom := by
    intro l
    have h_chart_bd :
        eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal (Cwp l * Real.sqrt ((i.fst.val)⁻¹)) *
            ENNReal.ofReal φnorm := by
      rw [hD_weak_partial l, hφnorm_def, hvec_def]
      exact hCwp_bd l i
    have h_mono :
        eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω')) ≤
          ENNReal.ofReal
            ((Cwp l * Real.sqrt ((i.fst.val)⁻¹)) * φnorm) := by
      refine (eLpNorm_mono_measure _ h_restrict_mono).trans ?_
      rw [ENNReal.ofReal_mul (mul_nonneg (hCwp_nn l) (Real.sqrt_nonneg _))]
      exact h_chart_bd
    have h_real_le :
        (Cwp l * Real.sqrt ((i.fst.val)⁻¹)) * φnorm ≤ T_atom := by
      rw [hT_atom_def]
      have hstep : Cwp l * Real.sqrt ((i.fst.val)⁻¹) ≤
          Cdat * (i.fst.val)⁻¹ := by
        calc Cwp l * Real.sqrt ((i.fst.val)⁻¹)
            ≤ Catom * (i.fst.val)⁻¹ :=
              mul_le_mul (hCwp_le l) h_sqrt_μinv_le (Real.sqrt_nonneg _)
                hCatom_nn
          _ ≤ Cdat * (i.fst.val)⁻¹ :=
              mul_le_mul_of_nonneg_right hCatom_le_Cdat hμinv_pos.le
      exact mul_le_mul_of_nonneg_right hstep hφnorm_nn
    have h_toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_mono
    rw [ENNReal.toReal_ofReal
      (mul_nonneg (mul_nonneg (hCwp_nn l) (Real.sqrt_nonneg _)) hφnorm_nn)]
      at h_toReal
    exact h_toReal.trans h_real_le
  have h_uChart_toReal_le :
      (eLpNorm D.u_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ T_atom := by
    have h_weighted :
        eLpNorm D.u_chart 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal Ccomp * ENNReal.ofReal φnorm := by
      rw [hD_u_chart, hφnorm_def]
      exact hCcomp_bd vec
    have h_density := h_fchart_density D.u_chart
    have h_vol_le :
        eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω')) ≤
          ENNReal.ofReal (c_d * Ccomp * φnorm) := by
      refine h_density.trans ?_
      refine (mul_le_mul_of_nonneg_left h_weighted (zero_le _)).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc_d_nn,
        ← ENNReal.ofReal_mul (mul_nonneg hc_d_nn hCcomp_nn)]
    have h_real_le : c_d * Ccomp * φnorm ≤ T_atom := by
      rw [hT_atom_def]
      have hstep : c_d * Ccomp ≤ Cdat * (i.fst.val)⁻¹ := by
        have hcC : c_d * Ccomp ≤ Cdat := by
          rw [hCdat_def]; nlinarith [hCcomp_le, hc_d_nn, hCatom_nn, hCcomp_nn]
        exact le_trans hcC (le_mul_of_one_le_right hCdat_nn h_one_le_μinv)
      exact mul_le_mul_of_nonneg_right hstep hφnorm_nn
    have h_toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_vol_le
    rw [ENNReal.toReal_ofReal
      (mul_nonneg (mul_nonneg hc_d_nn hCcomp_nn) hφnorm_nn)] at h_toReal
    exact h_toReal.trans h_real_le
  have h_fChart_toReal_le :
      (eLpNorm D.f_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ T_atom := by
    have h_weighted :
        eLpNorm D.f_chart 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal (Cf * (i.fst.val)⁻¹) * ENNReal.ofReal φnorm := by
      rw [hD_f_chart, hφnorm_def, hvec_def]
      exact hCf_bd i
    have h_density := h_fchart_density D.f_chart
    have h_vol_le :
        eLpNorm D.f_chart 2
            ((volume : Measure EuclN).restrict (closure Ω')) ≤
          ENNReal.ofReal (c_d * (Cf * (i.fst.val)⁻¹) * φnorm) := by
      refine h_density.trans ?_
      refine (mul_le_mul_of_nonneg_left h_weighted (zero_le _)).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc_d_nn,
        ← ENNReal.ofReal_mul
          (mul_nonneg hc_d_nn (mul_nonneg hCf_nn hμinv_pos.le))]
    have h_real_le : c_d * (Cf * (i.fst.val)⁻¹) * φnorm ≤ T_atom := by
      rw [hT_atom_def]
      have hstep : c_d * (Cf * (i.fst.val)⁻¹) ≤ Cdat * (i.fst.val)⁻¹ := by
        have hcCf : c_d * Cf ≤ Cdat := by
          rw [hCdat_def]; nlinarith [hCf_le, hc_d_nn, hCatom_nn, hCf_nn]
        calc c_d * (Cf * (i.fst.val)⁻¹)
            = (c_d * Cf) * (i.fst.val)⁻¹ := by ring
          _ ≤ Cdat * (i.fst.val)⁻¹ :=
              mul_le_mul_of_nonneg_right hcCf hμinv_pos.le
      exact mul_le_mul_of_nonneg_right hstep hφnorm_nn
    have h_toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_vol_le
    rw [ENNReal.toReal_ofReal
      (mul_nonneg (mul_nonneg hc_d_nn (mul_nonneg hCf_nn hμinv_pos.le))
        hφnorm_nn)] at h_toReal
    exact h_toReal.trans h_real_le
  set DATA : ℝ :=
    (∑ l : Fin (Module.finrank ℝ E),
      (eLpNorm (D.weak_partial l) 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
    + (eLpNorm D.u_chart 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
    + (eLpNorm D.f_chart 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
    with hDATA_def
  have h_sqrt_DATA_le :
      Real.sqrt DATA ≤ Real.sqrt ((n : ℝ) + 2) * T_atom := by
    rw [hDATA_def, hn_def]
    exact sqrt_energy_le_of_atoms_le hT_atom_nn
      (fun l => by
        rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact h_wp_toReal_le l)
      (by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact h_uChart_toReal_le)
      (by rw [abs_of_nonneg ENNReal.toReal_nonneg]; exact h_fChart_toReal_le)
  have hDATA_nn : 0 ≤ DATA := by
    rw [hDATA_def]
    have h1 : 0 ≤ ∑ l : Fin (Module.finrank ℝ E),
        (eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg _)
    positivity
  have h_gik_bound : ∀ i' k' : Fin (Module.finrank ℝ E),
      ∃ g_ik : EuclN → ℝ,
        MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
        DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k' g_ik
          (D.weak_partial i') Ω'' ∧
        eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
          ENNReal.ofReal
            (C_geom_max * (Real.sqrt ((n : ℝ) + 2) * T_atom)) := by
    intro i' k'
    obtain ⟨g_ik, hg_memLp, hg_weak, hg_norm⟩ := hC_geom D i' k'
    refine ⟨g_ik, hg_memLp, hg_weak, ?_⟩
    have h_real_le :
        C_geom i' k' * Real.sqrt DATA ≤
          C_geom_max * (Real.sqrt ((n : ℝ) + 2) * T_atom) := by
      have h_sqrt_nn : 0 ≤ Real.sqrt DATA := Real.sqrt_nonneg _
      have h_rhs_nn : 0 ≤ Real.sqrt ((n : ℝ) + 2) * T_atom :=
        mul_nonneg (Real.sqrt_nonneg _) hT_atom_nn
      calc C_geom i' k' * Real.sqrt DATA
          ≤ C_geom i' k' * (Real.sqrt ((n : ℝ) + 2) * T_atom) :=
            mul_le_mul_of_nonneg_left h_sqrt_DATA_le (hC_geom_nn i' k')
        _ ≤ C_geom_max * (Real.sqrt ((n : ℝ) + 2) * T_atom) :=
            mul_le_mul_of_nonneg_right (hC_geom_le_max i' k') h_rhs_nn
    refine hg_norm.trans ?_
    exact ENNReal.ofReal_le_ofReal (by rw [← hDATA_def]; exact h_real_le)
  obtain ⟨h_uChart_memW1p, h_wp_memW1p⟩ :=
    tensorChartBilinear_chartComponent_regularity_of_data
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_uChart_memWkp_two_Ω'' :
      MemWkp (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p, fun j => ?_⟩
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j (D.weak_partial j) D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial j)
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j
        (chosenWeakPartial' 2 j D.u_chart Ω'') D.u_chart Ω'' :=
      chosenWeakPartial'_isWeakPartial_of_mem h_uChart_memW1p j
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (chosenWeakPartial' 2 j D.u_chart Ω'')
        ((volume : Measure EuclN).restrict Ω'') :=
      (chosenWeakPartial'_memLp_of_mem h_uChart_memW1p j).locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial j)
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p j).1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        chosenWeakPartial' 2 j D.u_chart Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω'']
          D.weak_partial j :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
    rw [MemWkp.one_iff_memW1p]
    exact (MemW1p_congr_ae hΩ''_open h_ae.symm).mp (h_wp_memW1p j)
  have h_chosen_ae_wp : ∀ i' : Fin (Module.finrank ℝ E),
      chosenWeakPartial' 2 i' D.u_chart Ω''
        =ᵐ[(volume : Measure EuclN).restrict Ω''] D.weak_partial i' := by
    intro i'
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i' (D.weak_partial i') D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial i')
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i'
        (chosenWeakPartial' 2 i' D.u_chart Ω'') D.u_chart Ω'' :=
      chosenWeakPartial'_isWeakPartial_of_mem h_uChart_memW1p i'
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (chosenWeakPartial' 2 i' D.u_chart Ω'')
        ((volume : Measure EuclN).restrict Ω'') :=
      (chosenWeakPartial'_memLp_of_mem h_uChart_memW1p i').locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial i')
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p i').1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
      h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
  set Tsum : ℝ≥0∞ := ENNReal.ofReal (Cbig * T_atom) with hTsum_def
  have h_wp_eLpNorm_Ω''_le : ∀ l : Fin (Module.finrank ℝ E),
      eLpNorm (D.weak_partial l) 2 ((volume : Measure EuclN).restrict Ω'') ≤
        Tsum := by
    intro l
    have h_mono :
        eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict Ω'') ≤
          eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω')) :=
      eLpNorm_mono_measure _
        (Measure.restrict_mono hΩ''_sub_closureΩ' le_rfl)
    have h_toReal := h_wp_toReal_le l
    have h_ne : eLpNorm (D.weak_partial l) 2
        ((volume : Measure EuclN).restrict (closure Ω')) ≠ ⊤ :=
      (D.weak_partial_locally_memLp l hΩ'_compact_closure
        h_closureΩ'_in_chart).eLpNorm_lt_top.ne
    have h_clΩ'_le : eLpNorm (D.weak_partial l) 2
        ((volume : Measure EuclN).restrict (closure Ω')) ≤
          ENNReal.ofReal T_atom :=
      (ENNReal.le_ofReal_iff_toReal_le h_ne hT_atom_nn).mpr h_toReal
    refine (h_mono.trans h_clΩ'_le).trans ?_
    rw [hTsum_def]
    exact ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_left hT_atom_nn (by
        rw [hCbig_def]
        have := Real.sqrt_nonneg ((n : ℝ) + 2)
        nlinarith [hC_geom_max_nn, this]))
  have h_uChart_eLpNorm_Ω''_le :
      eLpNorm D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') ≤ Tsum := by
    have h_mono :
        eLpNorm D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') ≤
          eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω')) :=
      eLpNorm_mono_measure _
        (Measure.restrict_mono hΩ''_sub_closureΩ' le_rfl)
    have h_toReal := h_uChart_toReal_le
    have h_ne : eLpNorm D.u_chart 2
        ((volume : Measure EuclN).restrict (closure Ω')) ≠ ⊤ :=
      (D.memLp_volume_restrict_u_chart hΩ'_compact_closure
        hΩ'_compact_closure.isClosed.measurableSet
        h_closureΩ'_in_chart).eLpNorm_lt_top.ne
    have h_clΩ'_le : eLpNorm D.u_chart 2
        ((volume : Measure EuclN).restrict (closure Ω')) ≤
          ENNReal.ofReal T_atom :=
      (ENNReal.le_ofReal_iff_toReal_le h_ne hT_atom_nn).mpr h_toReal
    refine (h_mono.trans h_clΩ'_le).trans ?_
    rw [hTsum_def]
    exact ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_left hT_atom_nn (by
        rw [hCbig_def]
        have := Real.sqrt_nonneg ((n : ℝ) + 2)
        nlinarith [hC_geom_max_nn, this]))
  have h_interior_bound :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 D.u_chart Ω''
        ≤ ENNReal.ofReal (Cint * (i.fst.val)⁻¹ * φnorm) := by
    rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial 1 2 Ω'' D.u_chart]
    have h_per_i : ∀ i' : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (chosenWeakPartial' 2 i' D.u_chart Ω'') Ω''
          ≤ Tsum + ∑ _k' : Fin (Module.finrank ℝ E), Tsum := by
      intro i'
      rw [wkpNorm_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open
        (h_chosen_ae_wp i')]
      rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial 0 2 Ω'' (D.weak_partial i')]
      refine add_le_add (h_wp_eLpNorm_Ω''_le i') (Finset.sum_le_sum
        (fun k' _ => ?_))
      rw [wkpNorm_zero]
      obtain ⟨g_ik, hg_memLp, hg_weak, hg_norm⟩ := h_gik_bound i' k'
      have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
          (d := Module.finrank ℝ E) k'
          (chosenWeakPartial' 2 k' (D.weak_partial i') Ω'')
          (D.weak_partial i') Ω'' :=
        chosenWeakPartial'_isWeakPartial_of_mem (h_wp_memW1p i') k'
      have h_chosen_loc : MeasureTheory.LocallyIntegrable
          (chosenWeakPartial' 2 k' (D.weak_partial i') Ω'')
          ((volume : Measure EuclN).restrict Ω'') :=
        (chosenWeakPartial'_memLp_of_mem (h_wp_memW1p i') k').locallyIntegrable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_g_loc : MeasureTheory.LocallyIntegrable g_ik
          ((volume : Measure EuclN).restrict Ω'') :=
        hg_memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_ae :
          chosenWeakPartial' 2 k' (D.weak_partial i') Ω''
            =ᵐ[(volume : Measure EuclN).restrict Ω''] g_ik :=
        DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial hg_weak
          h_chosen_loc h_g_loc
      rw [eLpNorm_congr_ae h_ae]
      refine hg_norm.trans ?_
      rw [hTsum_def]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hCbig_def]
      have h_rearrange :
          C_geom_max * (Real.sqrt ((n : ℝ) + 2) * T_atom) =
            (C_geom_max * Real.sqrt ((n : ℝ) + 2)) * T_atom := by ring
      rw [h_rearrange]
      exact mul_le_mul_of_nonneg_right (by linarith) hT_atom_nn
    refine (add_le_add h_uChart_eLpNorm_Ω''_le
      (Finset.sum_le_sum (fun i' _ => h_per_i i'))).trans ?_
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h_collapse :
        Tsum + (Module.finrank ℝ E) • (Tsum +
            (Module.finrank ℝ E) • Tsum) =
          ENNReal.ofReal (Cint * (i.fst.val)⁻¹ * φnorm) := by
      rw [hTsum_def, hCint_def, hT_atom_def]
      rw [nsmul_eq_mul, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast (Module.finrank ℝ E)]
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine congrArg ENNReal.ofReal ?_
      rw [← hn_def]
      ring
    rw [h_collapse]
  have h_ae_zero :
      D.u_chart =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K)] 0 := by
    rw [hK_def]
    have h_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
        y ∉ chartPouKernel (I := I) (M := M) α →
          D.u_chart y = 0 := by
      rw [hD_u_chart]
      exact tensorL2ChartComponent_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s vec α P₀
    have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α) :=
      (h_chart_open.sdiff hK_compact.isClosed).measurableSet
    have h_ae_V : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)),
        y ∉ chartPouKernel (I := I) (M := M) α →
          D.u_chart y = 0 :=
      ae_mono (Measure.restrict_mono_set _ Set.diff_subset) h_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
    filter_upwards [(ae_restrict_iff' hV_meas).mp h_ae_V] with y hy
    intro hy_V
    exact hy hy_V hy_V.2
  have h_global :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 D.u_chart
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal K_prom *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' :=
    hK_prom_bd D.u_chart h_ae_zero h_uChart_memWkp_two_Ω''
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 D.u_chart
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal K_prom *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := h_global
    _ ≤ ENNReal.ofReal K_prom *
          ENNReal.ofReal (Cint * (i.fst.val)⁻¹ * φnorm) :=
        mul_le_mul_of_nonneg_left h_interior_bound (by positivity)
    _ = ENNReal.ofReal (K_prom * (Cint * (i.fst.val)⁻¹ * φnorm)) := by
        rw [← ENNReal.ofReal_mul hK_prom_pos.le]
    _ ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ * φnorm) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hC_def]
        have h_expand : K_prom * (Cint * (i.fst.val)⁻¹ * φnorm) =
            (K_prom * Cint) * (i.fst.val)⁻¹ * φnorm := by ring
        rw [h_expand]
        have h_le : (K_prom * Cint) ≤ K_prom * Cint + 1 := by linarith
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h_le hμinv_pos.le) hφnorm_nn
    _ = ENNReal.ofReal (C * (i.fst.val)⁻¹) * ENNReal.ofReal φnorm := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hC_nn hμinv_pos.le)]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
