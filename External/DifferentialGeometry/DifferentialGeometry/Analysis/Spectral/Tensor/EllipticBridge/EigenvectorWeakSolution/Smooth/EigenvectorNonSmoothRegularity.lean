import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorVariationalIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.TensorNonSmoothDiffQuot
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity

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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private lemma thickening_mono_of_lt
    {β : Type*} [PseudoEMetricSpace β]
    {r r' : ℝ} (hr_lt : r < r') (K : Set β) :
    Metric.thickening r K ⊆ Metric.thickening r' K := by
  intro y hy
  refine Metric.mem_thickening_iff_infEDist_lt.mpr ?_
  have h := Metric.mem_thickening_iff_infEDist_lt.mp hy
  exact lt_of_lt_of_le h (ENNReal.ofReal_le_ofReal hr_lt.le)

private lemma self_subset_thickening_of_pos
    {β : Type*} [PseudoEMetricSpace β]
    {r : ℝ} (hr_pos : 0 < r) (K : Set β) :
    K ⊆ Metric.thickening r K :=
  Metric.self_subset_thickening hr_pos K

omit [CompleteSpace E] in
private lemma eigenvectorTensorChartBilinear_uniform_diffQuot_bound
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ M_bound i k) ∧
      (∀ (j k : Fin (Module.finrank ℝ E)) (h : ℝ),
        0 < |h| → |h| ≤ R₀ / 16 →
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              ((eigenvectorTensorChartBilinearData (I := I) (M := M)
                g r s i α P₀).weak_partial j)) 2
            ((volume : Measure EuclN).restrict Ω'')
          ≤ ENNReal.ofReal (M_bound j k)) := by
  classical
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorTensorChartBilinearData (I := I) (M := M) g r s i α P₀
    with hD_def
  set K_α : Set EuclN := closure Ω'' with hK_α_def
  have hK_α_compact : IsCompact K_α := hΩ''_compact_closure
  set ε : ℝ := R₀ / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set Ω' : Set EuclN := Metric.thickening (8 * ε) K_α with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) K_α :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart : Metric.cthickening (8 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R₀ := by change 8 * (R₀ / 16) ≤ R₀; linarith
    exact (Metric.cthickening_mono hle K_α).trans
      ((Metric.cthickening_mono (le_refl R₀) K_α).trans h_room)
  have h_closureΩ'_in_chart :
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ'_sub
  set K_η : Set EuclN := Metric.cthickening (3 * ε) K_α with hK_η_def
  have hK_η_compact : IsCompact K_η := hK_α_compact.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) K_α with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η :=
    Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_α
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
    have hy_K_α : y ∈ K_α := subset_closure hy
    exact Metric.self_subset_cthickening _ hy_K_α
  have hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1 :=
    fun x hx => hη_one_on_K_η x (hΩ''_sub_K_η hx)
  have hη_in_Ω' : tsupport η ⊆ Ω' := by
    refine hη_tsupp_in_Ω_η.trans ?_
    rw [hΩ_η_def, hΩ'_def]
    exact thickening_mono_of_lt (by linarith) K_α
  have hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ ε →
      Metric.cthickening |h| (tsupport η) ⊆ Ω' := by
    intro h hh
    have h_tsupp_in_cthick_5ε : tsupport η ⊆ Metric.cthickening (5 * ε) K_α := by
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
          Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 : Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) ⊆
          Metric.cthickening (|h| + 5 * ε) K_α := by
        apply Metric.cthickening_cthickening_subset
        · exact h_abs_pos.le
        · positivity
      have h_le : |h| + 5 * ε < 8 * ε := by
        have : |h| + 5 * ε ≤ ε + 5 * ε := by linarith
        nlinarith [hε_pos]
      have h3 : Metric.cthickening (|h| + 5 * ε) K_α ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le K_α
      exact (h1.trans h2).trans h3
  obtain ⟨M_bound, hM_nn, h_bd⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data
      (I := I) (M := M) (g := g) (α := α) D.toChartData
      hη_smooth hη_supp hη_range hN_nn h_fderiv_eta
      hΩ'_open h_closureΩ'_in_chart hΩ'_compact_closure
      hη_in_Ω' hε_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  refine ⟨M_bound, hM_nn, fun j k h hh_pos hh_le => ?_⟩
  exact h_bd j k h hh_pos (by rw [hε_def] at *; linarith)


omit [CompleteSpace E] in
theorem eigenvector_chartComponent_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' := by
  classical
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorTensorChartBilinearData (I := I) (M := M) g r s i α P₀
    with hD_def
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    exact h_room (Metric.self_subset_cthickening _ hx)
  have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => h_closureΩ''_in_chart (subset_closure hy)
  set R_dq : ℝ := R₀ / 16 with hR_dq_def
  have hR_dq_pos : 0 < R_dq := by positivity
  have h_room_dq : Metric.cthickening R_dq (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    refine subset_trans ?_ h_room
    exact Metric.cthickening_mono (by rw [hR_dq_def]; linarith) (closure Ω'')
  obtain ⟨M_bound, hM_nn, h_diffQuot_bd⟩ :=
    eigenvectorTensorChartBilinear_uniform_diffQuot_bound
      (I := I) (M := M) (g := g) (r := r) (s := s) i α P₀
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_h2 :=
    tensor_h2_chart_loc_of_uniform_bound (I := I) (M := M)
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR_dq_pos h_room_dq hM_nn h_diffQuot_bd
  have h_uChart_memLp_vol_Ω'' :
      MemLp D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') :=
    D.memLp_volume_restrict_u_chart hΩ''_compact_closure
      hΩ''_compact_closure.isClosed.measurableSet h_closureΩ''_in_chart
        |>.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have h_dwp_memLp_Ω'' :
      ∀ j, MemLp (D.weak_partial j) 2 ((volume : Measure EuclN).restrict Ω'') := by
    intro j
    exact (D.weak_partial_locally_memLp j hΩ''_compact_closure
      h_closureΩ''_in_chart).mono_measure
        (Measure.restrict_mono subset_closure le_rfl)
  have h_dwp_weak_uChart_Ω'' :
      ∀ j, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
        (D.weak_partial j) D.u_chart Ω'' := by
    intro j
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
      (D.weak_partial_isWeakPartial j)
  have h_uChart_memW1p_Ω'' :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memLp_vol_Ω'', ?_⟩
    intro j
    exact ⟨D.weak_partial j, h_dwp_memLp_Ω'' j, h_dwp_weak_uChart_Ω'' j⟩
  have h_wp_j_memW1p_Ω'' : ∀ j,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 (D.weak_partial j) Ω'' := by
    intro j
    refine ⟨h_dwp_memLp_Ω'' j, ?_⟩
    intro k
    obtain ⟨g_jk, hg_jk_memLp, hg_jk_partial, _hg_jk_norm⟩ := h_h2 j k
    exact ⟨g_jk, hg_jk_memLp, hg_jk_partial⟩
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p_Ω'', ?_⟩
    intro j
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p_Ω'' j
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p_Ω'' j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial j)
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_dwp_memLp_Ω'' j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω'']
            D.weak_partial j :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        (h_dwp_weak_uChart_Ω'' j) h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_j_memW1p_Ω'' j)
  exact h_uChart_memWkp_two_Ω''

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
            (I := I) (M := M) g r s) i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω'' :=
  eigenvector_chartComponent_memWkp g r s i α P₀
    hΩ''_open hΩ''_compact_closure hR₀_pos h_room

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
