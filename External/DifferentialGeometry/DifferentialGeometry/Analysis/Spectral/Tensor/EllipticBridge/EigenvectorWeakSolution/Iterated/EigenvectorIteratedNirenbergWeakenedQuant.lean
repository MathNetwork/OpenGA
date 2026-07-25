import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedNirenbergWeakened
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.TensorNonSmoothDiffQuotQuant
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
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma sqrt_geometricEnergy_le
    {n : ℕ} {A B K_f : ℝ} {a : Fin n → ℝ} {a_u a_f : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hK_f : 0 ≤ K_f)
    (ha_nn : ∀ l, 0 ≤ a l) (ha_le : ∀ l, a l ≤ A)
    (ha_u_nn : 0 ≤ a_u) (ha_u_le : a_u ≤ A)
    (ha_f_nn : 0 ≤ a_f) (ha_f_le : a_f ≤ K_f * B) :
    Real.sqrt ((∑ l : Fin n, (a l) ^ 2) + a_u ^ 2 + a_f ^ 2) ≤
      Real.sqrt ((n : ℝ) + 1 + K_f ^ 2) * (A + B) := by
  set C₂ : ℝ := Real.sqrt ((n : ℝ) + 1 + K_f ^ 2) with hC₂_def
  have hC₂_nn : 0 ≤ C₂ := Real.sqrt_nonneg _
  have h_radicand_nn : 0 ≤ (n : ℝ) + 1 + K_f ^ 2 := by positivity
  have h_sum_le : (∑ l : Fin n, (a l) ^ 2) ≤ (n : ℝ) * A ^ 2 := by
    have h_each : ∀ l : Fin n, (a l) ^ 2 ≤ A ^ 2 := fun l =>
      pow_le_pow_left₀ (ha_nn l) (ha_le l) 2
    calc (∑ l : Fin n, (a l) ^ 2) ≤ ∑ _l : Fin n, A ^ 2 :=
          Finset.sum_le_sum (fun l _ => h_each l)
      _ = (n : ℝ) * A ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  have h_u_le : a_u ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ha_u_nn ha_u_le 2
  have h_f_le : a_f ^ 2 ≤ K_f ^ 2 * B ^ 2 := by
    have h1 : a_f ^ 2 ≤ (K_f * B) ^ 2 := pow_le_pow_left₀ ha_f_nn ha_f_le 2
    calc a_f ^ 2 ≤ (K_f * B) ^ 2 := h1
      _ = K_f ^ 2 * B ^ 2 := by ring
  have h_energy_le :
      (∑ l : Fin n, (a l) ^ 2) + a_u ^ 2 + a_f ^ 2 ≤
        ((n : ℝ) + 1 + K_f ^ 2) * (A + B) ^ 2 := by
    have h_AB_sq : A ^ 2 ≤ (A + B) ^ 2 := by nlinarith [hB, hA, sq_nonneg B]
    have h_BB_sq : B ^ 2 ≤ (A + B) ^ 2 := by nlinarith [hB, hA, sq_nonneg A]
    have h_step : (∑ l : Fin n, (a l) ^ 2) + a_u ^ 2 + a_f ^ 2 ≤
        (n : ℝ) * A ^ 2 + A ^ 2 + K_f ^ 2 * B ^ 2 := by
      have := h_sum_le
      have := h_u_le
      have := h_f_le
      linarith
    have h_step2 : (n : ℝ) * A ^ 2 + A ^ 2 + K_f ^ 2 * B ^ 2 ≤
        ((n : ℝ) + 1 + K_f ^ 2) * (A + B) ^ 2 := by
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [h_AB_sq, h_BB_sq, hn_nn, sq_nonneg K_f, _hK_f]
    linarith
  calc Real.sqrt ((∑ l : Fin n, (a l) ^ 2) + a_u ^ 2 + a_f ^ 2)
      ≤ Real.sqrt (((n : ℝ) + 1 + K_f ^ 2) * (A + B) ^ 2) :=
        Real.sqrt_le_sqrt h_energy_le
    _ = Real.sqrt ((n : ℝ) + 1 + K_f ^ 2) * Real.sqrt ((A + B) ^ 2) := by
        rw [Real.sqrt_mul h_radicand_nn]
    _ = C₂ * (A + B) := by
        rw [hC₂_def, Real.sqrt_sq (by linarith [hA, hB])]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma eLpNorm_volume_restrict_compact_le_weighted
    (g : SmoothRiemannianMetric I M) (α : M) (f : EuclN → ℝ)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c_d : ℝ, 0 ≤ c_d ∧
      eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
        ENNReal.ofReal c_d *
          eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) α hK_compact hK_meas hK_in
  set c_d_enn : ℝ≥0∞ :=
    (ENNReal.ofReal c) ^ ((1 / 2 : ℝ≥0∞).toReal) with hc_d_enn_def
  have hc_d_enn_ne_top : c_d_enn ≠ ⊤ := by
    rw [hc_d_enn_def]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  refine ⟨c_d_enn.toReal, ENNReal.toReal_nonneg, ?_⟩
  have h_mono :
      eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
        eLpNorm f 2 (ENNReal.ofReal c •
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) :=
    eLpNorm_mono_measure f h_le
  have h_smul :
      eLpNorm f 2 (ENNReal.ofReal c •
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) =
        c_d_enn •
          eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hc_d_enn_def]
    exact eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f
      (ENNReal.ofReal c)
  have h_smul_eq :
      c_d_enn •
        eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal c_d_enn.toReal *
        eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [smul_eq_mul, ENNReal.ofReal_toReal hc_d_enn_ne_top]
  rw [h_smul, h_smul_eq] at h_mono
  exact h_mono

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma eLpNorm_volume_restrict_compact_le_weighted_uniform
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c_d : ℝ, 0 ≤ c_d ∧
      ∀ f : EuclN → ℝ,
        eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
          ENNReal.ofReal c_d *
            eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) α hK_compact hK_meas hK_in
  set c_d_enn : ℝ≥0∞ :=
    (ENNReal.ofReal c) ^ ((1 / 2 : ℝ≥0∞).toReal) with hc_d_enn_def
  have hc_d_enn_ne_top : c_d_enn ≠ ⊤ := by
    rw [hc_d_enn_def]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  refine ⟨c_d_enn.toReal, ENNReal.toReal_nonneg, fun f => ?_⟩
  have h_mono :
      eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
        eLpNorm f 2 (ENNReal.ofReal c •
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) :=
    eLpNorm_mono_measure f h_le
  have h_smul :
      eLpNorm f 2 (ENNReal.ofReal c •
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) =
        c_d_enn •
          eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hc_d_enn_def]
    exact eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f
      (ENNReal.ofReal c)
  have h_smul_eq :
      c_d_enn •
        eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal c_d_enn.toReal *
        eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [smul_eq_mul, ENNReal.ofReal_toReal hc_d_enn_ne_top]
  rw [h_smul, h_smul_eq] at h_mono
  exact h_mono

set_option maxHeartbeats 1600000 in

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_wkpNorm_two_two_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m)
    (h_dir : D_m.directions = directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m directions)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ ∃ C : ℝ, 0 < C ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m directions)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C *
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m directions)
            (chartTargetEuclid (I := I) (M := M) α)
          + eLpNorm
              ((eigenvectorIteratedTensorChartBilinearData_toData
                  (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart)
              2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorIteratedTensorChartBilinearData_toData
      (I := I) (M := M) g r s i α P₀ D_m h_parent
    with hD_def
  have hD_u_chart : D.u_chart =
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m D_m.directions := rfl
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m directions)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartIteratedPartial_memWkp_two_two
      g r s i α P₀ directions D_m h_dir h_parent
  set P : EuclN → ℝ :=
    eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s i α P₀ m directions with hP_def
  have hD_u_chart_P : D.u_chart = P := by rw [hD_u_chart, hP_def, h_dir]
  have hD_weak_partial : ∀ j,
      D.weak_partial j =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j P (chartTargetEuclid (I := I) (M := M) α) := by
    intro j
    rw [hP_def]
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        2 j (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m D_m.directions)
        (chartTargetEuclid (I := I) (M := M) α) = _
    rw [h_dir]
  have hD_f_chart : D.f_chart = D_m.diffChartForcing := rfl
  refine ⟨h_first, ?_⟩
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
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
  obtain ⟨h_uChart_memW1p, h_wp_memW1p⟩ :=
    tensorChartBilinear_chartComponent_regularity_of_data
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p, fun j => ?_⟩
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j (D.weak_partial j) D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial j)
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p j
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial j)
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p j).1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω'']
            D.weak_partial j :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_memW1p j)
  set K_Ω : Set EuclN := closure Ω'' with hK_Ω_def
  have hK_Ω_compact : IsCompact K_Ω := hΩ''_compact_closure
  set ε : ℝ := R₀ / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set Ω' : Set EuclN := Metric.thickening (8 * ε) K_Ω with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) K_Ω :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart : Metric.cthickening (8 * ε) K_Ω ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R₀ := by rw [hε_def]; linarith
    exact (Metric.cthickening_mono hle K_Ω).trans h_room
  have h_closureΩ'_in_chart :
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hK_Ω_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ'_sub
  set K_η : Set EuclN := Metric.cthickening (3 * ε) K_Ω with hK_η_def
  have hK_η_compact : IsCompact K_η := hK_Ω_compact.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) K_Ω with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η :=
    Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_Ω
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
    have h_tsupp_in_cthick_5ε : tsupport η ⊆ Metric.cthickening (5 * ε) K_Ω := by
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
          Metric.cthickening |h| (Metric.cthickening (5 * ε) K_Ω) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 : Metric.cthickening |h| (Metric.cthickening (5 * ε) K_Ω) ⊆
          Metric.cthickening (|h| + 5 * ε) K_Ω :=
        Metric.cthickening_cthickening_subset h_abs_pos.le (by positivity) K_Ω
      have h_le : |h| + 5 * ε < 8 * ε := by nlinarith [hε_pos]
      have h3 : Metric.cthickening (|h| + 5 * ε) K_Ω ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le K_Ω
      exact (h1.trans h2).trans h3
  have h_room_ε : Metric.cthickening ε (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    (Metric.cthickening_mono (by rw [hε_def]; linarith) (closure Ω'')).trans h_room
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    tensor_h2_chart_loc_of_data_quantitative (I := I) (M := M) (g := g)
      (α := α) (r := r) (s := s) (P₀ := P₀)
      hη_smooth hη_supp hη_range hN_nn h_fderiv_eta hΩ'_open h_closureΩ'_in_chart
      hΩ'_compact_closure hη_in_Ω' hε_pos hh_supp_in_Ω' hη_one_on_Ω''
      hΩ''_open hΩ''_compact_closure h_room_ε
  clear_value P K Ω'' Ω'
  set RHS_inner : ℝ≥0∞ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 2 P (chartTargetEuclid (I := I) (M := M) α)
    + eLpNorm D.f_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) with hRHS_inner_def
  have h_P_W1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2 P
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
      (by norm_num : (1 : ℕ) ≤ 2) h_first
  have h_wkpNorm1_finite :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2 P
        (chartTargetEuclid (I := I) (M := M) α) < ⊤ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_lt_top_of_memWkp
      h_P_W1
  have h_fchart_memLp :
      MemLp D.f_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hD_f_chart]
    exact D_m.fChartEff_memLp_weighted
  have h_fchart_eLpNorm_finite :
      eLpNorm D.f_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≠ ⊤ :=
    h_fchart_memLp.eLpNorm_lt_top.ne
  set A : ℝ :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 2 P
      (chartTargetEuclid (I := I) (M := M) α)).toReal with hA_def
  set B : ℝ :=
    (eLpNorm D.f_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))).toReal with hB_def
  have hA_nn : 0 ≤ A := ENNReal.toReal_nonneg
  have hB_nn : 0 ≤ B := ENNReal.toReal_nonneg
  have h_ofReal_A_le :
      ENNReal.ofReal A ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2 P
          (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hA_def]; exact ENNReal.ofReal_toReal_le
  have h_ofReal_B_le :
      ENNReal.ofReal B ≤
        eLpNorm D.f_chart 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hB_def]; exact ENNReal.ofReal_toReal_le
  have h_ofReal_AB_le_RHS :
      ENNReal.ofReal A + ENNReal.ofReal B ≤ RHS_inner := by
    rw [hRHS_inner_def]
    exact add_le_add h_ofReal_A_le h_ofReal_B_le
  obtain ⟨c_d, hc_d_nn, h_fchart_density⟩ :=
    eLpNorm_volume_restrict_compact_le_weighted (I := I) (M := M) g α D.f_chart
      hΩ'_compact_closure hΩ'_compact_closure.isClosed.measurableSet
      h_closureΩ'_in_chart
  have h_restrict_mono :
      (volume : Measure EuclN).restrict (closure Ω') ≤
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) :=
    Measure.restrict_mono h_closureΩ'_in_chart (le_refl (volume : Measure EuclN))
  have h_wp_eLpNorm_le : ∀ l,
      eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω')) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2 P
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro l
    have h_mono :
        eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω')) ≤
          eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
      eLpNorm_mono_measure _ h_restrict_mono
    have h_eq :
        eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) =
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 0 2
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 l P (chartTargetEuclid (I := I) (M := M) α))
            (chartTargetEuclid (I := I) (M := M) α) := by
      rw [hD_weak_partial l,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero]
    have h_chosen_le :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 0 2
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 l P (chartTargetEuclid (I := I) (M := M) α))
            (chartTargetEuclid (I := I) (M := M) α) ≤
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2 P
            (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_chosenWeakPartial_le
        0 h_chart_open P l
    exact h_mono.trans (h_eq ▸ h_chosen_le)
  have h_uChart_eLpNorm_le :
      eLpNorm D.u_chart 2
          ((volume : Measure EuclN).restrict (closure Ω')) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2 P
          (chartTargetEuclid (I := I) (M := M) α) := by
    have h_mono :
        eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω')) ≤
          eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
      eLpNorm_mono_measure _ h_restrict_mono
    rw [hD_u_chart_P] at h_mono ⊢
    exact h_mono.trans
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_le_wkpNorm
        1 2 (chartTargetEuclid (I := I) (M := M) α) P)
  have h_wp_toReal_le : ∀ l,
      (eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ A := by
    intro l
    rw [hA_def]
    exact ENNReal.toReal_mono h_wkpNorm1_finite.ne (h_wp_eLpNorm_le l)
  have h_uChart_toReal_le :
      (eLpNorm D.u_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ A := by
    rw [hA_def]
    exact ENNReal.toReal_mono h_wkpNorm1_finite.ne h_uChart_eLpNorm_le
  have h_fchart_toReal_le :
      (eLpNorm D.f_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ c_d * B := by
    have h_rhs_ne_top :
        ENNReal.ofReal c_d *
            eLpNorm D.f_chart 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_fchart_eLpNorm_finite
    have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_fchart_density
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_d_nn, ← hB_def] at h_toReal
  set C₂ : ℝ :=
    Real.sqrt (((Module.finrank ℝ E : ℕ) : ℝ) + 1 + c_d ^ 2) with hC₂_def
  have hC₂_nn : 0 ≤ C₂ := Real.sqrt_nonneg _
  have h_sqrt_data_le :
      Real.sqrt (
        (∑ l : Fin (Module.finrank ℝ E),
          (eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        + (eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
        + (eLpNorm D.f_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
      ≤ C₂ * (A + B) := by
    rw [hC₂_def]
    exact sqrt_geometricEnergy_le hA_nn hB_nn hc_d_nn
      (fun l => ENNReal.toReal_nonneg) h_wp_toReal_le
      ENNReal.toReal_nonneg h_uChart_toReal_le
      ENNReal.toReal_nonneg h_fchart_toReal_le
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
  set C₁ : ℝ := C_geom_max * C₂ with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := mul_nonneg hC_geom_max_nn hC₂_nn
  have h_gik_bound : ∀ i' k' : Fin (Module.finrank ℝ E),
      ∃ g_ik : EuclN → ℝ,
        MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
        DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k' g_ik
          (D.weak_partial i') Ω'' ∧
        eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
          ENNReal.ofReal C₁ * RHS_inner := by
    intro i' k'
    obtain ⟨g_ik, hg_ik_memLp, hg_ik_weak, hg_ik_norm⟩ := hC_geom D i' k'
    refine ⟨g_ik, hg_ik_memLp, hg_ik_weak, ?_⟩
    have h_real_le :
        C_geom i' k' * Real.sqrt (
          (∑ l : Fin (Module.finrank ℝ E),
            (eLpNorm (D.weak_partial l) 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
          + (eLpNorm D.u_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
          + (eLpNorm D.f_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        ≤ C₁ * (A + B) := by
      have h_sqrt_nn : 0 ≤ Real.sqrt (
          (∑ l : Fin (Module.finrank ℝ E),
            (eLpNorm (D.weak_partial l) 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
          + (eLpNorm D.u_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
          + (eLpNorm D.f_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2) :=
        Real.sqrt_nonneg _
      have h_AB_nn : 0 ≤ A + B := by linarith
      calc C_geom i' k' * Real.sqrt _
          ≤ C_geom i' k' * (C₂ * (A + B)) :=
            mul_le_mul_of_nonneg_left h_sqrt_data_le (hC_geom_nn i' k')
        _ ≤ C_geom_max * (C₂ * (A + B)) :=
            mul_le_mul_of_nonneg_right (hC_geom_le_max i' k')
              (mul_nonneg hC₂_nn h_AB_nn)
        _ = C₁ * (A + B) := by rw [hC₁_def]; ring
    refine hg_ik_norm.trans ?_
    calc ENNReal.ofReal (C_geom i' k' * Real.sqrt _)
        ≤ ENNReal.ofReal (C₁ * (A + B)) := ENNReal.ofReal_le_ofReal h_real_le
      _ = ENNReal.ofReal C₁ * (ENNReal.ofReal A + ENNReal.ofReal B) := by
          rw [ENNReal.ofReal_mul hC₁_nn, ENNReal.ofReal_add hA_nn hB_nn]
      _ ≤ ENNReal.ofReal C₁ * RHS_inner :=
          mul_le_mul_right h_ofReal_AB_le_RHS _
  have h_chosen_ae_wp : ∀ i' : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i' D.u_chart Ω''
        =ᵐ[(volume : Measure EuclN).restrict Ω''] D.weak_partial i' := by
    intro i'
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i' (D.weak_partial i') D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial i')
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i'
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i' D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p i'
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i' D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p i').locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial i')
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p i').1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
      h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
  have h_per_i_bound : ∀ i' : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            2 i' D.u_chart Ω'') Ω''
        ≤ RHS_inner +
          ∑ _k' : Fin (Module.finrank ℝ E), ENNReal.ofReal C₁ * RHS_inner := by
    intro i'
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open (h_chosen_ae_wp i')]
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_succ_eq_eLpNorm_add_sum_partial
      0 2 Ω'' (D.weak_partial i')]
    refine add_le_add ?_ (Finset.sum_le_sum (fun k' _ => ?_))
    · have h_mono :
          eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict Ω'') ≤
            eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_mono_measure _
          (Measure.restrict_mono hΩ''_in_chart
            (le_refl (volume : Measure EuclN)))
      have h_wp_eq :
          eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 0 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                2 i' P (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hD_weak_partial i',
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero]
      have h_chosen_le :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 0 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                2 i' P (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α) ≤
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_chosenWeakPartial_le
          0 h_chart_open P i'
      have h_le_wkpNorm1 :
          eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict Ω'') ≤
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) :=
        h_mono.trans (h_wp_eq ▸ h_chosen_le)
      exact h_le_wkpNorm1.trans (by rw [hRHS_inner_def]; exact le_self_add)
    · rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero]
      obtain ⟨g_ik, hg_ik_memLp, hg_ik_weak, hg_ik_bd⟩ := h_gik_bound i' k'
      have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
          (d := Module.finrank ℝ E) k'
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            2 k' (D.weak_partial i') Ω'') (D.weak_partial i') Ω'' :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
          (h_wp_memW1p i') k'
      have h_chosen_loc : MeasureTheory.LocallyIntegrable
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            2 k' (D.weak_partial i') Ω'') ((volume : Measure EuclN).restrict Ω'') :=
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
          (h_wp_memW1p i') k').locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_g_ik_loc : MeasureTheory.LocallyIntegrable g_ik
          ((volume : Measure EuclN).restrict Ω'') :=
        hg_ik_memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_ae :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 k' (D.weak_partial i') Ω''
            =ᵐ[(volume : Measure EuclN).restrict Ω''] g_ik :=
        DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial hg_ik_weak
          h_chosen_loc h_g_ik_loc
      rw [eLpNorm_congr_ae h_ae]
      exact hg_ik_bd
  set C' : ℝ :=
    1 + ((Module.finrank ℝ E : ℕ) : ℝ)
      + ((Module.finrank ℝ E : ℕ) : ℝ) ^ 2 * C₁ with hC'_def
  have hC'_pos : 0 < C' := by
    rw [hC'_def]
    have h1 : (0 : ℝ) ≤ ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ ((Module.finrank ℝ E : ℕ) : ℝ) ^ 2 * C₁ :=
      mul_nonneg (by positivity) hC₁_nn
    linarith
  have h_interior_bound :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 D.u_chart Ω''
        ≤ ENNReal.ofReal C' * RHS_inner := by
    rw [show (2 : ℕ) = 1 + 1 from rfl,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_succ_eq_eLpNorm_add_sum_partial
        1 2 Ω'' D.u_chart]
    have h_uChart_le_RHS :
        eLpNorm D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') ≤
          RHS_inner := by
      have h_mono :
          eLpNorm D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') ≤
            eLpNorm D.u_chart 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_mono_measure _
          (Measure.restrict_mono hΩ''_in_chart
            (le_refl (volume : Measure EuclN)))
      rw [hD_u_chart_P] at h_mono ⊢
      have h_le_wkpNorm1 :
          eLpNorm P 2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_le_wkpNorm
          1 2 (chartTargetEuclid (I := I) (M := M) α) P
      calc eLpNorm P 2 ((volume : Measure EuclN).restrict Ω'')
          ≤ eLpNorm P 2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := h_mono
        _ ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) := h_le_wkpNorm1
        _ ≤ RHS_inner := by rw [hRHS_inner_def]; exact le_self_add
    have h_sum_le :
        (∑ i' : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 i' D.u_chart Ω'') Ω'')
          ≤ ∑ _i' : Fin (Module.finrank ℝ E),
              (RHS_inner +
                ∑ _k' : Fin (Module.finrank ℝ E),
                  ENNReal.ofReal C₁ * RHS_inner) :=
      Finset.sum_le_sum (fun i' _ => h_per_i_bound i')
    refine (add_le_add h_uChart_le_RHS h_sum_le).trans ?_
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h_ofReal_C' :
        ENNReal.ofReal C' =
          1 + ((Module.finrank ℝ E : ℕ) : ℝ≥0∞)
            + ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal C₁ := by
      rw [hC'_def]
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by norm_num) (Nat.cast_nonneg _),
        ENNReal.ofReal_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_natCast]
    rw [h_ofReal_C']
    simp only [nsmul_eq_mul]
    exact le_of_eq (by ring)
  have h_global_Lp : MemLp P 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hP_def]
    exact eigenvectorChartIteratedPartial_memLp_volume
      (I := I) (M := M) g r s i α P₀ m directions
  have h_ae_zero :
      P =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K)] 0 := by
    rw [hP_def, hK_def]
    exact eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m directions
  obtain ⟨K_prom, hK_prom_pos, hK_prom_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_le_of_memWkp_precompact_of_ae_zero_off_compact
      (d := Module.finrank ℝ E) (k := 2) (p := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
      h_ae_zero (hD_u_chart_P ▸ h_uChart_memWkp_two_Ω'')
  refine ⟨K_prom * C', mul_pos hK_prom_pos hC'_pos, ?_⟩
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 P
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal K_prom *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2 P Ω'' := hK_prom_bound
    _ = ENNReal.ofReal K_prom *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
        rw [hD_u_chart_P]
    _ ≤ ENNReal.ofReal K_prom * (ENNReal.ofReal C' * RHS_inner) :=
        mul_le_mul_right h_interior_bound _
    _ = ENNReal.ofReal (K_prom * C') * RHS_inner := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK_prom_pos.le]

set_option maxHeartbeats 1600000 in

omit [CompleteSpace E] in
theorem eigenvectorChartIteratedPartial_wkpNorm_two_two_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (directions : Fin m → Fin (Module.finrank ℝ E))
        (D_m : eigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
          g r s i α P₀ m)
        (_h_dir : D_m.directions = directions)
        (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m directions)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ m directions)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
                (d := Module.finrank ℝ E) 1 2
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ m directions)
                (chartTargetEuclid (I := I) (M := M) α)
              + eLpNorm
                  ((eigenvectorIteratedTensorChartBilinearData_toData
                      (I := I) (M := M) g r s i α P₀ D_m h_parent).f_chart)
                  2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
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
  set K_Ω : Set EuclN := closure Ω'' with hK_Ω_def
  have hK_Ω_compact : IsCompact K_Ω := hΩ''_compact_closure
  set ε : ℝ := R₀ / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set Ω' : Set EuclN := Metric.thickening (8 * ε) K_Ω with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) K_Ω :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart : Metric.cthickening (8 * ε) K_Ω ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R₀ := by rw [hε_def]; linarith
    exact (Metric.cthickening_mono hle K_Ω).trans h_room
  have h_closureΩ'_in_chart :
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hK_Ω_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ'_sub
  set K_η : Set EuclN := Metric.cthickening (3 * ε) K_Ω with hK_η_def
  have hK_η_compact : IsCompact K_η := hK_Ω_compact.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) K_Ω with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η :=
    Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_Ω
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
    have h_tsupp_in_cthick_5ε : tsupport η ⊆ Metric.cthickening (5 * ε) K_Ω := by
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
          Metric.cthickening |h| (Metric.cthickening (5 * ε) K_Ω) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 : Metric.cthickening |h| (Metric.cthickening (5 * ε) K_Ω) ⊆
          Metric.cthickening (|h| + 5 * ε) K_Ω :=
        Metric.cthickening_cthickening_subset h_abs_pos.le (by positivity) K_Ω
      have h_le : |h| + 5 * ε < 8 * ε := by nlinarith [hε_pos]
      have h3 : Metric.cthickening (|h| + 5 * ε) K_Ω ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le K_Ω
      exact (h1.trans h2).trans h3
  have h_room_ε : Metric.cthickening ε (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    (Metric.cthickening_mono (by rw [hε_def]; linarith) (closure Ω'')).trans h_room
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    tensor_h2_chart_loc_of_data_quantitative (I := I) (M := M) (g := g)
      (α := α) (r := r) (s := s) (P₀ := P₀)
      hη_smooth hη_supp hη_range hN_nn h_fderiv_eta hΩ'_open h_closureΩ'_in_chart
      hΩ'_compact_closure hη_in_Ω' hε_pos hh_supp_in_Ω' hη_one_on_Ω''
      hΩ''_open hΩ''_compact_closure h_room_ε
  clear_value K Ω'' Ω'
  obtain ⟨c_d, hc_d_nn, h_fchart_density_uniform⟩ :=
    eLpNorm_volume_restrict_compact_le_weighted_uniform (I := I) (M := M) g α
      hΩ'_compact_closure hΩ'_compact_closure.isClosed.measurableSet
      h_closureΩ'_in_chart
  obtain ⟨K_prom, hK_prom_pos, hK_prom_bound_uniform⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_le_of_memWkp_precompact_of_ae_zero_off_compact_uniform
      (d := Module.finrank ℝ E) (k := 2) (p := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      h_chart_open hΩ''_open hK_compact hK_in_Ω'' h_closureΩ''_in_chart
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
  set C₂ : ℝ :=
    Real.sqrt (((Module.finrank ℝ E : ℕ) : ℝ) + 1 + c_d ^ 2) with hC₂_def
  have hC₂_nn : 0 ≤ C₂ := Real.sqrt_nonneg _
  set C₁ : ℝ := C_geom_max * C₂ with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := mul_nonneg hC_geom_max_nn hC₂_nn
  set C' : ℝ :=
    1 + ((Module.finrank ℝ E : ℕ) : ℝ)
      + ((Module.finrank ℝ E : ℕ) : ℝ) ^ 2 * C₁ with hC'_def
  have hC'_pos : 0 < C' := by
    rw [hC'_def]
    have h1 : (0 : ℝ) ≤ ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ ((Module.finrank ℝ E : ℕ) : ℝ) ^ 2 * C₁ :=
      mul_nonneg (by positivity) hC₁_nn
    linarith
  refine ⟨K_prom * C', mul_pos hK_prom_pos hC'_pos, ?_⟩
  intro i directions D_m h_dir h_parent
  set D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
    eigenvectorIteratedTensorChartBilinearData_toData
      (I := I) (M := M) g r s i α P₀ D_m h_parent
    with hD_def
  have hD_u_chart : D.u_chart =
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m D_m.directions := rfl
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m directions)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartIteratedPartial_memWkp_two_two
      g r s i α P₀ directions D_m h_dir h_parent
  set P : EuclN → ℝ :=
    eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s i α P₀ m directions with hP_def
  have hD_u_chart_P : D.u_chart = P := by rw [hD_u_chart, hP_def, h_dir]
  have hD_weak_partial : ∀ j,
      D.weak_partial j =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j P (chartTargetEuclid (I := I) (M := M) α) := by
    intro j
    rw [hP_def]
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        2 j (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m D_m.directions)
        (chartTargetEuclid (I := I) (M := M) α) = _
    rw [h_dir]
  have hD_f_chart : D.f_chart = D_m.diffChartForcing := rfl
  refine ⟨h_first, ?_⟩
  obtain ⟨h_uChart_memW1p, h_wp_memW1p⟩ :=
    tensorChartBilinear_chartComponent_regularity_of_data
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_uChart_memWkp_two_Ω'' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
    refine ⟨h_uChart_memW1p, fun j => ?_⟩
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j (D.weak_partial j) D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial j)
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) j
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p j
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial j)
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p j).1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 j D.u_chart Ω'' =ᵐ[(volume : Measure EuclN).restrict Ω'']
            D.weak_partial j :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
      hΩ''_open h_ae.symm).mp (h_wp_memW1p j)
  set RHS_inner : ℝ≥0∞ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 2 P (chartTargetEuclid (I := I) (M := M) α)
    + eLpNorm D.f_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) with hRHS_inner_def
  have h_P_W1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2 P
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
      (by norm_num : (1 : ℕ) ≤ 2) h_first
  have h_wkpNorm1_finite :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2 P
        (chartTargetEuclid (I := I) (M := M) α) < ⊤ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_lt_top_of_memWkp
      h_P_W1
  have h_fchart_memLp :
      MemLp D.f_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hD_f_chart]
    exact D_m.fChartEff_memLp_weighted
  have h_fchart_eLpNorm_finite :
      eLpNorm D.f_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≠ ⊤ :=
    h_fchart_memLp.eLpNorm_lt_top.ne
  set A : ℝ :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 2 P
      (chartTargetEuclid (I := I) (M := M) α)).toReal with hA_def
  set B : ℝ :=
    (eLpNorm D.f_chart 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))).toReal with hB_def
  have hA_nn : 0 ≤ A := ENNReal.toReal_nonneg
  have hB_nn : 0 ≤ B := ENNReal.toReal_nonneg
  have h_ofReal_A_le :
      ENNReal.ofReal A ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2 P
          (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hA_def]; exact ENNReal.ofReal_toReal_le
  have h_ofReal_B_le :
      ENNReal.ofReal B ≤
        eLpNorm D.f_chart 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hB_def]; exact ENNReal.ofReal_toReal_le
  have h_ofReal_AB_le_RHS :
      ENNReal.ofReal A + ENNReal.ofReal B ≤ RHS_inner := by
    rw [hRHS_inner_def]
    exact add_le_add h_ofReal_A_le h_ofReal_B_le
  have h_fchart_density :
      eLpNorm D.f_chart 2 ((volume : Measure EuclN).restrict (closure Ω')) ≤
        ENNReal.ofReal c_d *
          eLpNorm D.f_chart 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
    h_fchart_density_uniform D.f_chart
  have h_restrict_mono :
      (volume : Measure EuclN).restrict (closure Ω') ≤
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) :=
    Measure.restrict_mono h_closureΩ'_in_chart (le_refl (volume : Measure EuclN))
  have h_wp_eLpNorm_le : ∀ l,
      eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω')) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2 P
          (chartTargetEuclid (I := I) (M := M) α) := by
    intro l
    have h_mono :
        eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω')) ≤
          eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
      eLpNorm_mono_measure _ h_restrict_mono
    have h_eq :
        eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) =
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 0 2
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 l P (chartTargetEuclid (I := I) (M := M) α))
            (chartTargetEuclid (I := I) (M := M) α) := by
      rw [hD_weak_partial l,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero]
    have h_chosen_le :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 0 2
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 l P (chartTargetEuclid (I := I) (M := M) α))
            (chartTargetEuclid (I := I) (M := M) α) ≤
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2 P
            (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_chosenWeakPartial_le
        0 h_chart_open P l
    exact h_mono.trans (h_eq ▸ h_chosen_le)
  have h_uChart_eLpNorm_le :
      eLpNorm D.u_chart 2
          ((volume : Measure EuclN).restrict (closure Ω')) ≤
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2 P
          (chartTargetEuclid (I := I) (M := M) α) := by
    have h_mono :
        eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω')) ≤
          eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
      eLpNorm_mono_measure _ h_restrict_mono
    rw [hD_u_chart_P] at h_mono ⊢
    exact h_mono.trans
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_le_wkpNorm
        1 2 (chartTargetEuclid (I := I) (M := M) α) P)
  have h_wp_toReal_le : ∀ l,
      (eLpNorm (D.weak_partial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ A := by
    intro l
    rw [hA_def]
    exact ENNReal.toReal_mono h_wkpNorm1_finite.ne (h_wp_eLpNorm_le l)
  have h_uChart_toReal_le :
      (eLpNorm D.u_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ A := by
    rw [hA_def]
    exact ENNReal.toReal_mono h_wkpNorm1_finite.ne h_uChart_eLpNorm_le
  have h_fchart_toReal_le :
      (eLpNorm D.f_chart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ≤ c_d * B := by
    have h_rhs_ne_top :
        ENNReal.ofReal c_d *
            eLpNorm D.f_chart 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_fchart_eLpNorm_finite
    have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_fchart_density
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc_d_nn, ← hB_def] at h_toReal
  have h_sqrt_data_le :
      Real.sqrt (
        (∑ l : Fin (Module.finrank ℝ E),
          (eLpNorm (D.weak_partial l) 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        + (eLpNorm D.u_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
        + (eLpNorm D.f_chart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
      ≤ C₂ * (A + B) := by
    rw [hC₂_def]
    exact sqrt_geometricEnergy_le hA_nn hB_nn hc_d_nn
      (fun l => ENNReal.toReal_nonneg) h_wp_toReal_le
      ENNReal.toReal_nonneg h_uChart_toReal_le
      ENNReal.toReal_nonneg h_fchart_toReal_le
  have h_gik_bound : ∀ i' k' : Fin (Module.finrank ℝ E),
      ∃ g_ik : EuclN → ℝ,
        MemLp g_ik 2 ((volume : Measure EuclN).restrict Ω'') ∧
        DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k' g_ik
          (D.weak_partial i') Ω'' ∧
        eLpNorm g_ik 2 ((volume : Measure EuclN).restrict Ω'') ≤
          ENNReal.ofReal C₁ * RHS_inner := by
    intro i' k'
    obtain ⟨g_ik, hg_ik_memLp, hg_ik_weak, hg_ik_norm⟩ := hC_geom D i' k'
    refine ⟨g_ik, hg_ik_memLp, hg_ik_weak, ?_⟩
    have h_real_le :
        C_geom i' k' * Real.sqrt (
          (∑ l : Fin (Module.finrank ℝ E),
            (eLpNorm (D.weak_partial l) 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
          + (eLpNorm D.u_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
          + (eLpNorm D.f_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        ≤ C₁ * (A + B) := by
      have h_sqrt_nn : 0 ≤ Real.sqrt (
          (∑ l : Fin (Module.finrank ℝ E),
            (eLpNorm (D.weak_partial l) 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
          + (eLpNorm D.u_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
          + (eLpNorm D.f_chart 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2) :=
        Real.sqrt_nonneg _
      have h_AB_nn : 0 ≤ A + B := by linarith
      calc C_geom i' k' * Real.sqrt _
          ≤ C_geom i' k' * (C₂ * (A + B)) :=
            mul_le_mul_of_nonneg_left h_sqrt_data_le (hC_geom_nn i' k')
        _ ≤ C_geom_max * (C₂ * (A + B)) :=
            mul_le_mul_of_nonneg_right (hC_geom_le_max i' k')
              (mul_nonneg hC₂_nn h_AB_nn)
        _ = C₁ * (A + B) := by rw [hC₁_def]; ring
    refine hg_ik_norm.trans ?_
    calc ENNReal.ofReal (C_geom i' k' * Real.sqrt _)
        ≤ ENNReal.ofReal (C₁ * (A + B)) := ENNReal.ofReal_le_ofReal h_real_le
      _ = ENNReal.ofReal C₁ * (ENNReal.ofReal A + ENNReal.ofReal B) := by
          rw [ENNReal.ofReal_mul hC₁_nn, ENNReal.ofReal_add hA_nn hB_nn]
      _ ≤ ENNReal.ofReal C₁ * RHS_inner :=
          mul_le_mul_right h_ofReal_AB_le_RHS _
  have h_chosen_ae_wp : ∀ i' : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i' D.u_chart Ω''
        =ᵐ[(volume : Measure EuclN).restrict Ω''] D.weak_partial i' := by
    intro i'
    have h_dwp_weak_uChart_Ω'' : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i' (D.weak_partial i') D.u_chart Ω'' :=
      DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
        (D.weak_partial_isWeakPartial i')
    have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i'
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i' D.u_chart Ω'') D.u_chart Ω'' :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
        h_uChart_memW1p i'
    have h_chosen_loc : MeasureTheory.LocallyIntegrable
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          2 i' D.u_chart Ω'') ((volume : Measure EuclN).restrict Ω'') :=
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
        h_uChart_memW1p i').locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_loc : MeasureTheory.LocallyIntegrable (D.weak_partial i')
        ((volume : Measure EuclN).restrict Ω'') :=
      (h_wp_memW1p i').1.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
      h_dwp_weak_uChart_Ω'' h_chosen_loc h_dwp_loc
  have h_per_i_bound : ∀ i' : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            2 i' D.u_chart Ω'') Ω''
        ≤ RHS_inner +
          ∑ _k' : Fin (Module.finrank ℝ E), ENNReal.ofReal C₁ * RHS_inner := by
    intro i'
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ''_open (h_chosen_ae_wp i')]
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_succ_eq_eLpNorm_add_sum_partial
      0 2 Ω'' (D.weak_partial i')]
    refine add_le_add ?_ (Finset.sum_le_sum (fun k' _ => ?_))
    · have h_mono :
          eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict Ω'') ≤
            eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_mono_measure _
          (Measure.restrict_mono hΩ''_in_chart
            (le_refl (volume : Measure EuclN)))
      have h_wp_eq :
          eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 0 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                2 i' P (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hD_weak_partial i',
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero]
      have h_chosen_le :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 0 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                2 i' P (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α) ≤
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_chosenWeakPartial_le
          0 h_chart_open P i'
      have h_le_wkpNorm1 :
          eLpNorm (D.weak_partial i') 2
              ((volume : Measure EuclN).restrict Ω'') ≤
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) :=
        h_mono.trans (h_wp_eq ▸ h_chosen_le)
      exact h_le_wkpNorm1.trans (by rw [hRHS_inner_def]; exact le_self_add)
    · rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero]
      obtain ⟨g_ik, hg_ik_memLp, hg_ik_weak, hg_ik_bd⟩ := h_gik_bound i' k'
      have h_chosen_partial : DeGiorgi.HasWeakPartialDeriv
          (d := Module.finrank ℝ E) k'
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            2 k' (D.weak_partial i') Ω'') (D.weak_partial i') Ω'' :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
          (h_wp_memW1p i') k'
      have h_chosen_loc : MeasureTheory.LocallyIntegrable
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            2 k' (D.weak_partial i') Ω'') ((volume : Measure EuclN).restrict Ω'') :=
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
          (h_wp_memW1p i') k').locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_g_ik_loc : MeasureTheory.LocallyIntegrable g_ik
          ((volume : Measure EuclN).restrict Ω'') :=
        hg_ik_memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have h_ae :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 k' (D.weak_partial i') Ω''
            =ᵐ[(volume : Measure EuclN).restrict Ω''] g_ik :=
        DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial hg_ik_weak
          h_chosen_loc h_g_ik_loc
      rw [eLpNorm_congr_ae h_ae]
      exact hg_ik_bd
  have h_interior_bound :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 D.u_chart Ω''
        ≤ ENNReal.ofReal C' * RHS_inner := by
    rw [show (2 : ℕ) = 1 + 1 from rfl,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_succ_eq_eLpNorm_add_sum_partial
        1 2 Ω'' D.u_chart]
    have h_uChart_le_RHS :
        eLpNorm D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') ≤
          RHS_inner := by
      have h_mono :
          eLpNorm D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') ≤
            eLpNorm D.u_chart 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) :=
        eLpNorm_mono_measure _
          (Measure.restrict_mono hΩ''_in_chart
            (le_refl (volume : Measure EuclN)))
      rw [hD_u_chart_P] at h_mono ⊢
      have h_le_wkpNorm1 :
          eLpNorm P 2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_le_wkpNorm
          1 2 (chartTargetEuclid (I := I) (M := M) α) P
      calc eLpNorm P 2 ((volume : Measure EuclN).restrict Ω'')
          ≤ eLpNorm P 2 ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := h_mono
        _ ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2 P
              (chartTargetEuclid (I := I) (M := M) α) := h_le_wkpNorm1
        _ ≤ RHS_inner := by rw [hRHS_inner_def]; exact le_self_add
    have h_sum_le :
        (∑ i' : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              2 i' D.u_chart Ω'') Ω'')
          ≤ ∑ _i' : Fin (Module.finrank ℝ E),
              (RHS_inner +
                ∑ _k' : Fin (Module.finrank ℝ E),
                  ENNReal.ofReal C₁ * RHS_inner) :=
      Finset.sum_le_sum (fun i' _ => h_per_i_bound i')
    refine (add_le_add h_uChart_le_RHS h_sum_le).trans ?_
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h_ofReal_C' :
        ENNReal.ofReal C' =
          1 + ((Module.finrank ℝ E : ℕ) : ℝ≥0∞)
            + ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal C₁ := by
      rw [hC'_def]
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by norm_num) (Nat.cast_nonneg _),
        ENNReal.ofReal_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_natCast]
    rw [h_ofReal_C']
    simp only [nsmul_eq_mul]
    exact le_of_eq (by ring)
  have h_global_Lp : MemLp P 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [hP_def]
    exact eigenvectorChartIteratedPartial_memLp_volume
      (I := I) (M := M) g r s i α P₀ m directions
  have h_ae_zero :
      P =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ K)] 0 := by
    rw [hP_def, hK_def]
    exact eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m directions
  have hK_prom_bound :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 P
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal K_prom *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 2 2 P Ω'' :=
    hK_prom_bound_uniform P h_ae_zero (hD_u_chart_P ▸ h_uChart_memWkp_two_Ω'')
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 2 2 P
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal K_prom *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2 P Ω'' := hK_prom_bound
    _ = ENNReal.ofReal K_prom *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2 D.u_chart Ω'' := by
        rw [hD_u_chart_P]
    _ ≤ ENNReal.ofReal K_prom * (ENNReal.ofReal C' * RHS_inner) :=
        mul_le_mul_right h_interior_bound _
    _ = ENNReal.ofReal (K_prom * C') * RHS_inner := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK_prom_pos.le]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
