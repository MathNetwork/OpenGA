import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreyHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK


noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Chart.TowerStep
  (subcriticalConstant subcriticalConstant_nonneg MemWkp_subcritical_iterated)

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

private theorem tower_to_supercritical_quant
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) (m : ℕ) :
    ∀ (s : ℕ) {p : ℝ}, 1 ≤ p →
      RegularExponent.IsRegular (d : ℝ) p (s + 1) →
      (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p →
      ∀ {f : EuN → ℝ}, HasCompactSupport f → tsupport f ⊆ Ω →
        MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω →
          ∃ q : ℝ, 1 ≤ q ∧ (d : ℝ) < q ∧
            ∃ C : ℝ, 0 ≤ C ∧
              MemWkp (d := d) (m + 1) (ENNReal.ofReal q) f Ω ∧
              iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal q) f Ω ≤
                ENNReal.ofReal C *
                  iteratedWeakSobolevNorm (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω := by
  intro s
  induction s with
  | zero =>
      intro p hp_one _hreg hkp f _hf_cpt _hf_supp hf
      have hp_dim : (d : ℝ) < p := by
        have : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hkp
        exact hkp
      refine ⟨p, hp_one, hp_dim, 1, by norm_num, by simpa using hf, ?_⟩
      simp only [add_zero] at hf ⊢
      rw [ENNReal.ofReal_one, one_mul]
  | succ s ih =>
      intro p hp_one hreg hkp f hf_cpt hf_supp hf
      have hp_ne_d : p ≠ (d : ℝ) := hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hp_ne_d with hp_lt | hp_gt
      · have hp_pos : 0 < p := by linarith
        have hf' : MemWkp (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
          rw [h_idx] at hf
          exact hf
        obtain ⟨h_mem_p1, h_norm_p1⟩ :=
          MemWkp_subcritical_iterated (d := d) (m + 1 + s)
            hp_one hp_lt hΩ_open hf_cpt hf_supp hf'
        set p_1 : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_1_def
        have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
        have hd_p_pos : 0 < (d : ℝ) - p := by linarith
        have hp_1_ge_p : p ≤ p_1 := by
          rw [hp_1_def, le_div_iff₀ hd_p_pos]
          nlinarith [hp_pos]
        have hp_1_one : 1 ≤ p_1 := le_trans hp_one hp_1_ge_p
        have hkp_next : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p_1 := by
          have h_form : (d : ℝ) < ((s + 1 : ℕ) + 1 : ℝ) * p := by
            have hkp_cast : ((s + 1 + 1 : ℕ) : ℝ) * p =
                ((s + 1 : ℕ) + 1 : ℝ) * p := by push_cast; ring
            rw [hkp_cast] at hkp
            exact hkp
          have h_id :=
            DifferentialGeometry.Analysis.Sobolev.Chart.IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
              (d := d) (s + 1) p hp_pos hp_lt h_form
          rw [hp_1_def]
          exact h_id
        have hreg_p_1 : RegularExponent.IsRegular (d : ℝ) p_1 (s + 1) := by
          rw [hp_1_def]
          exact hreg.tower_step hp_one hp_lt
        have h_mem_p1' : MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω := by
          rw [hp_1_def]; exact h_mem_p1
        obtain ⟨q, hq_one, hq_dim, C', hC'_nn, h_mem_q, h_norm_q⟩ :=
          ih hp_1_one hreg_p_1 hkp_next hf_cpt hf_supp h_mem_p1'
        refine ⟨q, hq_one, hq_dim,
          C' * subcriticalConstant (m + 1 + s) d p,
          mul_nonneg hC'_nn (subcriticalConstant_nonneg _ _ _), h_mem_q, ?_⟩
        have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
        have h_step_norm :
            iteratedWeakSobolevNorm (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω ≤
              ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                iteratedWeakSobolevNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          rw [hp_1_def]; exact h_norm_p1
        have h_chain :
            iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal q) f Ω ≤
              ENNReal.ofReal C' *
                (ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                  iteratedWeakSobolevNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω) :=
          le_trans h_norm_q (mul_le_mul_of_nonneg_left h_step_norm (zero_le _))
        have h_rhs_eq :
            ENNReal.ofReal C' *
                (ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                  iteratedWeakSobolevNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω) =
              ENNReal.ofReal (C' * subcriticalConstant (m + 1 + s) d p) *
                iteratedWeakSobolevNorm (d := d) (m + 1 + (s + 1)) (ENNReal.ofReal p) f Ω := by
          rw [ENNReal.ofReal_mul hC'_nn, h_idx]; ring
        rw [← h_rhs_eq]; exact h_chain
      · refine ⟨p, hp_one, hp_gt, 1, by norm_num,
          MemWkp.le_of_le (by omega) hf, ?_⟩
        rw [ENNReal.ofReal_one, one_mul]
        exact wkpNorm_mono_order (d := d) (by omega) f Ω

private theorem tower_to_supercritical_quant_uniform
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) (m : ℕ) :
    ∀ (s : ℕ) {p : ℝ}, 1 ≤ p →
      RegularExponent.IsRegular (d : ℝ) p (s + 1) →
      (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p →
        ∃ q : ℝ, 1 ≤ q ∧ (d : ℝ) < q ∧
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ {f : EuN → ℝ}, HasCompactSupport f → tsupport f ⊆ Ω →
              MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω →
                MemWkp (d := d) (m + 1) (ENNReal.ofReal q) f Ω ∧
                  iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal q) f Ω ≤
                    ENNReal.ofReal C *
                      iteratedWeakSobolevNorm (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω := by
  intro s
  induction s with
  | zero =>
      intro p hp_one _hreg hkp
      have hp_dim : (d : ℝ) < p := by
        have : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hkp
        exact hkp
      refine ⟨p, hp_one, hp_dim, 1, by norm_num, ?_⟩
      intro f _hf_cpt _hf_supp hf
      refine ⟨by simpa using hf, ?_⟩
      simp only [add_zero] at hf ⊢
      rw [ENNReal.ofReal_one, one_mul]
  | succ s ih =>
      intro p hp_one hreg hkp
      have hp_ne_d : p ≠ (d : ℝ) := hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hp_ne_d with hp_lt | hp_gt
      · have hp_pos : 0 < p := by linarith
        set p_1 : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_1_def
        have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
        have hd_p_pos : 0 < (d : ℝ) - p := by linarith
        have hp_1_ge_p : p ≤ p_1 := by
          rw [hp_1_def, le_div_iff₀ hd_p_pos]; nlinarith [hp_pos]
        have hp_1_one : 1 ≤ p_1 := le_trans hp_one hp_1_ge_p
        have hkp_next : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p_1 := by
          have h_form : (d : ℝ) < ((s + 1 : ℕ) + 1 : ℝ) * p := by
            have hkp_cast : ((s + 1 + 1 : ℕ) : ℝ) * p =
                ((s + 1 : ℕ) + 1 : ℝ) * p := by push_cast; ring
            rw [hkp_cast] at hkp; exact hkp
          have h_id :=
            DifferentialGeometry.Analysis.Sobolev.Chart.IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
              (d := d) (s + 1) p hp_pos hp_lt h_form
          rw [hp_1_def]; exact h_id
        have hreg_p_1 : RegularExponent.IsRegular (d : ℝ) p_1 (s + 1) := by
          rw [hp_1_def]; exact hreg.tower_step hp_one hp_lt
        obtain ⟨q, hq_one, hq_dim, C', hC'_nn, h_uniform⟩ :=
          ih hp_1_one hreg_p_1 hkp_next
        refine ⟨q, hq_one, hq_dim,
          C' * subcriticalConstant (m + 1 + s) d p,
          mul_nonneg hC'_nn (subcriticalConstant_nonneg _ _ _), ?_⟩
        intro f hf_cpt hf_supp hf
        have hf' : MemWkp (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
          rw [h_idx] at hf; exact hf
        obtain ⟨h_mem_p1, h_norm_p1⟩ :=
          MemWkp_subcritical_iterated (d := d) (m + 1 + s)
            hp_one hp_lt hΩ_open hf_cpt hf_supp hf'
        have h_mem_p1' : MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω := by
          rw [hp_1_def]; exact h_mem_p1
        obtain ⟨h_mem_q, h_norm_q⟩ := h_uniform hf_cpt hf_supp h_mem_p1'
        refine ⟨h_mem_q, ?_⟩
        have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
        have h_step_norm :
            iteratedWeakSobolevNorm (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω ≤
              ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                iteratedWeakSobolevNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          rw [hp_1_def]; exact h_norm_p1
        have h_chain :
            iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal q) f Ω ≤
              ENNReal.ofReal C' *
                (ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                  iteratedWeakSobolevNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω) :=
          le_trans h_norm_q (mul_le_mul_of_nonneg_left h_step_norm (zero_le _))
        have h_rhs_eq :
            ENNReal.ofReal C' *
                (ENNReal.ofReal (subcriticalConstant (m + 1 + s) d p) *
                  iteratedWeakSobolevNorm (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω) =
              ENNReal.ofReal (C' * subcriticalConstant (m + 1 + s) d p) *
                iteratedWeakSobolevNorm (d := d) (m + 1 + (s + 1)) (ENNReal.ofReal p) f Ω := by
          rw [ENNReal.ofReal_mul hC'_nn, h_idx]; ring
        rw [← h_rhs_eq]; exact h_chain
      · refine ⟨p, hp_one, hp_gt, 1, by norm_num, ?_⟩
        intro f _hf_cpt _hf_supp hf
        refine ⟨MemWkp.le_of_le (by omega) hf, ?_⟩
        rw [ENNReal.ofReal_one, one_mul]
        exact wkpNorm_mono_order (d := d) (by omega) f Ω

omit [NeZero d] in
private theorem eLpNorm_iterWeakPartial_le_eLpNorm_iteratedFDeriv
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (j : ℕ) (β : Fin j → Fin d) {ψ : EuN → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ) (hψ_supp : tsupport ψ ⊆ Ω) :
    eLpNorm (iterWeakPartial (d := d) p j β ψ Ω) p (volume.restrict Ω) ≤
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j ψ z‖) p (volume.restrict Ω) := by
  have h_ae :=
    iterWeakPartial_smooth_ae_eq_iterClassicalPartial (d := d) hp_one hΩ_open j β
      hψ_smooth hψ_cpt hψ_supp
  rw [eLpNorm_congr_ae h_ae]
  refine eLpNorm_mono (fun x => ?_)
  have h := norm_iterClassicalPartial_le_iteratedFDeriv (d := d) j β hψ_smooth x
  simpa [norm_norm] using h

private theorem wkpNorm_le_sum_eLpNorm_iteratedFDeriv
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (k : ℕ) {ψ : EuN → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cpt : HasCompactSupport ψ) (hψ_supp : tsupport ψ ⊆ Ω) :
    iteratedWeakSobolevNorm (d := d) k p ψ Ω ≤
      (d ^ k : ℕ) *
        ∑ j ∈ Finset.range (k + 1),
          eLpNorm (fun z => ‖iteratedFDeriv ℝ j ψ z‖) p (volume.restrict Ω) := by
  classical
  rw [wkpNorm_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hj_le : j ≤ k := by rw [Finset.mem_range] at hj; omega
  have h_card_le :
      ∑ _β : Fin j → Fin d,
          eLpNorm (fun z => ‖iteratedFDeriv ℝ j ψ z‖) p (volume.restrict Ω) ≤
        (d ^ k : ℕ) *
          eLpNorm (fun z => ‖iteratedFDeriv ℝ j ψ z‖) p (volume.restrict Ω) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
    refine mul_le_mul' ?_ (le_refl _)
    exact_mod_cast Nat.pow_le_pow_right (NeZero.pos d) hj_le
  refine le_trans (Finset.sum_le_sum (fun β _ => ?_)) h_card_le
  exact eLpNorm_iterWeakPartial_le_eLpNorm_iteratedFDeriv (d := d) hΩ_open hp_one
    j β hψ_smooth hψ_cpt hψ_supp

omit [NeZero d] in
private theorem eLpNorm_le_eLpNorm_two_mul_rpow_ball
    {p' : ℝ} (hp'_one : 1 ≤ p') (hp'_two : p' ≤ 2)
    {x₀ : EuN} {R : ℝ} {g : EuN → ℝ} (hg : AEStronglyMeasurable g
      (volume.restrict (Metric.ball x₀ R))) :
    eLpNorm g (ENNReal.ofReal p') (volume.restrict (Metric.ball x₀ R)) ≤
      eLpNorm g 2 (volume.restrict (Metric.ball x₀ R)) *
        (volume (Metric.ball x₀ R)) ^
          (1 / p' - 1 / (2 : ℝ)) := by
  have hpq : ENNReal.ofReal p' ≤ (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal hp'_two
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Metric.ball x₀ R))
    (f := g) hpq hg
  rw [Measure.restrict_apply_univ] at h
  have h_toReal_p' : (ENNReal.ofReal p').toReal = p' :=
    ENNReal.toReal_ofReal (by linarith)
  have h_toReal_two : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rwa [h_toReal_p', h_toReal_two] at h

omit [NeZero d] in
private theorem smooth_iteratedFDeriv_norm_eLpNorm_ball_ne_top
    {p : ℝ≥0∞} {x₀ : EuN} {R : ℝ} (j : ℕ)
    {u : EuN → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    eLpNorm (fun z => ‖iteratedFDeriv ℝ j u z‖) p
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := by
  have h_iter_cont : Continuous (fun z : EuN => iteratedFDeriv ℝ j u z) := by
    have h := hu.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
    simpa using h.continuous
  have hcont : Continuous (fun z : EuN => ‖iteratedFDeriv ℝ j u z‖) :=
    continuous_norm.comp h_iter_cont
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall x₀ R) hcont.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  refine MemLp.eLpNorm_ne_top ?_
  refine MemLp.of_le_mul (g := fun _ : EuN => (1 : ℝ)) (c := M) ?_ ?_ ?_
  · exact memLp_const (1 : ℝ)
  · exact hcont.aestronglyMeasurable.restrict
  · refine (ae_restrict_iff' measurableSet_ball).mpr ?_
    filter_upwards with z hz
    have hz' : z ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hz
    rw [norm_one, mul_one]
    exact hM z hz'

omit [NeZero d] in
private theorem eLpNorm_iteratedFDeriv_smul_le
    {x₀ : EuN} {R : ℝ}
    {χ f : EuN → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Cχ : ℝ} (hCχ : 0 ≤ Cχ) (j : ℕ)
    (hχ_bound : ∀ i ≤ j, ∀ x : EuN, ‖iteratedFDeriv ℝ i χ x‖ ≤ Cχ) :
    eLpNorm (fun z => ‖iteratedFDeriv ℝ j (fun y => χ y * f y) z‖) 2
        (volume.restrict (Metric.ball x₀ R)) ≤
      ∑ i ∈ Finset.range (j + 1),
        ENNReal.ofReal ((j.choose i : ℝ) * Cχ) *
          eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
            (volume.restrict (Metric.ball x₀ R)) := by
  classical
  set μ : Measure EuN := volume.restrict (Metric.ball x₀ R) with hμ
  set g : ℕ → EuN → ℝ :=
    fun i z => (j.choose i : ℝ) * Cχ * ‖iteratedFDeriv ℝ (j - i) f z‖ with hg
  have h_pt : ∀ z : EuN,
      ‖(fun z => ‖iteratedFDeriv ℝ j (fun y => χ y * f y) z‖) z‖ ≤
        ‖(∑ i ∈ Finset.range (j + 1), g i) z‖ := by
    intro z
    have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := j)
      (f := χ) (g := f) hχ hf z (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    have h_sum_nonneg : 0 ≤ ∑ i ∈ Finset.range (j + 1), g i z :=
      Finset.sum_nonneg fun i _ => by
        have : 0 ≤ (j.choose i : ℝ) * Cχ :=
          mul_nonneg (Nat.cast_nonneg _) hCχ
        exact mul_nonneg this (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [Finset.sum_apply, Real.norm_eq_abs, abs_of_nonneg h_sum_nonneg]
    refine h_leib.trans ?_
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi_le : i ≤ j := by rw [Finset.mem_range] at hi; omega
    have h_χ_le : ‖iteratedFDeriv ℝ i χ z‖ ≤ Cχ := hχ_bound i hi_le z
    have h_step :
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ z‖ *
            ‖iteratedFDeriv ℝ (j - i) f z‖ ≤
          (j.choose i : ℝ) * Cχ * ‖iteratedFDeriv ℝ (j - i) f z‖ := by
      gcongr
    simpa [hg, mul_assoc] using h_step
  refine (eLpNorm_mono h_pt).trans ?_
  have h_meas : ∀ i ∈ Finset.range (j + 1), AEStronglyMeasurable (g i) μ := by
    intro i _
    have h_iter_cont : Continuous (fun z : EuN => iteratedFDeriv ℝ (j - i) f z) := by
      have h := hf.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j - i)
      simpa using h.continuous
    have hcont : Continuous (g i) := by
      simp only [hg]
      exact (continuous_const.mul (continuous_norm.comp h_iter_cont))
    exact hcont.aestronglyMeasurable
  refine (eLpNorm_sum_le h_meas (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h_smul : g i = ((j.choose i : ℝ) * Cχ) •
      (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) := by
    funext z; simp [hg, smul_eq_mul, mul_assoc]
  rw [h_smul, eLpNorm_const_smul,
    Real.enorm_eq_ofReal (mul_nonneg (Nat.cast_nonneg _) hCχ)]

theorem smooth_localBall_L2_pointwise_embedding
    {K : ℕ} (hdK : (d : ℝ) < 2 * K)
    {x₀ : EuN} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : EuN → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
        ∀ x ∈ Metric.ball x₀ (R / 4),
          ‖f x‖ ≤ C *
            ∑ j ∈ Finset.range (2 * K + 1),
              (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2
                (volume.restrict (Metric.ball x₀ R))).toReal := by
  classical
  set Ω : Set EuN := Metric.ball x₀ R with hΩ_def
  have hΩ_open : IsOpen Ω := Metric.isOpen_ball
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hK_pos : 1 ≤ K := by
    by_contra h
    have hK0 : K = 0 := by omega
    rw [hK0] at hdK; simp at hdK; linarith [hd_pos, hdK]
  set s : ℕ := 2 * K - 1 with hs_def
  have hs1 : s + 1 = 2 * K := by omega
  have hball_sub : Metric.closedBall x₀ (R / 2) ⊆ Ω := by
    rw [hΩ_def]
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨δ, χ, hδ_pos, _hδ_sub, hχ_smooth, hχ_cpt, _hχ_range, hχ_one, hχ_supp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d)
      (isCompact_closedBall x₀ (R / 2)) hΩ_open hball_sub
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport (d := d)
      hχ_smooth hχ_cpt (2 * K)
  have h_Ioo_inf : (Set.Ioo (1 : ℝ) 2).Infinite := Set.Ioo_infinite (by norm_num)
  obtain ⟨p', hp'_mem, hp'_notMem⟩ :=
    h_Ioo_inf.exists_notMem_finset
      ((Finset.Icc 1 (2 * K)).image (fun m : ℕ => (d : ℝ) / (m : ℝ)))
  have hp'_one : (1 : ℝ) ≤ p' := le_of_lt hp'_mem.1
  have hp'_two : p' ≤ 2 := le_of_lt hp'_mem.2
  have hp'_pos : 0 < p' := by linarith
  have hreg : RegularExponent.IsRegular (d : ℝ) p' (2 * K) := by
    intro m hm hm_le hmp
    apply hp'_notMem
    rw [Finset.mem_image]
    refine ⟨m, Finset.mem_Icc.mpr ⟨hm, hm_le⟩, ?_⟩
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    rw [div_eq_iff (ne_of_gt hm_pos)]
    linarith [hmp]
  have hkp : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p' := by
    rw [hs1]
    have : ((2 * K : ℕ) : ℝ) = 2 * K := by push_cast; ring
    rw [this]
    calc (d : ℝ) < 2 * K := hdK
      _ = 2 * K * 1 := by ring
      _ ≤ 2 * K * p' := by
          apply mul_le_mul_of_nonneg_left hp'_one
          positivity
  have hreg_s : RegularExponent.IsRegular (d : ℝ) p' (s + 1) := by rw [hs1]; exact hreg
  obtain ⟨q, hq_one, hq_dim, C₁, hC₁_nn, h_tower⟩ :=
    tower_to_supercritical_quant_uniform (d := d) hΩ_open 0 s hp'_one hreg_s hkp
  obtain ⟨C₂, hC₂_nn, hC₂_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_iteratedFDeriv_bound_uniform
      (d := d) (p := q) hq_dim (x₀ := x₀) (R := R) hR 0
  set Vexp : ℝ := (volume Ω ^ (1 / p' - 1 / (2 : ℝ))).toReal with hVexp_def
  have hVexp_nn : 0 ≤ Vexp := ENNReal.toReal_nonneg
  set Cleib : ℝ := (2 : ℝ) ^ (2 * K) * Cχ with hCleib_def
  have hCleib_nn : 0 ≤ Cleib := by positivity
  set Npairs : ℝ := ∑ j ∈ Finset.range (2 * K + 1), ((j : ℝ) + 1) with hNpairs_def
  have hNpairs_nn : 0 ≤ Npairs :=
    Finset.sum_nonneg (fun j _ => by positivity)
  set dpow : ℝ := ((d ^ (2 * K) : ℕ) : ℝ) with hdpow_def
  have hdpow_nn : 0 ≤ dpow := by positivity
  refine ⟨C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs)))),
    by positivity, ?_⟩
  intro f hf_smooth x hx
  set χf : EuN → ℝ := fun y => χ y * f y with hχf_def
  have hχf_smooth : ContDiff ℝ (⊤ : ℕ∞) χf := hχ_smooth.mul hf_smooth
  have hχf_cpt : HasCompactSupport χf := hχ_cpt.mul_right
  have hχf_supp : tsupport χf ⊆ Ω :=
    (tsupport_smul_subset_left χ f).trans hχ_supp
  have hχf_mem_p' : MemWkp (d := d) (2 * K) (ENNReal.ofReal p') χf Ω :=
    MemWkp_of_smooth_compactSupport (d := d) hΩ_open hχf_smooth hχf_cpt hχf_supp
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'_one) (2 * K)
  have hχf_mem_p'_idx : MemWkp (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω := by
    have : 0 + 1 + s = 2 * K := by omega
    rw [this]; exact hχf_mem_p'
  obtain ⟨hχf_mem_q, h_tower_norm⟩ := h_tower hχf_cpt hχf_supp hχf_mem_p'_idx
  set T : ℝ := ∑ j ∈ Finset.range (2 * K + 1),
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2 (volume.restrict Ω)).toReal with hT_def
  have hT_nn : 0 ≤ T := Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)
  have hfin_f : ∀ (e : ℝ≥0∞) (j : ℕ),
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) e (volume.restrict Ω) ≠ ⊤ := by
    intro e j; rw [hΩ_def]
    exact smooth_iteratedFDeriv_norm_eLpNorm_ball_ne_top (j := j) hf_smooth
  have hfin_χf : ∀ (e : ℝ≥0∞) (j : ℕ),
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) e (volume.restrict Ω) ≠ ⊤ := by
    intro e j; rw [hΩ_def]
    exact smooth_iteratedFDeriv_norm_eLpNorm_ball_ne_top (j := j) hχf_smooth
  have hx_half : x ∈ Metric.ball x₀ (R / 2) :=
    Metric.ball_subset_ball (by linarith) hx
  have h_morrey := hC₂_bound (u := χf) hχf_smooth x hx_half
  have hq_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq_one
  set S_q : ℝ := ∑ j ∈ Finset.range (0 + 2),
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal q)
      (volume.restrict Ω)).toReal with hS_q_def
  have h_Sq_le :
      S_q ≤ (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal := by
    have h_bridge :=
      eLpNorm_iteratedFDeriv_le_wkpNorm (d := d) hΩ_open hq_enn_one
        1 hχf_smooth hχf_cpt hχf_supp
    rw [hS_q_def, show (0 + 2 : ℕ) = 1 + 1 by rfl,
      ← ENNReal.toReal_sum (fun j _ => hfin_χf _ j)]
    exact ENNReal.toReal_mono (wkpNorm_lt_top_of_memWkp hχf_mem_q).ne h_bridge
  have h_wk1_finite : iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω ≠ ⊤ :=
    (wkpNorm_lt_top_of_memWkp hχf_mem_q).ne
  have h_wk2_finite : iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω ≠ ⊤ :=
    (wkpNorm_lt_top_of_memWkp hχf_mem_p'_idx).ne
  have h_tower_real :
      (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal ≤
        C₁ * (iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω).toReal := by
    have h_mul_finite :
        ENNReal.ofReal C₁ *
            iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_wk2_finite
    have := ENNReal.toReal_mono h_mul_finite h_tower_norm
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₁_nn] at this
  set Wsum_p' : ℝ := ∑ j ∈ Finset.range (s + 1 + 1),
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
      (volume.restrict Ω)).toReal with hWsum_p'_def
  have hp'_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p' := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'_one
  have h_revbridge :
      (iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω).toReal ≤
        dpow * Wsum_p' := by
    have h := wkpNorm_le_sum_eLpNorm_iteratedFDeriv (d := d) hΩ_open hp'_enn_one
      (0 + 1 + s) hχf_smooth hχf_cpt hχf_supp
    have h_sum_finite :
        (((d ^ (0 + 1 + s) : ℕ) : ℝ≥0∞) *
          ∑ j ∈ Finset.range (0 + 1 + s + 1),
            eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
              (volume.restrict Ω)) ≠ ⊤ := by
      refine ENNReal.mul_ne_top (by simp) ?_
      exact (ENNReal.sum_lt_top.mpr (fun j _ => lt_of_le_of_ne le_top (hfin_χf _ j))).ne
    have h_toReal := ENNReal.toReal_mono h_sum_finite h
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun j _ => hfin_χf _ j)] at h_toReal
    have h_idx1 : 0 + 1 + s = s + 1 := by omega
    have h_idx2 : 0 + 1 + s + 1 = s + 1 + 1 := by omega
    rw [hWsum_p'_def, hdpow_def]
    rw [h_idx1] at h_toReal ⊢
    have h_dcast : (((d ^ (s + 1) : ℕ) : ℝ≥0∞)).toReal = ((d ^ (2 * K) : ℕ) : ℝ) := by
      rw [hs1]; simp
    rw [h_dcast] at h_toReal
    rw [show (s + 1 + 1 : ℕ) = 0 + 1 + s + 1 by omega] at h_toReal ⊢
    convert h_toReal using 3
  have h_per_j : ∀ j ∈ Finset.range (s + 1 + 1),
      (eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
          (volume.restrict Ω)).toReal ≤
        Vexp * (((j : ℝ) + 1) * (Cleib * T)) := by
    intro j hj
    have hj_le : j ≤ 2 * K := by rw [Finset.mem_range] at hj; omega
    have h_meas_χf : AEStronglyMeasurable
        (fun z => ‖iteratedFDeriv ℝ j χf z‖) (volume.restrict Ω) := by
      have h_iter_cont : Continuous (fun z : EuN => iteratedFDeriv ℝ j χf z) := by
        have h := hχf_smooth.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
        simpa using h.continuous
      exact (continuous_norm.comp h_iter_cont).aestronglyMeasurable
    have h_hold := eLpNorm_le_eLpNorm_two_mul_rpow_ball (d := d)
      hp'_one hp'_two (x₀ := x₀) (R := R)
      (g := fun z => ‖iteratedFDeriv ℝ j χf z‖) (by rw [hΩ_def] at h_meas_χf; exact h_meas_χf)
    rw [← hΩ_def] at h_hold
    have h_leib := eLpNorm_iteratedFDeriv_smul_le (d := d) (x₀ := x₀) (R := R)
      hχ_smooth hf_smooth hCχ_nn j (fun i hi z => hCχ_bound z i (hi.trans hj_le))
    rw [← hΩ_def] at h_leib
    have h_combined :
        eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
            (volume.restrict Ω) ≤
          (∑ i ∈ Finset.range (j + 1),
            ENNReal.ofReal ((j.choose i : ℝ) * Cχ) *
              eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
                (volume.restrict Ω)) *
            (volume Ω) ^ (1 / p' - 1 / (2 : ℝ)) :=
      h_hold.trans (mul_le_mul' h_leib (le_refl _))
    have h_sum_fin :
        (∑ i ∈ Finset.range (j + 1),
            ENNReal.ofReal ((j.choose i : ℝ) * Cχ) *
              eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
                (volume.restrict Ω)) ≠ ⊤ := by
      refine (ENNReal.sum_lt_top.mpr (fun i _ => ?_)).ne
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_ne le_top (hfin_f _ (j - i)))
    have h_vol_fin : (volume Ω) ^ (1 / p' - 1 / (2 : ℝ)) ≠ ⊤ := by
      rw [hΩ_def]
      exact (ENNReal.rpow_lt_top_of_nonneg (by
        rw [sub_nonneg, one_div, one_div, inv_le_inv₀ (by norm_num) hp'_pos]; exact hp'_two)
        measure_ball_lt_top.ne).ne
    have h_prod_fin :
        (∑ i ∈ Finset.range (j + 1),
            ENNReal.ofReal ((j.choose i : ℝ) * Cχ) *
              eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
                (volume.restrict Ω)) *
            (volume Ω) ^ (1 / p' - 1 / (2 : ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top h_sum_fin h_vol_fin
    have h_toReal := ENNReal.toReal_mono h_prod_fin h_combined
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum
      (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin_f _ (j - i)))] at h_toReal
    refine h_toReal.trans ?_
    rw [show ((volume Ω) ^ (1 / p' - 1 / (2 : ℝ))).toReal = Vexp from rfl]
    rw [mul_comm Vexp _]
    refine mul_le_mul_of_nonneg_right ?_ hVexp_nn
    simp only [ENNReal.toReal_mul]
    have h_each : ∀ i ∈ Finset.range (j + 1),
        (ENNReal.ofReal ((j.choose i : ℝ) * Cχ)).toReal *
            (eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
              (volume.restrict Ω)).toReal ≤ Cleib * T := by
      intro i hi
      have hi_le : i ≤ j := by rw [Finset.mem_range] at hi; omega
      rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hCχ_nn)]
      have h_a_le : (j.choose i : ℝ) * Cχ ≤ Cleib := by
        rw [hCleib_def]
        apply mul_le_mul_of_nonneg_right _ hCχ_nn
        have h_ch : (j.choose i : ℝ) ≤ (2 : ℝ) ^ j := by
          have : j.choose i ≤ 2 ^ j := Nat.choose_le_two_pow j i
          calc (j.choose i : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast this
            _ = (2 : ℝ) ^ j := by push_cast; ring
        calc (j.choose i : ℝ) ≤ (2 : ℝ) ^ j := h_ch
          _ ≤ (2 : ℝ) ^ (2 * K) := pow_le_pow_right₀ (by norm_num) hj_le
      have h_b_le :
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
            (volume.restrict Ω)).toReal ≤ T := by
        rw [hT_def]
        refine Finset.single_le_sum (f := fun m =>
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ m f z‖) 2 (volume.restrict Ω)).toReal)
          (fun m _ => ENNReal.toReal_nonneg) ?_
        rw [Finset.mem_range]; omega
      exact mul_le_mul h_a_le h_b_le ENNReal.toReal_nonneg hCleib_nn
    have h_sum_each := Finset.sum_le_sum h_each
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_each
    refine h_sum_each.trans (le_of_eq ?_)
    push_cast; ring
  have h_idx_range : Finset.range (s + 1 + 1) = Finset.range (2 * K + 1) := by
    congr 1; omega
  have h_Wsum_le : Wsum_p' ≤ Vexp * (Cleib * Npairs) * T := by
    have h_sum_le :
        Wsum_p' ≤ ∑ j ∈ Finset.range (s + 1 + 1), Vexp * (((j : ℝ) + 1) * (Cleib * T)) := by
      rw [hWsum_p'_def]
      exact Finset.sum_le_sum h_per_j
    refine h_sum_le.trans (le_of_eq ?_)
    rw [h_idx_range, hNpairs_def]
    rw [← Finset.mul_sum]
    rw [show (∑ j ∈ Finset.range (2 * K + 1), ((j : ℝ) + 1) * (Cleib * T)) =
        (∑ j ∈ Finset.range (2 * K + 1), ((j : ℝ) + 1)) * (Cleib * T) from
      (Finset.sum_mul ..).symm]
    ring
  have h_wk_chain :
      (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal ≤
        C₁ * (dpow * (Vexp * (Cleib * Npairs) * T)) := by
    refine h_tower_real.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁_nn
    refine h_revbridge.trans ?_
    exact mul_le_mul_of_nonneg_left h_Wsum_le hdpow_nn
  have h_morrey_chain : ‖χf x‖ ≤ C₂ * (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal := by
    have h0 : ‖iteratedFDeriv ℝ 0 χf x‖ = ‖χf x‖ := by rw [norm_iteratedFDeriv_zero]
    rw [← h0]
    refine h_morrey.trans ?_
    exact mul_le_mul_of_nonneg_left h_Sq_le hC₂_nn
  have hχ_x : χ x = 1 := by
    refine hχ_one x ?_
    have hx_cb : x ∈ Metric.closedBall x₀ (R / 2) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hx)
    exact Metric.self_subset_cthickening _ hx_cb
  have hχf_x : χf x = f x := by rw [hχf_def]; simp [hχ_x]
  calc ‖f x‖ = ‖χf x‖ := by rw [hχf_x]
    _ ≤ C₂ * (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal := h_morrey_chain
    _ ≤ C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs) * T))) :=
        mul_le_mul_of_nonneg_left h_wk_chain hC₂_nn
    _ = C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs)))) * T := by ring
    _ = C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs)))) *
          ∑ j ∈ Finset.range (2 * K + 1),
            (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2
              (volume.restrict (Metric.ball x₀ R))).toReal := by
        rw [hT_def, hΩ_def]

theorem smooth_localBall_L2_pointwise_embedding_supercritical
    (m : ℕ) (hdm : (d : ℝ) < 2 * m)
    {x₀ : EuN} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : EuN → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
        ∀ x ∈ Metric.ball x₀ (R / 4),
          ‖f x‖ ≤ C *
            ∑ j ∈ Finset.range (m + 1),
              (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2
                (volume.restrict (Metric.ball x₀ R))).toReal := by
  classical
  set Ω : Set EuN := Metric.ball x₀ R with hΩ_def
  have hΩ_open : IsOpen Ω := Metric.isOpen_ball
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hm_one : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0] at hdm; simp at hdm; linarith [hd_pos, hdm]
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm_one
  set s : ℕ := m - 1 with hs_def
  have hs1 : s + 1 = m := by omega
  have hball_sub : Metric.closedBall x₀ (R / 2) ⊆ Ω := by
    rw [hΩ_def]
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨δ, χ, hδ_pos, _hδ_sub, hχ_smooth, hχ_cpt, _hχ_range, hχ_one, hχ_supp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d)
      (isCompact_closedBall x₀ (R / 2)) hΩ_open hball_sub
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport (d := d)
      hχ_smooth hχ_cpt (m)
  set L : ℝ := max 1 ((d : ℝ) / (m)) with hL_def
  have hL_lt_two : L < 2 := by
    rw [hL_def]
    refine max_lt (by norm_num) ?_
    rw [div_lt_iff₀ hm_pos]; linarith [hdm]
  have h_Ioo_inf : (Set.Ioo L 2).Infinite := Set.Ioo_infinite hL_lt_two
  obtain ⟨p', hp'_mem, hp'_notMem⟩ :=
    h_Ioo_inf.exists_notMem_finset
      ((Finset.Icc 1 m).image (fun t : ℕ => (d : ℝ) / (t : ℝ)))
  have hL_le_p' : L < p' := hp'_mem.1
  have hp'_one : (1 : ℝ) ≤ p' :=
    le_of_lt (lt_of_le_of_lt (le_max_left _ _) hL_le_p')
  have hp'_two : p' ≤ 2 := le_of_lt hp'_mem.2
  have hp'_pos : 0 < p' := by linarith
  have hp'_lb : (d : ℝ) / (m) < p' :=
    lt_of_le_of_lt (le_max_right _ _) hL_le_p'
  have hreg : RegularExponent.IsRegular (d : ℝ) p' (m) := by
    intro t ht ht_le htp
    apply hp'_notMem
    rw [Finset.mem_image]
    refine ⟨t, Finset.mem_Icc.mpr ⟨ht, ht_le⟩, ?_⟩
    have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht
    rw [div_eq_iff (ne_of_gt ht_pos)]
    linarith [htp]
  have hkp : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p' := by
    rw [hs1]
    have h_lb : (d : ℝ) = (d : ℝ) / m * m :=
      (div_mul_cancel₀ _ (ne_of_gt hm_pos)).symm
    rw [h_lb]
    calc (d : ℝ) / m * m < p' * m := mul_lt_mul_of_pos_right hp'_lb hm_pos
      _ = (m : ℝ) * p' := by ring
  have hreg_s : RegularExponent.IsRegular (d : ℝ) p' (s + 1) := by rw [hs1]; exact hreg
  obtain ⟨q, hq_one, hq_dim, C₁, hC₁_nn, h_tower⟩ :=
    tower_to_supercritical_quant_uniform (d := d) hΩ_open 0 s hp'_one hreg_s hkp
  obtain ⟨C₂, hC₂_nn, hC₂_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_iteratedFDeriv_bound_uniform
      (d := d) (p := q) hq_dim (x₀ := x₀) (R := R) hR 0
  set Vexp : ℝ := (volume Ω ^ (1 / p' - 1 / (2 : ℝ))).toReal with hVexp_def
  have hVexp_nn : 0 ≤ Vexp := ENNReal.toReal_nonneg
  set Cleib : ℝ := (2 : ℝ) ^ (m) * Cχ with hCleib_def
  have hCleib_nn : 0 ≤ Cleib := by positivity
  set Npairs : ℝ := ∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1) with hNpairs_def
  have hNpairs_nn : 0 ≤ Npairs :=
    Finset.sum_nonneg (fun j _ => by positivity)
  set dpow : ℝ := ((d ^ (m) : ℕ) : ℝ) with hdpow_def
  have hdpow_nn : 0 ≤ dpow := by positivity
  refine ⟨C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs)))),
    by positivity, ?_⟩
  intro f hf_smooth x hx
  set χf : EuN → ℝ := fun y => χ y * f y with hχf_def
  have hχf_smooth : ContDiff ℝ (⊤ : ℕ∞) χf := hχ_smooth.mul hf_smooth
  have hχf_cpt : HasCompactSupport χf := hχ_cpt.mul_right
  have hχf_supp : tsupport χf ⊆ Ω :=
    (tsupport_smul_subset_left χ f).trans hχ_supp
  have hχf_mem_p' : MemWkp (d := d) (m) (ENNReal.ofReal p') χf Ω :=
    MemWkp_of_smooth_compactSupport (d := d) hΩ_open hχf_smooth hχf_cpt hχf_supp
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'_one) (m)
  have hχf_mem_p'_idx : MemWkp (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω := by
    have : 0 + 1 + s = m := by omega
    rw [this]; exact hχf_mem_p'
  obtain ⟨hχf_mem_q, h_tower_norm⟩ := h_tower hχf_cpt hχf_supp hχf_mem_p'_idx
  set T : ℝ := ∑ j ∈ Finset.range (m + 1),
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2 (volume.restrict Ω)).toReal with hT_def
  have hT_nn : 0 ≤ T := Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)
  have hfin_f : ∀ (e : ℝ≥0∞) (j : ℕ),
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) e (volume.restrict Ω) ≠ ⊤ := by
    intro e j; rw [hΩ_def]
    exact smooth_iteratedFDeriv_norm_eLpNorm_ball_ne_top (j := j) hf_smooth
  have hfin_χf : ∀ (e : ℝ≥0∞) (j : ℕ),
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) e (volume.restrict Ω) ≠ ⊤ := by
    intro e j; rw [hΩ_def]
    exact smooth_iteratedFDeriv_norm_eLpNorm_ball_ne_top (j := j) hχf_smooth
  have hx_half : x ∈ Metric.ball x₀ (R / 2) :=
    Metric.ball_subset_ball (by linarith) hx
  have h_morrey := hC₂_bound (u := χf) hχf_smooth x hx_half
  have hq_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq_one
  set S_q : ℝ := ∑ j ∈ Finset.range (0 + 2),
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal q)
      (volume.restrict Ω)).toReal with hS_q_def
  have h_Sq_le :
      S_q ≤ (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal := by
    have h_bridge :=
      eLpNorm_iteratedFDeriv_le_wkpNorm (d := d) hΩ_open hq_enn_one
        1 hχf_smooth hχf_cpt hχf_supp
    rw [hS_q_def, show (0 + 2 : ℕ) = 1 + 1 by rfl,
      ← ENNReal.toReal_sum (fun j _ => hfin_χf _ j)]
    exact ENNReal.toReal_mono (wkpNorm_lt_top_of_memWkp hχf_mem_q).ne h_bridge
  have h_wk1_finite : iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω ≠ ⊤ :=
    (wkpNorm_lt_top_of_memWkp hχf_mem_q).ne
  have h_wk2_finite : iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω ≠ ⊤ :=
    (wkpNorm_lt_top_of_memWkp hχf_mem_p'_idx).ne
  have h_tower_real :
      (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal ≤
        C₁ * (iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω).toReal := by
    have h_mul_finite :
        ENNReal.ofReal C₁ *
            iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_wk2_finite
    have := ENNReal.toReal_mono h_mul_finite h_tower_norm
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₁_nn] at this
  set Wsum_p' : ℝ := ∑ j ∈ Finset.range (s + 1 + 1),
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
      (volume.restrict Ω)).toReal with hWsum_p'_def
  have hp'_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p' := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp'_one
  have h_revbridge :
      (iteratedWeakSobolevNorm (d := d) (0 + 1 + s) (ENNReal.ofReal p') χf Ω).toReal ≤
        dpow * Wsum_p' := by
    have h := wkpNorm_le_sum_eLpNorm_iteratedFDeriv (d := d) hΩ_open hp'_enn_one
      (0 + 1 + s) hχf_smooth hχf_cpt hχf_supp
    have h_sum_finite :
        (((d ^ (0 + 1 + s) : ℕ) : ℝ≥0∞) *
          ∑ j ∈ Finset.range (0 + 1 + s + 1),
            eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
              (volume.restrict Ω)) ≠ ⊤ := by
      refine ENNReal.mul_ne_top (by simp) ?_
      exact (ENNReal.sum_lt_top.mpr (fun j _ => lt_of_le_of_ne le_top (hfin_χf _ j))).ne
    have h_toReal := ENNReal.toReal_mono h_sum_finite h
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun j _ => hfin_χf _ j)] at h_toReal
    have h_idx1 : 0 + 1 + s = s + 1 := by omega
    have h_idx2 : 0 + 1 + s + 1 = s + 1 + 1 := by omega
    rw [hWsum_p'_def, hdpow_def]
    rw [h_idx1] at h_toReal ⊢
    have h_dcast : (((d ^ (s + 1) : ℕ) : ℝ≥0∞)).toReal = ((d ^ (m) : ℕ) : ℝ) := by
      rw [hs1]; simp
    rw [h_dcast] at h_toReal
    rw [show (s + 1 + 1 : ℕ) = 0 + 1 + s + 1 by omega] at h_toReal ⊢
    convert h_toReal using 3
  have h_per_j : ∀ j ∈ Finset.range (s + 1 + 1),
      (eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
          (volume.restrict Ω)).toReal ≤
        Vexp * (((j : ℝ) + 1) * (Cleib * T)) := by
    intro j hj
    have hj_le : j ≤ m := by rw [Finset.mem_range] at hj; omega
    have h_meas_χf : AEStronglyMeasurable
        (fun z => ‖iteratedFDeriv ℝ j χf z‖) (volume.restrict Ω) := by
      have h_iter_cont : Continuous (fun z : EuN => iteratedFDeriv ℝ j χf z) := by
        have h := hχf_smooth.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
        simpa using h.continuous
      exact (continuous_norm.comp h_iter_cont).aestronglyMeasurable
    have h_hold := eLpNorm_le_eLpNorm_two_mul_rpow_ball (d := d)
      hp'_one hp'_two (x₀ := x₀) (R := R)
      (g := fun z => ‖iteratedFDeriv ℝ j χf z‖) (by rw [hΩ_def] at h_meas_χf; exact h_meas_χf)
    rw [← hΩ_def] at h_hold
    have h_leib := eLpNorm_iteratedFDeriv_smul_le (d := d) (x₀ := x₀) (R := R)
      hχ_smooth hf_smooth hCχ_nn j (fun i hi z => hCχ_bound z i (hi.trans hj_le))
    rw [← hΩ_def] at h_leib
    have h_combined :
        eLpNorm (fun z => ‖iteratedFDeriv ℝ j χf z‖) (ENNReal.ofReal p')
            (volume.restrict Ω) ≤
          (∑ i ∈ Finset.range (j + 1),
            ENNReal.ofReal ((j.choose i : ℝ) * Cχ) *
              eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
                (volume.restrict Ω)) *
            (volume Ω) ^ (1 / p' - 1 / (2 : ℝ)) :=
      h_hold.trans (mul_le_mul' h_leib (le_refl _))
    have h_sum_fin :
        (∑ i ∈ Finset.range (j + 1),
            ENNReal.ofReal ((j.choose i : ℝ) * Cχ) *
              eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
                (volume.restrict Ω)) ≠ ⊤ := by
      refine (ENNReal.sum_lt_top.mpr (fun i _ => ?_)).ne
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_ne le_top (hfin_f _ (j - i)))
    have h_vol_fin : (volume Ω) ^ (1 / p' - 1 / (2 : ℝ)) ≠ ⊤ := by
      rw [hΩ_def]
      exact (ENNReal.rpow_lt_top_of_nonneg (by
        rw [sub_nonneg, one_div, one_div, inv_le_inv₀ (by norm_num) hp'_pos]; exact hp'_two)
        measure_ball_lt_top.ne).ne
    have h_prod_fin :
        (∑ i ∈ Finset.range (j + 1),
            ENNReal.ofReal ((j.choose i : ℝ) * Cχ) *
              eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
                (volume.restrict Ω)) *
            (volume Ω) ^ (1 / p' - 1 / (2 : ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top h_sum_fin h_vol_fin
    have h_toReal := ENNReal.toReal_mono h_prod_fin h_combined
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum
      (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin_f _ (j - i)))] at h_toReal
    refine h_toReal.trans ?_
    rw [show ((volume Ω) ^ (1 / p' - 1 / (2 : ℝ))).toReal = Vexp from rfl]
    rw [mul_comm Vexp _]
    refine mul_le_mul_of_nonneg_right ?_ hVexp_nn
    simp only [ENNReal.toReal_mul]
    have h_each : ∀ i ∈ Finset.range (j + 1),
        (ENNReal.ofReal ((j.choose i : ℝ) * Cχ)).toReal *
            (eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
              (volume.restrict Ω)).toReal ≤ Cleib * T := by
      intro i hi
      have hi_le : i ≤ j := by rw [Finset.mem_range] at hi; omega
      rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hCχ_nn)]
      have h_a_le : (j.choose i : ℝ) * Cχ ≤ Cleib := by
        rw [hCleib_def]
        apply mul_le_mul_of_nonneg_right _ hCχ_nn
        have h_ch : (j.choose i : ℝ) ≤ (2 : ℝ) ^ j := by
          have : j.choose i ≤ 2 ^ j := Nat.choose_le_two_pow j i
          calc (j.choose i : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast this
            _ = (2 : ℝ) ^ j := by push_cast; ring
        calc (j.choose i : ℝ) ≤ (2 : ℝ) ^ j := h_ch
          _ ≤ (2 : ℝ) ^ (m) := pow_le_pow_right₀ (by norm_num) hj_le
      have h_b_le :
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ (j - i) f z‖) 2
            (volume.restrict Ω)).toReal ≤ T := by
        rw [hT_def]
        refine Finset.single_le_sum (f := fun t =>
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ t f z‖) 2 (volume.restrict Ω)).toReal)
          (fun t _ => ENNReal.toReal_nonneg) ?_
        rw [Finset.mem_range]; omega
      exact mul_le_mul h_a_le h_b_le ENNReal.toReal_nonneg hCleib_nn
    have h_sum_each := Finset.sum_le_sum h_each
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_each
    refine h_sum_each.trans (le_of_eq ?_)
    push_cast; ring
  have h_idx_range : Finset.range (s + 1 + 1) = Finset.range (m + 1) := by
    congr 1; omega
  have h_Wsum_le : Wsum_p' ≤ Vexp * (Cleib * Npairs) * T := by
    have h_sum_le :
        Wsum_p' ≤ ∑ j ∈ Finset.range (s + 1 + 1), Vexp * (((j : ℝ) + 1) * (Cleib * T)) := by
      rw [hWsum_p'_def]
      exact Finset.sum_le_sum h_per_j
    refine h_sum_le.trans (le_of_eq ?_)
    rw [h_idx_range, hNpairs_def]
    rw [← Finset.mul_sum]
    rw [show (∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1) * (Cleib * T)) =
        (∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1)) * (Cleib * T) from
      (Finset.sum_mul ..).symm]
    ring
  have h_wk_chain :
      (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal ≤
        C₁ * (dpow * (Vexp * (Cleib * Npairs) * T)) := by
    refine h_tower_real.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁_nn
    refine h_revbridge.trans ?_
    exact mul_le_mul_of_nonneg_left h_Wsum_le hdpow_nn
  have h_morrey_chain : ‖χf x‖ ≤ C₂ * (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal := by
    have h0 : ‖iteratedFDeriv ℝ 0 χf x‖ = ‖χf x‖ := by rw [norm_iteratedFDeriv_zero]
    rw [← h0]
    refine h_morrey.trans ?_
    exact mul_le_mul_of_nonneg_left h_Sq_le hC₂_nn
  have hχ_x : χ x = 1 := by
    refine hχ_one x ?_
    have hx_cb : x ∈ Metric.closedBall x₀ (R / 2) :=
      Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hx)
    exact Metric.self_subset_cthickening _ hx_cb
  have hχf_x : χf x = f x := by rw [hχf_def]; simp [hχ_x]
  calc ‖f x‖ = ‖χf x‖ := by rw [hχf_x]
    _ ≤ C₂ * (iteratedWeakSobolevNorm (d := d) 1 (ENNReal.ofReal q) χf Ω).toReal := h_morrey_chain
    _ ≤ C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs) * T))) :=
        mul_le_mul_of_nonneg_left h_wk_chain hC₂_nn
    _ = C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs)))) * T := by ring
    _ = C₂ * (C₁ * (dpow * (Vexp * (Cleib * Npairs)))) *
          ∑ j ∈ Finset.range (m + 1),
            (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2
              (volume.restrict (Metric.ball x₀ R))).toReal := by
        rw [hT_def, hΩ_def]

theorem smooth_localBall_L2_pointwise_embedding_sharp
    (a : ℕ) (hda : (d : ℝ) < 2 * (2 * a))
    {x₀ : EuN} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : EuN → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
        ∀ x ∈ Metric.ball x₀ (R / 4),
          ‖f x‖ ≤ C *
            ∑ j ∈ Finset.range (2 * a + 1),
              (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2
                (volume.restrict (Metric.ball x₀ R))).toReal := by
  have hda' : (d : ℝ) < 2 * ((2 * a : ℕ) : ℝ) := by push_cast; linarith
  exact smooth_localBall_L2_pointwise_embedding_supercritical (2 * a) hda' hR

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
