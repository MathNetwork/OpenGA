import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreyHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding


noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EuclideanIteratedEmbedding

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem exists_cutoff_ball
    {x₀ : EuN} {R : ℝ} (hR : 0 < R) :
    ∃ χ : EuN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      Set.range χ ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.closedBall x₀ R, χ x = 1) ∧
      tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) := by
  classical
  have hδ_pos : (0 : ℝ) < R / 4 := by linarith
  have hclosed : IsClosed (Metric.closedBall x₀ R) := Metric.isClosed_closedBall
  have hopen_thick :
      IsOpen (Metric.thickening (R / 4) (Metric.closedBall x₀ R)) :=
    isOpen_thickening
  have hsub : Metric.closedBall x₀ R ⊆
      Metric.thickening (R / 4) (Metric.closedBall x₀ R) :=
    Metric.self_subset_thickening hδ_pos _
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ EuN)
      (s := Metric.thickening (R / 4) (Metric.closedBall x₀ R))
      (t := Metric.closedBall x₀ R)
      hopen_thick hclosed hsub with
    ⟨χ, hχ_smooth, hχ_range, hχ_support, hχ_one_iff⟩
  have h_supp_in_closedBall :
      tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) := by
    have h_closed : IsClosed (Metric.closedBall x₀ (3 * R / 2)) :=
      Metric.isClosed_closedBall
    rw [tsupport, hχ_support]
    refine closure_minimal ?_ h_closed
    intro y hy
    rw [Metric.mem_thickening_iff] at hy
    rcases hy with ⟨z, hz_mem, hyz⟩
    rw [Metric.mem_closedBall] at hz_mem ⊢
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ ≤ R / 4 + R := by
          have hyz_le : dist y z ≤ R / 4 := le_of_lt hyz
          linarith
      _ ≤ 3 * R / 2 := by linarith
  refine ⟨χ, contMDiff_iff_contDiff.mp hχ_smooth, ?_, hχ_range, ?_,
    h_supp_in_closedBall⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (3 * R / 2)) ?_
    exact (subset_tsupport _).trans h_supp_in_closedBall
  · intro x hx
    exact (hχ_one_iff x).1 hx

omit [NeZero d] in
private lemma exists_uniform_iteratedFDeriv_bound
    {χ : EuN → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_compact : HasCompactSupport χ)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x : EuN, ‖iteratedFDeriv ℝ j χ x‖ ≤ C := by
  classical
  have h_per_j : ∀ j, ∃ Cj : ℝ, 0 ≤ Cj ∧
      ∀ x : EuN, ‖iteratedFDeriv ℝ j χ x‖ ≤ Cj := by
    intro j
    have h_cont : Continuous (fun x : EuN => iteratedFDeriv ℝ j χ x) :=
      hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have h_supp : HasCompactSupport (fun x : EuN => iteratedFDeriv ℝ j χ x) :=
      hχ_compact.iteratedFDeriv (𝕜 := ℝ) j
    obtain ⟨Mj, hMj⟩ := h_supp.exists_bound_of_continuous h_cont
    exact ⟨max 0 Mj, le_max_left _ _, fun x => (hMj x).trans (le_max_right _ _)⟩
  let Cj : ℕ → ℝ := fun j => Classical.choose (h_per_j j)
  have hCj_nn : ∀ j, 0 ≤ Cj j := fun j => (Classical.choose_spec (h_per_j j)).1
  have hCj_bound : ∀ j, ∀ x : EuN, ‖iteratedFDeriv ℝ j χ x‖ ≤ Cj j := fun j =>
    (Classical.choose_spec (h_per_j j)).2
  have h_nonempty : (Finset.range (m + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let C : ℝ := (Finset.range (m + 1)).sup' h_nonempty Cj
  have hC_ge : ∀ j ∈ Finset.range (m + 1), Cj j ≤ C := fun j hj =>
    Finset.le_sup' Cj hj
  refine ⟨C, le_trans (hCj_nn 0)
    (hC_ge 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _))), ?_⟩
  intro j hj x
  exact le_trans (hCj_bound j x)
    (hC_ge j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

omit [NeZero d] in
private lemma cutoff_memWkp_two
    {x₀ : EuN} {R : ℝ} (hR : 0 < R)
    {χ : EuN → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_compact : HasCompactSupport χ)
    {u : EuN → ℝ} {Ω : Set EuN} (hΩ : IsOpen Ω)
    (hball : Metric.ball x₀ (2 * R) ⊆ Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) (k : ℕ) :
    MemWkp (d := d) k 2 (fun x => χ x * u x) (Metric.ball x₀ (2 * R)) := by
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have hball_open : IsOpen (Metric.ball x₀ (2 * R)) := Metric.isOpen_ball
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_ball : MemWkp (d := d) k 2 u (Metric.ball x₀ (2 * R)) :=
    MemWkp.mono_set (d := d) hp_one hΩ hball_open hball (hu k)
  obtain ⟨C, _hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound (d := d) hχ hχ_compact k
  have hχ_bound : ∀ j ≤ k, ∀ x ∈ Metric.ball x₀ (2 * R),
      ‖iteratedFDeriv ℝ j χ x‖ ≤ C := fun j hj x _ => hC_bound j hj x
  exact MemWkp.smul_smooth_bounded (d := d) k hp_one hball_open hχ hχ_bound hu_ball

private theorem tower_to_supercritical
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) (m : ℕ) :
    ∀ (s : ℕ) {p : ℝ}, 1 ≤ p →
      RegularExponent.IsRegular (d : ℝ) p (s + 1) →
      (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p →
      ∀ {f : EuN → ℝ}, HasCompactSupport f → tsupport f ⊆ Ω →
        MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω →
          ∃ q : ℝ, 1 ≤ q ∧ (d : ℝ) < q ∧
            MemWkp (d := d) (m + 1) (ENNReal.ofReal q) f Ω := by
  intro s
  induction s with
  | zero =>
      intro p hp_one _hreg hkp f _hf_cpt _hf_supp hf
      have hp_dim : (d : ℝ) < p := by
        have : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hkp
        exact hkp
      exact ⟨p, hp_one, hp_dim, by simpa using hf⟩
  | succ s ih =>
      intro p hp_one hreg hkp f hf_cpt hf_supp hf
      have hp_ne_d : p ≠ (d : ℝ) := hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hp_ne_d with hp_lt | hp_gt
      · have hp_pos : 0 < p := by linarith
        have hf' : MemWkp (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
          rw [h_idx] at hf
          exact hf
        obtain ⟨h_mem_p1, _h_norm_p1⟩ :=
          TowerStep.MemWkp_subcritical_iterated (d := d) (m + 1 + s)
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
            IterationCalc.kp1_real_gt_d_of_kp1p_gt_d d (s + 1) p hp_pos hp_lt h_form
          rw [hp_1_def]
          exact h_id
        have hreg_p_1 : RegularExponent.IsRegular (d : ℝ) p_1 (s + 1) := by
          rw [hp_1_def]
          exact hreg.tower_step hp_one hp_lt
        have h_mem_p1' : MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω := by
          rw [hp_1_def]; exact h_mem_p1
        exact ih hp_1_one hreg_p_1 hkp_next hf_cpt hf_supp h_mem_p1'
      · exact ⟨p, hp_one, hp_gt, MemWkp.le_of_le (by omega) hf⟩

private theorem exists_contDiff_m_rep_ball
    {x₀ : EuN} {R : ℝ} (hR : 0 < R)
    {u : EuN → ℝ} {Ω : Set EuN} (hΩ : IsOpen Ω)
    (hball : Metric.ball x₀ (2 * R) ⊆ Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) (m : ℕ) :
    ∃ f : EuN → ℝ,
      ContDiff ℝ m f ∧
      u =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] f := by
  classical
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have hball_open : IsOpen (Metric.ball x₀ (2 * R)) := Metric.isOpen_ball
  have hd_pos : 0 < d := NeZero.pos d
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  obtain ⟨χ, hχ_smooth, hχ_cpt, _hχ_range, hχ_one, hχ_supp⟩ :=
    exists_cutoff_ball (d := d) hR
  set v : EuN → ℝ := fun x => χ x * u x with hv_def
  have hv_memWkp : ∀ k : ℕ,
      MemWkp (d := d) k 2 v (Metric.ball x₀ (2 * R)) := fun k =>
    cutoff_memWkp_two (d := d) hR hχ_smooth hχ_cpt hΩ hball hu k
  have h_supp_subset : Function.support v ⊆ Function.support χ := by
    intro x hx
    have hvx : v x ≠ 0 := hx
    intro hχx
    exact hvx (by simp [hv_def, hχx])
  have hv_supp_subset_χ : tsupport v ⊆ tsupport χ := closure_mono h_supp_subset
  have hv_supp_closed : tsupport v ⊆ Metric.closedBall x₀ (3 * R / 2) :=
    hv_supp_subset_χ.trans hχ_supp
  have hcball_subset_ball :
      Metric.closedBall x₀ (3 * R / 2) ⊆ Metric.ball x₀ (2 * R) := by
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    linarith
  have hv_supp_ball : tsupport v ⊆ Metric.ball x₀ (2 * R) :=
    hv_supp_closed.trans hcball_subset_ball
  have hv_cpt : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (3 * R / 2))
      ((subset_tsupport _).trans hv_supp_closed)
  have hs_max_succ_pos : 1 ≤ d + 1 := by omega
  have hp_2_strict : (1 : ℝ) < 2 := by norm_num
  have h_d_lt_kp_2 : (d : ℝ) < ((d + 1 : ℕ) : ℝ) * 2 := by
    have heq : ((d + 1 : ℕ) : ℝ) * 2 = (2 * (d + 1) : ℕ) := by
      push_cast; ring
    rw [heq]
    have : (d : ℝ) < (2 * (d + 1) : ℕ) := by
      push_cast; linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
    exact this
  obtain ⟨p₀, hp₀_one, hp₀_lt, h_d_lt_kp₀, hp₀_reg⟩ :=
    RegularExponent.exists_regular_exponent_below
      (d : ℝ) (d + 1) hs_max_succ_pos hp_2_strict h_d_lt_kp_2
  have hv_mem_two : MemWkp (d := d) (m + 1 + d) 2 v
      (Metric.ball x₀ (2 * R)) := hv_memWkp (m + 1 + d)
  have hp₀_le_two_enn : ENNReal.ofReal p₀ ≤ (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]; rfl]
    exact ENNReal.ofReal_le_ofReal hp₀_lt.le
  have hp₀_one_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p₀ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp₀_one
  have hv_mem_p₀ : MemWkp (d := d) (m + 1 + d) (ENNReal.ofReal p₀) v
      (Metric.ball x₀ (2 * R)) :=
    EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset (d := d)
      (m + 1 + d) hball_open Metric.isClosed_closedBall
      ((measure_closedBall_lt_top (x := x₀) (r := 3 * R / 2)).ne)
      hp₀_one_enn hp₀_le_two_enn hv_supp_closed hv_mem_two
  obtain ⟨q, _hq_one, hq_dim, hv_mem_q⟩ :=
    tower_to_supercritical (d := d) hball_open m d hp₀_one hp₀_reg
      h_d_lt_kp₀ hv_cpt hv_supp_ball hv_mem_p₀
  obtain ⟨f, hf_cdiff, hf_ae⟩ :=
    EuclideanMorrey.morrey_iteratedFDeriv_representative (d := d) (p := q)
      (x₀ := x₀) (R := 2 * R) (u := v) hq_dim h2R_pos m hv_mem_q
  refine ⟨f, hf_cdiff, ?_⟩
  have h_ball_eq : Metric.ball x₀ (2 * R / 4) = Metric.ball x₀ (R / 2) := by
    congr 1; ring
  have hu_eq_v : u =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] v := by
    refine (ae_restrict_iff' (Metric.isOpen_ball.measurableSet)).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx_closed : x ∈ Metric.closedBall x₀ R := by
      rw [Metric.mem_ball] at hx
      rw [Metric.mem_closedBall]
      linarith
    simp only [hv_def, hχ_one x hx_closed, one_mul]
  have hv_eq_f : v =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] f := by
    rw [← h_ball_eq]
    exact hf_ae
  exact hu_eq_v.trans hv_eq_f

private theorem exists_contDiffOn_top_rep_ball
    {x₀ : EuN} {R : ℝ} (hR : 0 < R)
    {u : EuN → ℝ} {Ω : Set EuN} (hΩ : IsOpen Ω)
    (hball : Metric.ball x₀ (2 * R) ⊆ Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) :
    ∃ f : EuN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) f (Metric.ball x₀ (R / 2)) ∧
      u =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] f := by
  classical
  have hR2_pos : (0 : ℝ) < R / 2 := by linarith
  have h_ball_open : IsOpen (Metric.ball x₀ (R / 2)) := Metric.isOpen_ball
  obtain ⟨f₀, hf₀_cdiff, hf₀_ae⟩ :=
    exists_contDiff_m_rep_ball (d := d) hR hΩ hball hu 0
  refine ⟨f₀, ?_, hf₀_ae⟩
  rw [contDiffOn_infty]
  intro m
  obtain ⟨fₘ, hfₘ_cdiff, hfₘ_ae⟩ :=
    exists_contDiff_m_rep_ball (d := d) hR hΩ hball hu m
  have h_ae_eq : f₀ =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] fₘ :=
    (hf₀_ae.symm).trans hfₘ_ae
  have h_eqOn : Set.EqOn f₀ fₘ (Metric.ball x₀ (R / 2)) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq h_ae_eq h_ball_open
      hf₀_cdiff.continuous.continuousOn hfₘ_cdiff.continuous.continuousOn
  refine (hfₘ_cdiff.contDiffOn (s := Metric.ball x₀ (R / 2))).congr ?_
  intro x hx
  exact h_eqOn hx

private theorem exists_contDiffOn_top_rep_nhd
    {u : EuN → ℝ} {Ω : Set EuN} (hΩ : IsOpen Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) {x : EuN} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Ω ∧
      ∃ f : EuN → ℝ,
        ContDiffOn ℝ (∞ : WithTop ℕ∞) f (Metric.ball x r) ∧
        u =ᵐ[volume.restrict (Metric.ball x r)] f := by
  classical
  obtain ⟨ρ, hρ_pos, hρ_subset⟩ := Metric.isOpen_iff.mp hΩ x hx
  set R : ℝ := ρ / 4 with hR_def
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  have hball_subset : Metric.ball x (2 * R) ⊆ Ω := by
    intro y hy
    refine hρ_subset ?_
    rw [Metric.mem_ball] at hy ⊢
    have h2R : 2 * R ≤ ρ := by rw [hR_def]; linarith
    exact lt_of_lt_of_le hy h2R
  obtain ⟨f, hf_cdiff, hf_ae⟩ :=
    exists_contDiffOn_top_rep_ball (d := d) hR_pos hΩ hball_subset hu
  exact ⟨R / 2, by linarith, fun y hy => hball_subset (by
    rw [Metric.mem_ball] at hy ⊢; linarith), f, hf_cdiff, hf_ae⟩

theorem contDiffOn_of_forall_memWkp_two
    {u : EuN → ℝ} {Ω : Set EuN} (hΩ : IsOpen Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) :
    ∃ u_smooth : EuN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth Ω ∧
      u =ᵐ[volume.restrict Ω] u_smooth := by
  classical
  have h_choice : ∀ x : Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball (x : EuN) r ⊆ Ω ∧
      ∃ f : EuN → ℝ,
        ContDiffOn ℝ (∞ : WithTop ℕ∞) f (Metric.ball (x : EuN) r) ∧
        u =ᵐ[volume.restrict (Metric.ball (x : EuN) r)] f := fun x =>
    exists_contDiffOn_top_rep_nhd (d := d) hΩ hu x.2
  choose rad hrad_pos hball_subset frep hfrep_cdiff hfrep_ae using h_choice
  set S : Ω → Set EuN := fun x => Metric.ball (x : EuN) (rad x) with hS_def
  have hS_open : ∀ x : Ω, IsOpen (S x) := fun x => Metric.isOpen_ball
  have hS_subset : ∀ x : Ω, S x ⊆ Ω := hball_subset
  have hx_mem_S : ∀ x : Ω, (x : EuN) ∈ S x := fun x => by
    rw [hS_def]; exact Metric.mem_ball_self (hrad_pos x)
  have hΩ_subset_iUnion : Ω ⊆ ⋃ x : Ω, S x := fun y hy =>
    Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hx_mem_S ⟨y, hy⟩⟩
  have hfrep_cont : ∀ x : Ω, ContinuousOn (frep x) (S x) := fun x =>
    (hfrep_cdiff x).continuousOn
  have h_consistent : ∀ (x y : Ω) (z : EuN) (hzx : z ∈ S x) (hzy : z ∈ S y),
      frep x z = frep y z := by
    intro x y z hzx hzy
    set W : Set EuN := S x ∩ S y with hW_def
    have hW_open : IsOpen W := (hS_open x).inter (hS_open y)
    have hW_sub_x : W ⊆ S x := Set.inter_subset_left
    have hW_sub_y : W ⊆ S y := Set.inter_subset_right
    have hae_x : u =ᵐ[volume.restrict W] frep x :=
      ae_restrict_of_ae_restrict_of_subset hW_sub_x (hfrep_ae x)
    have hae_y : u =ᵐ[volume.restrict W] frep y :=
      ae_restrict_of_ae_restrict_of_subset hW_sub_y (hfrep_ae y)
    have hae_xy : frep x =ᵐ[volume.restrict W] frep y := (hae_x.symm).trans hae_y
    have h_eqOn : Set.EqOn (frep x) (frep y) W :=
      MeasureTheory.Measure.eqOn_open_of_ae_eq hae_xy hW_open
        ((hfrep_cont x).mono hW_sub_x) ((hfrep_cont y).mono hW_sub_y)
    exact h_eqOn ⟨hzx, hzy⟩
  set gΩ : ↥Ω → ℝ :=
    Set.iUnionLift S (fun x z => frep x (z : EuN))
      (fun x y z hzx hzy => h_consistent x y z hzx hzy) Ω hΩ_subset_iUnion
    with hgΩ_def
  set u_smooth : EuN → ℝ := fun y => if h : y ∈ Ω then gΩ ⟨y, h⟩ else 0
    with hu_smooth_def
  have h_u_smooth_eq : ∀ (x : Ω) (z : EuN), z ∈ S x →
      u_smooth z = frep x z := by
    intro x z hz
    have hz_Ω : z ∈ Ω := hS_subset x hz
    have h_lift : gΩ ⟨z, hz_Ω⟩ = frep x (z : EuN) :=
      Set.iUnionLift_of_mem (S := S) (T := (Ω : Set EuN)) ⟨z, hz_Ω⟩ hz
    rw [hu_smooth_def]
    simp only [hz_Ω, dif_pos]
    exact h_lift
  refine ⟨u_smooth, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn ?_
    intro y hy
    refine ⟨S ⟨y, hy⟩, hS_open ⟨y, hy⟩, hx_mem_S ⟨y, hy⟩, ?_⟩
    refine ((hfrep_cdiff ⟨y, hy⟩).mono (Set.inter_subset_right)).congr ?_
    intro z hz
    exact h_u_smooth_eq ⟨y, hy⟩ z hz.2
  · obtain ⟨T, hT_countable, hT_cover⟩ :=
      TopologicalSpace.isOpen_iUnion_countable S hS_open
    have hΩ_sub_biUnion : Ω ⊆ ⋃ x ∈ T, S x := by
      rw [hT_cover]; exact hΩ_subset_iUnion
    have hae_each : ∀ x ∈ T, u =ᵐ[volume.restrict (S x)] u_smooth := by
      intro x _hxT
      have h1 : u =ᵐ[volume.restrict (S x)] frep x := hfrep_ae x
      refine h1.trans ?_
      refine (ae_restrict_iff' (hS_open x).measurableSet).mpr ?_
      exact Filter.Eventually.of_forall fun z hz => (h_u_smooth_eq x z hz).symm
    have hae_biUnion :
        u =ᵐ[volume.restrict (⋃ x ∈ T, S x)] u_smooth :=
      (MeasureTheory.ae_eq_restrict_biUnion_iff S hT_countable u u_smooth).mpr
        hae_each
    exact hae_biUnion.filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono hΩ_sub_biUnion le_rfl))

end EuclideanIteratedEmbedding
end Sobolev
end Analysis
end DifferentialGeometry
