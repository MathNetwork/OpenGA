import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Approximation
import DifferentialGeometry.External.DeGiorgi.Poincare
import DifferentialGeometry.External.DeGiorgi.SobolevPoincare
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreyRieszKernel
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreySmoothHolderBound
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreySmoothInequality


noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EuclideanMorrey
variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem exists_smooth_cutoff_ball
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) :
    ∃ η : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.closedBall x₀ (3 * R / 4), η x = 1) ∧
      tsupport η ⊆ Metric.closedBall x₀ (7 * R / 8) := by
  classical
  have hR34_pos : 0 < 3 * R / 4 := by linarith
  have hR78_pos : 0 < 7 * R / 8 := by linarith
  have hR_pos : 0 < R := hR
  have hδ_pos : (0 : ℝ) < R / 16 := by linarith
  have hclosed_R34 : IsClosed (Metric.closedBall x₀ (3 * R / 4)) :=
    Metric.isClosed_closedBall
  have hopen_R78 : IsOpen (Metric.thickening (R / 16) (Metric.closedBall x₀ (3 * R / 4))) :=
    isOpen_thickening
  have hRsub : Metric.closedBall x₀ (3 * R / 4) ⊆
      Metric.thickening (R / 16) (Metric.closedBall x₀ (3 * R / 4)) :=
    Metric.self_subset_thickening hδ_pos _
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d)))
      (s := Metric.thickening (R / 16) (Metric.closedBall x₀ (3 * R / 4)))
      (t := Metric.closedBall x₀ (3 * R / 4))
      hopen_R78 hclosed_R34 hRsub with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  have h_support_in_closedBall :
      tsupport η ⊆ Metric.closedBall x₀ (7 * R / 8) := by
    have hRR_le : 3 * R / 4 + R / 16 ≤ 7 * R / 8 := by linarith
    have h_closed : IsClosed (Metric.closedBall x₀ (7 * R / 8)) :=
      Metric.isClosed_closedBall
    rw [tsupport, hη_support]
    refine closure_minimal ?_ h_closed
    intro y hy
    rw [Metric.mem_thickening_iff] at hy
    rcases hy with ⟨z, hz_mem, hyz⟩
    rw [Metric.mem_closedBall] at hz_mem ⊢
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ ≤ R / 16 + 3 * R / 4 := by
          have hyz_le : dist y z ≤ R / 16 := le_of_lt hyz
          linarith
      _ ≤ 7 * R / 8 := by linarith
  refine ⟨η, contMDiff_iff_contDiff.mp hη_smooth, ?_, hη_range, ?_, h_support_in_closedBall⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (7 * R / 8)) ?_
    exact (subset_tsupport _).trans h_support_in_closedBall
  · intro x hx
    exact (hη_one_iff x).1 hx

omit [NeZero d] in
private lemma cutoff_norm_le_one {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1) (x : EuclideanSpace ℝ (Fin d)) :
    |η x| ≤ 1 := by
  have hx : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
  rcases hx with ⟨h0, h1⟩
  rw [abs_of_nonneg h0]
  exact h1

omit [NeZero d] in
private lemma exists_grad_bound_of_smooth_compactSupport
    {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖fderiv ℝ η x‖ ≤ C := by
  have h_fderiv_cont : Continuous (fderiv ℝ η) :=
    hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have h_grad_compact : HasCompactSupport (fderiv ℝ η) := hη_compact.fderiv (𝕜 := ℝ)
  have h_norm_cont : Continuous (fun x => ‖fderiv ℝ η x‖) := h_fderiv_cont.norm
  have h_norm_compact : HasCompactSupport (fun x => ‖fderiv ℝ η x‖) :=
    h_grad_compact.norm
  obtain ⟨M, hM_nn, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ η x‖ ≤ M := by
    by_cases h_supp : (Function.support fun x => ‖fderiv ℝ η x‖).Nonempty
    · have h_compact_set : IsCompact (tsupport (fun x => ‖fderiv ℝ η x‖)) :=
        h_norm_compact
      have h_continuousOn : ContinuousOn (fun x => ‖fderiv ℝ η x‖)
          (tsupport (fun x => ‖fderiv ℝ η x‖)) := h_norm_cont.continuousOn
      have h_compact_nonempty :
          (tsupport (fun x => ‖fderiv ℝ η x‖)).Nonempty :=
        h_supp.mono (subset_tsupport _)
      obtain ⟨x_max, hx_in, hx_max⟩ :=
        h_compact_set.exists_isMaxOn h_compact_nonempty h_continuousOn
      refine ⟨‖fderiv ℝ η x_max‖, norm_nonneg _, ?_⟩
      intro x
      by_cases h_in : x ∈ tsupport (fun x => ‖fderiv ℝ η x‖)
      · exact hx_max h_in
      · have h_zero : ‖fderiv ℝ η x‖ = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun x => ‖fderiv ℝ η x‖) h_in
        rw [h_zero]
        exact norm_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      have hx : x ∉ Function.support (fun x => ‖fderiv ℝ η x‖) := by
        intro hx_in
        exact h_supp ⟨x, hx_in⟩
      simp only [Function.mem_support, ne_eq, not_not] at hx
      rw [hx]
  exact ⟨M, hM_nn, hM⟩

omit [NeZero d] in
private lemma euclideanBasis_norm_one (i : Fin d) :
    ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by
  simp

omit [NeZero d] in
private lemma partial_deriv_norm_le_fderiv
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |(fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ))| ≤ ‖fderiv ℝ f x‖ := by
  have h := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
  rw [euclideanBasis_norm_one, mul_one] at h
  rwa [Real.norm_eq_abs] at h

omit [NeZero d] in
private lemma euclidean_norm_le_sum_abs (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ ∑ i : Fin d, |v i| := by
  exact euclidean_norm_le_sum_norms v

omit [NeZero d] in
private lemma norm_fderiv_eq_partial_norm
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ f x‖ =
      ‖(WithLp.toLp 2
        (fun i : Fin d => (fderiv ℝ f x) (EuclideanSpace.single i 1)) :
          EuclideanSpace ℝ (Fin d))‖ :=
  norm_fderiv_eq_norm_partials_local (ψ := f) x

private theorem smooth_pointwise_holder_bound_components
    {p : ℝ} (hp : (d : ℝ) < p) {z : E} {r : ℝ} (hr : 0 < r)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {x : E} (hx : x ∈ Metric.ball z r) :
    ‖u x - ⨍ y in Metric.ball z r, u y ∂volume‖ ≤
      smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) *
        (∑ i : Fin d, eLpNorm
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball z r))).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have hC_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  have h_r_pow_nn : 0 ≤ r ^ (1 - (d : ℝ) / p) := Real.rpow_nonneg hr.le _
  have hpp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one.le
  have hbound := smooth_pointwise_holder_bound_explicit (d := d) hp hr hu hx
  have h_norm_le : ∀ y : E,
      ‖fderiv ℝ u y‖ ≤
        ∑ i : Fin d, ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖ := by
    intro y
    rw [norm_fderiv_eq_norm_partials_local (d := d) (ψ := u) y]
    refine (euclidean_norm_le_sum_norms (d := d) _).trans ?_
    apply le_of_eq
    refine Finset.sum_congr rfl ?_
    intro i _
    simp
  have h_eLpNorm_le :
      eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball z r)) ≤
        eLpNorm (fun y => ∑ i : Fin d,
          ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball z r)) := by
    refine eLpNorm_mono ?_
    intro y
    rw [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    exact h_norm_le y
  have h_aesm : ∀ i : Fin d,
      AEStronglyMeasurable (fun y => ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖)
        (volume.restrict (Metric.ball z r)) := by
    intro i
    have hcont : Continuous (fun y => ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖) :=
      (((hu.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const).norm)
    exact hcont.aestronglyMeasurable.restrict
  have h_sum_eLpNorm_le :
      eLpNorm (fun y => ∑ i : Fin d,
        ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) ≤
      ∑ i : Fin d, eLpNorm (fun y =>
        ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) := by
    have h_eq : (fun y => ∑ i : Fin d,
        ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin d, (fun y =>
          ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖) := by
      ext y; simp [Finset.sum_apply]
    rw [h_eq]
    exact eLpNorm_sum_le (fun i _ => h_aesm i) hpp_one
  have h_comp_eq : ∀ i : Fin d,
      eLpNorm (fun y => ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) =
      eLpNorm (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) := fun i => eLpNorm_norm _
  have h_eLpNorm_total :
      eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) ≤
      ∑ i : Fin d, eLpNorm (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1))
        (ENNReal.ofReal p) (volume.restrict (Metric.ball z r)) := by
    refine h_eLpNorm_le.trans (h_sum_eLpNorm_le.trans (le_of_eq ?_))
    refine Finset.sum_congr rfl ?_
    intro i _; exact h_comp_eq i
  have h_eLpNorm_lt : eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball z r)) ≠ ⊤ := by
    have h_memLp : MemLp (fun y : E => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) :=
      smooth_grad_memLp_on_ball (d := d) hp_pos hr hu
    exact h_memLp.eLpNorm_ne_top
  have h_sum_lt :
      (∑ i : Fin d, eLpNorm (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1))
        (ENNReal.ofReal p) (volume.restrict (Metric.ball z r))) ≠ ⊤ := by
    refine ne_of_lt ?_
    refine ENNReal.sum_lt_top.mpr ?_
    intro i _
    refine lt_of_le_of_lt (b := eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r))) ?_ (lt_of_le_of_ne le_top h_eLpNorm_lt)
    refine eLpNorm_mono ?_
    intro y
    have hbound_pt : ‖(fderiv ℝ u y) (EuclideanSpace.single i 1)‖ ≤
        ‖fderiv ℝ u y‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hsingle_norm : ‖(EuclideanSpace.single i (1 : ℝ) : E)‖ = 1 := by
      simp
    rw [hsingle_norm, mul_one] at hbound_pt
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hbound_pt
  have h_real_le :
      (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r))).toReal ≤
      (∑ i : Fin d, eLpNorm (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1))
        (ENNReal.ofReal p) (volume.restrict (Metric.ball z r))).toReal :=
    ENNReal.toReal_mono h_sum_lt h_eLpNorm_total
  calc ‖u x - ⨍ y in Metric.ball z r, u y ∂volume‖
      ≤ smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball z r))).toReal := hbound
    _ ≤ smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) *
          (∑ i : Fin d, eLpNorm (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball z r))).toReal := by
        apply mul_le_mul_of_nonneg_left h_real_le
        exact mul_nonneg hC_nn h_r_pow_nn

private noncomputable def cutoffWitness
    {p : ℝ} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u η : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1) :
    DeGiorgi.MemW1pWitness (ENNReal.ofReal p) (fun x => η x * u x) Ω :=
  DeGiorgi.MemW1pWitness.mul_smooth_bounded_p (d := d)
    (hp := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal hp_one)
    hΩ hu hη
    (C₀ := 1)
    (C₁ := Classical.choose (exists_grad_bound_of_smooth_compactSupport (d := d) hη hη_compact))
    (by norm_num)
    (Classical.choose_spec
      (exists_grad_bound_of_smooth_compactSupport (d := d) hη hη_compact)).1
    (fun x => cutoff_norm_le_one (d := d) hη_range x)
    (Classical.choose_spec
      (exists_grad_bound_of_smooth_compactSupport (d := d) hη hη_compact)).2

omit [NeZero d] in
private lemma tsupport_smul_subset_left'
    {η u : E → ℝ} :
    tsupport (fun x => η x * u x) ⊆ tsupport η := by
  refine closure_mono ?_
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  intro hη
  apply hx
  rw [hη, zero_mul]

private theorem exists_smooth_cutoff_approx
    {p : ℝ} (hp : 1 < p)
    {Ω K : Set E} (hΩ_open : IsOpen Ω)
    (hK_compact : IsCompact K) (hKΩ : K ⊆ Ω)
    {u η : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    (hη_supp : tsupport η ⊆ K) :
    ∃ φ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Ω) ∧
      Tendsto
        (fun n => eLpNorm (fun x => φ n x - η x * u x)
          (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (𝓝 0) ∧
      (∀ i : Fin d,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
                  (cutoffWitness (d := d) hp.le hΩ_open hu hη hη_compact hη_range).weakGrad x i)
              (ENNReal.ofReal p) (volume.restrict Ω))
          atTop (𝓝 0)) := by
  classical
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  let hw' := cutoffWitness (d := d) hp.le hΩ_open hu hη hη_compact hη_range
  have h_supp_sub : tsupport (fun x => η x * u x) ⊆ K :=
    (tsupport_smul_subset_left' (d := d) (η := η) (u := u)).trans hη_supp
  have hgrad_sub : ∀ i : Fin d, tsupport (fun x => hw'.weakGrad x i) ⊆ K := by
    intro i
    have hcl : Function.support (fun x => hw'.weakGrad x i) ⊆ K := by
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx
      by_contra hxK
      apply hx
      have hx_not_supp : x ∉ tsupport η := fun h => hxK (hη_supp h)
      have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx_not_supp
      have hη_fderiv_zero : (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) = 0 := by
        have h_supp_fderiv_apply : tsupport
            (fun y => (fderiv ℝ η y) (EuclideanSpace.single i (1 : ℝ))) ⊆ tsupport η :=
          tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i (1 : ℝ))
        have hxh : x ∉ tsupport
            (fun y => (fderiv ℝ η y) (EuclideanSpace.single i (1 : ℝ))) :=
          fun h => hx_not_supp (h_supp_fderiv_apply h)
        exact image_eq_zero_of_notMem_tsupport
          (f := fun y => (fderiv ℝ η y) (EuclideanSpace.single i (1 : ℝ))) hxh
      change (η x • hu.weakGrad x +
          (WithLp.toLp 2 fun j : Fin d =>
            (fderiv ℝ η x) (EuclideanSpace.single j 1) * u x : E)) i = 0
      simp [hη_zero, hη_fderiv_zero]
    refine (closure_mono hcl).trans ?_
    exact hK_compact.isClosed.closure_subset
  rcases DeGiorgi.exists_smooth_W1p_approx_of_supportedWitness (d := d)
    hΩ_open hp hw' hK_compact hKΩ h_supp_sub hgrad_sub with
    ⟨φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩
  exact ⟨φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩

omit [NeZero d] in
private lemma eLpNorm_one_le_eLpNorm_p_finite_measure
    {p : ℝ} (hp : 1 < p) {μ : Measure E} [IsFiniteMeasure μ]
    {f : E → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm f 1 μ ≤ eLpNorm f (ENNReal.ofReal p) μ *
      (μ Set.univ) ^ (1 - 1 / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := f)
    hp_le_p hf.aestronglyMeasurable
  have h_exp_eq : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal = 1 - 1 / p := by
    rw [ENNReal.toReal_ofReal hp_pos.le]
    simp
  rw [h_exp_eq] at h
  exact h

omit [NeZero d] in
private lemma tendsto_eLpNorm_one_of_tendsto_eLpNorm_p
    {p : ℝ} (hp : 1 < p) {μ : Measure E} [IsFiniteMeasure μ]
    {F : ℕ → E → ℝ} (hF : ∀ n, MemLp (F n) (ENNReal.ofReal p) μ)
    (h : Tendsto (fun n => eLpNorm (F n) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 1 μ) atTop (𝓝 0) := by
  have hμ_top : (μ Set.univ) ≠ ⊤ := measure_ne_top _ _
  have h_pow_ne_top : (μ Set.univ) ^ (1 - 1 / p) ≠ ∞ := by
    have h_exp_nn : 0 ≤ 1 - 1 / p := by
      have hp_pos : 0 < p := lt_trans zero_lt_one hp
      have : 1 / p < 1 := (div_lt_one hp_pos).mpr hp
      linarith
    exact ENNReal.rpow_ne_top_of_nonneg h_exp_nn hμ_top
  have h_const :
      Tendsto (fun n =>
        eLpNorm (F n) (ENNReal.ofReal p) μ *
          (μ Set.univ) ^ (1 - 1 / p)) atTop (𝓝 (0 * (μ Set.univ) ^ (1 - 1 / p))) :=
    ENNReal.Tendsto.mul_const h (Or.inr h_pow_ne_top)
  rw [zero_mul] at h_const
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const
    (Filter.Eventually.of_forall fun _ => zero_le _)
    (Filter.Eventually.of_forall ?_)
  intro n
  exact eLpNorm_one_le_eLpNorm_p_finite_measure (d := d) hp (hF n)

omit [NeZero d] in
private lemma tendsto_setIntegral_of_eLpNorm_p_to_zero
    {p : ℝ} (hp : 1 < p) {Ω : Set E} (_hΩ : MeasurableSet Ω)
    (hΩ_finite : volume Ω ≠ ⊤)
    {g : E → ℝ} {F : ℕ → E → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict Ω))
    (hF : ∀ n, MemLp (F n) (ENNReal.ofReal p) (volume.restrict Ω))
    (h : Tendsto
      (fun n => eLpNorm (fun x => F n x - g x) (ENNReal.ofReal p)
        (volume.restrict Ω)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in Ω, F n x ∂volume) atTop
      (𝓝 (∫ x in Ω, g x ∂volume)) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict Ω : Measure E) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hΩ_finite
  have h_diff_memLp : ∀ n, MemLp (fun x => F n x - g x) (ENNReal.ofReal p)
      (volume.restrict Ω) := fun n => (hF n).sub hg
  have h_L1 : Tendsto (fun n =>
      eLpNorm (fun x => F n x - g x) 1 (volume.restrict Ω)) atTop (𝓝 0) :=
    tendsto_eLpNorm_one_of_tendsto_eLpNorm_p (d := d) hp h_diff_memLp h
  have h_lint : Tendsto (fun n =>
      ∫⁻ x, ‖F n x - g x‖ₑ ∂(volume.restrict Ω)) atTop (𝓝 0) := by
    have h_eq : ∀ n,
        eLpNorm (fun x => F n x - g x) 1 (volume.restrict Ω) =
          ∫⁻ x, ‖F n x - g x‖ₑ ∂(volume.restrict Ω) := by
      intro n
      rw [eLpNorm_one_eq_lintegral_enorm]
    refine (Filter.tendsto_congr h_eq).mp h_L1
  have hg_int : Integrable g (volume.restrict Ω) := by
    have h_one_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal hp.le
    exact (memLp_one_iff_integrable.mp
      (hg.mono_exponent h_one_le_p))
  have hF_int : ∀ n, Integrable (F n) (volume.restrict Ω) := fun n => by
    have h_one_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal hp.le
    exact memLp_one_iff_integrable.mp ((hF n).mono_exponent h_one_le_p)
  have h_int_tendsto :=
    MeasureTheory.tendsto_integral_of_L1 (μ := volume.restrict Ω) g hg_int
      (Filter.Eventually.of_forall hF_int) h_lint
  have hF_eq_setInt : ∀ n, ∫ x, F n x ∂(volume.restrict Ω) =
      ∫ x in Ω, F n x ∂volume := fun n => rfl
  have hg_eq_setInt : ∫ x, g x ∂(volume.restrict Ω) = ∫ x in Ω, g x ∂volume := rfl
  rw [show (fun n => ∫ x in Ω, F n x ∂volume) = (fun n => ∫ x, F n x ∂(volume.restrict Ω)) from
    funext (fun n => (hF_eq_setInt n).symm)]
  rw [show ∫ x in Ω, g x ∂volume = ∫ x, g x ∂(volume.restrict Ω) from hg_eq_setInt.symm]
  exact h_int_tendsto

omit [NeZero d] in
private lemma tendsto_setAverage_of_eLpNorm_p_to_zero
    {p : ℝ} (hp : 1 < p) {z : E} {r : ℝ} (hr : 0 < r)
    {g : E → ℝ} {F : ℕ → E → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict (Metric.ball z r)))
    (hF : ∀ n, MemLp (F n) (ENNReal.ofReal p) (volume.restrict (Metric.ball z r)))
    (h : Tendsto
      (fun n => eLpNorm (fun x => F n x - g x) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r))) atTop (𝓝 0)) :
    Tendsto (fun n => ⨍ x in Metric.ball z r, F n x ∂volume) atTop
      (𝓝 (⨍ x in Metric.ball z r, g x ∂volume)) := by
  have h_int_tendsto :=
    tendsto_setIntegral_of_eLpNorm_p_to_zero (d := d) hp measurableSet_ball
      measure_ball_lt_top.ne hg hF h
  have hvol_pos : 0 < (volume (Metric.ball z r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume z hr).ne' measure_ball_lt_top.ne
  have h_inv_tendsto : Tendsto
      (fun n => ((volume (Metric.ball z r)).toReal)⁻¹ * ∫ x in Metric.ball z r, F n x ∂volume)
      atTop
      (𝓝 (((volume (Metric.ball z r)).toReal)⁻¹ * ∫ x in Metric.ball z r, g x ∂volume)) :=
    h_int_tendsto.const_mul _
  have h_avg_eq : ∀ n,
      ⨍ x in Metric.ball z r, F n x ∂volume =
        ((volume (Metric.ball z r)).toReal)⁻¹ * ∫ x in Metric.ball z r, F n x ∂volume := by
    intro n
    rw [setAverage_eq, measureReal_def, smul_eq_mul]
  have h_avg_g_eq :
      ⨍ x in Metric.ball z r, g x ∂volume =
        ((volume (Metric.ball z r)).toReal)⁻¹ * ∫ x in Metric.ball z r, g x ∂volume := by
    rw [setAverage_eq, measureReal_def, smul_eq_mul]
  rw [show (fun n => ⨍ x in Metric.ball z r, F n x ∂volume) =
    (fun n => ((volume (Metric.ball z r)).toReal)⁻¹ *
      ∫ x in Metric.ball z r, F n x ∂volume) from funext h_avg_eq]
  rw [h_avg_g_eq]
  exact h_inv_tendsto

omit [NeZero d] in
private lemma eLpNorm_sub_le_eLpNorm_diff_real
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure E} {f g : E → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ) :
    |((eLpNorm f p μ).toReal) - ((eLpNorm g p μ).toReal)| ≤
      ((eLpNorm (fun x => f x - g x) p μ).toReal) := by
  have h1 : eLpNorm f p μ ≤ eLpNorm g p μ + eLpNorm (fun x => f x - g x) p μ := by
    have h_eq : f = (fun x => g x + (f x - g x)) := by funext; ring
    nth_rewrite 1 [h_eq]
    refine (eLpNorm_add_le hg.aestronglyMeasurable
      (hf.sub hg).aestronglyMeasurable hp).trans (le_refl _)
  have h2 : eLpNorm g p μ ≤ eLpNorm f p μ + eLpNorm (fun x => f x - g x) p μ := by
    have h_eq : g = (fun x => f x + (g x - f x)) := by funext; ring
    nth_rewrite 1 [h_eq]
    have h_step : eLpNorm (fun x => f x + (g x - f x)) p μ ≤
        eLpNorm f p μ + eLpNorm (fun x => g x - f x) p μ :=
      eLpNorm_add_le hf.aestronglyMeasurable
        ((hg.sub hf).aestronglyMeasurable) hp
    refine h_step.trans ?_
    have h_eLpNorm_eq : eLpNorm (fun x => g x - f x) p μ =
        eLpNorm (fun x => f x - g x) p μ := by
      have h_neg : (fun x => g x - f x) = -(fun x => f x - g x) := by
        funext x
        change g x - f x = -(f x - g x)
        ring
      rw [h_neg, eLpNorm_neg]
    rw [h_eLpNorm_eq]
  have h_finite_f : eLpNorm f p μ ≠ ⊤ := hf.eLpNorm_ne_top
  have h_finite_g : eLpNorm g p μ ≠ ⊤ := hg.eLpNorm_ne_top
  have h_finite_diff : eLpNorm (fun x => f x - g x) p μ ≠ ⊤ :=
    (hf.sub hg).eLpNorm_ne_top
  have h1_real : (eLpNorm f p μ).toReal ≤
      (eLpNorm g p μ).toReal + (eLpNorm (fun x => f x - g x) p μ).toReal := by
    have h_finite_sum : eLpNorm g p μ + eLpNorm (fun x => f x - g x) p μ ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨h_finite_g, h_finite_diff⟩
    rw [← ENNReal.toReal_add h_finite_g h_finite_diff]
    exact ENNReal.toReal_mono h_finite_sum h1
  have h2_real : (eLpNorm g p μ).toReal ≤
      (eLpNorm f p μ).toReal + (eLpNorm (fun x => f x - g x) p μ).toReal := by
    have h_finite_sum : eLpNorm f p μ + eLpNorm (fun x => f x - g x) p μ ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨h_finite_f, h_finite_diff⟩
    rw [← ENNReal.toReal_add h_finite_f h_finite_diff]
    exact ENNReal.toReal_mono h_finite_sum h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

omit [NeZero d] in
private lemma tendsto_eLpNorm_toReal_of_diff_tendsto_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure E} {g : E → ℝ} {F : ℕ → E → ℝ}
    (hg : MemLp g p μ) (hF : ∀ n, MemLp (F n) p μ)
    (h : Tendsto (fun n => eLpNorm (fun x => F n x - g x) p μ) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (F n) p μ).toReal) atTop
      (𝓝 ((eLpNorm g p μ).toReal)) := by
  have h_diff_real : Tendsto
      (fun n => (eLpNorm (fun x => F n x - g x) p μ).toReal) atTop (𝓝 0) := by
    have h_finite : ∀ n, eLpNorm (fun x => F n x - g x) p μ ≠ ⊤ := fun n =>
      ((hF n).sub hg).eLpNorm_ne_top
    exact (ENNReal.tendsto_toReal_iff h_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤)).mpr (by simpa using h)
  have h_bound : ∀ n,
      |((eLpNorm (F n) p μ).toReal) - ((eLpNorm g p μ).toReal)| ≤
        (eLpNorm (fun x => F n x - g x) p μ).toReal :=
    fun n => eLpNorm_sub_le_eLpNorm_diff_real (d := d) hp (hF n) hg
  rw [Metric.tendsto_atTop] at h_diff_real
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h_diff_real ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (h_bound n) ?_
  have hN_n := hN n hn
  rw [Real.dist_eq, sub_zero] at hN_n
  have h_nn : 0 ≤ (eLpNorm (fun x => F n x - g x) p μ).toReal :=
    ENNReal.toReal_nonneg
  rw [abs_of_nonneg h_nn] at hN_n
  exact hN_n

private theorem smooth_pair_bound_inner
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {x y : E}
    (hx : x ∈ Metric.ball x₀ (R / 4)) (hy : y ∈ Metric.ball x₀ (R / 4)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
        (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
  have hR'_pos : 0 < 3 * R / 4 := by linarith
  obtain ⟨C, hC_nn, hbound⟩ :=
    smooth_morrey_pair_bound (d := d) hp hR'_pos hu (x₀ := x₀)
  have hx' : x ∈ Metric.ball x₀ ((3 * R / 4) / 2) := by
    rw [Metric.mem_ball] at hx ⊢
    linarith
  have hy' : y ∈ Metric.ball x₀ ((3 * R / 4) / 2) := by
    rw [Metric.mem_ball] at hy ⊢
    linarith
  exact ⟨C, hC_nn, hbound hx' hy'⟩

private lemma smooth_avg_diff_pointwise_bound
    {p : ℝ} (hp : (d : ℝ) < p)
    {z c : E} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (h_sub : Metric.ball c ρ ⊆ Metric.ball z r)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ‖(⨍ w in Metric.ball c ρ, φ w ∂volume) -
      (⨍ w in Metric.ball z r, φ w ∂volume)‖ ≤
        smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball z r))).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hC_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  have h_r_pow_nn : 0 ≤ r ^ (1 - (d : ℝ) / p) := Real.rpow_nonneg hr.le _
  have h_eLp_nn : 0 ≤ (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball z r))).toReal := ENNReal.toReal_nonneg
  set Mavg : ℝ := ⨍ w in Metric.ball z r, φ w ∂volume with hMavg_def
  set Cval : ℝ := smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) *
      (eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r))).toReal with hCval_def
  have hCval_nn : 0 ≤ Cval := by
    rw [hCval_def]
    exact mul_nonneg (mul_nonneg hC_nn h_r_pow_nn) h_eLp_nn
  have h_pointwise : ∀ w ∈ Metric.ball z r, ‖φ w - Mavg‖ ≤ Cval := by
    intro w hw
    show ‖φ w - Mavg‖ ≤ Cval
    exact smooth_pointwise_holder_bound_explicit (d := d) hp hr hφ hw
  have hvol_finite : (volume (Metric.ball c ρ) : ℝ≥0∞) ≠ ⊤ := measure_ball_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c ρ) : Measure E) := by
    refine ⟨?_⟩; rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hvol_finite
  have hvol_pos : 0 < (volume (Metric.ball c ρ)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume c hρ).ne' measure_ball_lt_top.ne
  have hφ_int : IntegrableOn φ (Metric.ball c ρ) volume := by
    have h_int_compact : IntegrableOn φ (Metric.closedBall c ρ) volume :=
      hφ.continuous.continuousOn.integrableOn_compact (isCompact_closedBall c ρ)
    exact h_int_compact.mono_set ball_subset_closedBall
  have hMavg_const_int :
      Integrable (fun _ : E => Mavg) (volume.restrict (Metric.ball c ρ)) :=
    integrable_const Mavg
  have hMavg_const_intOn :
      IntegrableOn (fun _ : E => Mavg) (Metric.ball c ρ) volume := hMavg_const_int
  have hφ_diff_int :
      IntegrableOn (fun w => φ w - Mavg) (Metric.ball c ρ) volume :=
    hφ_int.sub hMavg_const_intOn
  have hφ_norm_int :
      IntegrableOn (fun w => ‖φ w - Mavg‖) (Metric.ball c ρ) volume :=
    hφ_diff_int.norm
  have h_avg_diff_eq :
      (⨍ w in Metric.ball c ρ, φ w ∂volume) - Mavg =
        ((volume (Metric.ball c ρ)).toReal)⁻¹ *
          ∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume := by
    have h_avg : ⨍ w in Metric.ball c ρ, φ w ∂volume =
        ((volume (Metric.ball c ρ)).toReal)⁻¹ *
          ∫ w in Metric.ball c ρ, φ w ∂volume := by
      rw [setAverage_eq, measureReal_def, smul_eq_mul]
    rw [h_avg]
    have h_int_split : ∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume =
        ∫ w in Metric.ball c ρ, φ w ∂volume - Mavg * (volume (Metric.ball c ρ)).toReal := by
      rw [MeasureTheory.integral_sub hφ_int hMavg_const_intOn]
      have h_const_int : ∫ _ in Metric.ball c ρ, Mavg ∂volume =
          Mavg * (volume (Metric.ball c ρ)).toReal := by
        rw [setIntegral_const]
        rw [measureReal_def, smul_eq_mul, mul_comm]
      rw [h_const_int]
    rw [h_int_split]
    field_simp
  rw [h_avg_diff_eq]
  have h_int_norm_bound : |∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume| ≤
      ∫ w in Metric.ball c ρ, ‖φ w - Mavg‖ ∂volume := by
    rw [show |∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume| =
      ‖∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume‖ from rfl]
    exact norm_integral_le_integral_norm _
  have h_int_norm_le :
      ∫ w in Metric.ball c ρ, ‖φ w - Mavg‖ ∂volume ≤
        Cval * (volume (Metric.ball c ρ)).toReal := by
    have h1 : ∫ w in Metric.ball c ρ, ‖φ w - Mavg‖ ∂volume ≤
        ∫ _ in Metric.ball c ρ, Cval ∂volume := by
      refine setIntegral_mono_on hφ_norm_int ?_ measurableSet_ball ?_
      · exact integrableOn_const
      · intro w hw
        exact h_pointwise w (h_sub hw)
    have h_const_int : ∫ _ in Metric.ball c ρ, Cval ∂volume =
        Cval * (volume (Metric.ball c ρ)).toReal := by
      rw [setIntegral_const]
      rw [measureReal_def, smul_eq_mul, mul_comm]
    rw [← h_const_int]; exact h1
  have h_vol_inv_nn : 0 ≤ ((volume (Metric.ball c ρ)).toReal)⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  calc ‖((volume (Metric.ball c ρ)).toReal)⁻¹ *
          ∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume‖
      = ((volume (Metric.ball c ρ)).toReal)⁻¹ *
          ‖∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h_vol_inv_nn]
    _ = ((volume (Metric.ball c ρ)).toReal)⁻¹ *
          |∫ w in Metric.ball c ρ, (φ w - Mavg) ∂volume| := by rfl
    _ ≤ ((volume (Metric.ball c ρ)).toReal)⁻¹ *
          ∫ w in Metric.ball c ρ, ‖φ w - Mavg‖ ∂volume := by
        exact mul_le_mul_of_nonneg_left h_int_norm_bound h_vol_inv_nn
    _ ≤ ((volume (Metric.ball c ρ)).toReal)⁻¹ *
          (Cval * (volume (Metric.ball c ρ)).toReal) := by
        exact mul_le_mul_of_nonneg_left h_int_norm_le h_vol_inv_nn
    _ = Cval := by
        field_simp

omit [NeZero d] in
private lemma eLpNorm_fderiv_norm_le_sum_components
    {p : ℝ} (hp : 1 < p) {z : E} {r : ℝ}
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) ≤
      ∑ i : Fin d, eLpNorm
        (fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
        (ENNReal.ofReal p) (volume.restrict (Metric.ball z r)) := by
  classical
  have hpp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  have h_norm_le : ∀ y : E,
      ‖fderiv ℝ φ y‖ ≤
        ∑ i : Fin d, ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖ := by
    intro y
    rw [norm_fderiv_eq_norm_partials_local (d := d) (ψ := φ) y]
    refine (euclidean_norm_le_sum_norms (d := d) _).trans ?_
    apply le_of_eq
    refine Finset.sum_congr rfl ?_
    intro i _
    simp
  have h_eLpNorm_le :
      eLpNorm (fun y => ‖fderiv ℝ φ y‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball z r)) ≤
        eLpNorm (fun y => ∑ i : Fin d,
          ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball z r)) := by
    refine eLpNorm_mono ?_
    intro y
    rw [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    exact h_norm_le y
  have h_aesm : ∀ i : Fin d,
      AEStronglyMeasurable (fun y => ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖)
        (volume.restrict (Metric.ball z r)) := by
    intro i
    have hcont : Continuous (fun y => ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖) :=
      (((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const).norm)
    exact hcont.aestronglyMeasurable.restrict
  have h_sum_eLpNorm_le :
      eLpNorm (fun y => ∑ i : Fin d,
        ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) ≤
      ∑ i : Fin d, eLpNorm (fun y =>
        ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) := by
    have h_eq : (fun y => ∑ i : Fin d,
        ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin d, (fun y =>
          ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖) := by
      ext y; simp [Finset.sum_apply]
    rw [h_eq]
    exact eLpNorm_sum_le (fun i _ => h_aesm i) hpp_one
  have h_comp_eq : ∀ i : Fin d,
      eLpNorm (fun y => ‖(fderiv ℝ φ y) (EuclideanSpace.single i 1)‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) =
      eLpNorm (fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r)) := fun i => eLpNorm_norm _
  refine h_eLpNorm_le.trans (h_sum_eLpNorm_le.trans (le_of_eq ?_))
  refine Finset.sum_congr rfl ?_
  intro i _; exact h_comp_eq i

omit [NeZero d] in
private lemma cutoffWitness_weakGrad_eq_on_open
    {p : ℝ} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {u η : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {U : Set E} (hU_open : IsOpen U)
    (h_eta_one_on : ∀ x ∈ U, η x = 1) (i : Fin d) :
    ∀ x ∈ U, (cutoffWitness (d := d) hp_one hΩ_open hu hη hη_compact hη_range).weakGrad x i =
      hu.weakGrad x i := by
  classical
  intro x hx
  have h_eta_eq_one : η =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    refine eventually_of_mem (hU_open.mem_nhds hx) ?_
    intro y hy
    exact h_eta_one_on y hy
  have h_fderiv_zero : fderiv ℝ η x = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq h_eta_eq_one]; simp
  have h_eta_x : η x = 1 := h_eta_one_on x hx
  change ((η x) • hu.weakGrad x +
      (WithLp.toLp 2 fun j : Fin d =>
        (fderiv ℝ η x) (EuclideanSpace.single j 1) * u x : E)) i = hu.weakGrad x i
  simp [h_eta_x, h_fderiv_zero]

set_option maxHeartbeats 1600000 in

theorem mean_value_inequality_W1p
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {x y : EuclideanSpace ℝ (Fin d)},
        x ∈ Metric.ball x₀ (R / 4) → y ∈ Metric.ball x₀ (R / 4) →
          ‖meanLebesgueOnBall (Metric.ball x (dist x y / 2)) u -
              meanLebesgueOnBall (Metric.ball y (dist x y / 2)) u‖
            ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
                (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball x₀ R))).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have h_exp_pos : 0 < 1 - (d : ℝ) / p := by
    rw [sub_pos, div_lt_one hp_pos]; exact hp
  have hC₀_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  have hvol_pos : (0 : ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set C : ℝ := 2 * (d : ℝ) * smoothHolderConst d p + 1 with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def]
    have : 0 ≤ 2 * (d : ℝ) * smoothHolderConst d p := by
      apply mul_nonneg
      · exact mul_nonneg (by norm_num) hd_pos.le
      · exact hC₀_nn
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro x y hx hy
  obtain ⟨η, hη_smooth, hη_compact, hη_range, hη_one, hη_supp⟩ :=
    exists_smooth_cutoff_ball (d := d) (x₀ := x₀) hR
  have hsupp_in_ball : tsupport η ⊆ Metric.ball x₀ R := by
    intro z hz
    have hz_close : z ∈ Metric.closedBall x₀ (7 * R / 8) := hη_supp hz
    rw [Metric.mem_closedBall] at hz_close
    rw [Metric.mem_ball]
    linarith
  have hΩ_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  set hw' := cutoffWitness (d := d) hp_one.le hΩ_open hu hη_smooth hη_compact hη_range
  set K : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall x₀ (7 * R / 8) with hK_def
  have hK_compact : IsCompact K := isCompact_closedBall x₀ (7 * R / 8)
  have hKΩ : K ⊆ Metric.ball x₀ R := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]; linarith
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩ :=
    exists_smooth_cutoff_approx (d := d) hp_one hΩ_open hK_compact hKΩ hu
      hη_smooth hη_compact hη_range hη_supp
  by_cases h_xy_eq : x = y
  · subst h_xy_eq
    have h_means_zero :
        meanLebesgueOnBall (Metric.ball x (dist x x / 2)) u -
            meanLebesgueOnBall (Metric.ball x (dist x x / 2)) u = 0 := sub_self _
    rw [h_means_zero, norm_zero]
    have h_zero_pow : (0 : ℝ) ^ (1 - (d : ℝ) / p) = 0 := Real.zero_rpow h_exp_pos.ne'
    have h_zero : (dist x x) ^ (1 - (d : ℝ) / p) = 0 := by
      rw [dist_self]; exact h_zero_pow
    rw [h_zero, mul_zero, zero_mul]
  · have h_dist_pos : 0 < dist x y := dist_pos.mpr h_xy_eq
    set ρ : ℝ := dist x y / 2 with hρ_def
    have hρ_pos : 0 < ρ := by rw [hρ_def]; linarith
    set m : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • (x + y) with hm_def
    have h_x_minus_m : x - m = (1 / 2 : ℝ) • (x - y) := by
      rw [hm_def, smul_add]
      have hx_split : x = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x := by
        rw [← add_smul]
        rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
      rw [smul_sub]
      nth_rewrite 1 [hx_split]
      abel
    have h_y_minus_m : y - m = (1 / 2 : ℝ) • (y - x) := by
      rw [hm_def, smul_add]
      have hy_split : y = (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y := by
        rw [← add_smul]
        rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
      rw [smul_sub]
      nth_rewrite 1 [hy_split]
      abel
    have h_dx_m : dist x m = ρ := by
      rw [dist_eq_norm, h_x_minus_m, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [← dist_eq_norm, hρ_def]; ring
    have h_dy_m : dist y m = ρ := by
      rw [dist_eq_norm, h_y_minus_m, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [show y - x = -(x - y) from by abel, norm_neg]
      rw [← dist_eq_norm, hρ_def]; ring
    have h_m_dist : dist m x₀ < R / 4 := by
      have hxR4 : dist x x₀ < R / 4 := by rw [Metric.mem_ball] at hx; exact hx
      have hyR4 : dist y x₀ < R / 4 := by rw [Metric.mem_ball] at hy; exact hy
      have h_m_minus_x₀ : m - x₀ = (1 / 2 : ℝ) • (x - x₀) + (1 / 2 : ℝ) • (y - x₀) := by
        rw [hm_def, smul_add]
        have hx₀_split : x₀ = (1 / 2 : ℝ) • x₀ + (1 / 2 : ℝ) • x₀ := by
          rw [← add_smul]
          rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
        nth_rewrite 1 [hx₀_split]
        rw [smul_sub, smul_sub]
        abel
      have h_mid : dist m x₀ ≤
          (1 / 2 : ℝ) * dist x x₀ + (1 / 2 : ℝ) * dist y x₀ := by
        rw [dist_eq_norm, h_m_minus_x₀]
        have hsum : ‖(1 / 2 : ℝ) • (x - x₀) + (1 / 2 : ℝ) • (y - x₀)‖ ≤
            ‖(1 / 2 : ℝ) • (x - x₀)‖ + ‖(1 / 2 : ℝ) • (y - x₀)‖ := norm_add_le _ _
        rw [norm_smul, norm_smul] at hsum
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hsum
        rw [show ‖x - x₀‖ = dist x x₀ from (dist_eq_norm _ _).symm,
          show ‖y - x₀‖ = dist y x₀ from (dist_eq_norm _ _).symm] at hsum
        exact hsum
      linarith
    have h_dist_xy_lt : dist x y < R / 2 := by
      have hxR4 : dist x x₀ < R / 4 := by rw [Metric.mem_ball] at hx; exact hx
      have hyR4 : dist y x₀ < R / 4 := by rw [Metric.mem_ball] at hy; exact hy
      have : dist x y ≤ dist x x₀ + dist x₀ y := dist_triangle x x₀ y
      rw [dist_comm x₀ y] at this
      linarith
    have h_ball_m_sub : Metric.ball m (dist x y) ⊆ Metric.ball x₀ (3 * R / 4) := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      calc dist z x₀ ≤ dist z m + dist m x₀ := dist_triangle _ _ _
        _ < dist x y + R / 4 := add_lt_add hz h_m_dist
        _ < R / 2 + R / 4 := by linarith
        _ = 3 * R / 4 := by ring
    have h_ball_m_sub_full : Metric.ball m (dist x y) ⊆ Metric.ball x₀ R := by
      refine h_ball_m_sub.trans ?_
      intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith
    have h_ball_x_sub_m : Metric.ball x ρ ⊆ Metric.ball m (dist x y) := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      calc dist z m ≤ dist z x + dist x m := dist_triangle _ _ _
        _ < ρ + ρ := by rw [h_dx_m]; linarith
        _ = dist x y := by rw [hρ_def]; ring
    have h_ball_y_sub_m : Metric.ball y ρ ⊆ Metric.ball m (dist x y) := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      calc dist z m ≤ dist z y + dist y m := dist_triangle _ _ _
        _ < ρ + ρ := by rw [h_dy_m]; linarith
        _ = dist x y := by rw [hρ_def]; ring
    have h_ball_x_sub_full : Metric.ball x ρ ⊆ Metric.ball x₀ (3 * R / 4) :=
      h_ball_x_sub_m.trans h_ball_m_sub
    have h_ball_y_sub_full : Metric.ball y ρ ⊆ Metric.ball x₀ (3 * R / 4) :=
      h_ball_y_sub_m.trans h_ball_m_sub
    have h_eta_one_on_ball : ∀ z ∈ Metric.ball x₀ (3 * R / 4), η z = 1 := by
      intro z hz
      apply hη_one
      rw [Metric.mem_ball] at hz
      rw [Metric.mem_closedBall]; linarith
    have h_eta_u_eq_u : ∀ z ∈ Metric.ball x₀ (3 * R / 4), η z * u z = u z := by
      intro z hz
      rw [h_eta_one_on_ball z hz, one_mul]
    have hdistxy_pow_nn : 0 ≤ (dist x y) ^ (1 - (d : ℝ) / p) :=
      Real.rpow_nonneg dist_nonneg _
    have h_each_n :
        ∀ n,
          ‖meanLebesgueOnBall (Metric.ball x ρ) (φ n) -
              meanLebesgueOnBall (Metric.ball y ρ) (φ n)‖ ≤
            2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
              (∑ i : Fin d,
                eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                  (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
      intro n
      have h_bound_x := smooth_avg_diff_pointwise_bound (d := d) hp h_dist_pos hρ_pos
        h_ball_x_sub_m (hφ_smooth n)
      have h_bound_y := smooth_avg_diff_pointwise_bound (d := d) hp h_dist_pos hρ_pos
        h_ball_y_sub_m (hφ_smooth n)
      have h_triangle :
          ‖(⨍ z in Metric.ball x ρ, φ n z ∂volume) -
              (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖ ≤
            ‖(⨍ z in Metric.ball x ρ, φ n z ∂volume) -
                (⨍ z in Metric.ball m (dist x y), φ n z ∂volume)‖ +
            ‖(⨍ z in Metric.ball m (dist x y), φ n z ∂volume) -
                (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖ := by
        have h_eq : (⨍ z in Metric.ball x ρ, φ n z ∂volume) -
            (⨍ z in Metric.ball y ρ, φ n z ∂volume) =
          ((⨍ z in Metric.ball x ρ, φ n z ∂volume) -
              (⨍ z in Metric.ball m (dist x y), φ n z ∂volume)) +
            ((⨍ z in Metric.ball m (dist x y), φ n z ∂volume) -
              (⨍ z in Metric.ball y ρ, φ n z ∂volume)) := by ring
        rw [h_eq]
        exact norm_add_le _ _
      have h_bound_y_sym :
          ‖(⨍ z in Metric.ball m (dist x y), φ n z ∂volume) -
              (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖ ≤
            smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
              (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball m (dist x y)))).toReal := by
        rw [show (⨍ z in Metric.ball m (dist x y), φ n z ∂volume) -
            (⨍ z in Metric.ball y ρ, φ n z ∂volume) =
          -(((⨍ z in Metric.ball y ρ, φ n z ∂volume) -
              (⨍ z in Metric.ball m (dist x y), φ n z ∂volume))) from by ring,
          norm_neg]
        exact h_bound_y
      have h_combined :
          ‖(⨍ z in Metric.ball x ρ, φ n z ∂volume) -
              (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖ ≤
            2 * (smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
              (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball m (dist x y)))).toReal) := by
        have h := h_triangle.trans (add_le_add h_bound_x h_bound_y_sym)
        linarith
      have hR'_pos : (0 : ℝ) < 3 * R / 4 := by linarith
      have h_phi_grad_memLp_R34_local :
          MemLp (fun z => ‖fderiv ℝ (φ n) z‖)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4))) :=
        smooth_grad_memLp_on_ball (d := d) hp_pos hR'_pos (hφ_smooth n)
      have h_eLp_le :
          (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball m (dist x y)))).toReal ≤
            (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
        refine ENNReal.toReal_mono ?_ ?_
        · exact h_phi_grad_memLp_R34_local.eLpNorm_ne_top
        · exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ h_ball_m_sub)
      have h_eLp_le_components :
          (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
            (∑ i : Fin d,
              eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
        have h_memLp := h_phi_grad_memLp_R34_local
        have h_le_enn :
            eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4))) ≤
              ∑ i : Fin d,
                eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                  (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball x₀ (3 * R / 4))) :=
          eLpNorm_fderiv_norm_le_sum_components (d := d) hp_one (hφ_smooth n)
        have h_sum_lt :
            (∑ i : Fin d,
              eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4)))) ≠ ⊤ := by
          refine ne_of_lt ?_
          refine ENNReal.sum_lt_top.mpr ?_
          intro i _
          have h_lt :
              eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4))) < ⊤ := by
            refine lt_of_le_of_lt
              (b := eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4)))) ?_
              (lt_of_le_of_ne le_top h_memLp.eLpNorm_ne_top)
            refine eLpNorm_mono ?_
            intro z
            have hbound_pt :
                ‖(fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)‖ ≤
                  ‖fderiv ℝ (φ n) z‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
              ContinuousLinearMap.le_opNorm _ _
            have hsingle_norm :
                ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
            rw [hsingle_norm, mul_one] at hbound_pt
            rw [Real.norm_of_nonneg (norm_nonneg _)]
            exact hbound_pt
          exact h_lt
        exact ENNReal.toReal_mono h_sum_lt h_le_enn
      have h_full_bound :
          ‖meanLebesgueOnBall (Metric.ball x ρ) (φ n) -
              meanLebesgueOnBall (Metric.ball y ρ) (φ n)‖ ≤
            2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
              (∑ i : Fin d,
                eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                  (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
        change ‖(⨍ z in Metric.ball x ρ, φ n z ∂volume) -
            (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖ ≤ _
        have h_eLp_chain :
            (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball m (dist x y)))).toReal ≤
              (∑ i : Fin d,
                eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                  (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal :=
          h_eLp_le.trans h_eLp_le_components
        have h_step1 :
            ‖(⨍ z in Metric.ball x ρ, φ n z ∂volume) -
                (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖ ≤
              2 * (smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
                (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball m (dist x y)))).toReal) := h_combined
        refine h_step1.trans ?_
        have h_const_factor : 0 ≤ smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) :=
          mul_nonneg hC₀_nn hdistxy_pow_nn
        calc 2 * (smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
              (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball m (dist x y)))).toReal)
            ≤ 2 * (smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
                (∑ i : Fin d,
                  eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                    (ENNReal.ofReal p)
                    (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
              exact mul_le_mul_of_nonneg_left h_eLp_chain h_const_factor
          _ = 2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
                (∑ i : Fin d,
                  eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                    (ENNReal.ofReal p)
                    (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by ring
      exact h_full_bound
    have h_phi_memLp : ∀ n, MemLp (φ n) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) := by
      intro n
      exact ((hφ_smooth n).continuous.memLp_of_hasCompactSupport
        (hφ_compact n)).restrict (Metric.ball x₀ R)
    have h_eta_u_memLp : MemLp (fun z => η z * u z) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) := hw'.memLp
    have h_phi_to_eta_u :
        Tendsto (fun n => eLpNorm (fun z => φ n z - η z * u z)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))) atTop (𝓝 0) := hφ_fun
    have h_phi_memLp_x : ∀ n, MemLp (φ n) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x ρ)) := fun n =>
      (h_phi_memLp n).mono_measure (Measure.restrict_mono_set _ (h_ball_x_sub_full.trans
        (by intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith)))
    have h_phi_memLp_y : ∀ n, MemLp (φ n) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball y ρ)) := fun n =>
      (h_phi_memLp n).mono_measure (Measure.restrict_mono_set _ (h_ball_y_sub_full.trans
        (by intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith)))
    have h_eta_u_memLp_x : MemLp (fun z => η z * u z) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x ρ)) :=
      h_eta_u_memLp.mono_measure (Measure.restrict_mono_set _ (h_ball_x_sub_full.trans
        (by intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith)))
    have h_eta_u_memLp_y : MemLp (fun z => η z * u z) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball y ρ)) :=
      h_eta_u_memLp.mono_measure (Measure.restrict_mono_set _ (h_ball_y_sub_full.trans
        (by intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith)))
    have h_diff_x : Tendsto
        (fun n => eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x ρ))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        h_phi_to_eta_u (Filter.Eventually.of_forall fun _ => zero_le _)
        (Filter.Eventually.of_forall ?_)
      intro n
      refine eLpNorm_mono_measure _ ?_
      exact Measure.restrict_mono_set _ (h_ball_x_sub_full.trans
        (by intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith))
    have h_diff_y : Tendsto
        (fun n => eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball y ρ))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        h_phi_to_eta_u (Filter.Eventually.of_forall fun _ => zero_le _)
        (Filter.Eventually.of_forall ?_)
      intro n
      refine eLpNorm_mono_measure _ ?_
      exact Measure.restrict_mono_set _ (h_ball_y_sub_full.trans
        (by intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith))
    have h_avg_x_to_eta_u : Tendsto
        (fun n => ⨍ z in Metric.ball x ρ, φ n z ∂volume) atTop
        (𝓝 (⨍ z in Metric.ball x ρ, η z * u z ∂volume)) := by
      exact tendsto_setAverage_of_eLpNorm_p_to_zero (d := d) hp_one hρ_pos h_eta_u_memLp_x
        h_phi_memLp_x h_diff_x
    have h_avg_y_to_eta_u : Tendsto
        (fun n => ⨍ z in Metric.ball y ρ, φ n z ∂volume) atTop
        (𝓝 (⨍ z in Metric.ball y ρ, η z * u z ∂volume)) := by
      exact tendsto_setAverage_of_eLpNorm_p_to_zero (d := d) hp_one hρ_pos h_eta_u_memLp_y
        h_phi_memLp_y h_diff_y
    have h_avg_x_eq : ⨍ z in Metric.ball x ρ, η z * u z ∂volume =
        ⨍ z in Metric.ball x ρ, u z ∂volume := by
      refine setAverage_congr_fun measurableSet_ball ?_
      refine ae_of_all _ (fun z hz => ?_)
      exact h_eta_u_eq_u z (h_ball_x_sub_full hz)
    have h_avg_y_eq : ⨍ z in Metric.ball y ρ, η z * u z ∂volume =
        ⨍ z in Metric.ball y ρ, u z ∂volume := by
      refine setAverage_congr_fun measurableSet_ball ?_
      refine ae_of_all _ (fun z hz => ?_)
      exact h_eta_u_eq_u z (h_ball_y_sub_full hz)
    rw [h_avg_x_eq] at h_avg_x_to_eta_u
    rw [h_avg_y_eq] at h_avg_y_to_eta_u
    have h_lhs_tendsto :
        Tendsto (fun n =>
          ‖(⨍ z in Metric.ball x ρ, φ n z ∂volume) -
              (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖) atTop
          (𝓝 ‖(⨍ z in Metric.ball x ρ, u z ∂volume) -
              (⨍ z in Metric.ball y ρ, u z ∂volume)‖) := by
      refine (h_avg_x_to_eta_u.sub h_avg_y_to_eta_u).norm
    have h_R34_pos : (0 : ℝ) < 3 * R / 4 := by linarith
    have h_ball_R34_sub : Metric.ball x₀ (3 * R / 4) ⊆ Metric.ball x₀ R := by
      intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith
    have h_R34_open : Metric.ball x₀ (3 * R / 4) = Metric.ball x₀ (3 * R / 4) := rfl
    have h_eta_eq_on : ∀ z ∈ Metric.ball x₀ (3 * R / 4), η z = 1 := h_eta_one_on_ball
    have h_R34_open' : IsOpen (Metric.ball x₀ (3 * R / 4)) := Metric.isOpen_ball
    have h_weakGrad_eq : ∀ i : Fin d, ∀ z ∈ Metric.ball x₀ (3 * R / 4),
        hw'.weakGrad z i = hu.weakGrad z i := by
      intro i z hz
      exact cutoffWitness_weakGrad_eq_on_open (d := d) hp_one.le hΩ_open hu hη_smooth
        hη_compact hη_range h_R34_open' h_eta_eq_on i z hz
    have h_eLpNorm_weakGrad_eq : ∀ i : Fin d,
        eLpNorm (fun z => hw'.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4))) =
        eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4))) := by
      intro i
      refine eLpNorm_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
      exact h_weakGrad_eq i z hz
    have h_per_comp_full : ∀ i : Fin d, Tendsto
        (fun n => eLpNorm
          (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1) - hw'.weakGrad z i)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))) atTop (𝓝 0) :=
      fun i => hφ_grad i
    have h_per_comp_R34 : ∀ i : Fin d, Tendsto
        (fun n => eLpNorm
          (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1) - hw'.weakGrad z i)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))) atTop (𝓝 0) := by
      intro i
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (h_per_comp_full i) (Filter.Eventually.of_forall fun _ => zero_le _)
        (Filter.Eventually.of_forall ?_)
      intro n
      exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ h_ball_R34_sub)
    have h_phi_grad_memLp_R34 : ∀ n, ∀ i : Fin d,
        MemLp (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4))) := by
      intro n i
      have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)) := by
        have hf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (φ n)) := by
          have h_fd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (φ n)) := by
            refine (hφ_smooth n).fderiv_right (m := (⊤ : ℕ∞)) ?_
            simp
          simpa using h_fd
        exact hf.clm_apply contDiff_const
      exact (h_smooth.continuous.memLp_of_hasCompactSupport
        (hφ_compact n |>.fderiv_apply (𝕜 := ℝ) _)).restrict (Metric.ball x₀ (3 * R / 4))
    have h_w_grad_memLp_R34 : ∀ i : Fin d,
        MemLp (fun z => hw'.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4))) := by
      intro i
      exact (hw'.weakGrad_component_memLp i).mono_measure
        (Measure.restrict_mono_set _ h_ball_R34_sub)
    have h_per_comp_toReal : ∀ i : Fin d,
        Tendsto (fun n =>
          (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop
          (𝓝 ((eLpNorm (fun z => hw'.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) := by
      intro i
      refine tendsto_eLpNorm_toReal_of_diff_tendsto_zero (d := d)
        (by rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp];
            exact ENNReal.ofReal_le_ofReal hp_one.le)
        (h_w_grad_memLp_R34 i) (fun n => h_phi_grad_memLp_R34 n i) (h_per_comp_R34 i)
    have h_per_comp_toReal_u : ∀ i : Fin d,
        Tendsto (fun n =>
          (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop
          (𝓝 ((eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) := by
      intro i
      have h := h_per_comp_toReal i
      rw [h_eLpNorm_weakGrad_eq i] at h
      exact h
    have h_sum_toReal_tendsto : Tendsto (fun n =>
        (∑ i : Fin d,
          eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop
        (𝓝 ((∑ i : Fin d,
          eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) := by
      have h_sum_real_eq : ∀ n,
          (∑ i : Fin d,
            eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
              (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal =
          ∑ i : Fin d,
            (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
              (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
        intro n
        refine ENNReal.toReal_sum ?_
        intro i _
        exact (h_phi_grad_memLp_R34 n i).eLpNorm_ne_top
      have h_target_eq :
          (∑ i : Fin d,
            eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal =
          ∑ i : Fin d,
            (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
        refine ENNReal.toReal_sum ?_
        intro i _
        have : MemLp (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4))) :=
          (hu.weakGrad_component_memLp i).mono_measure
            (Measure.restrict_mono_set _ h_ball_R34_sub)
        exact this.eLpNorm_ne_top
      rw [h_target_eq]
      refine (Filter.tendsto_congr h_sum_real_eq).mpr ?_
      exact tendsto_finset_sum _ (fun i _ => h_per_comp_toReal_u i)
    have h_n_bound :
        ∀ n,
          ‖(⨍ z in Metric.ball x ρ, φ n z ∂volume) -
              (⨍ z in Metric.ball y ρ, φ n z ∂volume)‖ ≤
            2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
              (∑ i : Fin d,
                eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                  (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
      intro n
      change ‖meanLebesgueOnBall (Metric.ball x ρ) (φ n) -
          meanLebesgueOnBall (Metric.ball y ρ) (φ n)‖ ≤ _
      exact h_each_n n
    have h_RHS_tendsto :
        Tendsto (fun n => 2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
            (∑ i : Fin d,
              eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
                (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop
          (𝓝 (2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
            (∑ i : Fin d,
              eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) :=
      h_sum_toReal_tendsto.const_mul _
    have h_lim_LHS_le_RHS :
        ‖(⨍ z in Metric.ball x ρ, u z ∂volume) -
            (⨍ z in Metric.ball y ρ, u z ∂volume)‖ ≤
          2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) *
            (∑ i : Fin d,
              eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal :=
      le_of_tendsto_of_tendsto h_lhs_tendsto h_RHS_tendsto
        (Filter.Eventually.of_forall h_n_bound)
    have h_sum_le :
        (∑ i : Fin d,
          eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
        (d : ℝ) *
          (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal := by
      have h_sum_real_eq :
          (∑ i : Fin d,
            eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal =
          ∑ i : Fin d,
            (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
        refine ENNReal.toReal_sum ?_
        intro i _
        have : MemLp (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4))) :=
          (hu.weakGrad_component_memLp i).mono_measure
            (Measure.restrict_mono_set _ h_ball_R34_sub)
        exact this.eLpNorm_ne_top
      rw [h_sum_real_eq]
      have h_each_le : ∀ i : Fin d,
          (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
          (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal := by
        intro i
        have h_lt : eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ :=
          hu.weakGrad_norm_memLp.eLpNorm_ne_top
        refine ENNReal.toReal_mono h_lt ?_
        have h_pt : ∀ z, |hu.weakGrad z i| ≤ ‖hu.weakGrad z‖ := by
          intro z
          have := EuclideanSpace.norm_eq (𝕜 := ℝ) (n := Fin d) (hu.weakGrad z)
          have h_sq : (hu.weakGrad z i)^2 ≤ ∑ j : Fin d, (hu.weakGrad z j)^2 := by
            have h_pos : 0 ≤ (hu.weakGrad z i)^2 := sq_nonneg _
            refine Finset.single_le_sum (f := fun j => (hu.weakGrad z j)^2)
              (fun j _ => sq_nonneg _) ?_
            exact Finset.mem_univ _
          have h_sqrt : |hu.weakGrad z i| ≤ Real.sqrt (∑ j : Fin d, (hu.weakGrad z j)^2) := by
            rw [show |hu.weakGrad z i| = Real.sqrt ((hu.weakGrad z i)^2) from
              (Real.sqrt_sq_eq_abs _).symm]
            exact Real.sqrt_le_sqrt h_sq
          rw [this]
          have h_norm_eq : Real.sqrt (∑ j : Fin d, (hu.weakGrad z j)^2) =
              Real.sqrt (∑ j : Fin d, ‖hu.weakGrad z j‖^2) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [show (hu.weakGrad z j)^2 = ‖hu.weakGrad z j‖^2 from by
              rw [Real.norm_eq_abs, sq_abs]]
          rw [← h_norm_eq]; exact h_sqrt
        have h_eLp_pt :
            eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4))) ≤
            eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ R)) := by
          have h_step1 :
              eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4))) ≤
              eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ (3 * R / 4))) := by
            refine eLpNorm_mono ?_
            intro z
            rw [Real.norm_of_nonneg (norm_nonneg _)]
            have hzi : |hu.weakGrad z i| ≤ ‖hu.weakGrad z‖ := h_pt z
            rw [show ‖hu.weakGrad z i‖ = |hu.weakGrad z i| from rfl]
            exact hzi
          refine h_step1.trans ?_
          exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ h_ball_R34_sub)
        exact h_eLp_pt
      calc ∑ i : Fin d,
            (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal
          ≤ ∑ _i : Fin d,
              (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal := by
            refine Finset.sum_le_sum ?_; intro i _; exact h_each_le i
        _ = (d : ℝ) *
              (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
    set N := (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R))).toReal with hN_def
    have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
    have h_const_factor_nn : 0 ≤ 2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) := by
      have h1 : (0 : ℝ) ≤ 2 * smoothHolderConst d p := by
        apply mul_nonneg (by norm_num) hC₀_nn
      exact mul_nonneg h1 hdistxy_pow_nn
    have h_lim_LHS_le_C_d_N :
        ‖(⨍ z in Metric.ball x ρ, u z ∂volume) -
            (⨍ z in Metric.ball y ρ, u z ∂volume)‖ ≤
          (2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p)) *
            ((d : ℝ) * N) := by
      refine h_lim_LHS_le_RHS.trans ?_
      have h_step :
          (2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p)) *
              (∑ i : Fin d,
                eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
            (2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p)) *
              ((d : ℝ) * N) :=
        mul_le_mul_of_nonneg_left h_sum_le h_const_factor_nn
      exact h_step
    have h_eq_form :
        2 * smoothHolderConst d p * (dist x y) ^ (1 - (d : ℝ) / p) * ((d : ℝ) * N) =
        (2 * (d : ℝ) * smoothHolderConst d p) * (dist x y) ^ (1 - (d : ℝ) / p) * N := by ring
    rw [h_eq_form] at h_lim_LHS_le_C_d_N
    have h_C_le : 2 * (d : ℝ) * smoothHolderConst d p ≤ C := by
      rw [hC_def]; linarith
    have h_step_final :
        (2 * (d : ℝ) * smoothHolderConst d p) * (dist x y) ^ (1 - (d : ℝ) / p) * N ≤
          C * (dist x y) ^ (1 - (d : ℝ) / p) * N := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right h_C_le hdistxy_pow_nn
      · exact hN_nn
    have h_final :
        ‖(⨍ z in Metric.ball x ρ, u z ∂volume) -
            (⨍ z in Metric.ball y ρ, u z ∂volume)‖ ≤
          C * (dist x y) ^ (1 - (d : ℝ) / p) * N :=
      h_lim_LHS_le_C_d_N.trans h_step_final
    change ‖(⨍ z in Metric.ball x (dist x y / 2), u z ∂volume) -
        (⨍ z in Metric.ball y (dist x y / 2), u z ∂volume)‖ ≤
      C * (dist x y) ^ (1 - (d : ℝ) / p) * N
    exact h_final

omit [NeZero d] in
private theorem exists_smooth_cutoff_inner
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      Set.range χ ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.closedBall x₀ (R / 4), χ x = 1) ∧
      tsupport χ ⊆ Metric.closedBall x₀ (R / 3) := by
  classical
  have hδ_pos : (0 : ℝ) < R / 24 := by linarith
  have hclosed : IsClosed (Metric.closedBall x₀ (R / 4)) := Metric.isClosed_closedBall
  have hopen_thick : IsOpen (Metric.thickening (R / 24) (Metric.closedBall x₀ (R / 4))) :=
    isOpen_thickening
  have hsub : Metric.closedBall x₀ (R / 4) ⊆
      Metric.thickening (R / 24) (Metric.closedBall x₀ (R / 4)) :=
    Metric.self_subset_thickening hδ_pos _
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d)))
      (s := Metric.thickening (R / 24) (Metric.closedBall x₀ (R / 4)))
      (t := Metric.closedBall x₀ (R / 4))
      hopen_thick hclosed hsub with
    ⟨χ, hχ_smooth, hχ_range, hχ_support, hχ_one_iff⟩
  have h_supp_in_closedBall :
      tsupport χ ⊆ Metric.closedBall x₀ (R / 3) := by
    have h_closed_R3 : IsClosed (Metric.closedBall x₀ (R / 3)) := Metric.isClosed_closedBall
    rw [tsupport, hχ_support]
    refine closure_minimal ?_ h_closed_R3
    intro y hy
    rw [Metric.mem_thickening_iff] at hy
    rcases hy with ⟨z, hz_mem, hyz⟩
    rw [Metric.mem_closedBall] at hz_mem ⊢
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ ≤ R / 24 + R / 4 := by
          have hyz_le : dist y z ≤ R / 24 := le_of_lt hyz
          linarith
      _ ≤ R / 3 := by linarith
  refine ⟨χ, contMDiff_iff_contDiff.mp hχ_smooth, ?_, hχ_range, ?_, h_supp_in_closedBall⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (R / 3)) ?_
    exact (subset_tsupport _).trans h_supp_in_closedBall
  · intro x hx
    exact (hχ_one_iff x).1 hx

omit [NeZero d] in
private lemma eLpNorm_diff_real_bound
    {p : ℝ} (hp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p)
    {μ : Measure E}
    {g : E → ℝ} {F : ℕ → E → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) μ)
    (hF : ∀ n, MemLp (F n) (ENNReal.ofReal p) μ) (n m : ℕ) :
    (eLpNorm (fun x => F n x - F m x) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (fun x => F n x - g x) (ENNReal.ofReal p) μ).toReal +
      (eLpNorm (fun x => F m x - g x) (ENNReal.ofReal p) μ).toReal := by
  have h_eq_fun : (fun x => F n x - F m x) =
      (fun x => (F n x - g x) - (F m x - g x)) := by
    funext x; ring
  rw [h_eq_fun]
  have h_diff_n : MemLp (fun x => F n x - g x) (ENNReal.ofReal p) μ := (hF n).sub hg
  have h_diff_m : MemLp (fun x => F m x - g x) (ENNReal.ofReal p) μ := (hF m).sub hg
  have h_le_enn :
      eLpNorm (fun x => (F n x - g x) - (F m x - g x)) (ENNReal.ofReal p) μ ≤
        eLpNorm (fun x => F n x - g x) (ENNReal.ofReal p) μ +
          eLpNorm (fun x => F m x - g x) (ENNReal.ofReal p) μ := by
    have h_sub_eq : (fun x => (F n x - g x) - (F m x - g x)) =
        (fun x => (F n x - g x) + (-(F m x - g x))) := by
      funext x; ring
    rw [h_sub_eq]
    have h_neg_diff_m : MemLp (fun x => -(F m x - g x)) (ENNReal.ofReal p) μ :=
      h_diff_m.neg
    refine (eLpNorm_add_le h_diff_n.aestronglyMeasurable
      h_neg_diff_m.aestronglyMeasurable hp_one).trans ?_
    have h_neg_eLp : eLpNorm (fun x => -(F m x - g x)) (ENNReal.ofReal p) μ =
        eLpNorm (fun x => F m x - g x) (ENNReal.ofReal p) μ := by
      have : (fun x => -(F m x - g x)) = -(fun x => F m x - g x) := by
        funext x; rfl
      rw [this, eLpNorm_neg]
    rw [h_neg_eLp]
  have h_finite_n : eLpNorm (fun x => F n x - g x) (ENNReal.ofReal p) μ ≠ ⊤ :=
    h_diff_n.eLpNorm_ne_top
  have h_finite_m : eLpNorm (fun x => F m x - g x) (ENNReal.ofReal p) μ ≠ ⊤ :=
    h_diff_m.eLpNorm_ne_top
  have h_sum_finite : eLpNorm (fun x => F n x - g x) (ENNReal.ofReal p) μ +
      eLpNorm (fun x => F m x - g x) (ENNReal.ofReal p) μ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h_finite_n, h_finite_m⟩
  rw [← ENNReal.toReal_add h_finite_n h_finite_m]
  exact ENNReal.toReal_mono h_sum_finite h_le_enn

omit [NeZero d] in
private lemma eLpNorm_grad_norm_le_sum_components_real
    {p : ℝ} (hp_one : 1 < p) {z : E} {r : ℝ}
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h_memLp : ∀ i : Fin d,
      MemLp (fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r))) :
    (eLpNorm (fun y => ‖fderiv ℝ f y‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball z r))).toReal ≤
      ∑ i : Fin d,
        (eLpNorm (fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball z r))).toReal := by
  have h_le_enn := eLpNorm_fderiv_norm_le_sum_components (d := d) hp_one hf (z := z) (r := r)
  have h_finite : ∀ i : Fin d,
      eLpNorm (fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1))
        (ENNReal.ofReal p) (volume.restrict (Metric.ball z r)) ≠ ⊤ := fun i =>
    (h_memLp i).eLpNorm_ne_top
  have h_sum_finite : (∑ i : Fin d,
      eLpNorm (fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1))
        (ENNReal.ofReal p) (volume.restrict (Metric.ball z r))) ≠ ⊤ :=
    ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ => lt_of_le_of_ne le_top (h_finite i))
  have h_real_le := ENNReal.toReal_mono h_sum_finite h_le_enn
  rw [ENNReal.toReal_sum (fun i _ => h_finite i)] at h_real_le
  exact h_real_le

private lemma eLpNorm_weakGrad_component_le_norm_real
    {p : ℝ} {x₀ : E} {R : ℝ}
    {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R))
    {S : Set E} (hS : S ⊆ Metric.ball x₀ R) (i : Fin d) :
    (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
      (volume.restrict S)).toReal ≤
      (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R))).toReal := by
  have h_finite : eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := hu.weakGrad_norm_memLp.eLpNorm_ne_top
  refine ENNReal.toReal_mono h_finite ?_
  have h_pt : ∀ z, |hu.weakGrad z i| ≤ ‖hu.weakGrad z‖ := by
    intro z
    have hh := EuclideanSpace.norm_eq (𝕜 := ℝ) (n := Fin d) (hu.weakGrad z)
    have h_sq : (hu.weakGrad z i)^2 ≤ ∑ j : Fin d, (hu.weakGrad z j)^2 :=
      Finset.single_le_sum (f := fun j => (hu.weakGrad z j)^2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ _)
    have h_sqrt : |hu.weakGrad z i| ≤ Real.sqrt (∑ j : Fin d, (hu.weakGrad z j)^2) := by
      rw [show |hu.weakGrad z i| = Real.sqrt ((hu.weakGrad z i)^2) from
        (Real.sqrt_sq_eq_abs _).symm]
      exact Real.sqrt_le_sqrt h_sq
    rw [hh]
    have h_norm_eq : Real.sqrt (∑ j : Fin d, (hu.weakGrad z j)^2) =
        Real.sqrt (∑ j : Fin d, ‖hu.weakGrad z j‖^2) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [show (hu.weakGrad z j)^2 = ‖hu.weakGrad z j‖^2 from by
        rw [Real.norm_eq_abs, sq_abs]]
    rw [← h_norm_eq]; exact h_sqrt
  have h_step1 :
      eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p) (volume.restrict S) ≤
      eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p) (volume.restrict S) := by
    refine eLpNorm_mono ?_
    intro z
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    rw [show ‖hu.weakGrad z i‖ = |hu.weakGrad z i| from rfl]
    exact h_pt z
  refine h_step1.trans ?_
  exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ hS)

set_option maxHeartbeats 4000000 in

private theorem morrey_representative_of_W1pWitness
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R)) :
    ∃ (ũ : EuclideanSpace ℝ (Fin d) → ℝ) (CHolder Csup : ℝ),
      Continuous ũ ∧ 0 ≤ CHolder ∧ 0 ≤ Csup ∧
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))), ũ z = u z) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4), ∀ y ∈ Metric.ball x₀ (R / 4),
        ‖ũ x - ũ y‖ ≤ CHolder * (dist x y) ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4), ‖ũ x‖ ≤ Csup * (
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal +
        (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal)) := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have hpp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one.le
  have h_exp_pos : 0 < 1 - (d : ℝ) / p := by
    rw [sub_pos, div_lt_one hp_pos]; exact hp
  obtain ⟨η, hη_smooth, hη_compact, hη_range, hη_one, hη_supp⟩ :=
    exists_smooth_cutoff_ball (d := d) (x₀ := x₀) hR
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_range, hχ_one, hχ_supp⟩ :=
    exists_smooth_cutoff_inner (d := d) (x₀ := x₀) hR
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hΩ_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  have h_R34_pos : (0 : ℝ) < 3 * R / 4 := by linarith
  have h_R38_pos : (0 : ℝ) < 3 * R / 8 := by linarith
  have h_R3_pos : (0 : ℝ) < R / 3 := by linarith
  have h_R4_pos : (0 : ℝ) < R / 4 := by linarith
  have h_ball_R34_sub_R : Metric.ball x₀ (3 * R / 4) ⊆ Metric.ball x₀ R := by
    intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith
  have h_closedBall_R3_sub_R38 :
      Metric.closedBall x₀ (R / 3) ⊆ Metric.ball x₀ (3 * R / 8) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have h_ball_R4_sub_closedBall_R4 :
      Metric.ball x₀ (R / 4) ⊆ Metric.closedBall x₀ (R / 4) := Metric.ball_subset_closedBall
  have h_closedBall_R4_sub_R3 :
      Metric.closedBall x₀ (R / 4) ⊆ Metric.closedBall x₀ (R / 3) := by
    intro z hz; rw [Metric.mem_closedBall] at hz ⊢; linarith
  have h_ball_R4_sub_R34 :
      Metric.ball x₀ (R / 4) ⊆ Metric.ball x₀ (3 * R / 4) := by
    intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith
  have h_ball_R4_sub_R : Metric.ball x₀ (R / 4) ⊆ Metric.ball x₀ R :=
    h_ball_R4_sub_R34.trans h_ball_R34_sub_R
  have h_closedBall_R3_sub_R34 :
      Metric.closedBall x₀ (R / 3) ⊆ Metric.ball x₀ (3 * R / 4) := by
    intro z hz; rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have h_x_in_R38 : ∀ x ∈ Metric.ball x₀ (R / 4), x ∈ Metric.ball x₀ (3 * R / 4 / 2) := by
    intro x hx
    have h_eq : (3 * R / 4) / 2 = 3 * R / 8 := by ring
    rw [h_eq]
    rw [Metric.mem_ball] at hx ⊢; linarith
  have hK_compact : IsCompact (Metric.closedBall x₀ (7 * R / 8)) :=
    isCompact_closedBall x₀ (7 * R / 8)
  have hKΩ : Metric.closedBall x₀ (7 * R / 8) ⊆ Metric.ball x₀ R := by
    intro z hz; rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_sub, hφ_fun, hφ_grad⟩ :=
    exists_smooth_cutoff_approx (d := d) hp_one hΩ_open hK_compact hKΩ hu
      hη_smooth hη_compact hη_range hη_supp
  let hw' := cutoffWitness (d := d) hp_one.le hΩ_open hu hη_smooth hη_compact hη_range
  have h_eta_one_on_R34 : ∀ z ∈ Metric.ball x₀ (3 * R / 4), η z = 1 := fun z hz => by
    apply hη_one
    rw [Metric.mem_ball] at hz; rw [Metric.mem_closedBall]; linarith
  have h_eta_u_eq_u_on_R34 : ∀ z ∈ Metric.ball x₀ (3 * R / 4), η z * u z = u z := fun z hz => by
    rw [h_eta_one_on_R34 z hz, one_mul]
  have h_chi_one_on_R4 : ∀ z ∈ Metric.ball x₀ (R / 4), χ z = 1 := fun z hz => by
    apply hχ_one
    rw [Metric.mem_ball] at hz; rw [Metric.mem_closedBall]; linarith
  obtain ⟨C_sup_smooth, hC_sup_nn, h_sup_bound⟩ :=
    smooth_morrey_sup_bound_uniform (d := d) hp h_R34_pos (x₀ := x₀)
  obtain ⟨C_pair_smooth, hC_pair_nn, h_pair_bound⟩ :=
    smooth_morrey_pair_bound_uniform (d := d) hp h_R34_pos (x₀ := x₀)
  have h_eta_u_memLp_R : MemLp (fun z => η z * u z) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) := hw'.memLp
  have h_phi_memLp_R : ∀ n, MemLp (φ n) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) := fun n =>
    ((hφ_smooth n).continuous.memLp_of_hasCompactSupport (hφ_compact n)).restrict _
  have h_phi_memLp_R34 : ∀ n, MemLp (φ n) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ (3 * R / 4))) := fun n =>
    (h_phi_memLp_R n).mono_measure (Measure.restrict_mono_set _ h_ball_R34_sub_R)
  have h_eta_u_memLp_R34 : MemLp (fun z => η z * u z) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ (3 * R / 4))) :=
    h_eta_u_memLp_R.mono_measure (Measure.restrict_mono_set _ h_ball_R34_sub_R)
  have h_phi_grad_memLp_R34 : ∀ n, ∀ i : Fin d,
      MemLp (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4))) := by
    intro n i
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)) := by
      have hf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (φ n)) := by
        have h_fd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (φ n)) := by
          refine (hφ_smooth n).fderiv_right (m := (⊤ : ℕ∞)) ?_; simp
        simpa using h_fd
      exact hf.clm_apply contDiff_const
    exact (h_smooth.continuous.memLp_of_hasCompactSupport
      (hφ_compact n |>.fderiv_apply (𝕜 := ℝ) _)).restrict _
  have h_w_grad_memLp_R34 : ∀ i : Fin d,
      MemLp (fun z => hw'.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4))) := fun i =>
    (hw'.weakGrad_component_memLp i).mono_measure
      (Measure.restrict_mono_set _ h_ball_R34_sub_R)
  have h_phi_to_eta_u_R34 : Tendsto
      (fun n => eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hφ_fun (Filter.Eventually.of_forall fun _ => zero_le _)
      (Filter.Eventually.of_forall ?_)
    intro n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ h_ball_R34_sub_R)
  have h_phi_to_eta_u_R34_real : Tendsto
      (fun n => (eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop (𝓝 0) := by
    have h_finite : ∀ n, eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4))) ≠ ⊤ := fun n =>
      ((h_phi_memLp_R34 n).sub h_eta_u_memLp_R34).eLpNorm_ne_top
    exact (ENNReal.tendsto_toReal_iff h_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤)).mpr
      (by simpa using h_phi_to_eta_u_R34)
  have h_phi_grad_to_w_R34 : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
        - hw'.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))) atTop (𝓝 0) := by
    intro i
    have h_full : Tendsto
        (fun n => eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
          - hw'.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))) atTop (𝓝 0) := hφ_grad i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_full
      (Filter.Eventually.of_forall fun _ => zero_le _)
      (Filter.Eventually.of_forall ?_)
    intro n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ h_ball_R34_sub_R)
  have h_phi_grad_to_w_R34_real : ∀ i : Fin d, Tendsto
      (fun n => (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
        - hw'.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop (𝓝 0) := by
    intro i
    have h_finite : ∀ n, eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
        - hw'.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4))) ≠ ⊤ := fun n =>
      ((h_phi_grad_memLp_R34 n i).sub (h_w_grad_memLp_R34 i)).eLpNorm_ne_top
    exact (ENNReal.tendsto_toReal_iff h_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤)).mpr
      (by simpa using h_phi_grad_to_w_R34 i)
  set a : ℕ → ℝ := fun n =>
    (eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
    ∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
      - hw'.weakGrad z i) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal with ha_def
  have ha_nn : ∀ n, 0 ≤ a n := fun n => by
    rw [ha_def]
    refine add_nonneg ENNReal.toReal_nonneg ?_
    exact Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have ha_to_zero : Tendsto a atTop (𝓝 0) := by
    have h_split : (0 : ℝ) = 0 + 0 := by ring
    rw [h_split, ha_def]
    have h_sum_to_zero : Tendsto (fun n => ∑ i : Fin d,
        (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
          - hw'.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop (𝓝 0) := by
      have h_zero_eq : (0 : ℝ) = ∑ _i : Fin d, (0 : ℝ) := by simp
      rw [h_zero_eq]
      exact tendsto_finset_sum _ (fun i _ => h_phi_grad_to_w_R34_real i)
    exact h_phi_to_eta_u_R34_real.add h_sum_to_zero
  have h_phi_diff_smooth : ∀ n m, ContDiff ℝ (⊤ : ℕ∞) (fun z => φ n z - φ m z) :=
    fun n m => (hφ_smooth n).sub (hφ_smooth m)
  have h_fderiv_sub : ∀ n m z, fderiv ℝ (fun z => φ n z - φ m z) z =
      fderiv ℝ (φ n) z - fderiv ℝ (φ m) z := fun n m z => by
    have h1 : DifferentiableAt ℝ (φ n) z := (hφ_smooth n).differentiable (by norm_cast) z
    have h2 : DifferentiableAt ℝ (φ m) z := (hφ_smooth m).differentiable (by norm_cast) z
    exact fderiv_sub h1 h2
  have h_sup_diff_via_a : ∀ n m, ∀ x ∈ Metric.ball x₀ (3 * R / 8),
      ‖φ n x - φ m x‖ ≤ C_sup_smooth * (a n + a m) := by
    intro n m x hx
    have h_smooth_diff : ContDiff ℝ (⊤ : ℕ∞) (fun z => φ n z - φ m z) := h_phi_diff_smooth n m
    have h_x_R8 : x ∈ Metric.ball x₀ (3 * R / 4 / 2) := by
      have : (3 * R / 4) / 2 = 3 * R / 8 := by ring
      rw [this]; exact hx
    have h_bound := h_sup_bound (u := fun z => φ n z - φ m z) h_smooth_diff x h_x_R8
    have h_lp_diff := eLpNorm_diff_real_bound (d := d) hpp_one h_eta_u_memLp_R34
      h_phi_memLp_R34 n m
    have h_grad_le_components_phi_nm :
        (eLpNorm (fun z => ‖fderiv ℝ (fun z => φ n z - φ m z) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
        ∑ i : Fin d,
          (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
      have h_le_enn :
          eLpNorm (fun z => ‖fderiv ℝ (fun z => φ n z - φ m z) z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4))) ≤
          ∑ i : Fin d,
            eLpNorm (fun z => (fderiv ℝ (fun z => φ n z - φ m z) z) (EuclideanSpace.single i 1))
              (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4))) :=
        eLpNorm_fderiv_norm_le_sum_components (d := d) hp_one h_smooth_diff
      have h_eq : ∀ i : Fin d,
          eLpNorm (fun z => (fderiv ℝ (fun z => φ n z - φ m z) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4))) =
          eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4))) := by
        intro i
        apply eLpNorm_congr_ae
        filter_upwards with z
        rw [h_fderiv_sub n m z]; rfl
      have h_finite : ∀ i : Fin d,
          eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4))) ≠ ⊤ := fun i =>
        ((h_phi_grad_memLp_R34 n i).sub (h_phi_grad_memLp_R34 m i)).eLpNorm_ne_top
      have h_sum_finite : (∑ i : Fin d,
          eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))) ≠ ⊤ :=
        ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ => lt_of_le_of_ne le_top (h_finite i))
      have h_sum_eq : (∑ i : Fin d,
          eLpNorm (fun z => (fderiv ℝ (fun z => φ n z - φ m z) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))) =
          (∑ i : Fin d,
          eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))) :=
        Finset.sum_congr rfl (fun i _ => h_eq i)
      have h_real_le := ENNReal.toReal_mono (h_sum_eq ▸ h_sum_finite) h_le_enn
      rw [h_sum_eq] at h_real_le
      rw [ENNReal.toReal_sum (fun i _ => h_finite i)] at h_real_le
      exact h_real_le
    have h_grad_le_sum_dev :
        ∑ i : Fin d,
          (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
        (∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
          - hw'.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) +
        (∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)
          - hw'.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := by
      have h_sum_split :
          (∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - hw'.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) +
          (∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)
            - hw'.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) =
          ∑ i : Fin d, ((eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1)
            - hw'.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
            (eLpNorm (fun z => (fderiv ℝ (φ m) z) (EuclideanSpace.single i 1)
              - hw'.weakGrad z i) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := by
        rw [← Finset.sum_add_distrib]
      rw [h_sum_split]
      refine Finset.sum_le_sum ?_
      intro i _
      exact eLpNorm_diff_real_bound (d := d) hpp_one (h_w_grad_memLp_R34 i)
        (fun n => h_phi_grad_memLp_R34 n i) n m
    have h_combined :
        (eLpNorm (fun z => φ n z - φ m z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        (eLpNorm (fun z => ‖fderiv ℝ (fun z => φ n z - φ m z) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤ a n + a m := by
      rw [ha_def]
      have h_grad_le := h_grad_le_components_phi_nm.trans h_grad_le_sum_dev
      linarith
    have h_target : ‖φ n x - φ m x‖ ≤ C_sup_smooth * (
        (eLpNorm (fun z => φ n z - φ m z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        (eLpNorm (fun z => ‖fderiv ℝ (fun z => φ n z - φ m z) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := by
      simpa using h_bound
    refine h_target.trans ?_
    exact mul_le_mul_of_nonneg_left h_combined hC_sup_nn
  have h_uniform_cauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ x ∈ Metric.closedBall x₀ (R / 3),
      |φ n x - φ m x| < ε := by
    intro ε hε
    have h_eps2_pos : 0 < ε / 2 := by linarith
    have h_C_a_to_zero : Tendsto (fun n => C_sup_smooth * a n) atTop (𝓝 0) := by
      have h_eq : (0 : ℝ) = C_sup_smooth * 0 := by ring
      rw [h_eq]
      exact ha_to_zero.const_mul _
    rw [Metric.tendsto_atTop] at h_C_a_to_zero
    obtain ⟨N, hN⟩ := h_C_a_to_zero (ε / 2) h_eps2_pos
    refine ⟨N, fun n hn m hm x hx => ?_⟩
    have h_x_R38 : x ∈ Metric.ball x₀ (3 * R / 8) := h_closedBall_R3_sub_R38 hx
    have h_ineq : ‖φ n x - φ m x‖ ≤ C_sup_smooth * (a n + a m) := h_sup_diff_via_a n m x h_x_R38
    have h_split : C_sup_smooth * (a n + a m) = C_sup_smooth * a n + C_sup_smooth * a m := by ring
    rw [h_split] at h_ineq
    have h_C_an : |C_sup_smooth * a n| < ε / 2 := by
      have hh := hN n hn
      rw [Real.dist_eq, sub_zero] at hh
      exact hh
    have h_C_am : |C_sup_smooth * a m| < ε / 2 := by
      have hh := hN m hm
      rw [Real.dist_eq, sub_zero] at hh
      exact hh
    have h_Can_nn : 0 ≤ C_sup_smooth * a n := mul_nonneg hC_sup_nn (ha_nn n)
    have h_Cam_nn : 0 ≤ C_sup_smooth * a m := mul_nonneg hC_sup_nn (ha_nn m)
    rw [abs_of_nonneg h_Can_nn] at h_C_an
    rw [abs_of_nonneg h_Cam_nn] at h_C_am
    have h_total : C_sup_smooth * a n + C_sup_smooth * a m < ε := by linarith
    have h_norm_eq : ‖φ n x - φ m x‖ = |φ n x - φ m x| := rfl
    rw [← h_norm_eq]
    exact h_ineq.trans_lt h_total
  obtain ⟨h_g_cauchy_pointwise, hg_cont, hg_zero_outside⟩ :
      (∀ x : EuclideanSpace ℝ (Fin d), CauchySeq (fun n => χ x * φ n x)) ×'
      (∀ n, Continuous (fun x => χ x * φ n x)) ×'
      (∀ n, ∀ x ∉ Metric.closedBall x₀ (R / 3), χ x * φ n x = 0) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := h_uniform_cauchy ε hε
      refine ⟨N, fun n hn m hm => ?_⟩
      rw [Real.dist_eq]
      by_cases hx : x ∈ Metric.closedBall x₀ (R / 3)
      · have h_factor : χ x * φ n x - χ x * φ m x = χ x * (φ n x - φ m x) := by ring
        rw [h_factor, abs_mul]
        have h_phi_lt : |φ n x - φ m x| < ε := hN n hn m hm x hx
        have h_chi_le_one : |χ x| ≤ 1 := cutoff_norm_le_one (d := d) (η := χ) hχ_range x
        calc |χ x| * |φ n x - φ m x|
            ≤ 1 * |φ n x - φ m x| :=
              mul_le_mul_of_nonneg_right h_chi_le_one (abs_nonneg _)
          _ = |φ n x - φ m x| := by ring
          _ < ε := h_phi_lt
      · have hx_not_supp : x ∉ tsupport χ := fun h => hx (hχ_supp h)
        have hχ_zero : χ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_supp
        rw [hχ_zero, zero_mul, zero_mul, sub_zero, abs_zero]
        exact hε
    · intro n
      exact hχ_cont.mul (hφ_smooth n).continuous
    · intro n x hx
      have hx_not_supp : x ∉ tsupport χ := fun h => hx (hχ_supp h)
      have hχ_zero : χ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_supp
      rw [hχ_zero, zero_mul]
  have h_g_to_ũ_pre :
      ∀ x : EuclideanSpace ℝ (Fin d),
        Tendsto (fun n => χ x * φ n x) atTop (𝓝 (limUnder atTop (fun n => χ x * φ n x))) := by
    intro x
    exact (h_g_cauchy_pointwise x).tendsto_limUnder
  have h_g_uniform_cauchy :
      UniformCauchySeqOn (fun n x => χ x * φ n x) atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := h_uniform_cauchy ε hε
    refine ⟨N, fun n hn m hm x _ => ?_⟩
    rw [Real.dist_eq]
    by_cases hx : x ∈ Metric.closedBall x₀ (R / 3)
    · have h_factor : χ x * φ n x - χ x * φ m x = χ x * (φ n x - φ m x) := by ring
      rw [h_factor, abs_mul]
      have h_phi_lt : |φ n x - φ m x| < ε := hN n hn m hm x hx
      have h_chi_le_one : |χ x| ≤ 1 := cutoff_norm_le_one (d := d) (η := χ) hχ_range x
      calc |χ x| * |φ n x - φ m x|
          ≤ 1 * |φ n x - φ m x| :=
            mul_le_mul_of_nonneg_right h_chi_le_one (abs_nonneg _)
        _ = |φ n x - φ m x| := by ring
        _ < ε := h_phi_lt
    · rw [hg_zero_outside n x hx, hg_zero_outside m x hx, sub_zero, abs_zero]
      exact hε
  have h_g_to_ũ_uniform : TendstoUniformlyOn (fun n x => χ x * φ n x)
      (fun x => limUnder atTop (fun n => χ x * φ n x)) atTop Set.univ :=
    h_g_uniform_cauchy.tendstoUniformlyOn_of_tendsto (fun x _ => h_g_to_ũ_pre x)
  have h_g_to_ũ_uniformly : TendstoUniformly (fun n x => χ x * φ n x)
      (fun x => limUnder atTop (fun n => χ x * φ n x)) atTop := by
    rw [← tendstoUniformlyOn_univ] at *
    exact h_g_to_ũ_uniform
  set ũ : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x => limUnder atTop (fun n => χ x * φ n x) with hũ_def
  have hũ_cont : Continuous ũ :=
    h_g_to_ũ_uniformly.continuous (Filter.Frequently.of_forall hg_cont)
  have h_phi_to_ũ_R4 : ∀ x ∈ Metric.ball x₀ (R / 4),
      Tendsto (fun n => φ n x) atTop
        (𝓝 (limUnder atTop (fun n => χ x * φ n x))) := by
    intro x hx
    have h_g_eq : ∀ n, χ x * φ n x = φ n x := fun n => by
      rw [h_chi_one_on_R4 x hx, one_mul]
    have h_pt := h_g_to_ũ_pre x
    have h_fun_eq : (fun n => χ x * φ n x) = (fun n => φ n x) := funext h_g_eq
    rw [h_fun_eq] at h_pt
    have h_lim_eq : limUnder atTop (fun n => χ x * φ n x) =
        limUnder atTop (fun n => φ n x) := by
      congr 1
    rw [h_lim_eq]
    exact h_pt
  have h_ae_eq : ∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))),
      limUnder atTop (fun n => χ z * φ n z) = u z := by
    have h_phi_to_eta_u_R4 : Tendsto
        (fun n => eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (R / 4)))) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        h_phi_to_eta_u_R34 (Filter.Eventually.of_forall fun _ => zero_le _)
        (Filter.Eventually.of_forall ?_)
      intro n
      exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ h_ball_R4_sub_R34)
    have h_eta_u_eq_u_ae_R4 : (fun z => η z * u z) =ᵐ[volume.restrict (Metric.ball x₀ (R / 4))]
        u := by
      filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
      exact h_eta_u_eq_u_on_R34 z (h_ball_R4_sub_R34 hz)
    have h_phi_to_u_R4 : Tendsto
        (fun n => eLpNorm (fun z => φ n z - u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (R / 4)))) atTop (𝓝 0) := by
      have h_eq : ∀ n, eLpNorm (fun z => φ n z - u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (R / 4))) =
          eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (R / 4))) := fun n => by
        refine eLpNorm_congr_ae ?_
        filter_upwards [h_eta_u_eq_u_ae_R4] with z hz
        rw [hz]
      rw [show (fun n => eLpNorm (fun z => φ n z - u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (R / 4)))) =
          fun n => eLpNorm (fun z => φ n z - η z * u z) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (R / 4))) from funext h_eq]
      exact h_phi_to_eta_u_R4
    have h_phi_memLp_R4 : ∀ n, MemLp (φ n) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (R / 4))) := fun n =>
      (h_phi_memLp_R34 n).mono_measure (Measure.restrict_mono_set _ h_ball_R4_sub_R34)
    have h_u_memLp_R4 : MemLp u (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (R / 4))) := by
      have h_eta_u_R4 : MemLp (fun z => η z * u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (R / 4))) :=
        h_eta_u_memLp_R34.mono_measure (Measure.restrict_mono_set _ h_ball_R4_sub_R34)
      exact h_eta_u_R4.ae_eq h_eta_u_eq_u_ae_R4
    have h_p_ne_zero : (ENNReal.ofReal p) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hp_pos).ne'
    have h_phi_to_u_R4_alt : Tendsto (fun n => eLpNorm (φ n - u) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (R / 4)))) atTop (𝓝 0) := by
      have h_eq_fun : ∀ n, (φ n - u) = (fun z => φ n z - u z) := fun n => by funext z; rfl
      rw [show (fun n => eLpNorm (φ n - u) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (R / 4)))) =
          fun n => eLpNorm (fun z => φ n z - u z) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (R / 4))) from
        funext (fun n => eLpNorm_congr_ae (Filter.Eventually.of_forall fun z => by simp))]
      exact h_phi_to_u_R4
    have h_in_measure : TendstoInMeasure (volume.restrict (Metric.ball x₀ (R / 4)))
        φ atTop u :=
      tendstoInMeasure_of_tendsto_eLpNorm h_p_ne_zero
        (fun n => (h_phi_memLp_R4 n).aestronglyMeasurable)
        h_u_memLp_R4.aestronglyMeasurable h_phi_to_u_R4_alt
    obtain ⟨ns, hns_strict, h_ae_phi⟩ := h_in_measure.exists_seq_tendsto_ae
    have h_subseq_to_ũ : ∀ x ∈ Metric.ball x₀ (R / 4),
        Tendsto (fun i => φ (ns i) x) atTop
          (𝓝 (limUnder atTop (fun n => χ x * φ n x))) := fun x hx =>
      (h_phi_to_ũ_R4 x hx).comp hns_strict.tendsto_atTop
    filter_upwards [h_ae_phi, self_mem_ae_restrict measurableSet_ball] with z h_to_u h_z_in
    exact tendsto_nhds_unique (h_subseq_to_ũ z h_z_in) h_to_u
  have h_R34_open : IsOpen (Metric.ball x₀ (3 * R / 4)) := Metric.isOpen_ball
  have h_weakGrad_eq_R34 : ∀ i : Fin d, ∀ z ∈ Metric.ball x₀ (3 * R / 4),
      hw'.weakGrad z i = hu.weakGrad z i := fun i z hz =>
    cutoffWitness_weakGrad_eq_on_open (d := d) hp_one.le hΩ_open hu hη_smooth
      hη_compact hη_range h_R34_open h_eta_one_on_R34 i z hz
  have h_eLpNorm_weakGrad_eq_R34 : ∀ i : Fin d,
      eLpNorm (fun z => hw'.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4))) =
      eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4))) := fun i => by
    refine eLpNorm_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    exact h_weakGrad_eq_R34 i z hz
  set N : ℝ := (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have h_sum_weakGrad_le_dN :
      ∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤ (d : ℝ) * N := by
    calc ∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal
        ≤ ∑ _i : Fin d, N :=
          Finset.sum_le_sum
            (fun i _ => eLpNorm_weakGrad_component_le_norm_real (d := d) hu h_ball_R34_sub_R i)
      _ = (d : ℝ) * N := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_phi_grad_real_to_w_u : ∀ i : Fin d, Tendsto
      (fun n => (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
        (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop
      (𝓝 ((eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) := by
    intro i
    have h_to_w := tendsto_eLpNorm_toReal_of_diff_tendsto_zero (d := d) hpp_one
      (h_w_grad_memLp_R34 i) (fun n => h_phi_grad_memLp_R34 n i) (h_phi_grad_to_w_R34 i)
    rw [h_eLpNorm_weakGrad_eq_R34 i] at h_to_w
    exact h_to_w
  have h_sum_grad_real_to_w_u : Tendsto
      (fun n => ∑ i : Fin d,
        (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop
      (𝓝 (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) :=
    tendsto_finset_sum _ (fun i _ => h_phi_grad_real_to_w_u i)
  have h_grad_norm_le_sum_components : ∀ n,
      (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
      ∑ i : Fin d,
        (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := fun n =>
    eLpNorm_grad_norm_le_sum_components_real (d := d) hp_one (hφ_smooth n)
      (h_phi_grad_memLp_R34 n)
  have h_holder_phi_n : ∀ n, ∀ x ∈ Metric.ball x₀ (R / 4), ∀ y ∈ Metric.ball x₀ (R / 4),
      ‖φ n x - φ n y‖ ≤ C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) *
        (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := fun n x hx y hy =>
    h_pair_bound (u := φ n) (hφ_smooth n) (h_x_in_R38 x hx) (h_x_in_R38 y hy)
  have h_holder_ũ_pre : ∀ x ∈ Metric.ball x₀ (R / 4), ∀ y ∈ Metric.ball x₀ (R / 4),
      ‖ũ x - ũ y‖ ≤ C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) *
        (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := by
    intro x hx y hy
    have h_dxy_pow_nn : 0 ≤ (dist x y) ^ (1 - (d : ℝ) / p) :=
      Real.rpow_nonneg dist_nonneg _
    have h_factor_nn : 0 ≤ C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) :=
      mul_nonneg hC_pair_nn h_dxy_pow_nn
    have h_lhs_to : Tendsto (fun n => ‖φ n x - φ n y‖) atTop (𝓝 ‖ũ x - ũ y‖) :=
      ((h_phi_to_ũ_R4 x hx).sub (h_phi_to_ũ_R4 y hy)).norm
    have h_n_bound_summed : ∀ n,
        ‖φ n x - φ n y‖ ≤ C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) *
          (∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := by
      intro n
      have h1 := h_holder_phi_n n x hx y hy
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_left (h_grad_norm_le_sum_components n) h_factor_nn
    have h_rhs_to : Tendsto
        (fun n => C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) *
          (∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) atTop
        (𝓝 (C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) *
          (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal))) :=
      h_sum_grad_real_to_w_u.const_mul _
    exact le_of_tendsto_of_tendsto h_lhs_to h_rhs_to
      (Filter.Eventually.of_forall h_n_bound_summed)
  have h_holder_ũ : ∀ x ∈ Metric.ball x₀ (R / 4), ∀ y ∈ Metric.ball x₀ (R / 4),
      ‖ũ x - ũ y‖ ≤ ((d : ℝ) * C_pair_smooth) * (dist x y) ^ (1 - (d : ℝ) / p) * N := by
    intro x hx y hy
    have h := h_holder_ũ_pre x hx y hy
    refine h.trans ?_
    have h_dxy_pow_nn : 0 ≤ (dist x y) ^ (1 - (d : ℝ) / p) :=
      Real.rpow_nonneg dist_nonneg _
    have h_factor_nn : 0 ≤ C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) :=
      mul_nonneg hC_pair_nn h_dxy_pow_nn
    calc C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) *
          (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)
        ≤ C_pair_smooth * (dist x y) ^ (1 - (d : ℝ) / p) * ((d : ℝ) * N) :=
          mul_le_mul_of_nonneg_left h_sum_weakGrad_le_dN h_factor_nn
      _ = ((d : ℝ) * C_pair_smooth) * (dist x y) ^ (1 - (d : ℝ) / p) * N := by ring
  have h_sup_phi_n : ∀ n, ∀ x ∈ Metric.ball x₀ (R / 4),
      ‖φ n x‖ ≤ C_sup_smooth * (
        (eLpNorm (φ n) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := fun n x hx =>
    h_sup_bound (u := φ n) (hφ_smooth n) x (h_x_in_R38 x hx)
  have h_phi_norm_to_eta_u : Tendsto
      (fun n => (eLpNorm (φ n) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) atTop
      (𝓝 ((eLpNorm (fun z => η z * u z) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) :=
    tendsto_eLpNorm_toReal_of_diff_tendsto_zero (d := d) hpp_one
      h_eta_u_memLp_R34 h_phi_memLp_R34 h_phi_to_eta_u_R34
  have h_eta_u_eq_u_eLp : eLpNorm (fun z => η z * u z) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ (3 * R / 4))) =
      eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4))) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    exact h_eta_u_eq_u_on_R34 z hz
  set Nu : ℝ := (eLpNorm u (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hNu_def
  have hNu_nn : 0 ≤ Nu := ENNReal.toReal_nonneg
  have h_u_R34_le_R : (eLpNorm u (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤ Nu := by
    have h_lt : eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ :=
      hu.memLp.eLpNorm_ne_top
    refine ENNReal.toReal_mono h_lt ?_
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ h_ball_R34_sub_R)
  have h_sup_phi_n_via_components : ∀ n, ∀ x ∈ Metric.ball x₀ (R / 4),
      ‖φ n x‖ ≤ C_sup_smooth * (
        (eLpNorm (φ n) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        ∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := by
    intro n x hx
    refine (h_sup_phi_n n x hx).trans ?_
    have h_inner :
        (eLpNorm (φ n) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        (eLpNorm (fun z => ‖fderiv ℝ (φ n) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal ≤
        (eLpNorm (φ n) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        ∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal := by
      have := h_grad_norm_le_sum_components n
      linarith
    exact mul_le_mul_of_nonneg_left h_inner hC_sup_nn
  have h_sup_ũ_pre : ∀ x ∈ Metric.ball x₀ (R / 4),
      ‖ũ x‖ ≤ C_sup_smooth * (
        (eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) := by
    intro x hx
    have h_lhs_to : Tendsto (fun n => ‖φ n x‖) atTop (𝓝 ‖ũ x‖) :=
      (h_phi_to_ũ_R4 x hx).norm
    have h_rhs_to : Tendsto
        (fun n => C_sup_smooth * (
          (eLpNorm (φ n) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
          ∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) atTop
        (𝓝 (C_sup_smooth * (
          (eLpNorm (fun z => η z * u z) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
          (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)))) :=
      (h_phi_norm_to_eta_u.add h_sum_grad_real_to_w_u).const_mul _
    have h_n_bound : ∀ n, ‖φ n x‖ ≤ C_sup_smooth * (
        (eLpNorm (φ n) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        ∑ i : Fin d, (eLpNorm (fun z => (fderiv ℝ (φ n) z) (EuclideanSpace.single i 1))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) := fun n =>
      h_sup_phi_n_via_components n x hx
    have h_limit_le := le_of_tendsto_of_tendsto h_lhs_to h_rhs_to
      (Filter.Eventually.of_forall h_n_bound)
    rw [h_eta_u_eq_u_eLp] at h_limit_le
    exact h_limit_le
  have h_sup_ũ : ∀ x ∈ Metric.ball x₀ (R / 4),
      ‖ũ x‖ ≤ ((d : ℝ) + 1) * C_sup_smooth * (Nu + N) := by
    intro x hx
    refine (h_sup_ũ_pre x hx).trans ?_
    have h_inner_le :
        (eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
        (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal) ≤
        Nu + (d : ℝ) * N := by
      have h_sum_le := h_sum_weakGrad_le_dN
      linarith
    have h_factor_le :
        Nu + (d : ℝ) * N ≤ ((d : ℝ) + 1) * (Nu + N) := by
      have h_d_nn : (0 : ℝ) ≤ d := hd_pos.le
      nlinarith [hN_nn, hNu_nn]
    have h_C_left :
        C_sup_smooth * ((eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal +
          (∑ i : Fin d, (eLpNorm (fun z => hu.weakGrad z i) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ (3 * R / 4)))).toReal)) ≤
        C_sup_smooth * (Nu + (d : ℝ) * N) :=
      mul_le_mul_of_nonneg_left h_inner_le hC_sup_nn
    have h_C_right : C_sup_smooth * (Nu + (d : ℝ) * N) ≤
        ((d : ℝ) + 1) * C_sup_smooth * (Nu + N) := by
      have h_C_factor_nn : 0 ≤ ((d : ℝ) + 1) * C_sup_smooth :=
        mul_nonneg (by linarith) hC_sup_nn
      have h_inner_chain : C_sup_smooth * (Nu + (d : ℝ) * N) ≤
          C_sup_smooth * ((d + 1) * (Nu + N)) :=
        mul_le_mul_of_nonneg_left h_factor_le hC_sup_nn
      linarith
    exact h_C_left.trans h_C_right
  refine ⟨ũ, (d : ℝ) * C_pair_smooth, ((d : ℝ) + 1) * C_sup_smooth, hũ_cont, ?_, ?_, h_ae_eq, ?_, ?_⟩
  · exact mul_nonneg hd_pos.le hC_pair_nn
  · exact mul_nonneg (by linarith) hC_sup_nn
  · intro x hx y hy
    exact h_holder_ũ x hx y hy
  · intro x hx
    exact h_sup_ũ x hx

theorem morrey_holder_representative
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R)) :
    ∃ (ũ : EuclideanSpace ℝ (Fin d) → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))), ũ z = u z) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4), ∀ y ∈ Metric.ball x₀ (R / 4),
        ‖ũ x - ũ y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal) := by
  obtain ⟨ũ, CHolder, _, hũ_cont, hC_nn, _, h_ae, h_holder, _⟩ :=
    morrey_representative_of_W1pWitness (d := d) hp hR hu
  exact ⟨ũ, CHolder, hũ_cont, hC_nn, h_ae, h_holder⟩

theorem morrey_sup_bound
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) u (Metric.ball x₀ R)) :
    ∃ (ũ : EuclideanSpace ℝ (Fin d) → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ z ∂(volume.restrict (Metric.ball x₀ (R / 4))), ũ z = u z) ∧
      (∀ x ∈ Metric.ball x₀ (R / 4), ‖ũ x‖ ≤ C * (
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) +
         eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
           (volume.restrict (Metric.ball x₀ R))).toReal)) := by
  obtain ⟨ũ, _, Csup, hũ_cont, _, hC_nn, h_ae, _, h_sup⟩ :=
    morrey_representative_of_W1pWitness (d := d) hp hR hu
  refine ⟨ũ, Csup, hũ_cont, hC_nn, h_ae, ?_⟩
  intro x hx
  have h_u_finite : eLpNorm u (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := hu.memLp.eLpNorm_ne_top
  have h_grad_finite : eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := hu.weakGrad_norm_memLp.eLpNorm_ne_top
  have h_sum_eq : (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) +
        eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal =
      (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal +
      (eLpNorm (fun z => ‖hu.weakGrad z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R))).toReal :=
    ENNReal.toReal_add h_u_finite h_grad_finite
  rw [h_sum_eq]
  exact h_sup x hx

end EuclideanMorrey
end Sobolev
end Analysis
end DifferentialGeometry
