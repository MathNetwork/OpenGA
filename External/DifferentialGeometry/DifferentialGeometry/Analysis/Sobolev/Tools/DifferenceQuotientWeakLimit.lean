import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothTestPairing
import DifferentialGeometry.Analysis.Sobolev.Tools.WeakPartialLimit
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space


noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma smoothCS_zero_mem :
    ContDiff ℝ (⊤ : ℕ∞) (0 : E → ℝ) ∧ HasCompactSupport (0 : E → ℝ) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩

omit [NeZero d] in
private lemma smoothCS_add_mem
    {φ ψ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (φ + ψ) ∧ HasCompactSupport (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

omit [NeZero d] in
private lemma smoothCS_smul_mem
    (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (c • φ) ∧ HasCompactSupport (c • φ) :=
  ⟨contDiff_const.smul hφ.1, hφ.2.smul_left⟩

def smoothCSSubmodule : Submodule ℝ (E → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  add_mem' := fun hφ hψ => smoothCS_add_mem hφ hψ
  zero_mem' := smoothCS_zero_mem
  smul_mem' := fun c _ hφ => smoothCS_smul_mem c hφ

omit [NeZero d] in
@[simp] lemma mem_smoothCSSubmodule {φ : E → ℝ} :
    φ ∈ (smoothCSSubmodule (d := d)) ↔
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ := Iff.rfl

omit [NeZero d] in
private lemma smoothCSSubmodule_add_coe
    (φ ψ : (smoothCSSubmodule (d := d))) :
    ((φ + ψ : (smoothCSSubmodule (d := d))) : E → ℝ) = φ.1 + ψ.1 := rfl

omit [NeZero d] in
private lemma smoothCSSubmodule_smul_coe
    (c : ℝ) (φ : (smoothCSSubmodule (d := d))) :
    ((c • φ : (smoothCSSubmodule (d := d))) : E → ℝ) = c • φ.1 := rfl

omit [NeZero d] in

private lemma memLp_two_of_smoothCS
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ) :
    MemLp φ 2 (volume : Measure E) :=
  hφ.continuous.memLp_of_hasCompactSupport hφ_supp

def smoothCSToLp :
    smoothCSSubmodule (d := d) →ₗ[ℝ] Lp ℝ 2 (volume : Measure E) where
  toFun φ :=
    (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1
  map_add' φ ψ := by
    refine Lp.ext ?_
    have h1 : ⇑((memLp_two_of_smoothCS (d := d)
        (φ + ψ).2.1 (φ + ψ).2.2).toLp ((φ + ψ).1)) =ᵐ[(volume : Measure E)]
          (φ + ψ).1 :=
      MemLp.coeFn_toLp _
    have h2 : ⇑((memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1 +
        (memLp_two_of_smoothCS (d := d) ψ.2.1 ψ.2.2).toLp ψ.1) =ᵐ[
          (volume : Measure E)]
          ⇑((memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1) +
            ⇑((memLp_two_of_smoothCS (d := d) ψ.2.1 ψ.2.2).toLp ψ.1) :=
      Lp.coeFn_add _ _
    have h3 : ⇑((memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1) =ᵐ[
          (volume : Measure E)] φ.1 :=
      MemLp.coeFn_toLp _
    have h4 : ⇑((memLp_two_of_smoothCS (d := d) ψ.2.1 ψ.2.2).toLp ψ.1) =ᵐ[
          (volume : Measure E)] ψ.1 :=
      MemLp.coeFn_toLp _
    have h_add_coe : ((φ + ψ : (smoothCSSubmodule (d := d))).1 : E → ℝ) =
        φ.1 + ψ.1 := rfl
    refine h1.trans ?_
    refine (h2.trans ?_).symm
    rw [h_add_coe]
    filter_upwards [h3, h4] with x hx3 hx4
    simp only [Pi.add_apply]
    rw [hx3, hx4]
  map_smul' c φ := by
    refine Lp.ext ?_
    have h1 : ⇑((memLp_two_of_smoothCS (d := d) (c • φ).2.1 (c • φ).2.2).toLp
          ((c • φ).1)) =ᵐ[(volume : Measure E)] (c • φ).1 :=
      MemLp.coeFn_toLp _
    have h2 : ⇑(c • (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1)
        =ᵐ[(volume : Measure E)]
          c • ⇑((memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1) :=
      Lp.coeFn_smul c _
    have h3 : ⇑((memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1) =ᵐ[
          (volume : Measure E)] φ.1 :=
      MemLp.coeFn_toLp _
    have h_smul_coe : ((c • φ : (smoothCSSubmodule (d := d))).1 : E → ℝ) =
        c • φ.1 := rfl
    refine h1.trans ?_
    rw [h_smul_coe]
    have h_id_eq :
        (RingHom.id ℝ) c • (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1
          = c • (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1 := rfl
    rw [show ⇑((RingHom.id ℝ) c •
        (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1) =
        ⇑(c • (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1) from by
      rw [h_id_eq]]
    filter_upwards [h2, h3] with x hx2 hx3
    rw [hx2, Pi.smul_apply, Pi.smul_apply, hx3]

omit [NeZero d] in
@[simp] lemma smoothCSToLp_apply (φ : smoothCSSubmodule (d := d)) :
    smoothCSToLp (d := d) φ =
      (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1 := rfl

omit [NeZero d] in
lemma denseRange_smoothCSToLp :
    DenseRange (smoothCSToLp (d := d)) := by
  intro f
  have h_dense :
      Dense {f : Lp ℝ 2 (volume : Measure E) | ∃ (g : E → ℝ),
        f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} := by
    have h0 := Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure E))
      (F := ℝ) (p := 2) (by norm_num)
    convert h0 using 1
  rw [Metric.mem_closure_iff]
  intro ε hε
  rw [Metric.dense_iff] at h_dense
  obtain ⟨h, hh_mem, ⟨g, hgeq, hg_cs, hg_smooth⟩⟩ := h_dense f ε hε
  refine ⟨smoothCSToLp (d := d) ⟨g, hg_smooth, hg_cs⟩, ?_, ?_⟩
  · exact ⟨⟨g, hg_smooth, hg_cs⟩, rfl⟩
  · have h_eq_h :
        smoothCSToLp (d := d) ⟨g, hg_smooth, hg_cs⟩ = h := by
      simp only [smoothCSToLp_apply]
      apply Lp.ext
      have h1 := MemLp.coeFn_toLp
        (memLp_two_of_smoothCS (d := d) hg_smooth hg_cs)
      exact h1.trans hgeq.symm
    rw [h_eq_h]
    rw [dist_comm]
    exact mem_ball.mp hh_mem

omit [NeZero d] in

private lemma integrable_w_partial_phi_univ
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) (k : Fin d) :
    Integrable (fun x => w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1))
      (volume : Measure E) := by
  have h_partial_cont : Continuous
      (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) :=
    (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have h_partial_supp :
      HasCompactSupport
        (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  have h_partial_memLp :
      MemLp (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) 2
        (volume : Measure E) :=
    h_partial_cont.memLp_of_hasCompactSupport h_partial_supp
  exact MemLp.integrable_mul hw_l2 h_partial_memLp

def smoothTestFunctional
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E)) (k : Fin d) :
    smoothCSSubmodule (d := d) →ₗ[ℝ] ℝ where
  toFun φ :=
    -∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
  map_add' φ ψ := by
    change -∫ x, w x * (fderiv ℝ ((φ + ψ : smoothCSSubmodule (d := d)).1) x)
            (EuclideanSpace.single k 1)
        = (-∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)) +
          (-∫ x, w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1))
    have hφ_diff : Differentiable ℝ φ.1 := φ.2.1.differentiable (by simp)
    have hψ_diff : Differentiable ℝ ψ.1 := ψ.2.1.differentiable (by simp)
    have h_fderiv_sum : ∀ x : E,
        (fderiv ℝ ((φ + ψ : smoothCSSubmodule (d := d)).1) x)
            (EuclideanSpace.single k 1) =
          (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
            (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1) := by
      intro x
      rw [smoothCSSubmodule_add_coe (d := d) φ ψ]
      rw [show (φ.1 + ψ.1 : E → ℝ) = fun y => φ.1 y + ψ.1 y from rfl]
      rw [fderiv_fun_add (hφ_diff.differentiableAt) (hψ_diff.differentiableAt)]
      simp
    have hint_sum : ∀ x : E,
        w x * (fderiv ℝ ((φ + ψ : smoothCSSubmodule (d := d)).1) x)
              (EuclideanSpace.single k 1) =
          w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
            w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1) := by
      intro x; rw [h_fderiv_sum x]; ring
    have hφ_int := integrable_w_partial_phi_univ hw_l2 φ.2.1 φ.2.2 k
    have hψ_int := integrable_w_partial_phi_univ hw_l2 ψ.2.1 ψ.2.2 k
    have h_int_eq :
        ∫ x, w x * (fderiv ℝ ((φ + ψ : smoothCSSubmodule (d := d)).1) x)
                (EuclideanSpace.single k 1) =
          (∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)) +
            ∫ x, w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1) := by
      rw [show (fun x => w x *
          (fderiv ℝ ((φ + ψ : smoothCSSubmodule (d := d)).1) x)
            (EuclideanSpace.single k 1)) =
        (fun x =>
            w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
              w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1)) from by
          ext x; exact hint_sum x]
      exact integral_add hφ_int hψ_int
    rw [h_int_eq]; ring
  map_smul' c φ := by
    change -∫ x, w x *
            (fderiv ℝ ((c • φ : smoothCSSubmodule (d := d)).1) x)
              (EuclideanSpace.single k 1) =
          c • (-∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1))
    have hφ_diff : Differentiable ℝ φ.1 := φ.2.1.differentiable (by simp)
    have h_fderiv_smul : ∀ x : E,
        (fderiv ℝ ((c • φ : smoothCSSubmodule (d := d)).1) x)
            (EuclideanSpace.single k 1) =
          c * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) := by
      intro x
      rw [smoothCSSubmodule_smul_coe (d := d) c φ]
      have heq2 : (c • φ.1 : E → ℝ) = fun y => c * φ.1 y := by ext y; rfl
      rw [heq2]
      rw [fderiv_const_mul (hφ_diff.differentiableAt) c]
      simp
    have hint_smul : ∀ x : E,
        w x * (fderiv ℝ ((c • φ : smoothCSSubmodule (d := d)).1) x)
              (EuclideanSpace.single k 1) =
          c * (w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)) := by
      intro x; rw [h_fderiv_smul x]; ring
    have h_int_eq :
        ∫ x, w x * (fderiv ℝ ((c • φ : smoothCSSubmodule (d := d)).1) x)
              (EuclideanSpace.single k 1) =
          c * ∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) := by
      rw [show (fun x => w x *
          (fderiv ℝ ((c • φ : smoothCSSubmodule (d := d)).1) x)
            (EuclideanSpace.single k 1)) =
        (fun x => c * (w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)))
          from by ext x; exact hint_smul x]
      exact integral_const_mul _ _
    rw [h_int_eq]
    rw [smul_eq_mul]; ring

omit [NeZero d] in
@[simp] lemma smoothTestFunctional_apply
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E)) (k : Fin d)
    (φ : smoothCSSubmodule (d := d)) :
    smoothTestFunctional (d := d) hw_l2 k φ =
      -∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) := rfl


omit [NeZero d] in
private lemma diffQuot_eq_zero_of_notMem_cthickening
    {φ : E → ℝ} (_hφ_supp : HasCompactSupport φ)
    (k : Fin d) {h₀ : ℝ} (_hh₀ : 0 ≤ h₀) {h : ℝ} (hh_bd : |h| ≤ h₀) :
    ∀ x : E, x ∉ Metric.cthickening h₀ (tsupport φ) →
      diffQuot k h φ x = 0 := by
  intro x hx
  have hxnot : x ∉ tsupport φ := fun h => hx (Metric.self_subset_cthickening _ h)
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxnot
  have hxhe : x + h • EuclideanSpace.single k 1 ∉ tsupport φ := by
    intro hin
    apply hx
    have hnorm :
        dist x (x + h • EuclideanSpace.single k 1) = |h| := by
      rw [dist_eq_norm]
      have heq : x - (x + h • EuclideanSpace.single k 1) =
          -(h • EuclideanSpace.single k 1) := by abel
      rw [heq, norm_neg, norm_smul]
      rw [show ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 by simp]
      rw [Real.norm_eq_abs, mul_one]
    have h_dist_le : dist x (x + h • EuclideanSpace.single k 1) ≤ h₀ := by
      rw [hnorm]; exact hh_bd
    exact Metric.mem_cthickening_of_dist_le x
      (x + h • EuclideanSpace.single k 1) h₀ (tsupport φ) hin h_dist_le
  have hφxhe : φ (x + h • EuclideanSpace.single k 1) = 0 :=
    image_eq_zero_of_notMem_tsupport hxhe
  by_cases hh : h = 0
  · rw [hh]; simp [diffQuot]
  · rw [diffQuot_apply_of_ne (d := d) k hh φ x]
    rw [hφx, hφxhe]
    simp

omit [NeZero d] in

private lemma abs_diffQuot_le_lipschitz_bound
    {φ : E → ℝ} (hφ_C1 : ContDiff ℝ 1 φ) (hφ_supp : HasCompactSupport φ)
    (k : Fin d) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ h : ℝ, ∀ x : E, |diffQuot k h φ x| ≤ L := by
  obtain ⟨L, hL_nn, hLip⟩ :=
    lipschitz_of_contDiff_compactSupport (d := d) hφ_C1 hφ_supp
  refine ⟨L, hL_nn, fun h x => ?_⟩
  by_cases hh : h = 0
  · rw [hh, diffQuot_zero_h]; simpa using hL_nn
  · rw [diffQuot_apply_of_ne (d := d) k hh φ x]
    have hLip_apply :
        ‖φ (x + h • EuclideanSpace.single k 1) - φ x‖ ≤
          L * ‖x + h • EuclideanSpace.single k 1 - x‖ := hLip _ _
    have hsimp : x + h • EuclideanSpace.single k 1 - x =
        h • EuclideanSpace.single k 1 := by
      rw [add_sub_cancel_left]
    rw [hsimp] at hLip_apply
    have hsing_norm :
        ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
    have hnorm_smul :
        ‖h • EuclideanSpace.single k (1 : ℝ)‖ = |h| := by
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
    rw [hnorm_smul] at hLip_apply
    rw [abs_div]
    have habs_h : 0 < |h| := abs_pos.mpr hh
    rw [div_le_iff₀ habs_h]
    have h_lhs_norm :
        |φ (x + h • EuclideanSpace.single k 1) - φ x| =
          ‖φ (x + h • EuclideanSpace.single k 1) - φ x‖ :=
      (Real.norm_eq_abs _).symm
    rw [h_lhs_norm]
    exact hLip_apply

omit [NeZero d] in

private lemma abs_partialDeriv_le_lipschitz_bound
    {φ : E → ℝ} (hφ_C1 : ContDiff ℝ 1 φ) (hφ_supp : HasCompactSupport φ)
    (k : Fin d) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : E,
      |(fderiv ℝ φ x) (EuclideanSpace.single k 1)| ≤ L := by
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_C1.continuous_fderiv (by simp)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    hφ_supp.fderiv ℝ
  obtain ⟨C, hC⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hbnd : ‖fderiv ℝ φ x‖ ≤ max C 0 := (hC x).trans (le_max_left _ _)
  have happ : ‖(fderiv ℝ φ x) (EuclideanSpace.single k 1)‖ ≤
      ‖fderiv ℝ φ x‖ * ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h_unit : ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
  rw [h_unit, mul_one] at happ
  have h_app_le : ‖(fderiv ℝ φ x) (EuclideanSpace.single k 1)‖ ≤ max C 0 :=
    happ.trans hbnd
  rwa [Real.norm_eq_abs] at h_app_le

omit [NeZero d] in

private lemma abs_integral_mul_le_eLpNorm_two
    {μ : Measure E} {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h_abs_le_lintegral :
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := by
    rw [← Real.norm_eq_abs]
    have hint : ‖∫ x, f x * g x ∂μ‖ₑ ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    have hofreal : ENNReal.ofReal ‖∫ x, f x * g x ∂μ‖ = ‖∫ x, f x * g x ∂μ‖ₑ :=
      ofReal_norm_eq_enorm _
    rw [hofreal]; exact hint
  have h_lintegral_eq :
      ∫⁻ x, ‖f x * g x‖ₑ ∂μ = eLpNorm (fun x => g x * f x) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr (fun x => ?_)
    simp [enorm_mul, mul_comm]
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    constructor
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
    rw [ENNReal.inv_two_add_inv_two]
  have h_smul_bound :
      eLpNorm (fun x => g x * f x) 1 μ ≤ eLpNorm g 2 μ * eLpNorm f 2 μ := by
    have h_mul_eq :
        (fun x => g x * f x) = (g : E → ℝ) • (f : E → ℝ) := by
      funext x; simp [smul_eq_mul]
    rw [h_mul_eq]
    haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := inferInstance
    exact eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hg.aestronglyMeasurable
  calc
    ENNReal.ofReal |∫ x, f x * g x ∂μ|
        ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := h_abs_le_lintegral
    _ = eLpNorm (fun x => g x * f x) 1 μ := h_lintegral_eq
    _ ≤ eLpNorm g 2 μ * eLpNorm f 2 μ := h_smul_bound
    _ = eLpNorm f 2 μ * eLpNorm g 2 μ := mul_comm _ _

omit [NeZero d] in

private lemma abs_integral_mul_le_norm_lp_mul_norm_lp
    {f g : E → ℝ} (hf : MemLp f 2 (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E)) :
    |∫ x, f x * g x ∂(volume : Measure E)| ≤
      (eLpNorm f 2 (volume : Measure E)).toReal *
        (eLpNorm g 2 (volume : Measure E)).toReal := by
  have h_ennreal := abs_integral_mul_le_eLpNorm_two
    (μ := (volume : Measure E)) hf hg
  have h_finite_f : eLpNorm f 2 (volume : Measure E) ≠ ∞ := hf.eLpNorm_lt_top.ne
  have h_finite_g : eLpNorm g 2 (volume : Measure E) ≠ ∞ := hg.eLpNorm_lt_top.ne
  have h_finite : eLpNorm f 2 (volume : Measure E) *
      eLpNorm g 2 (volume : Measure E) ≠ ∞ :=
    ENNReal.mul_ne_top h_finite_f h_finite_g
  have h_toReal := ENNReal.toReal_mono h_finite h_ennreal
  have hnn : 0 ≤ |∫ x, f x * g x ∂(volume : Measure E)| := abs_nonneg _
  rw [ENNReal.toReal_ofReal hnn] at h_toReal
  rw [ENNReal.toReal_mul] at h_toReal
  exact h_toReal

omit [NeZero d] in

private lemma volume_cthickening_lt_top
    {K : Set E} (hK : IsCompact K) (r : ℝ) :
    (volume : Measure E) (Metric.cthickening r K) < ∞ := by
  have hK_thick : IsCompact (Metric.cthickening r K) := hK.cthickening
  exact hK_thick.measure_lt_top


omit [NeZero d] in
private lemma tendsto_integral_w_diffQuot_phi
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) (k : Fin d)
    {hₙ : ℕ → ℝ} (hₙ_ne : ∀ n, hₙ n ≠ 0)
    (hₙ_tendsto : Tendsto hₙ atTop (𝓝 0)) :
    Tendsto (fun n =>
        ∫ x, w x * diffQuot k (-(hₙ n)) φ x ∂(volume : Measure E))
      atTop
      (𝓝 (∫ x, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E))) := by
  have hφ_C1 : ContDiff ℝ 1 φ := hφ_smooth.of_le (by norm_cast)
  obtain ⟨L, _hL_nn, hLip⟩ :=
    abs_diffQuot_le_lipschitz_bound (d := d) hφ_C1 hφ_supp k
  set h₀ : ℝ := 1 with h₀_def
  have hh₀_nn : (0 : ℝ) ≤ h₀ := by simp [h₀_def]
  have hN : ∀ᶠ n in atTop, |hₙ n| ≤ h₀ := by
    have hAbs : Tendsto (fun n => |hₙ n|) atTop (𝓝 0) := by
      have := hₙ_tendsto.abs; simpa using this
    have h_ev :
        ∀ᶠ n in atTop, dist (|hₙ n|) 0 < 1 :=
      hAbs.eventually (Metric.ball_mem_nhds 0 (by norm_num))
    filter_upwards [h_ev] with n hn
    have h_dist : dist (|hₙ n|) 0 = |hₙ n| := by
      rw [Real.dist_eq, sub_zero, abs_abs]
    rw [h_dist] at hn
    exact hn.le
  set K_thick : Set E := Metric.cthickening h₀ (tsupport φ) with hKt_def
  have hK_compact : IsCompact (tsupport φ) := hφ_supp
  have hK_thick_compact : IsCompact K_thick := hK_compact.cthickening
  have hK_thick_meas : MeasurableSet K_thick :=
    hK_thick_compact.measurableSet
  set bound : E → ℝ := fun x => K_thick.indicator (fun y => L * |w y|) x
  have hw_meas : AEStronglyMeasurable w (volume : Measure E) :=
    hw_l2.aestronglyMeasurable
  have h_indicator_memLp_2 :
      MemLp (fun x : E => K_thick.indicator (fun _ => (1 : ℝ)) x) 2
        (volume : Measure E) := by
    have h_finite : (volume : Measure E) K_thick ≠ ∞ :=
      hK_thick_compact.measure_lt_top.ne
    refine memLp_indicator_const _ hK_thick_meas (1 : ℝ) (Or.inr h_finite)
  have h_abs_eq_norm : (fun x => |w x|) = fun x => ‖w x‖ := by
    funext x; rw [Real.norm_eq_abs]
  have h_abs_w_memLp : MemLp (fun x => |w x|) 2 (volume : Measure E) := by
    rw [h_abs_eq_norm]
    exact hw_l2.norm
  have h_Labsw_memLp :
      MemLp (fun x => L * |w x|) 2 (volume : Measure E) :=
    h_abs_w_memLp.const_mul L
  have h_bound_eq :
      bound = (fun x => (L * |w x|) *
        K_thick.indicator (fun _ => (1 : ℝ)) x) := by
    funext x
    simp only [bound]
    by_cases hx : x ∈ K_thick
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have h_bound_int : Integrable bound (volume : Measure E) := by
    rw [h_bound_eq]
    exact MemLp.integrable_mul h_Labsw_memLp h_indicator_memLp_2
  have h_pointwise_bound :
      ∀ᶠ n in atTop, ∀ᵐ x ∂(volume : Measure E),
        ‖w x * diffQuot k (-(hₙ n)) φ x‖ ≤ bound x := by
    filter_upwards [hN] with n hn
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K_thick
    · simp only [bound, Set.indicator_of_mem hx]
      rw [Real.norm_eq_abs, abs_mul]
      have hL_dq : |diffQuot k (-(hₙ n)) φ x| ≤ L := hLip _ x
      have h_abs_w_nn : 0 ≤ |w x| := abs_nonneg _
      have h_LL : |w x| * |diffQuot k (-(hₙ n)) φ x| ≤ |w x| * L :=
        mul_le_mul_of_nonneg_left hL_dq h_abs_w_nn
      linarith
    · have h_neg_h_bd : |-(hₙ n)| ≤ h₀ := by rw [abs_neg]; exact hn
      have hdq_zero : diffQuot k (-(hₙ n)) φ x = 0 :=
        diffQuot_eq_zero_of_notMem_cthickening (d := d) hφ_supp k hh₀_nn
          h_neg_h_bd x hx
      rw [hdq_zero, mul_zero, norm_zero]
      simp [bound, Set.indicator_of_notMem hx]
  have h_pointwise_conv :
      ∀ᵐ x ∂(volume : Measure E),
        Tendsto (fun n => w x * diffQuot k (-(hₙ n)) φ x) atTop
          (𝓝 (w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1))) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h_minus_tendsto : Tendsto (fun n => -(hₙ n)) atTop (𝓝 0) := by
      have := hₙ_tendsto.neg; simpa using this
    have h_minus_ne : ∀ n, -(hₙ n) ≠ 0 := fun n hn =>
      hₙ_ne n (neg_eq_zero.mp hn)
    have h_dq_nhdsWithin :
        Tendsto (fun h : ℝ => diffQuot k h φ x) (𝓝[≠] 0)
          (𝓝 ((fderiv ℝ φ x) (EuclideanSpace.single k 1))) :=
      tendsto_diffQuot_of_contDiff (d := d) hφ_C1 k x
    have h_tendsto_within :
        Tendsto (fun n => -(hₙ n)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h_minus_tendsto, ?_⟩
      exact Filter.Eventually.of_forall fun n => h_minus_ne n
    have h_dq_tendsto :
        Tendsto (fun n => diffQuot k (-(hₙ n)) φ x) atTop
          (𝓝 ((fderiv ℝ φ x) (EuclideanSpace.single k 1))) :=
      h_dq_nhdsWithin.comp h_tendsto_within
    exact h_dq_tendsto.const_mul (w x)
  have h_aesm_seq : ∀ n, AEStronglyMeasurable
      (fun x => w x * diffQuot k (-(hₙ n)) φ x) (volume : Measure E) := by
    intro n
    have hdq_meas : AEStronglyMeasurable (diffQuot k (-(hₙ n)) φ) (volume : Measure E) :=
      aestronglyMeasurable_diffQuot (d := d) k _ hφ_smooth.continuous.aestronglyMeasurable
    exact hw_meas.mul hdq_meas
  exact tendsto_integral_filter_of_dominated_convergence
    bound (Filter.Eventually.of_forall h_aesm_seq)
    h_pointwise_bound h_bound_int h_pointwise_conv


omit [NeZero d] in
private lemma abs_smoothTestFunctional_le
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M) {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 (volume : Measure E) ≤ ENNReal.ofReal M)
    (φ : smoothCSSubmodule (d := d)) :
    |smoothTestFunctional (d := d) hw_l2 k φ| ≤
      M * (eLpNorm φ.1 2 (volume : Measure E)).toReal := by
  rw [smoothTestFunctional_apply]
  rw [abs_neg]
  set hₙ : ℕ → ℝ := fun n => h₀ / (n + 1)
  have hₙ_pos : ∀ n, 0 < hₙ n := fun n => by
    apply div_pos hh₀
    have : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.zero_lt_succ n
    exact this
  have hₙ_ne : ∀ n, hₙ n ≠ 0 := fun n => (hₙ_pos n).ne'
  have hₙ_bd : ∀ n, |hₙ n| ≤ h₀ := fun n => by
    rw [abs_of_pos (hₙ_pos n)]
    have h1 : (1 : ℝ) ≤ n + 1 := by
      have h0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      linarith
    rw [div_le_iff₀ (by exact_mod_cast Nat.zero_lt_succ n : (0 : ℝ) < n + 1)]
    have : h₀ ≤ h₀ * (n + 1) := by nlinarith [hh₀.le]
    linarith
  have hₙ_pos_abs : ∀ n, 0 < |hₙ n| := fun n => by
    rw [abs_of_pos (hₙ_pos n)]; exact hₙ_pos n
  have hₙ_tendsto : Tendsto hₙ atTop (𝓝 0) := by
    have hh0 : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 (0 : ℝ)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact this
    have h_eq : ∀ n, hₙ n = h₀ * (1 / ((n : ℝ) + 1)) := fun n => by
      simp only [hₙ]; ring
    rw [show hₙ = fun n : ℕ => h₀ * (1 / ((↑n : ℝ) + 1)) from funext h_eq]
    have hmul := hh0.const_mul h₀
    simpa using hmul
  have hφ_memLp : MemLp φ.1 2 (volume : Measure E) :=
    memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2
  have h_conv : Tendsto (fun n =>
      ∫ x, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)) atTop
      (𝓝 (∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E))) :=
    tendsto_integral_w_diffQuot_phi (d := d) hw_l2 φ.2.1 φ.2.2 k hₙ_ne hₙ_tendsto
  have h_dq_l2_bound : ∀ n,
      eLpNorm (diffQuot k (hₙ n) w) 2 (volume : Measure E) ≤
        ENNReal.ofReal M := fun n =>
    h_bdd (hₙ n) (hₙ_pos_abs n) (hₙ_bd n)
  have h_dq_memLp : ∀ n, MemLp (diffQuot k (hₙ n) w) 2 (volume : Measure E) := by
    intro n
    refine ⟨aestronglyMeasurable_diffQuot k (hₙ n) hw_l2.aestronglyMeasurable, ?_⟩
    calc eLpNorm (diffQuot k (hₙ n) w) 2 (volume : Measure E)
        ≤ ENNReal.ofReal M := h_dq_l2_bound n
      _ < ∞ := ENNReal.ofReal_lt_top
  have h_IBP : ∀ n,
      ∫ x, diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E) =
        -∫ x, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E) := by
    intro n
    exact integral_diffQuot_mul_eq_neg_integral_mul_diffQuot
      (d := d) k (hₙ_ne n) hw_l2 hφ_memLp
  have h_lhs_bound : ∀ n,
      |∫ x, diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 (volume : Measure E)).toReal := by
    intro n
    have h_cs := abs_integral_mul_le_norm_lp_mul_norm_lp
      (d := d) (h_dq_memLp n) hφ_memLp
    have h_dq_bound :
        (eLpNorm (diffQuot k (hₙ n) w) 2 (volume : Measure E)).toReal ≤ M := by
      have hMto : (ENNReal.ofReal M).toReal = M := ENNReal.toReal_ofReal hM_nn
      calc (eLpNorm (diffQuot k (hₙ n) w) 2 (volume : Measure E)).toReal
          ≤ (ENNReal.ofReal M).toReal := by
            refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
            exact h_dq_l2_bound n
        _ = M := hMto
    have h_phi_nn : 0 ≤ (eLpNorm φ.1 2 (volume : Measure E)).toReal :=
      ENNReal.toReal_nonneg
    have hMul :
        (eLpNorm (diffQuot k (hₙ n) w) 2 (volume : Measure E)).toReal *
            (eLpNorm φ.1 2 (volume : Measure E)).toReal ≤
          M * (eLpNorm φ.1 2 (volume : Measure E)).toReal :=
      mul_le_mul_of_nonneg_right h_dq_bound h_phi_nn
    linarith
  have h_lhs_eq : ∀ n,
      |∫ x, diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E)| =
        |∫ x, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| := by
    intro n
    rw [h_IBP n]; rw [abs_neg]
  have h_dual_bound : ∀ n,
      |∫ x, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 (volume : Measure E)).toReal := by
    intro n; rw [← h_lhs_eq n]; exact h_lhs_bound n
  have h_abs_conv :
      Tendsto (fun n =>
          |∫ x, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)|)
        atTop
        (𝓝 |∫ x, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
          ∂(volume : Measure E)|) := by
    have := h_conv.abs
    simpa using this
  have h_lim_le := le_of_tendsto_of_tendsto'
    h_abs_conv tendsto_const_nhds (fun n => h_dual_bound n)
  exact h_lim_le


omit [NeZero d] in
private lemma abs_smoothTestFunctional_le_lpNorm
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M) {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 (volume : Measure E) ≤ ENNReal.ofReal M)
    (φ : smoothCSSubmodule (d := d)) :
    |smoothTestFunctional (d := d) hw_l2 k φ| ≤
      M * ‖smoothCSToLp (d := d) φ‖ := by
  have h := abs_smoothTestFunctional_le (d := d) hw_l2 k hM_nn hh₀ h_bdd φ
  have h_norm_eq :
      ‖smoothCSToLp (d := d) φ‖ =
        (eLpNorm φ.1 2 (volume : Measure E)).toReal := by
    rw [show (smoothCSToLp (d := d) φ : Lp ℝ 2 (volume : Measure E)) =
      (memLp_two_of_smoothCS (d := d) φ.2.1 φ.2.2).toLp φ.1 from rfl]
    exact Lp.norm_toLp _ _
  rw [h_norm_eq]
  exact h

def smoothTestFunctional_ext
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E)) (k : Fin d) :
    Lp ℝ 2 (volume : Measure E) →L[ℝ] ℝ :=
  (smoothTestFunctional (d := d) hw_l2 k).extendOfNorm
    (smoothCSToLp (d := d))

omit [NeZero d] in
private lemma opNorm_smoothTestFunctional_ext_le
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M) {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 (volume : Measure E) ≤ ENNReal.ofReal M) :
    ‖smoothTestFunctional_ext (d := d) hw_l2 k‖ ≤ M := by
  unfold smoothTestFunctional_ext
  refine LinearMap.opNorm_extendOfNorm_le (denseRange_smoothCSToLp (d := d))
    hM_nn ?_
  intro φ
  exact abs_smoothTestFunctional_le_lpNorm (d := d) hw_l2 k hM_nn hh₀ h_bdd φ

omit [NeZero d] in
private lemma smoothTestFunctional_ext_apply
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M) {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 (volume : Measure E) ≤ ENNReal.ofReal M)
    (φ : smoothCSSubmodule (d := d)) :
    smoothTestFunctional_ext (d := d) hw_l2 k
        (smoothCSToLp (d := d) φ) =
      smoothTestFunctional (d := d) hw_l2 k φ := by
  unfold smoothTestFunctional_ext
  refine LinearMap.extendOfNorm_eq (denseRange_smoothCSToLp (d := d))
    ⟨M, ?_⟩ φ
  intro ψ
  exact abs_smoothTestFunctional_le_lpNorm (d := d) hw_l2 k hM_nn hh₀ h_bdd ψ

def smoothTestFunctional_riesz
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d) :
    Lp ℝ 2 (volume : Measure E) :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E))).symm
    (smoothTestFunctional_ext (d := d) hw_l2 k)

omit [NeZero d] in
private lemma norm_smoothTestFunctional_riesz
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d) :
    ‖smoothTestFunctional_riesz (d := d) hw_l2 k‖ =
      ‖smoothTestFunctional_ext (d := d) hw_l2 k‖ := by
  unfold smoothTestFunctional_riesz
  exact (InnerProductSpace.toDual ℝ
    (Lp ℝ 2 (volume : Measure E))).symm.norm_map _

omit [NeZero d] in
private lemma smoothTestFunctional_ext_eq_inner
    {w : E → ℝ} (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d)
    (f : Lp ℝ 2 (volume : Measure E)) :
    smoothTestFunctional_ext (d := d) hw_l2 k f =
      ⟪smoothTestFunctional_riesz (d := d) hw_l2 k, f⟫_ℝ := by
  unfold smoothTestFunctional_riesz
  rw [InnerProductSpace.toDual_symm_apply]

omit [NeZero d] in
theorem hasWeakPartialDeriv_of_diffQuot_uniform_bound_univ
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 (volume : Measure E))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M) {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 (volume : Measure E) ≤ ENNReal.ofReal M) :
    ∃ g : E → ℝ,
      MemLp g 2 (volume : Measure E) ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g w (Set.univ) ∧
      eLpNorm g 2 (volume : Measure E) ≤ ENNReal.ofReal M := by
  set g_lp : Lp ℝ 2 (volume : Measure E) :=
    smoothTestFunctional_riesz (d := d) hw_l2 k with hg_lp_def
  refine ⟨⇑g_lp, ?_, ?_, ?_⟩
  · exact Lp.memLp g_lp
  · intro φ hφ_smooth hφ_supp _
    rw [setIntegral_univ, setIntegral_univ]
    set φ_cs : smoothCSSubmodule (d := d) := ⟨φ, hφ_smooth, hφ_supp⟩
    have h_ext_apply :=
      smoothTestFunctional_ext_apply (d := d) hw_l2 k hM_nn hh₀ h_bdd φ_cs
    have h_ext_inner :=
      smoothTestFunctional_ext_eq_inner (d := d) hw_l2 k
        (smoothCSToLp (d := d) φ_cs)
    have h_func_val :
        smoothTestFunctional (d := d) hw_l2 k φ_cs =
          -∫ x, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) := by
      rw [smoothTestFunctional_apply]
    have h_inner_def := L2.inner_def (𝕜 := ℝ) g_lp (smoothCSToLp (d := d) φ_cs)
    have h_coeFn_phi :
        ⇑(smoothCSToLp (d := d) φ_cs) =ᵐ[(volume : Measure E)] φ := by
      simp only [smoothCSToLp_apply]
      exact MemLp.coeFn_toLp _
    have h_int_eq :
        ∫ x, ⟪g_lp x, (smoothCSToLp (d := d) φ_cs) x⟫_ℝ ∂(volume : Measure E) =
          ∫ x, g_lp x * φ x ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      filter_upwards [h_coeFn_phi] with x hx
      have h_inner_eq :
          ⟪(g_lp x : ℝ), (smoothCSToLp (d := d) φ_cs) x⟫_ℝ =
            (smoothCSToLp (d := d) φ_cs) x * (g_lp x : ℝ) :=
        RCLike.inner_apply (𝕜 := ℝ) (g_lp x) ((smoothCSToLp (d := d) φ_cs) x)
      rw [h_inner_eq, hx]; ring
    have h_chain :
        smoothTestFunctional (d := d) hw_l2 k φ_cs =
          ∫ x, g_lp x * φ x ∂(volume : Measure E) := by
      rw [← h_ext_apply, h_ext_inner, h_inner_def, h_int_eq]
    rw [h_func_val] at h_chain
    linarith [h_chain]
  · have h_norm_eq := norm_smoothTestFunctional_riesz (d := d) hw_l2 k
    have h_op_le := opNorm_smoothTestFunctional_ext_le (d := d)
      hw_l2 k hM_nn hh₀ h_bdd
    have h_g_lp_le : ‖g_lp‖ ≤ M := by
      rw [hg_lp_def]
      rw [h_norm_eq]
      exact h_op_le
    have h_g_lp_nn : 0 ≤ ‖g_lp‖ := norm_nonneg _
    have h_enorm_le : (‖g_lp‖ₑ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      have hofreal : (‖g_lp‖ₑ : ℝ≥0∞) = ENNReal.ofReal ‖g_lp‖ :=
        (ofReal_norm_eq_enorm _).symm
      rw [hofreal]
      exact ENNReal.ofReal_le_ofReal h_g_lp_le
    have h_enorm_eq : ‖g_lp‖ₑ = eLpNorm (⇑g_lp) 2 (volume : Measure E) :=
      Lp.enorm_def g_lp
    rw [← h_enorm_eq]
    exact h_enorm_le

end Sobolev
end Analysis
end DifferentialGeometry
