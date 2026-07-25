import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.MemW1pResidualFull
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.H2
import DifferentialGeometry.Analysis.Elliptic.Operator.SmoothBridge
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceForward


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothApproxSeqH1ComplTendsto

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MemW1pFChartResidualFull

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma wkpNorm_succ_ge
    (d : ℕ) (k : ℕ) (p : ℝ≥0∞)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) k p u Ω ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) (k + 1) p u Ω := by
  classical
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro _ _ _; exact zero_le _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma wkpNormChart_le_succ
    (g : SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) g k p u ≤
      wkpNormChart (I := I) (M := M) g (k + 1) p u := by
  classical
  unfold wkpNormChart
  refine ENNReal.tsum_le_tsum (fun α => ?_)
  exact wkpNorm_succ_ge (d := Module.finrank ℝ E) k p _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
lemma wkpNormChart_one_le_two
    (g : SmoothRiemannianMetric I M)
    (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) g 1 p u ≤
      wkpNormChart (I := I) (M := M) g 2 p u := by
  exact wkpNormChart_le_succ (I := I) (M := M) g 1 p u

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_smoothScalar_le_const_mul_wkpNormChart_one
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : SmoothScalar g,
        eLpNorm f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 2 f.toFun := by
  classical
  obtain ⟨C, hC_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceFull.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  refine ⟨C, hC_nn, ?_⟩
  intro f
  exact hbound f.smooth.continuous.measurable

private lemma eLpNorm_gNormGrad_smoothScalar_le_const_mul_wkpNormChart_one
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : SmoothScalar g,
        eLpNorm (fun x : M => Real.sqrt
            (g.inner x (gradFun (I := I) g f.toFun x)
              (gradFun (I := I) g f.toFun x))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 2 f.toFun := by
  classical
  obtain ⟨C, hC_nn, hbound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceFull.eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform
      (I := I) (M := M) g (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  refine ⟨C, hC_nn, ?_⟩
  intro f
  exact hbound f.smooth

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
private lemma eLpNorm_sq_toReal_eq_integral_sq
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    (eLpNorm f.toFun 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := f.norm_smoothToLp_sq
  have h_norm :
      ‖smoothToLpLin (I := I) (M := M) g f‖ =
        (eLpNorm f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    change ‖f.memLp_two.toLp f.toFun‖ = _
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [← h_norm]
  exact h

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_gNormGrad_sq_toReal_eq_integral_inner_grad
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    (eLpNorm (fun x : M => Real.sqrt
          (g.inner x (gradFun (I := I) g f.toFun x)
            (gradFun (I := I) g f.toFun x))) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ^ 2 =
      ∫ x, g.inner x
            ((grad_g (I := I) g f.smooth :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g f.smooth :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set ψ : M → ℝ := fun x : M => Real.sqrt
    (g.inner x (gradFun (I := I) g f.toFun x)
      (gradFun (I := I) g f.toFun x)) with hψ_def
  have hψ_sq : ∀ x : M, ψ x ^ 2 =
      g.inner x ((grad_g (I := I) g f.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g f.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [hψ_def]
    rw [grad_g_apply]
    rw [sq]
    rw [Real.mul_self_sqrt]
    exact SmoothRiemannianMetric_inner_self_nonneg g x _
  have hψ_cont : Continuous ψ := by
    have h_inner_cont : Continuous (fun x : M =>
        g.inner x (gradFun (I := I) g f.toFun x) (gradFun (I := I) g f.toFun x)) := by
      have h1 : (fun x : M =>
          g.inner x (gradFun (I := I) g f.toFun x) (gradFun (I := I) g f.toFun x)) =
          (fun x : M =>
            g.inner x ((grad_g (I := I) g f.smooth :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((grad_g (I := I) g f.smooth :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
        funext x
        rw [grad_g_apply]
      rw [h1]
      exact f.continuous_inner_grad f
    exact h_inner_cont.sqrt
  have hψ_memLp : MemLp ψ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hψ_cont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set ψ_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hψ_memLp.toLp ψ
  have h_inner := real_inner_self_eq_norm_sq ψ_Lp
  rw [L2.inner_def (𝕜 := ℝ)] at h_inner
  have h_norm_eq : ‖ψ_Lp‖ = (eLpNorm ψ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal :=
    MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq] at h_inner
  have hae : (fun a : M =>
      @inner ℝ _ _
        ((ψ_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) a)
        ((ψ_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
        (fun a : M => ψ a * ψ a) := by
    have hae_coe : (ψ_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] ψ := MemLp.coeFn_toLp _
    filter_upwards [hae_coe] with a ha
    rw [ha]; rfl
  rw [integral_congr_ae hae] at h_inner
  have h_integrand_eq :
      (fun a : M => ψ a * ψ a) = (fun a : M =>
        g.inner a ((grad_g (I := I) g f.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) a)
            ((grad_g (I := I) g f.smooth :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) a)) := by
    funext a
    rw [← sq]
    exact hψ_sq a
  rw [h_integrand_eq] at h_inner
  exact h_inner.symm

lemma norm_smoothScalar_le_const_mul_wkpNormChart_one
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : SmoothScalar g,
        wkpNormChart (I := I) (M := M) g 1 2 f.toFun ≠ ⊤ →
          ‖f‖ ≤ C *
            (wkpNormChart (I := I) (M := M) g 1 2 f.toFun).toReal := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bnd⟩ :=
    eLpNorm_smoothScalar_le_const_mul_wkpNormChart_one (I := I) (M := M) g
  obtain ⟨C₁, hC₁_nn, hC₁_bnd⟩ :=
    eLpNorm_gNormGrad_smoothScalar_le_const_mul_wkpNormChart_one (I := I) (M := M) g
  refine ⟨C₀ + C₁, add_nonneg hC₀_nn hC₁_nn, ?_⟩
  intro f h_wkpNorm_ne_top
  have h_sq : ‖f‖ ^ 2 = smoothScalarH1Inner (I := I) (M := M) f f :=
    f.norm_sq_eq_inner_self
  set L : ℝ := (eLpNorm f.toFun 2
    (riemannianVolumeMeasure (I := I) (M := M) g)).toReal with hL_def
  set Gnorm : ℝ := (eLpNorm (fun x : M => Real.sqrt
          (g.inner x (gradFun (I := I) g f.toFun x)
            (gradFun (I := I) g f.toFun x))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal with hGnorm_def
  have h_L_nn : 0 ≤ L := ENNReal.toReal_nonneg
  have h_Gnorm_nn : 0 ≤ Gnorm := ENNReal.toReal_nonneg
  have h_int_f_sq : ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = L ^ 2 := by
    rw [hL_def]
    exact (eLpNorm_sq_toReal_eq_integral_sq (I := I) (M := M) g f).symm
  have h_int_g_grad : ∫ x, g.inner x
        ((grad_g (I := I) g f.smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g f.smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = Gnorm ^ 2 := by
    rw [hGnorm_def]
    exact (eLpNorm_gNormGrad_sq_toReal_eq_integral_inner_grad (I := I) (M := M) g f).symm
  have h_norm_sq_eq : ‖f‖ ^ 2 = L ^ 2 + Gnorm ^ 2 := by
    rw [h_sq]
    unfold smoothScalarH1Inner
    rw [h_int_f_sq, h_int_g_grad]
  have h_norm_le_sum : ‖f‖ ≤ L + Gnorm := by
    have hnn : 0 ≤ L + Gnorm := add_nonneg h_L_nn h_Gnorm_nn
    have h_sq_le : ‖f‖ ^ 2 ≤ (L + Gnorm) ^ 2 := by
      rw [h_norm_sq_eq]
      have h_2lg : 0 ≤ 2 * L * Gnorm := by positivity
      nlinarith [h_2lg]
    exact abs_le_of_sq_le_sq' h_sq_le hnn |>.2
  set N : ℝ := (wkpNormChart (I := I) (M := M) g 1 2 f.toFun).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have h_L_le_C0N : L ≤ C₀ * N := by
    have h_bd := hC₀_bnd f
    have h_toReal_bd : L ≤ (ENNReal.ofReal C₀ *
        wkpNormChart (I := I) (M := M) g 1 2 f.toFun).toReal := by
      rw [hL_def]
      apply ENNReal.toReal_mono _ h_bd
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_wkpNorm_ne_top
    have h_eq :
        (ENNReal.ofReal C₀ *
            wkpNormChart (I := I) (M := M) g 1 2 f.toFun).toReal =
          C₀ * N := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀_nn, hN_def]
    rw [← h_eq]
    exact h_toReal_bd
  have h_Gnorm_le_C1N : Gnorm ≤ C₁ * N := by
    have h_bd := hC₁_bnd f
    have h_toReal_bd : Gnorm ≤ (ENNReal.ofReal C₁ *
        wkpNormChart (I := I) (M := M) g 1 2 f.toFun).toReal := by
      rw [hGnorm_def]
      apply ENNReal.toReal_mono _ h_bd
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_wkpNorm_ne_top
    have h_eq :
        (ENNReal.ofReal C₁ *
            wkpNormChart (I := I) (M := M) g 1 2 f.toFun).toReal =
          C₁ * N := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₁_nn, hN_def]
    rw [← h_eq]
    exact h_toReal_bd
  calc ‖f‖ ≤ L + Gnorm := h_norm_le_sum
    _ ≤ C₀ * N + C₁ * N := add_le_add h_L_le_C0N h_Gnorm_le_C1N
    _ = (C₀ + C₁) * N := by ring

omit [NeZero (Module.finrank ℝ E)] in
lemma wkpNormChart_one_two_smoothScalar_diff_ne_top
    (g : SmoothRiemannianMetric I M)
    (v w : SmoothScalar g) :
    wkpNormChart (I := I) (M := M) g 1 2
        (fun x : M => v.toFun x - w.toFun x) ≠ ⊤ := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hv_mem : MemWkpChart (I := I) (M := M) g 1 2 v.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one 1 v.smooth
  have hw_mem : MemWkpChart (I := I) (M := M) g 1 2 w.toFun :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) g hp_one 1 w.smooth
  have h_diff_mem : MemWkpChart (I := I) (M := M) g 1 2
      (fun x : M => v.toFun x - w.toFun x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) g hp_one hv_mem hw_mem
  exact (wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp_one h_diff_mem).ne

theorem smoothApproxSeq_cauchy_smoothScalar
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    CauchySeq (fun n =>
      smoothApproxSeq (I := I) (M := M) g hu_h n) := by
  classical
  obtain ⟨C, hC_nn, hC_bnd⟩ :=
    norm_smoothScalar_le_const_mul_wkpNormChart_one (I := I) (M := M) g
  rw [Metric.cauchySeq_iff]
  intro ε hε_pos
  set Cp1 : ℝ := C + 1 with hCp1_def
  have hCp1_pos : 0 < Cp1 := by linarith
  set ε' : ℝ := ε / (2 * Cp1) with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / ε' - 1)
  have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
    have h_pos : 0 < 1 / ε' := by positivity
    linarith
  have hN0_inv_le : (1 : ℝ) / ((N0 : ℝ) + 1) ≤ ε' := by
    rw [div_le_iff₀ hN1_pos]
    have h1 : (1 : ℝ) = ε' * (1 / ε') := by
      rw [mul_one_div, div_self hε'_pos.ne']
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hε'_pos.le
    linarith
  refine ⟨N0, ?_⟩
  intro m hm n hn
  set vm : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h m with hvm_def
  set vn : SmoothScalar g := smoothApproxSeq (I := I) (M := M) g hu_h n with hvn_def
  rw [dist_eq_norm]
  set vdiff : SmoothScalar g := vm - vn with hvdiff_def
  have hvdiff_toFun : vdiff.toFun = fun x => vm.toFun x - vn.toFun x := by
    rw [hvdiff_def]; rfl
  have h_wkpNormChart_finite :
      wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun ≠ ⊤ := by
    rw [hvdiff_toFun]
    exact wkpNormChart_one_two_smoothScalar_diff_ne_top (I := I) (M := M) g vm vn
  have h_norm_bd : ‖vdiff‖ ≤ C *
      (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal :=
    hC_bnd vdiff h_wkpNormChart_finite
  have h_wkp_chart_2_2 :
      wkpNormChart (I := I) (M := M) g 2 2 vdiff.toFun ≤
        ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    rw [hvdiff_toFun]
    exact smoothApproxSeq_wkpNormChart_diff_le (I := I) (M := M) g hu_h m n
  have h_wkp_chart_1_2 :
      wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun ≤
        ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    (wkpNormChart_one_le_two (I := I) (M := M) g 2 vdiff.toFun).trans h_wkp_chart_2_2
  have h_sum_finite :
      ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have h_inv_m_nn : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
  have h_inv_n_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h_sum_toReal :
      (ENNReal.ofReal (1 / ((m : ℝ) + 1)) +
            ENNReal.ofReal (1 / ((n : ℝ) + 1))).toReal =
        1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal h_inv_m_nn, ENNReal.toReal_ofReal h_inv_n_nn]
  have h_wkp_toReal_le :
      (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
        1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
    have h_mono := ENNReal.toReal_mono h_sum_finite h_wkp_chart_1_2
    rwa [h_sum_toReal] at h_mono
  have hN0m : (N0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN0n : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hm_inv_le : (1 : ℝ) / ((m : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have hn_inv_le : (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have h_sum_le : 1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((N0 : ℝ) + 1)) := by
    linarith
  have h_wkp_toReal_le_2N : (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
        2 * (1 / ((N0 : ℝ) + 1)) :=
    h_wkp_toReal_le.trans h_sum_le
  have h_final : C * (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
      C * (2 * (1 / ((N0 : ℝ) + 1))) := by
    apply mul_le_mul_of_nonneg_left h_wkp_toReal_le_2N hC_nn
  have h_2N_le : 2 * (1 / ((N0 : ℝ) + 1)) ≤ 2 * ε' := by
    apply mul_le_mul_of_nonneg_left hN0_inv_le (by norm_num : (0 : ℝ) ≤ 2)
  have h_step1 : C * (wkpNormChart (I := I) (M := M) g 1 2 vdiff.toFun).toReal ≤
      C * (2 * ε') := by
    refine h_final.trans ?_
    exact mul_le_mul_of_nonneg_left h_2N_le hC_nn
  refine lt_of_le_of_lt (h_norm_bd.trans h_step1) ?_
  rw [hε'_def]
  have h1 : C * (2 * (ε / (2 * Cp1))) = C * ε / Cp1 := by
    field_simp
  rw [h1]
  rw [div_lt_iff₀ hCp1_pos]
  have hC_lt_Cp1 : C < Cp1 := by rw [hCp1_def]; linarith
  nlinarith [hε_pos]

theorem smoothToH1Compl_smoothApproxSeq_cauchy
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    CauchySeq (fun n =>
      smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeq (I := I) (M := M) g hu_h n)) := by
  have h_cauchy_smooth :=
    smoothApproxSeq_cauchy_smoothScalar (I := I) (M := M) g hu_h
  exact h_cauchy_smooth.map
    (smoothToH1Compl (I := I) (M := M) g).uniformContinuous

private theorem smoothToH1Compl_smoothApproxSeq_has_limit
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∃ u_star : H1Compl g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeq (I := I) (M := M) g hu_h n)) atTop (𝓝 u_star) :=
  cauchySeq_tendsto_of_complete
    (smoothToH1Compl_smoothApproxSeq_cauchy (I := I) (M := M) g hu_h)

private theorem eLpNorm_diff_smoothApproxSeq_tendsto_zero
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Tendsto (fun n => eLpNorm (fun x =>
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
          (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g))
      atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC_nn, hC_bnd⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceFull.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  have hu_meas : Measurable u := by
    rw [hu_def]
    exact (Lp.stronglyMeasurable _).measurable
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε_pos
  by_cases hC_zero : C = 0
  · refine ⟨0, ?_⟩
    intro n _
    have h_bnd := hC_bnd (u := fun x => u x - (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x)
        (hu_meas.sub
          (smoothApproxSeq (I := I) (M := M) g hu_h n).smooth.continuous.measurable)
    rw [hC_zero, ENNReal.ofReal_zero, zero_mul] at h_bnd
    exact h_bnd.trans (zero_le _)
  have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC_zero)
  by_cases hε_top : ε = ⊤
  · refine ⟨0, ?_⟩
    intro n _
    rw [hε_top]
    exact le_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_pos.ne' hε_top
  set ε_C : ℝ := ε.toReal / C with hε_C_def
  have hε_C_pos : 0 < ε_C := by positivity
  obtain ⟨N, hN_real⟩ := exists_nat_gt (1 / ε_C - 1)
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by
    have h_pos : 0 < 1 / ε_C := by positivity
    linarith
  have hN_inv_le : (1 : ℝ) / ((N : ℝ) + 1) ≤ ε_C := by
    rw [div_le_iff₀ hN1_pos]
    have h1 : (1 : ℝ) = ε_C * (1 / ε_C) := by
      rw [mul_one_div, div_self hε_C_pos.ne']
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hε_C_pos.le
    linarith
  refine ⟨N, ?_⟩
  intro n hn
  have h_meas : Measurable (fun x : M => u x -
      (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) :=
    hu_meas.sub
      (smoothApproxSeq (I := I) (M := M) g hu_h n).smooth.continuous.measurable
  have h_bnd := hC_bnd h_meas
  have h_chart_2_2 :
      wkpNormChart (I := I) (M := M) g 2 2
          (fun x : M => u x -
            (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    smoothApproxSeq_wkpNormChart_le (I := I) (M := M) g hu_h n
  have h_chart_1_2 :
      wkpNormChart (I := I) (M := M) g 1 2
          (fun x : M => u x -
            (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    (wkpNormChart_one_le_two (I := I) (M := M) g 2 _).trans h_chart_2_2
  have h_chain : eLpNorm
        (fun x => u x -
          (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal C * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    refine h_bnd.trans ?_
    gcongr
  refine h_chain.trans ?_
  have h_inv_n_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h_prod_eq : ENNReal.ofReal C * ENNReal.ofReal (1 / ((n : ℝ) + 1)) =
      ENNReal.ofReal (C * (1 / ((n : ℝ) + 1))) := by
    rw [← ENNReal.ofReal_mul hC_nn]
  rw [h_prod_eq]
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hn_inv_le_N_inv : (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((N : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos
    linarith
  have h_C_step : C * (1 / ((n : ℝ) + 1)) ≤ C * (1 / ((N : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hn_inv_le_N_inv hC_nn
  have h_C_ε_C : C * (1 / ((N : ℝ) + 1)) ≤ C * ε_C :=
    mul_le_mul_of_nonneg_left hN_inv_le hC_nn
  have h_C_ε_C_eq : C * ε_C = ε.toReal := by
    rw [hε_C_def]
    field_simp
  have h_final_real : C * (1 / ((n : ℝ) + 1)) ≤ ε.toReal := by
    calc C * (1 / ((n : ℝ) + 1))
        ≤ C * (1 / ((N : ℝ) + 1)) := h_C_step
      _ ≤ C * ε_C := h_C_ε_C
      _ = ε.toReal := h_C_ε_C_eq
  have h_ε_eq : ε = ENNReal.ofReal ε.toReal := (ENNReal.ofReal_toReal hε_top).symm
  rw [h_ε_eq]
  exact ENNReal.ofReal_le_ofReal h_final_real

set_option maxHeartbeats 1600000 in

private theorem smoothToLp_smoothApproxSeq_tendsto
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Tendsto (fun n => smoothToLp (I := I) (M := M) g
        (smoothApproxSeq (I := I) (M := M) g hu_h n))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε_pos
  have h_eLpNorm_tendsto :=
    eLpNorm_diff_smoothApproxSeq_tendsto_zero (I := I) (M := M) g hu_h
  rw [ENNReal.tendsto_atTop_zero] at h_eLpNorm_tendsto
  have hε_half_pos : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := h_eLpNorm_tendsto (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr hε_half_pos)
  refine ⟨N, ?_⟩
  intro n hn
  have h_eLpNorm_le := hN n hn
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  rw [dist_eq_norm]
  have h_norm_sub_comm :
      ‖smoothToLp (I := I) (M := M) g
            (smoothApproxSeq (I := I) (M := M) g hu_h n) -
          H1ComplToLp (I := I) (M := M) g u_h‖ =
      ‖H1ComplToLp (I := I) (M := M) g u_h -
          smoothToLp (I := I) (M := M) g
            (smoothApproxSeq (I := I) (M := M) g hu_h n)‖ :=
    norm_sub_rev _ _
  rw [h_norm_sub_comm]
  set Δ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    H1ComplToLp (I := I) (M := M) g u_h -
      smoothToLp (I := I) (M := M) g
        (smoothApproxSeq (I := I) (M := M) g hu_h n) with hΔ_def
  have h_Δ_coe_ae : (Δ : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => u x -
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) := by
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (H1ComplToLp (I := I) (M := M) g u_h)
      (smoothToLp (I := I) (M := M) g
        (smoothApproxSeq (I := I) (M := M) g hu_h n))
    have h_smoothToLp_coe :
        (smoothToLp (I := I) (M := M) g
            (smoothApproxSeq (I := I) (M := M) g hu_h n) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun :=
      MemLp.coeFn_toLp (smoothApproxSeq (I := I) (M := M) g hu_h n).memLp_two
    filter_upwards [h_sub, h_smoothToLp_coe] with x hx_sub hx_smoothToLp
    rw [hΔ_def, hx_sub, Pi.sub_apply, hx_smoothToLp]
  have h_norm_Δ : ‖Δ‖ = (eLpNorm (fun x => u x -
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae h_Δ_coe_ae]
  rw [h_norm_Δ]
  have h_eLpNorm_finite : eLpNorm (fun x => u x -
      (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ := by
    have h_le_half : eLpNorm (fun x => u x -
        (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal (ε / 2) := h_eLpNorm_le
    refine ne_of_lt ?_
    exact lt_of_le_of_lt h_le_half ENNReal.ofReal_lt_top
  have h_toReal_le : (eLpNorm (fun x => u x -
      (smoothApproxSeq (I := I) (M := M) g hu_h n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ≤ ε / 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_eLpNorm_le
    rw [ENNReal.toReal_ofReal hε_half_pos.le] at this
    exact this
  linarith

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothScalarH1Inner_eq_lpInner_oneSubLap_right
    (g : SmoothRiemannianMetric I M) (v f : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) v f =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g v⟫_ℝ := by
  rw [smoothScalarH1Inner_symm]
  exact smoothScalarH1Inner_eq_lpInner_oneSubLap f v

omit [NeZero (Module.finrank ℝ E)] in
lemma inner_h1Compl_smoothToH1Compl_eq_lpInner
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) (f : SmoothScalar g) :
    ⟪u_h, smoothToH1Compl (I := I) (M := M) g f⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ := by
  rw [real_inner_comm]
  have h_bilin :
      H1ComplBilin (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g f) u_h =
        lpFunctionalCLM (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g f.oneSubLapClassical) u_h :=
    smoothToH1Compl_bilin_eq_lpFunctional f u_h
  have h_LHS : ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ =
      H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g f) u_h := rfl
  rw [h_LHS, h_bilin]
  rw [lpFunctionalCLM_apply]
  exact real_inner_comm _ _

set_option maxHeartbeats 800000 in

private lemma inner_smoothToH1Compl_limit_eq_u_h
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    {u_star : H1Compl g}
    (h_tendsto_star : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g
        (smoothApproxSeq (I := I) (M := M) g hu_h n)) atTop (𝓝 u_star))
    (f : SmoothScalar g) :
    ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ =
      ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ := by
  classical
  have h_inner_star_lim : Tendsto (fun n =>
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeq (I := I) (M := M) g hu_h n)⟫_ℝ) atTop
        (𝓝 ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ) :=
    Tendsto.inner tendsto_const_nhds h_tendsto_star
  have h_rewrite : ∀ n,
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeq (I := I) (M := M) g hu_h n)⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g
          (smoothApproxSeq (I := I) (M := M) g hu_h n)⟫_ℝ := by
    intro n
    rw [inner_smoothToH1Compl_smoothToH1Compl]
    rw [smoothScalarH1Inner_symm]
    exact smoothScalarH1Inner_eq_lpInner_oneSubLap_right (I := I) (M := M) g
      (smoothApproxSeq (I := I) (M := M) g hu_h n) f
  have h_lp_tendsto :=
    smoothToLp_smoothApproxSeq_tendsto (I := I) (M := M) g hu_h
  have h_inner_lp_lim : Tendsto (fun n =>
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g
          (smoothApproxSeq (I := I) (M := M) g hu_h n)⟫_ℝ) atTop
        (𝓝 ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ) :=
    Tendsto.inner tendsto_const_nhds h_lp_tendsto
  have h_rewrite_func : (fun n =>
      ⟪smoothToH1Compl (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g
          (smoothApproxSeq (I := I) (M := M) g hu_h n)⟫_ℝ) =
      (fun n =>
        ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          smoothToLp (I := I) (M := M) g
            (smoothApproxSeq (I := I) (M := M) g hu_h n)⟫_ℝ) := by
    funext n; exact h_rewrite n
  rw [h_rewrite_func] at h_inner_star_lim
  have h_LHS_eq : ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ :=
    tendsto_nhds_unique h_inner_star_lim h_inner_lp_lim
  have h_RHS_eq : ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ := by
    have h_uh_f := inner_h1Compl_smoothToH1Compl_eq_lpInner (I := I) (M := M) g u_h f
    rw [← h_uh_f]
    exact real_inner_comm _ _
  rw [h_LHS_eq, h_RHS_eq]

theorem smoothApproxSeq_tendsto_h1Compl
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g
        (MemW1pFChartResidualFull.smoothApproxSeq
          (I := I) (M := M) g hu_h n))
      atTop (𝓝 u_h) := by
  classical
  obtain ⟨u_star, h_tendsto_star⟩ :=
    smoothToH1Compl_smoothApproxSeq_has_limit (I := I) (M := M) g hu_h
  suffices h_eq : u_star = u_h by
    convert h_tendsto_star using 2
    exact h_eq.symm
  apply ext_inner_left ℝ
  intro w
  have hL_cont : Continuous (fun w => ⟪w, u_star⟫_ℝ) :=
    ((innerSL ℝ (E := H1Compl g)).flip u_star).continuous
  have hR_cont : Continuous (fun w => ⟪w, u_h⟫_ℝ) :=
    ((innerSL ℝ (E := H1Compl g)).flip u_h).continuous
  have hLR_smooth :
      (fun w => ⟪w, u_star⟫_ℝ) ∘ (smoothToH1Compl (I := I) (M := M) g) =
        (fun w => ⟪w, u_h⟫_ℝ) ∘ (smoothToH1Compl (I := I) (M := M) g) := by
    funext f
    exact inner_smoothToH1Compl_limit_eq_u_h (I := I) (M := M) g hu_h h_tendsto_star f
  exact congrFun
    ((denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
      hL_cont hR_cont hLR_smooth) w

end SmoothApproxSeqH1ComplTendsto
end Laplacian
end Analysis
end DifferentialGeometry

end
