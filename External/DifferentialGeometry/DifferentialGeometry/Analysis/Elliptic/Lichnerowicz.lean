import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Geometry.Curvature.Bochner.BochnerConcrete
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
private theorem integral_Δ_g_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) :
    ∫ x, Δ_g (I := I) g hφ x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  exact integral_divergence_eq_zero_of_compact (I := I) g (grad_g (I := I) g hφ)

omit [NeZero (Module.finrank ℝ E)] in
private theorem integral_inner_grad_self_eq_neg_integral_f_Δf
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  exact green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g hf hf hf_cs

omit [NeZero (Module.finrank ℝ E)] in
theorem lichnerowicz_inequality
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hn_ge_two : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {lam : ℝ} (hlam_pos : 0 < lam)
    (hf_eigen : ∀ x : M, Δ_g (I := I) g hf x = -lam * f x)
    (gradNormSqSmooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => g.inner x
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
    (hessSqNorm : M → ℝ) (h_hessSqNorm_cont : Continuous hessSqNorm)
    (RicAtGrad : M → ℝ) (h_RicAtGrad_cont : Continuous RicAtGrad)
    (h_bochner : ∀ x : M,
      Δ_g (I := I) g gradNormSqSmooth x =
        2 * hessSqNorm x + 2 * RicAtGrad x +
          2 * g.inner x
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g (Δ_g_contMDiff (I := I) g hf) :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    (h_hess_lower_bound : ∀ x : M,
      (Δ_g (I := I) g hf x)^2 / (Module.finrank ℝ E : ℝ) ≤ hessSqNorm x)
    (h_ricci_lower_bound : ∀ x : M,
      ((Module.finrank ℝ E : ℝ) - 1) * K *
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ≤ RicAtGrad x)
    (h_f_sq_pos : 0 < ∫ x, f x * f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :
    (Module.finrank ℝ E : ℝ) * K ≤ lam := by
  classical
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_ge_two_real : (2 : ℝ) ≤ n := by
    rw [hn_def]; exact_mod_cast hn_ge_two
  have hn_pos : 0 < n := by linarith
  have hn_minus_one_pos : 0 < n - 1 := by linarith
  set Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hf with hGf_def
  have hΔf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (Δ_g (I := I) g hf) :=
    Δ_g_contMDiff (I := I) g hf
  set GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hΔf with hGΔf_def
  have hf_cont : Continuous f := hf.continuous
  have hΔf_cont : Continuous (Δ_g (I := I) g hf) := hΔf.continuous
  have hgrad_inner_cont :
      Continuous (fun x : M => g.inner x (Gf x) (Gf x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g Gf Gf
  have hgrad_Δ_inner_cont :
      Continuous (fun x : M => g.inner x (Gf x) (GΔf x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g Gf GΔf
  have integrable_of_cont :
      ∀ {φ : M → ℝ}, Continuous φ → Integrable φ μ := by
    intro φ hφ
    exact hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_LHS_zero :
      ∫ x, Δ_g (I := I) g gradNormSqSmooth x ∂μ = 0 :=
    integral_Δ_g_eq_zero (I := I) g gradNormSqSmooth
  have h_bochner_int :
      ∫ x, Δ_g (I := I) g gradNormSqSmooth x ∂μ =
        ∫ x, (2 * hessSqNorm x + 2 * RicAtGrad x +
            2 * g.inner x (Gf x) (GΔf x)) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact h_bochner x
  have h_int_hess2 : Integrable (fun x : M => 2 * hessSqNorm x) μ :=
    integrable_of_cont (continuous_const.mul h_hessSqNorm_cont)
  have h_int_ric2 : Integrable (fun x : M => 2 * RicAtGrad x) μ :=
    integrable_of_cont (continuous_const.mul h_RicAtGrad_cont)
  have h_int_inner2 :
      Integrable (fun x : M => 2 * g.inner x (Gf x) (GΔf x)) μ :=
    integrable_of_cont (continuous_const.mul hgrad_Δ_inner_cont)
  have h_int_first_two :
      Integrable (fun x : M => 2 * hessSqNorm x + 2 * RicAtGrad x) μ :=
    h_int_hess2.add h_int_ric2
  have h_sum :
      ∫ x, (2 * hessSqNorm x + 2 * RicAtGrad x +
            2 * g.inner x (Gf x) (GΔf x)) ∂μ =
        (∫ x, 2 * hessSqNorm x ∂μ) +
          (∫ x, 2 * RicAtGrad x ∂μ) +
          (∫ x, 2 * g.inner x (Gf x) (GΔf x) ∂μ) := by
    rw [integral_add h_int_first_two h_int_inner2,
        integral_add h_int_hess2 h_int_ric2]
  have h_pullout1 :
      ∫ x, 2 * hessSqNorm x ∂μ = 2 * (∫ x, hessSqNorm x ∂μ) :=
    integral_const_mul _ _
  have h_pullout2 :
      ∫ x, 2 * RicAtGrad x ∂μ = 2 * (∫ x, RicAtGrad x ∂μ) :=
    integral_const_mul _ _
  have h_pullout3 :
      ∫ x, 2 * g.inner x (Gf x) (GΔf x) ∂μ =
        2 * (∫ x, g.inner x (Gf x) (GΔf x) ∂μ) :=
    integral_const_mul _ _
  have h_main_zero :
      0 = 2 * (∫ x, hessSqNorm x ∂μ) +
            2 * (∫ x, RicAtGrad x ∂μ) +
            2 * (∫ x, g.inner x (Gf x) (GΔf x) ∂μ) := by
    rw [← h_pullout1, ← h_pullout2, ← h_pullout3, ← h_sum, ← h_bochner_int,
      h_LHS_zero]
  have h_eigen_inner :
      ∀ x : M, g.inner x (Gf x) (GΔf x) =
        -lam * g.inner x (Gf x) (Gf x) := by
    intro x
    have h_GΔf_apply : (GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x := by
      rw [hGΔf_def]; rfl
    have h_Gf_apply : (Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g f x := by
      rw [hGf_def]; rfl
    rw [h_GΔf_apply, h_Gf_apply]
    set d_f : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x with hd_f_def
    set d_Δf : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) (Δ_g (I := I) g hf) x
        with hd_Δf_def
    have h_lhs_eq :
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g (Δ_g (I := I) g hf) x)
          = d_Δf (gradFun (I := I) g f x) := by
      rw [hd_Δf_def]
      exact inner_gradFun_right (I := I) g (Δ_g (I := I) g hf) x
        (gradFun (I := I) g f x)
    have h_rhs_eq :
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
          = d_f (gradFun (I := I) g f x) := by
      rw [hd_f_def]
      exact inner_gradFun (I := I) g f x (gradFun (I := I) g f x)
    rw [h_lhs_eq, h_rhs_eq]
    have h_eq_fun : ∀ y : M, Δ_g (I := I) g hf y = ((-lam) • f) y := by
      intro y; exact hf_eigen y
    have h_eqOn_nhd : Δ_g (I := I) g hf =ᶠ[𝓝 x] ((-lam) • f) :=
      Filter.Eventually.of_forall h_eq_fun
    have h_d_Δf_eq : d_Δf = (-lam) • d_f := by
      rw [hd_Δf_def, hd_f_def]
      rw [Filter.EventuallyEq.mfderiv_eq h_eqOn_nhd]
      exact const_smul_mfderiv (hf.mdifferentiable (by simp) x) (-lam)
    rw [h_d_Δf_eq]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h_int_eigen_inner :
      ∫ x, g.inner x (Gf x) (GΔf x) ∂μ =
        -lam * ∫ x, g.inner x (Gf x) (Gf x) ∂μ := by
    have h_pt :
        (fun x : M => g.inner x (Gf x) (GΔf x)) =
          (fun x : M => -lam * g.inner x (Gf x) (Gf x)) := by
      funext x; exact h_eigen_inner x
    rw [h_pt, integral_const_mul]
  have h_green :
      ∫ x, g.inner x (Gf x) (Gf x) ∂μ =
        -∫ x, f x * Δ_g (I := I) g hf x ∂μ :=
    integral_inner_grad_self_eq_neg_integral_f_Δf (I := I) g hf
  have h_f_Δf_pt : ∀ x : M, f x * Δ_g (I := I) g hf x = -lam * (f x * f x) := by
    intro x
    rw [hf_eigen x]
    ring
  have h_int_f_Δf :
      ∫ x, f x * Δ_g (I := I) g hf x ∂μ =
        -lam * ∫ x, f x * f x ∂μ := by
    have h_pt :
        (fun x : M => f x * Δ_g (I := I) g hf x) =
          (fun x : M => -lam * (f x * f x)) := by
      funext x; exact h_f_Δf_pt x
    rw [h_pt, integral_const_mul]
  have h_int_grad_sq :
      ∫ x, g.inner x (Gf x) (Gf x) ∂μ =
        lam * ∫ x, f x * f x ∂μ := by
    rw [h_green, h_int_f_Δf]
    ring
  have h_int_hess_bound :
      ∫ x, (Δ_g (I := I) g hf x)^2 / n ∂μ ≤
        ∫ x, hessSqNorm x ∂μ := by
    apply integral_mono_of_nonneg
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : 0 ≤ (Δ_g (I := I) g hf x)^2 := sq_nonneg _
      exact div_nonneg h1 hn_pos.le
    · exact integrable_of_cont h_hessSqNorm_cont
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact h_hess_lower_bound x
  have h_inner_self_nonneg : ∀ x : M, 0 ≤ g.inner x (Gf x) (Gf x) := by
    intro x
    by_cases hv : (Gf : ∀ x, TangentSpace I x) x = 0
    · rw [hv]; simp
    · exact (g.pos x _ hv).le
  have h_int_ricci_bound :
      ∫ x, (n - 1) * K *
          g.inner x (Gf x) (Gf x) ∂μ ≤
        ∫ x, RicAtGrad x ∂μ := by
    apply integral_mono_of_nonneg
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h_prod1 : 0 ≤ (n - 1) * K := mul_nonneg hn_minus_one_pos.le hK.le
      exact mul_nonneg h_prod1 (h_inner_self_nonneg x)
    · exact integrable_of_cont h_RicAtGrad_cont
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact h_ricci_lower_bound x
  have h_Δf_sq_eq : ∀ x : M, (Δ_g (I := I) g hf x)^2 = lam^2 * (f x * f x) := by
    intro x
    rw [hf_eigen x]
    ring
  have h_int_Δf_sq :
      ∫ x, (Δ_g (I := I) g hf x)^2 / n ∂μ =
        (lam^2 / n) * ∫ x, f x * f x ∂μ := by
    have h_pt :
        (fun x : M => (Δ_g (I := I) g hf x)^2 / n) =
          (fun x : M => (lam^2 / n) * (f x * f x)) := by
      funext x
      rw [h_Δf_sq_eq x]
      field_simp
    rw [h_pt, integral_const_mul]
  have h_int_ricci_lower_simplified :
      ∫ x, (n - 1) * K *
          g.inner x (Gf x) (Gf x) ∂μ =
        ((n - 1) * K) * (lam * ∫ x, f x * f x ∂μ) := by
    have h_pt :
        (fun x : M => (n - 1) * K * g.inner x (Gf x) (Gf x)) =
          (fun x : M => ((n - 1) * K) * g.inner x (Gf x) (Gf x)) := by
      funext x; ring
    rw [h_pt, integral_const_mul, h_int_grad_sq]
  set S : ℝ := ∫ x, f x * f x ∂μ with hS_def
  have hS_pos : 0 < S := h_f_sq_pos
  have h_int_inner_grad_Δ : ∫ x, g.inner x (Gf x) (GΔf x) ∂μ = -lam * (lam * S) := by
    rw [h_int_eigen_inner, h_int_grad_sq, hS_def]
  have h_main_zero_subst :
      0 = 2 * (∫ x, hessSqNorm x ∂μ) +
            2 * (∫ x, RicAtGrad x ∂μ) -
            2 * lam^2 * S := by
    have := h_main_zero
    rw [h_int_inner_grad_Δ] at this
    linarith [this]
  have h_bochner_balanced :
      2 * lam^2 * S = 2 * (∫ x, hessSqNorm x ∂μ) +
            2 * (∫ x, RicAtGrad x ∂μ) := by
    linarith
  have h_hess_int_lower : (lam^2 / n) * S ≤ ∫ x, hessSqNorm x ∂μ := by
    have := h_int_hess_bound
    rw [h_int_Δf_sq] at this
    exact this
  have h_ric_int_lower : ((n - 1) * K) * (lam * S) ≤ ∫ x, RicAtGrad x ∂μ := by
    have := h_int_ricci_bound
    rw [h_int_ricci_lower_simplified] at this
    exact this
  have h_chain :
      2 * (lam^2 / n) * S + 2 * ((n - 1) * K) * (lam * S) ≤
        2 * lam^2 * S := by
    rw [h_bochner_balanced]
    linarith [h_hess_int_lower, h_ric_int_lower]
  have h_chain2 :
      (lam^2 / n) * S + ((n - 1) * K) * (lam * S) ≤ lam^2 * S := by
    linarith
  have h_chain3 :
      ((n - 1) * K) * (lam * S) ≤ lam^2 * S * (n - 1) / n := by
    have h1 : lam^2 * S - lam^2 / n * S = lam^2 * S * (n - 1) / n := by
      have hne : n ≠ 0 := ne_of_gt hn_pos
      field_simp
    linarith [h_chain2, h1]
  have hlam_S_pos : 0 < lam * S := mul_pos hlam_pos hS_pos
  have h_factor_pos : 0 < (n - 1) * (lam * S) := mul_pos hn_minus_one_pos hlam_S_pos
  have h_n_chain : n * (((n - 1) * K) * (lam * S)) ≤ lam^2 * S * (n - 1) := by
    have h1 : n * (lam^2 * S * (n - 1) / n) = lam^2 * S * (n - 1) := by
      field_simp
    have h2 : n * (((n - 1) * K) * (lam * S)) ≤ n * (lam^2 * S * (n - 1) / n) :=
      mul_le_mul_of_nonneg_left h_chain3 hn_pos.le
    linarith [h1, h2]
  have h_rearrange1 :
      n * (((n - 1) * K) * (lam * S)) = (n * K) * ((n - 1) * (lam * S)) := by ring
  have h_rearrange2 :
      lam^2 * S * (n - 1) = lam * ((n - 1) * (lam * S)) := by ring
  rw [h_rearrange1, h_rearrange2] at h_n_chain
  exact le_of_mul_le_mul_right (by linarith [h_n_chain]) h_factor_pos

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem g_inner_self_eq_sum_sq_inner_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (u : TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB_basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hB_eq : ∀ i, hB_basis i = B i)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    g.inner x u u =
      ∑ j : Fin (Module.finrank ℝ E), (g.inner x u (B j))^2 := by
  classical
  set c : Fin (Module.finrank ℝ E) → ℝ := fun j => hB_basis.repr u j with hc_def
  have hu_decomp : u =
      ∑ j : Fin (Module.finrank ℝ E),
        c j • (B j : TangentSpace I x) := by
    have h : (∑ i : Fin (Module.finrank ℝ E),
        hB_basis.repr u i • (hB_basis i : TangentSpace I x)) = u :=
      hB_basis.sum_repr u
    rw [← h]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hB_eq i]
  have h_coeff : ∀ k : Fin (Module.finrank ℝ E),
      g.inner x u (B k) = c k := by
    intro k
    rw [g.symm x u (B k)]
    have hgoal :
        g.inner x (B k) u =
          ∑ j : Fin (Module.finrank ℝ E), c j * g.inner x (B k) (B j) := by
      have h_apply : (g.inner x (B k)) u =
          (g.inner x (B k)) (∑ j : Fin (Module.finrank ℝ E),
            c j • (B j : TangentSpace I x)) :=
        congrArg (g.inner x (B k)) hu_decomp
      rw [h_apply]
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [(g.inner x (B k)).map_smul (c j) (B j), smul_eq_mul]
    rw [hgoal]
    rw [show (∑ j : Fin (Module.finrank ℝ E),
          c j * g.inner x (B k) (B j)) =
        ∑ j : Fin (Module.finrank ℝ E),
          c j * (if k = j then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hB_orth k j]]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hgoal :
      g.inner x u u = ∑ j : Fin (Module.finrank ℝ E),
        c j * g.inner x u (B j) := by
    have h_apply : (g.inner x u) u =
        (g.inner x u) (∑ j : Fin (Module.finrank ℝ E),
          c j • (B j : TangentSpace I x)) :=
      congrArg (g.inner x u) hu_decomp
    rw [h_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [(g.inner x u).map_smul (c j) (B j), smul_eq_mul]
  rw [hgoal]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_coeff j]
  ring

private theorem laplacian_sq_le_dim_mul_chartHessFrobeniusSq_pointwise
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) * chartHessFrobeniusSq (I := I) g f x := by
  classical
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hCS :
      (∑ i : Fin (Module.finrank ℝ E),
        abstractHessianLin (I := I) g f x (B i) (B i))^2 ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (abstractHessianLin (I := I) g f x (B i) (B j))^2 :=
    bilinForm_trace_sq_le_card_mul_frobenius_sq
      (V := TangentSpace I x) (ι := Fin (Module.finrank ℝ E))
      (abstractHessianLin (I := I) g f x) B
  rw [Fintype.card_fin] at hCS
  have hLHS_eq : ∑ i : Fin (Module.finrank ℝ E),
      abstractHessianLin (I := I) g f x (B i) (B i) =
      Δ_g (I := I) g hf x := by
    have h := sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf x B hB_orth
    refine h ▸ ?_
    refine Finset.sum_congr rfl ?_
    intro i _
    exact abstractHessianLin_apply (I := I) g f x (B i) (B i)
  rw [hLHS_eq] at hCS
  set T : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (LeviCivita (I := I) g).toFun
      (fun b : M => gradFun (I := I) g f b) x with hT_def
  have h_AH_eq_inner : ∀ v w : TangentSpace I x,
      abstractHessianLin (I := I) g f x v w =
        g.inner x (T v) w := by
    intro v w
    rw [abstractHessianLin_apply (I := I) g f x v w]
    rw [hT_def]
    rw [(abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x v w).symm]
  have hB_li : LinearIndependent ℝ B := by
    rw [linearIndependent_iff']
    intro s c hsum k hk_mem
    have h_zero : g.inner x (B k) (∑ j ∈ s, c j • B j) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ s, g.inner x (B k) (c j • B j) =
        c j * g.inner x (B k) (B j) := by
      intro j _
      rw [(g.inner x (B k)).map_smul (c j) (B j), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ s, c j * g.inner x (B k) (B j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp hpos
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set hB_basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hB_basis_def
  have hB_basis_eq : ∀ i, hB_basis i = B i := by
    intro i
    rw [hB_basis_def]
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have h_row : ∀ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
          (abstractHessianLin (I := I) g f x (B i) (B j))^2 =
        g.inner x (T (B i)) (T (B i)) := by
    intro i
    rw [show (∑ j : Fin (Module.finrank ℝ E),
            (abstractHessianLin (I := I) g f x (B i) (B j))^2) =
        ∑ j : Fin (Module.finrank ℝ E),
            (g.inner x (T (B i)) (B j))^2 from by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_AH_eq_inner (B i) (B j)]]
    exact (g_inner_self_eq_sum_sq_inner_orthonormal
      (g := g) (x := x) (u := T (B i)) (B := B)
      (hB_basis := hB_basis) (hB_eq := hB_basis_eq) (hB_orth := hB_orth)).symm
  have h_full_sum :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (abstractHessianLin (I := I) g f x (B i) (B j))^2 =
        frobeniusSq_grad_vector (I := I) g
          (fun b : M => gradFun (I := I) g f b) x := by
    rw [frobeniusSq_grad_vector_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact h_row i
  rw [h_full_sum] at hCS
  rw [frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x] at hCS
  exact hCS

omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciTensor_grad_grad_contMDiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b
        (gradFun (I := I) g f b) (gradFun (I := I) g f b)) := by
  classical
  have hRic := ricciTensor_contMDiff (I := I) g
  have hG := gradFun_contMDiff_total_section (I := I) g hf
  have happ :
      ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ricciTensor (I := I) g m
              (gradFun (I := I) g f m) (gradFun (I := I) g f m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hRic hG hG
  intro m
  have hpm := happ m
  rw [Bundle.contMDiffAt_totalSpace] at hpm
  exact hpm.2

omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciTensor_grad_grad_continuous
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun b : M => ricciTensor (I := I) g b
      (gradFun (I := I) g f b) (gradFun (I := I) g f b)) :=
  (ricciTensor_grad_grad_contMDiff (I := I) g hf).continuous

theorem chartHessFrobeniusSq_continuous
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun b : M => chartHessFrobeniusSq (I := I) g f b) := by
  classical
  set Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g (I := I) g hf with hGf_def
  have hΔf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (Δ_g (I := I) g hf) :=
    Δ_g_contMDiff (I := I) g hf
  set GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g (I := I) g hΔf with hGΔf_def
  have h1 : Continuous (Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf)) :=
    (Δ_g_contMDiff (I := I) g (normGradSqFun_contMDiff (I := I) g hf)).continuous
  have h2 : Continuous (fun b : M => ricciTensor (I := I) g b
      (gradFun (I := I) g f b) (gradFun (I := I) g f b)) :=
    ricciTensor_grad_grad_continuous (I := I) g hf
  have h3 : Continuous (fun b : M => g.inner b
      ((Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b)
      ((GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g Gf GΔf
  have h_bochner_isolate : ∀ x : M,
      chartHessFrobeniusSq (I := I) g f x =
        ((Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x) -
          2 * ricciTensor (I := I) g x
            (gradFun (I := I) g f x) (gradFun (I := I) g f x) -
          2 * g.inner x
            ((Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) / 2 := by
    intro x
    have hB := bochner_pointwise_concrete_metric_unconditional (I := I) g hf x
    have hGf_x : (Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g f x := by
      rw [hGf_def]; rfl
    have hGΔf_x : (GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x := by
      rw [hGΔf_def]; rfl
    rw [hGf_x, hGΔf_x]
    linarith [hB]
  have hRHS_cont : Continuous (fun x : M =>
      ((Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x) -
        2 * ricciTensor (I := I) g x
          (gradFun (I := I) g f x) (gradFun (I := I) g f x) -
        2 * g.inner x
          ((Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) / 2) := by
    refine ((h1.sub (continuous_const.mul h2)).sub
      (continuous_const.mul h3)).div_const 2
  refine hRHS_cont.congr ?_
  intro x
  exact (h_bochner_isolate x).symm

theorem lichnerowicz_eigenvalue_ge_dim_mul_curvature_of_closed
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hn_ge_two : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {lam : ℝ} (hlam_pos : 0 < lam)
    (hf_eigen : ∀ x : M, Δ_g (I := I) g hf x = -lam * f x)
    (h_ricci : ∀ x : M, ∀ X : TangentSpace I x,
      ((Module.finrank ℝ E : ℝ) - 1) * K * g.inner x X X ≤
        ricciTensor (I := I) g x X X)
    (h_f_sq_pos : 0 < ∫ x, f x * f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :
    (Module.finrank ℝ E : ℝ) * K ≤ lam := by
  classical
  have hgrad_norm_sq_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => g.inner x
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g hf) (grad_g (I := I) g hf)
  have h_frob_cont :
      Continuous (fun x : M => chartHessFrobeniusSq (I := I) g f x) :=
    chartHessFrobeniusSq_continuous (I := I) g hf
  have h_ricci_cont :
      Continuous (fun x : M => ricciTensor (I := I) g x
        (gradFun (I := I) g f x) (gradFun (I := I) g f x)) :=
    ricciTensor_grad_grad_continuous (I := I) g hf
  have h_bochner_section : ∀ x : M,
      Δ_g (I := I) g hgrad_norm_sq_smooth x =
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciTensor (I := I) g x
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
          2 * g.inner x
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g (Δ_g_contMDiff (I := I) g hf) :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    have hB := bochner_pointwise_concrete_metric_unconditional (I := I) g hf x
    have hGf_x : (grad_g (I := I) g hf :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g f x := grad_g_apply (I := I) g hf x
    have hGΔf_x : (grad_g (I := I) g (Δ_g_contMDiff (I := I) g hf) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x :=
      grad_g_apply (I := I) g (Δ_g_contMDiff (I := I) g hf) x
    rw [hGf_x, hGΔf_x]
    have hLHS_eq : Δ_g (I := I) g hgrad_norm_sq_smooth x =
        Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x := rfl
    rw [hLHS_eq]
    exact hB
  have h_hess_lower_bound : ∀ x : M,
      (Δ_g (I := I) g hf x)^2 / (Module.finrank ℝ E : ℝ) ≤
        chartHessFrobeniusSq (I := I) g f x := by
    intro x
    have hne : (Module.finrank ℝ E : ℕ) ≠ 0 := NeZero.ne _
    have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero hne
      exact_mod_cast this
    have h := laplacian_sq_le_dim_mul_chartHessFrobeniusSq_pointwise
      (I := I) g hf x
    exact (div_le_iff₀ hpos).mpr (by linarith [h])
  exact lichnerowicz_inequality (I := I) (M := M) g hn_ge_two hK hf hlam_pos
    hf_eigen hgrad_norm_sq_smooth
    (fun x => chartHessFrobeniusSq (I := I) g f x) h_frob_cont
    (fun x => ricciTensor (I := I) g x
      ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    (by
      refine h_ricci_cont.congr ?_
      intro x
      simp only [grad_g_apply])
    h_bochner_section
    h_hess_lower_bound
    (by
      intro x
      exact h_ricci x ((grad_g (I := I) g hf :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    h_f_sq_pos

end Laplacian
end Analysis
end DifferentialGeometry

end
