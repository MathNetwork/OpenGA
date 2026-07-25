import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.VariationalIdentity


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BochnerPolarised

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma grad_g_congr
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf₁ hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    (grad_g (I := I) g hf₁ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (grad_g (I := I) g hf₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
  refine ContMDiffSection.ext (fun _ => rfl)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma Δ_g_congr_func
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf₁ hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g hf₁ x = Δ_g (I := I) g hf₂ x := by
  have h := grad_g_congr (I := I) g hf₁ hf₂
  change divergence_g (I := I) g (grad_g (I := I) g hf₁) x =
    divergence_g (I := I) g (grad_g (I := I) g hf₂) x
  rw [h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma grad_g_congr_funext
    (g : SmoothRiemannianMetric I M) {f₁ f₂ : M → ℝ}
    (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁) (hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂)
    (h_eq : f₁ = f₂) :
    (grad_g (I := I) g hf₁ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (grad_g (I := I) g hf₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
  refine ContMDiffSection.ext (fun x => ?_)
  change gradFun (I := I) g f₁ x = gradFun (I := I) g f₂ x
  rw [h_eq]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma Δ_g_congr_funext
    (g : SmoothRiemannianMetric I M) {f₁ f₂ : M → ℝ}
    (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁) (hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂)
    (h_eq : f₁ = f₂) (x : M) :
    Δ_g (I := I) g hf₁ x = Δ_g (I := I) g hf₂ x := by
  have h := grad_g_congr_funext (I := I) g hf₁ hf₂ h_eq
  change divergence_g (I := I) g (grad_g (I := I) g hf₁) x =
    divergence_g (I := I) g (grad_g (I := I) g hf₂) x
  rw [h]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradFun_neg
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    gradFun (I := I) g (fun y : M => -f y) x =
      -gradFun (I := I) g f x := by
  have h_neg : (fun y : M => -f y) = (-1 : ℝ) • f := by
    funext y; simp [Pi.smul_apply]
  rw [h_neg]
  rw [gradFun_const_smul (I := I) g (-1 : ℝ) hf]
  rw [neg_smul, one_smul]

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradFun_sub
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    gradFun (I := I) g (fun y : M => f y - h y) x =
      gradFun (I := I) g f x - gradFun (I := I) g h x := by
  have h_sub : (fun y : M => f y - h y) = (fun y : M => f y + -h y) := by
    funext y; ring
  rw [h_sub]
  have h_neg_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => -h y) x := by
    have : (fun y : M => -h y) = (-1 : ℝ) • h := by funext y; simp [Pi.smul_apply]
    rw [this]
    exact hh.const_smul (-1 : ℝ)
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hf h_neg_diff]
  rw [gradFun_neg (I := I) g hh]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma Δ_g_neg
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∀ (hneg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => -f y)) (x : M),
    Δ_g (I := I) g hneg x = -Δ_g (I := I) g hf x := by
  intro hneg x
  have h_add := Δ_g_add (I := I) g hf hneg x
  have h_sum_eq_zero : (fun y : M => f y + -f y) = (fun _ : M => (0 : ℝ)) := by
    funext y; ring
  have h_zero_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) :=
    contMDiff_const
  have hΔ_sum_eq_zero :
      Δ_g (I := I) g (hf.add hneg) x = 0 := by
    rw [Δ_g_congr_funext (I := I) g (hf.add hneg) h_zero_smooth h_sum_eq_zero x]
    exact Δ_g_const (I := I) g (0 : ℝ) x
  linarith [h_add, hΔ_sum_eq_zero]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
lemma Δ_g_sub
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ∀ (hsub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => f y - h y)) (x : M),
    Δ_g (I := I) g hsub x = Δ_g (I := I) g hf x - Δ_g (I := I) g hh x := by
  intro hsub x
  have hneg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => -h y) := by
    have h_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (-1 : ℝ)) := contMDiff_const
    have h_smul := h_const.mul hh
    refine h_smul.congr ?_
    intro y
    simp
  have h_sub_eq_add_neg : (fun y : M => f y - h y) = (fun y : M => f y + -h y) := by
    funext y; ring
  rw [Δ_g_congr_funext (I := I) g hsub (hf.add hneg) h_sub_eq_add_neg x]
  rw [Δ_g_add (I := I) g hf hneg x]
  rw [Δ_g_neg (I := I) g hh hneg x]
  ring

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma normGradSqFun_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    normGradSqFun (I := I) g (fun y : M => φ y + v y) x -
        normGradSqFun (I := I) g (fun y : M => φ y - v y) x =
      4 * g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) := by
  unfold normGradSqFun
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (φ : M → ℝ) x :=
    φ.contMDiff.mdifferentiable (by simp) x
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (v : M → ℝ) x :=
    v.contMDiff.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hφ_diff hv_diff]
  rw [gradFun_sub (I := I) g hφ_diff hv_diff]
  exact g_inner_polar (I := I) (M := M) g x
    (gradFun (I := I) g (φ : M → ℝ) x)
    (gradFun (I := I) g (v : M → ℝ) x)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma ricciTensor_grad_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    ricciTensor (I := I) g x
        (gradFun (I := I) g (fun y : M => φ y + v y) x)
        (gradFun (I := I) g (fun y : M => φ y + v y) x) -
      ricciTensor (I := I) g x
        (gradFun (I := I) g (fun y : M => φ y - v y) x)
        (gradFun (I := I) g (fun y : M => φ y - v y) x) =
      4 * ricciTensor (I := I) g x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) := by
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (φ : M → ℝ) x :=
    φ.contMDiff.mdifferentiable (by simp) x
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (v : M → ℝ) x :=
    v.contMDiff.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hφ_diff hv_diff]
  rw [gradFun_sub (I := I) g hφ_diff hv_diff]
  exact ricciTensor_polar (I := I) (M := M) g x
    (gradFun (I := I) g (φ : M → ℝ) x)
    (gradFun (I := I) g (v : M → ℝ) x)

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma g_inner_grad_lap_polar
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M)
    (hφv_add : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y))
    (hφv_sub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y)) :
    g.inner x
        (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x)
        (gradFun (I := I) g (Δ_g (I := I) g hφv_add) x) -
      g.inner x
        (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x)
        (gradFun (I := I) g (Δ_g (I := I) g hφv_sub) x) =
      2 * (g.inner x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
          g.inner x
            (gradFun (I := I) g (v : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)) := by
  classical
  have hφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (φ : M → ℝ) x :=
    φ.contMDiff.mdifferentiable (by simp) x
  have hv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (v : M → ℝ) x :=
    v.contMDiff.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hφ_diff hv_diff]
  rw [gradFun_sub (I := I) g hφ_diff hv_diff]
  set Δφ : M → ℝ := Δ_g (I := I) g φ.contMDiff with hΔφ_def
  set Δv : M → ℝ := Δ_g (I := I) g v.contMDiff with hΔv_def
  have hΔφ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Δφ :=
    Δ_g_contMDiff (I := I) g φ.contMDiff
  have hΔv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Δv :=
    Δ_g_contMDiff (I := I) g v.contMDiff
  have h_Δ_add_func :
      (fun y : M => Δ_g (I := I) g hφv_add y) = (fun y : M => Δφ y + Δv y) := by
    funext y; exact Δ_g_add (I := I) g φ.contMDiff v.contMDiff y
  have h_Δ_sub_func :
      (fun y : M => Δ_g (I := I) g hφv_sub y) = (fun y : M => Δφ y - Δv y) := by
    funext y; exact Δ_g_sub (I := I) g φ.contMDiff v.contMDiff hφv_sub y
  have h_grad_Δ_add :
      gradFun (I := I) g (Δ_g (I := I) g hφv_add) x =
      gradFun (I := I) g (fun y : M => Δφ y + Δv y) x := by
    rw [show (Δ_g (I := I) g hφv_add : M → ℝ) = (fun y : M => Δφ y + Δv y) from
      h_Δ_add_func]
  have h_grad_Δ_sub :
      gradFun (I := I) g (Δ_g (I := I) g hφv_sub) x =
      gradFun (I := I) g (fun y : M => Δφ y - Δv y) x := by
    rw [show (Δ_g (I := I) g hφv_sub : M → ℝ) = (fun y : M => Δφ y - Δv y) from
      h_Δ_sub_func]
  rw [h_grad_Δ_add, h_grad_Δ_sub]
  have hΔφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) Δφ x :=
    hΔφ_smooth.mdifferentiable (by simp) x
  have hΔv_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) Δv x :=
    hΔv_smooth.mdifferentiable (by simp) x
  rw [DifferentialGeometry.Integral.Connection.gradFun_add (I := I) g hΔφ_diff hΔv_diff]
  rw [gradFun_sub (I := I) g hΔφ_diff hΔv_diff]
  set u : TangentSpace I x := gradFun (I := I) g (φ : M → ℝ) x with hu_def
  set w : TangentSpace I x := gradFun (I := I) g (v : M → ℝ) x with hw_def
  set p : TangentSpace I x := gradFun (I := I) g Δφ x with hp_def
  set q : TangentSpace I x := gradFun (I := I) g Δv x with hq_def
  have hp1 : g.inner x (u + w) (p + q) =
      g.inner x u p + g.inner x u q + g.inner x w p + g.inner x w q := by
    rw [ContinuousLinearMap.map_add (g.inner x) u w]
    rw [ContinuousLinearMap.add_apply]
    rw [(g.inner x u).map_add, (g.inner x w).map_add]
    ring
  have hp2 : g.inner x (u - w) (p - q) =
      g.inner x u p - g.inner x u q - g.inner x w p + g.inner x w q := by
    rw [ContinuousLinearMap.map_sub (g.inner x) u w]
    rw [ContinuousLinearMap.sub_apply]
    rw [(g.inner x u).map_sub, (g.inner x w).map_sub]
    ring
  rw [hp1, hp2]
  ring

omit [CompactSpace M] in
theorem bochner_polarised_pointwise
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯)
    (hφv_add : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y))
    (hφv_sub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y))
    (h_gphi_gv_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun y : M => g.inner y (gradFun (I := I) g (φ : M → ℝ) y)
          (gradFun (I := I) g (v : M → ℝ) y)))
    (x : M) :
    Δ_g (I := I) g h_gphi_gv_smooth x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
        g.inner x
          (gradFun (I := I) g (v : M → ℝ) x)
          (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x) +
        2 * hessPairingChart (I := I) g φ v x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) := by
  classical
  have hΔ_add := bochner_pointwise_concrete_metric_unconditional
    (I := I) g hφv_add x
  have hΔ_sub := bochner_pointwise_concrete_metric_unconditional
    (I := I) g hφv_sub x

  have hpolar_norm := normGradSqFun_polar (I := I) (M := M) g φ v x

  set N1 : M → ℝ := normGradSqFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y)
    with hN1_def
  set N2 : M → ℝ := normGradSqFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y)
    with hN2_def

  have hN1_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ N1 :=
    normGradSqFun_contMDiff (I := I) g hφv_add
  have hN2_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ N2 :=
    normGradSqFun_contMDiff (I := I) g hφv_sub

  have hN_sub_eq : ∀ y : M,
      (N1 y - N2 y) = 4 * g.inner y
        (gradFun (I := I) g (φ : M → ℝ) y)
        (gradFun (I := I) g (v : M → ℝ) y) :=
    fun y => normGradSqFun_polar (I := I) (M := M) g φ v y

  have hN_sub_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => N1 y - N2 y) :=
    hN1_smooth.sub hN2_smooth

  have h_4gphi_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : M => 4 * g.inner y
        (gradFun (I := I) g (φ : M → ℝ) y)
        (gradFun (I := I) g (v : M → ℝ) y)) := by
    have h_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (4 : ℝ)) := contMDiff_const
    exact h_const.mul h_gphi_gv_smooth

  have h_Δ_N_sub := Δ_g_sub (I := I) g hN1_smooth hN2_smooth hN_sub_smooth x

  have hN_eq_4ginner :
      (fun y : M => N1 y - N2 y) =
      (fun y : M => 4 * g.inner y
        (gradFun (I := I) g (φ : M → ℝ) y)
        (gradFun (I := I) g (v : M → ℝ) y)) := by
    funext y; exact hN_sub_eq y

  have h_Δ_N_sub_eq_Δ_4ginner :
      Δ_g (I := I) g hN_sub_smooth x =
      Δ_g (I := I) g h_4gphi_smooth x := by
    rw [Δ_g_def, Δ_g_def]
    have h_grad_eq :
        (grad_g (I := I) g hN_sub_smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
        (grad_g (I := I) g h_4gphi_smooth :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
      apply ContMDiffSection.coe_inj
      funext y
      rw [grad_g_apply, grad_g_apply]
      change gradFun (I := I) g (fun z : M => N1 z - N2 z) y =
        gradFun (I := I) g (fun z : M => 4 * g.inner z
          (gradFun (I := I) g (φ : M → ℝ) z)
          (gradFun (I := I) g (v : M → ℝ) z)) y
      rw [hN_eq_4ginner]
    rw [h_grad_eq]

  have h_const_smul_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (4 : ℝ)) := contMDiff_const

  have h_Δ_4ginner_eq :
      Δ_g (I := I) g h_4gphi_smooth x = 4 * Δ_g (I := I) g h_gphi_gv_smooth x := by
    have h_witness_eq :
        Δ_g (I := I) g h_4gphi_smooth x =
        Δ_g (I := I) g
          (h_const_smul_smooth.mul h_gphi_gv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun y : M => 4 * g.inner y
              (gradFun (I := I) g (φ : M → ℝ) y)
              (gradFun (I := I) g (v : M → ℝ) y))) x :=
      Δ_g_congr_func (I := I) g h_4gphi_smooth _ x
    rw [h_witness_eq]
    rw [Δ_g_smul_eq (I := I) (M := M) g h_const_smul_smooth h_gphi_gv_smooth x]
    have h_grad_const_zero :
        gradFun (I := I) g (fun _ : M => (4 : ℝ)) x = (0 : TangentSpace I x) :=
      DifferentialGeometry.Integral.DivergenceTheorem.gradFun_const
        (I := I) g (4 : ℝ) x
    rw [h_grad_const_zero]
    rw [show g.inner x (0 : TangentSpace I x) = (0 : TangentSpace I x →L[ℝ] ℝ) from
      map_zero _]
    have hΔ_const_4 :
        Δ_g (I := I) g h_const_smul_smooth x = 0 := by
      have h_witness :
          Δ_g (I := I) g h_const_smul_smooth x =
          Δ_g (I := I) g (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (4 : ℝ))) x :=
        Δ_g_congr_func (I := I) g h_const_smul_smooth _ x
      rw [h_witness]
      exact Δ_g_const (I := I) g (4 : ℝ) x
    rw [hΔ_const_4]
    simp only [ContinuousLinearMap.zero_apply, mul_zero, add_zero]

  have h_Δ_4ginner_eq_sub :
      4 * Δ_g (I := I) g h_gphi_gv_smooth x =
      Δ_g (I := I) g hN1_smooth x - Δ_g (I := I) g hN2_smooth x := by
    rw [← h_Δ_4ginner_eq]
    rw [← h_Δ_N_sub_eq_Δ_4ginner]
    exact h_Δ_N_sub

  have hN1_witness_eq : hN1_smooth = normGradSqFun_contMDiff (I := I) g hφv_add := rfl
  have hN2_witness_eq : hN2_smooth = normGradSqFun_contMDiff (I := I) g hφv_sub := rfl

  have hΔN1 :
      Δ_g (I := I) g hN1_smooth x =
        2 * chartHessFrobeniusSq (I := I) g
              (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x +
          2 * ricciTensor (I := I) g x
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x)
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x) +
          2 * g.inner x
              (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x)
              (gradFun (I := I) g (Δ_g (I := I) g hφv_add) x) := by
    rw [hN1_witness_eq]
    exact hΔ_add

  have hΔN2 :
      Δ_g (I := I) g hN2_smooth x =
        2 * chartHessFrobeniusSq (I := I) g
              (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x +
          2 * ricciTensor (I := I) g x
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x)
                (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x) +
          2 * g.inner x
              (gradFun (I := I) g (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x)
              (gradFun (I := I) g (Δ_g (I := I) g hφv_sub) x) := by
    rw [hN2_witness_eq]
    exact hΔ_sub

  have h_hessPolar :
      chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) x -
        chartHessFrobeniusSq (I := I) g
          (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) x =
      4 * hessPairingChart (I := I) g φ v x :=
    chartHessFrobeniusSq_polar_eq_hessPairing (I := I) (M := M) g φ v x

  have h_ricciPolar :=
    ricciTensor_grad_polar (I := I) (M := M) g φ v x

  have h_gradLapPolar :=
    g_inner_grad_lap_polar (I := I) (M := M) g φ v x hφv_add hφv_sub

  have key :
      4 * Δ_g (I := I) g h_gphi_gv_smooth x =
        8 * hessPairingChart (I := I) g φ v x +
          8 * ricciTensor (I := I) g x
                (gradFun (I := I) g (φ : M → ℝ) x)
                (gradFun (I := I) g (v : M → ℝ) x) +
          4 * (g.inner x
                (gradFun (I := I) g (φ : M → ℝ) x)
                (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x) +
              g.inner x
                (gradFun (I := I) g (v : M → ℝ) x)
                (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)) := by
    rw [h_Δ_4ginner_eq_sub]
    rw [hΔN1, hΔN2]
    linarith [h_hessPolar, h_ricciPolar, h_gradLapPolar]

  linarith [key]

omit [CompactSpace M] in
theorem bochner_polarised_pointwise_oneSubLap
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯)
    (hφv_add : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y))
    (hφv_sub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y))
    (h_gphi_gv_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun y : M => g.inner y (gradFun (I := I) g (φ : M → ℝ) y)
          (gradFun (I := I) g (v : M → ℝ) y)))
    (x : M) :
    g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) -
      Δ_g (I := I) g h_gphi_gv_smooth x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (v : M → ℝ) x)
        - g.inner x
            (gradFun (I := I) g (v : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g φ.contMDiff) x)
        - g.inner x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (Δ_g (I := I) g v.contMDiff) x)
        - 2 * hessPairingChart (I := I) g φ v x
        - 2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) := by
  rw [bochner_polarised_pointwise (I := I) (M := M) g φ v hφv_add hφv_sub
    h_gphi_gv_smooth x]
  ring

end BochnerPolarised
end Laplacian
end Analysis
end DifferentialGeometry

end
