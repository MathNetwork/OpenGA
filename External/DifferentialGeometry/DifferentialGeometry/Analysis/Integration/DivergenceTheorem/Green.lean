import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Closed
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Proper
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Integration.DivergenceTheorem.Gradient


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_supp : HasCompactSupport h) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hh with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hh hh_supp
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hf X hX_cs
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g hf X x]
    change g.inner x (X x) ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergence_g (I := I) g X x = f x * Δ_g (I := I) g hh x := by
    intro x
    rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * Δ_g (I := I) g hh x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

private theorem integral_inner_grad_eq_neg_integral_smul_laplacian'
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hf_supp : HasCompactSupport f) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hf with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g hf hf_supp
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hh X hX_cs
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X h x =
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hh :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g hh X x]
  have hRHS_eq : ∀ x : M,
      h x * divergence_g (I := I) g X x = h x * Δ_g (I := I) g hf x := by
    intro x; rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X h x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hh :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, h x * divergence_g (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, h x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

theorem green_second_integral_smul_laplacian_sub_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ∫ x, (f x * Δ_g (I := I) g hh x - h x * Δ_g (I := I) g hf x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  have hh_cs : HasCompactSupport h := HasCompactSupport.of_compactSpace _
  have h1 := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g hf hh hh_cs
  have h2 := integral_inner_grad_eq_neg_integral_smul_laplacian' (I := I) g hf hh hf_cs
  have h_eq : ∫ x, f x * Δ_g (I := I) g hh x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, h x * Δ_g (I := I) g hf x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have : -∫ x, f x * Δ_g (I := I) g hh x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          -∫ x, h x * Δ_g (I := I) g hf x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [← h1, h2]
    linarith
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hΔh_cont : Continuous (Δ_g (I := I) g hh) :=
    (Δ_g_contMDiff (I := I) g hh).continuous
  have hΔf_cont : Continuous (Δ_g (I := I) g hf) :=
    (Δ_g_contMDiff (I := I) g hf).continuous
  have hf_cont : Continuous f := hf.continuous
  have hh_cont : Continuous h := hh.continuous
  have h_int_fΔh : Integrable (fun x : M => f x * Δ_g (I := I) g hh x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => f x * Δ_g (I := I) g hh x) :=
      hf_cont.mul hΔh_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_hΔf : Integrable (fun x : M => h x * Δ_g (I := I) g hf x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => h x * Δ_g (I := I) g hf x) :=
      hh_cont.mul hΔf_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub h_int_fΔh h_int_hΔf]
  rw [h_eq, sub_self]










theorem expNegWeightedGreen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f q : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ q) :
    ∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hq x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, q x *
        Δ_g (I := I) g
          (by
            simpa using Real.contDiff_exp.contMDiff.comp hf.neg) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let expNeg : M → ℝ := fun x => Real.exp (-(f x))
  have hexp : ContMDiff I 𝓘(ℝ, ℝ) ∞ expNeg := by
    simpa [expNeg] using Real.contDiff_exp.contMDiff.comp hf.neg
  have hgreen := green_second_integral_smul_laplacian_sub_eq_zero
    (I := I) g (f := expNeg) (h := q) hexp hq
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hΔq_cont : Continuous (Δ_g (I := I) g hq) :=
    (Δ_g_contMDiff (I := I) g hq).continuous
  have hΔexp_cont : Continuous (Δ_g (I := I) g hexp) :=
    (Δ_g_contMDiff (I := I) g hexp).continuous
  have hexp_cont : Continuous expNeg := hexp.continuous
  have hq_cont : Continuous q := hq.continuous
  have h_int_expΔq :
      Integrable (fun x : M => expNeg x * Δ_g (I := I) g hq x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => expNeg x * Δ_g (I := I) g hq x) :=
      hexp_cont.mul hΔq_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_int_qΔexp :
      Integrable (fun x : M => q x * Δ_g (I := I) g hexp x)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M => q x * Δ_g (I := I) g hexp x) :=
      hq_cont.mul hΔexp_cont
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero :
      ∫ x, expNeg x * Δ_g (I := I) g hq x -
          q x * Δ_g (I := I) g hexp x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    simpa [expNeg] using hgreen
  rw [integral_sub h_int_expΔq h_int_qΔexp] at hzero
  have h_eq :
      ∫ x, expNeg x * Δ_g (I := I) g hq x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, q x * Δ_g (I := I) g hexp x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    linarith
  simpa [expNeg] using h_eq



theorem expNegLap
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    Δ_g (I := I) g
        (by
          simpa using Real.contDiff_exp.contMDiff.comp hf.neg) x =
      Real.exp (-(f x)) *
        (-Δ_g (I := I) g hf x +
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
  classical
  let expNeg : M → ℝ := fun y => Real.exp (-(f y))
  let phi : M → ℝ := fun y => -expNeg y
  have hexp : ContMDiff I 𝓘(ℝ, ℝ) ∞ expNeg := by
    simpa [expNeg] using Real.contDiff_exp.contMDiff.comp hf.neg
  have hphi : ContMDiff I 𝓘(ℝ, ℝ) ∞ phi := by
    simpa [phi] using hexp.neg
  have hsection :
      (grad_g (I := I) g hexp :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
        smoothSmul (I := I) phi hphi (grad_g (I := I) g hf) := by
    ext y
    rw [grad_g_apply, smoothSmul_apply, grad_g_apply]
    change gradFun (I := I) g (fun y : M => Real.exp (-(f y))) y =
      phi y • gradFun (I := I) g f y
    dsimp [phi, expNeg]
    exact gradFun_exp_neg (I := I) g (hf.mdifferentiable (by simp) y)
  have hactExp := tangentSectionAction_grad_g_eq_inner
    (I := I) g hexp (grad_g (I := I) g hf) x
  rw [hsection] at hactExp
  have hactPhi :
      tangentSectionAction (I := I) (grad_g (I := I) g hf) phi x =
        Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    have hneg :
        tangentSectionAction (I := I) (grad_g (I := I) g hf) phi x =
          -tangentSectionAction (I := I) (grad_g (I := I) g hf) expNeg x := by
      have hmdiff_exp : MDifferentiableAt I 𝓘(ℝ, ℝ) expNeg x :=
        hexp.mdifferentiable (by simp) x
      have hmf :
          mfderiv I 𝓘(ℝ, ℝ) phi x =
            -mfderiv I 𝓘(ℝ, ℝ) expNeg x := by
        simpa [phi] using hmdiff_exp.hasMFDerivAt.neg.mfderiv
      change mfderiv I 𝓘(ℝ, ℝ) phi x
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        -(mfderiv I 𝓘(ℝ, ℝ) expNeg x
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      rw [hmf]
      rfl
    rw [hneg, hactExp]
    rw [smoothSmul_apply, grad_g_apply]
    dsimp [phi, expNeg]
    simp [smul_eq_mul]
  change divergence_g (I := I) g
      (grad_g (I := I) g hexp) x = _
  rw [hsection]
  rw [divergence_g_smoothSmul (I := I) g phi hphi (grad_g (I := I) g hf) x]
  rw [hactPhi]
  simp [Δ_g, phi, expNeg]
  ring



theorem expNegGreen
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f q : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ q) :
    ∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hq x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, q x *
        (Real.exp (-(f x)) *
          (-Δ_g (I := I) g hf x +
            g.inner x ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [expNegWeightedGreen (I := I) g hf hq]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  change q x *
      Δ_g (I := I) g
        (by
          simpa using Real.contDiff_exp.contMDiff.comp hf.neg) x =
    q x *
      (Real.exp (-(f x)) *
        (-Δ_g (I := I) g hf x +
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
  rw [expNegLap (I := I) g hf x]



theorem expNegLap_eq_gradSq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, Real.exp (-(f x)) *
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let expNeg : M → ℝ := fun x => Real.exp (-(f x))
  have hexp : ContMDiff I 𝓘(ℝ, ℝ) ∞ expNeg := by
    simpa [expNeg] using Real.contDiff_exp.contMDiff.comp hf.neg
  have hgreen :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g (f := expNeg) (h := f) hexp hf
      (HasCompactSupport.of_compactSpace f)
  have hleft :
      ∫ x, g.inner x ((grad_g (I := I) g hexp :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, -(Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro x
    have hfx : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
      hf.mdifferentiable (by simp) x
    change
      g.inner x ((grad_g (I := I) g hexp :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        -(Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    rw [grad_g_apply (I := I) g hexp x, grad_g_apply (I := I) g hf x]
    dsimp [expNeg]
    change
      g.inner x (gradFun (I := I) g (fun y : M => Real.exp (-(f y))) x)
          (gradFun (I := I) g f x) =
        -(Real.exp (-(f x)) *
          g.inner x (gradFun (I := I) g f x)
            (gradFun (I := I) g f x))
    rw [gradFun_exp_neg (I := I) g hfx]
    rw [map_smul]
    rw [ContinuousLinearMap.smul_apply]
    rw [smul_eq_mul]
    ring_nf
  have hneg :
      -∫ x, Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, Real.exp (-(f x)) * Δ_g (I := I) g hf x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa [integral_neg, expNeg] using hleft.symm.trans hgreen
  exact (neg_injective hneg).symm




theorem expNegIBP
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hlap :
      Integrable (fun x : M =>
        Real.exp (-(f x)) * Δ_g (I := I) g hf x)
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hgrad :
      Integrable (fun x : M =>
        Real.exp (-(f x)) *
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, Real.exp (-(f x)) *
        (Δ_g (I := I) g hf x -
          g.inner x ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have hbase := expNegLap_eq_gradSq (I := I) g hf
  have hpoint :
      (fun x : M =>
        Real.exp (-(f x)) *
          (Δ_g (I := I) g hf x -
            g.inner x ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) =
      fun x : M =>
        Real.exp (-(f x)) * Δ_g (I := I) g hf x -
          Real.exp (-(f x)) *
            g.inner x ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    funext x
    ring
  rw [hpoint]
  rw [integral_sub hlap hgrad]
  rw [hbase, sub_self]

end DivergenceTheorem
end Integral
end DifferentialGeometry
