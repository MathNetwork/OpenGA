import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Curvature.Tensoriality
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame.Smoothness
import OpenGALib.Riemannian.Operators.Bochner.HessianExpansion
import OpenGALib.Riemannian.Operators.Bochner.BochnerExpansion
import OpenGALib.Riemannian.Operators.Bochner.PerSummand
import OpenGALib.Util.MFDeriv
import OpenGALib.Util.Notation
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Bochner–Weitzenböck identity

For a smooth scalar $f : M \to \mathbb{R}$ on a Riemannian manifold $(M, g)$:
$$\tfrac{1}{2}\,\Delta_g \, |\nabla f|_g^2
  = |\nabla^2 f|_g^2
    + \langle \nabla f,\, \nabla\,\Delta_g f\rangle_g
    + \mathrm{Ric}(\nabla f,\, \nabla f).$$

Reference: Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33;
do Carmo §6 (curvature commutators); Schoen-Simon 1981 §1 (variational
application).
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold Bundle Riemannian InnerProductSpace Topology

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-! ## Leibniz trace reduction (the LHS step) -/

/-- **Math.** **Leibniz trace reduction**: the scalar Laplacian of
$|\nabla f|_g^2$ decomposes as
$$\tfrac{1}{2}\,\Delta_g \, |\nabla f|_g^2 \;=\;
   \langle \Delta_\nabla \nabla f,\, \nabla f \rangle_g
   + |\nabla^2 f|_g^2.$$
Combines `hessian_gradientNormSq_apply_chartFrame` summed over
`stdOrthonormalBasis`, the trace identity for `connectionLaplacian`, and
`OrthonormalBasis.sum_sq_inner_left` for Frobenius². -/
theorem bochner_leibniz_trace_reduction
    [IsManifold I 2 M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x
      = ⟪connectionLaplacian HasMetric.metric (grad_g[I] f) x, (grad_g[I] f) x⟫_g
        + ‖hess_g[I] f‖²_g x := by
  classical
  have h_grad := manifoldGradient_smooth_of_smooth HasMetric.metric f hf
  show (1 / 2 : ℝ) * Operators.scalarLaplacian (I := I) (M := M) HasMetric.metric (‖grad_g[I] f‖²_g) x
      = metricInner x
          (connectionLaplacian (I := I) (M := M) HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x)
          (manifoldGradient (I := I) HasMetric.metric f x)
        + frobeniusSq (I := I) (M := M) (hessianBilin (I := I) HasMetric.metric f) x
  -- Wrap `smoothOrthoFrame · x i` as `SmoothVectorField` for `hessian_gradientNormSq_apply_section`.
  let Bi : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i
      smooth := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x i }
  -- Step 1: convert `scalarLaplacian` from std-basis trace to smoothOrthoFrame trace
  -- via Stage 7 basis-invariance of trace (`sum_diagonal_smoothOrthoFrame_eq_std`).
  have h_scalarLap_eq :
      Operators.scalarLaplacian (I := I) (M := M) HasMetric.metric (‖grad_g[I] f‖²_g) x
        = ∑ i, hessian (I := I) (M := M) HasMetric.metric (‖grad_g[I] f‖²_g)
            (Bi i).toFun (Bi i).toFun x := by
    rw [scalarLaplacian_eq_laplacian_hessianBilin HasMetric.metric]
    show laplacian (I := I) (M := M)
        (hessianBilin (I := I) HasMetric.metric (‖grad_g[I] f‖²_g)) x = _
    unfold laplacian
    rw [trace_def]
    rw [← Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x
          (hessianBilin (I := I) HasMetric.metric (‖grad_g[I] f‖²_g) x)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rfl
  rw [h_scalarLap_eq, Finset.mul_sum]
  -- Step 2: per-summand section-form Hess identity (`hessian_gradientNormSq_apply_section`).
  have h_summand : ∀ i,
      (1 / 2 : ℝ) * hessian (I := I) (M := M) HasMetric.metric (‖grad_g[I] f‖²_g)
        (Bi i).toFun (Bi i).toFun x
      = metricInner x
            (secondCovDerivSection (I := I) (M := M) HasMetric.metric
              (manifoldGradient (I := I) HasMetric.metric f) (Bi i).toFun (Bi i).toFun x)
            (manifoldGradient (I := I) HasMetric.metric f x)
          + metricInner x
              (covDeriv HasMetric.metric (Bi i).toFun (manifoldGradient (I := I) HasMetric.metric f) x)
              (covDeriv HasMetric.metric (Bi i).toFun (manifoldGradient (I := I) HasMetric.metric f) x) := by
    intro i
    show (1 / 2 : ℝ) * hessian (I := I) (M := M) HasMetric.metric
          (fun y => HasMetric.metric.metricInner y
            (manifoldGradient (I := I) HasMetric.metric f y)
            (manifoldGradient (I := I) HasMetric.metric f y))
          (Bi i).toFun (Bi i).toFun x = _
    rw [hessian_gradientNormSq_apply_section HasMetric.metric f (Bi i) x h_grad]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_summand i), Finset.sum_add_distrib]
  -- Step 3: identify the two sums.
  congr 1
  · -- First sum: ∑_i ⟨secondCovDerivSection ∇f (Bi · x) (Bi · x) x, ∇f x⟩
    --             = ⟨connectionLaplacian ∇f x, ∇f x⟩ via `sum_inner` + `connectionLaplacian_def`.
    show ∑ i, metricInner x
          (secondCovDerivSection (I := I) (M := M) HasMetric.metric
            (manifoldGradient (I := I) HasMetric.metric f) (Bi i).toFun (Bi i).toFun x)
          (manifoldGradient (I := I) HasMetric.metric f x)
        = metricInner x
            (connectionLaplacian (I := I) (M := M) HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x)
            (manifoldGradient (I := I) HasMetric.metric f x)
    unfold connectionLaplacian
    exact (sum_inner Finset.univ
      (fun i => secondCovDerivSection (I := I) (M := M) HasMetric.metric
        (manifoldGradient (I := I) HasMetric.metric f) (Bi i).toFun (Bi i).toFun x)
      (manifoldGradient (I := I) HasMetric.metric f x)).symm
  · -- Second sum: ∑_i ‖∇_{Bi · x x} ∇f x‖² = frobeniusSq (hessianBilin f) x.
    -- Approach: Stage 7 basis-invariance on the bilinear form
    -- `B(v, w) := ⟪covDerivAt HasMetric.metric ∇f x v, covDerivAt HasMetric.metric ∇f x w⟫_ℝ` (a `LinearMap.mk₂`),
    -- converts smoothOrthoFrame trace to std-basis trace; then the existing
    -- orthonormal-basis Frobenius identity closes.
    show ∑ i, metricInner x
            (covDeriv HasMetric.metric (Bi i).toFun (manifoldGradient (I := I) HasMetric.metric f) x)
            (covDeriv HasMetric.metric (Bi i).toFun (manifoldGradient (I := I) HasMetric.metric f) x)
        = frobeniusSq (I := I) (M := M) (hessianBilin (I := I) HasMetric.metric f) x
    -- Construct the bilinear form for Stage 7 swap.
    set B' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ
        (fun v w => @inner ℝ (TangentSpace I x) _
          (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v)
          (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w))
        (fun v₁ v₂ w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x (v₁ + v₂))
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
            = @inner ℝ (TangentSpace I x) _
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v₁)
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
              + @inner ℝ (TangentSpace I x) _
                  (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v₂)
                  (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
          rw [(covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x).map_add, inner_add_left])
        (fun c v w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x (c • v))
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
            = c • @inner ℝ (TangentSpace I x) _
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v)
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
          rw [(covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x).map_smul,
              real_inner_smul_left]; rfl)
        (fun v w₁ w₂ => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v)
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x (w₁ + w₂))
            = @inner ℝ (TangentSpace I x) _
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v)
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w₁)
              + @inner ℝ (TangentSpace I x) _
                  (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v)
                  (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w₂)
          rw [(covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x).map_add, inner_add_right])
        (fun c v w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v)
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x (c • w))
            = c • @inner ℝ (TangentSpace I x) _
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x v)
                (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x w)
          rw [(covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x).map_smul,
              real_inner_smul_right]; rfl) with hB'_def
    -- Stage 7 swap: ∑_i B'(Bi · x x, Bi · x x) = ∑_i B'(εᵢ, εᵢ).
    have h_stage7 :=
      Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x B'
    rw [hB'_def] at h_stage7
    simp only [LinearMap.mk₂_apply] at h_stage7
    -- LHS: rewrite `metricInner x (covDeriv HasMetric.metric (Bi · x) ∇f x) (covDeriv HasMetric.metric (Bi · x) ∇f x)`
    -- as `⟪covDerivAt HasMetric.metric ∇f x (Bi · x x), covDerivAt HasMetric.metric ∇f x (Bi · x x)⟫_ℝ` (def-eq), match h_stage7's LHS.
    show ∑ i, @inner ℝ (TangentSpace I x) _
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x
                (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
              (covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x
                (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
        = frobeniusSq (I := I) (M := M) (hessianBilin (I := I) HasMetric.metric f) x
    rw [h_stage7]
    -- Now goal: ∑_i ⟪covDerivAt HasMetric.metric ∇f x εᵢ, covDerivAt HasMetric.metric ∇f x εᵢ⟫_ℝ = frobeniusSq.
    -- Existing chain via OrthonormalBasis.sum_sq_inner_left.
    unfold frobeniusSq
    refine Finset.sum_congr rfl ?_
    intro i _
    set b := stdOrthonormalBasis ℝ (TangentSpace I x)
    set v : TangentSpace I x :=
      covDerivAt HasMetric.metric (manifoldGradient (I := I) HasMetric.metric f) x (b i)
    have h_hess_unfold : ∀ j, ((hessianBilin (I := I) HasMetric.metric f x) (b i)) (b j)
                            = metricInner x v (b j) := fun _ => rfl
    simp only [h_hess_unfold]
    calc @inner ℝ (TangentSpace I x) _ v v
        = ⟪v, v⟫_ℝ := rfl
      _ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      _ = ∑ j, ⟪v, b j⟫_ℝ ^ 2 := (b.sum_sq_inner_left v).symm
      _ = ∑ j, (metricInner x v (b j)) ^ 2 := rfl

/-- **Math.** **Explicit-`g` form of the Leibniz trace reduction**. -/
theorem bochner_leibniz_trace_reduction_g
    [IsManifold I 2 M]
    (g : RiemannianMetric I M) (hg : g = hm.metric)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (1 / 2 : ℝ) * Operators.scalarLaplacian g
        (fun y => g.metricInner y (manifoldGradient (I := I) g f y)
                                  (manifoldGradient (I := I) g f y)) x
      = g.metricInner x (connectionLaplacian g (manifoldGradient (I := I) g f) x)
            (manifoldGradient (I := I) g f x)
        + Operators.frobeniusSq (I := I) (M := M) (Operators.hessianBilin (I := I) g f) x := by
  subst hg
  exact bochner_leibniz_trace_reduction f hf x

/-! ## The headline identity -/

/-- **Math.** **Bochner–Weitzenböck identity** (unconditional under
`[I.Boundaryless]`):
$$\tfrac{1}{2}\,\Delta_g\,|\nabla f|_g^2
  = |\nabla^2 f|_g^2
    + \langle \nabla f,\, \nabla\,\Delta_g f\rangle_g
    + \mathrm{Ric}(\nabla f,\, \nabla f).$$
Composes `bochner_leibniz_trace_reduction` (LHS step) with
`bochner_connectionLaplacian_grad_decomposition` (RHS step, from
`Bochner/PerSummand.lean`).

Reference: Petersen Ch. 7 §1 Prop 33; do Carmo §6; Schoen-Simon 1981 §1. -/
theorem bochner_weitzenboeck
    [IsManifold I 2 M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x =
      ‖hess_g[I] f‖²_g x
      + ⟪(grad_g[I] f) x, (grad_g[I] (Δ_g[I] f)) x⟫_g
      + Ric_g((grad_g[I] f) x, (grad_g[I] f) x) x := by
  rw [bochner_leibniz_trace_reduction f hf x,
      bochner_connectionLaplacian_grad_decomposition f hf x]
  abel

/-- **Math.** **Explicit-`g` form of the Bochner–Weitzenböck identity**.
Same statement as `bochner_weitzenboeck` but the metric `g` is an explicit
`RiemannianMetric I M` parameter constrained by `hg : g = hm.metric`,
giving consumers a `g`-parametric API without changing the underlying
proof. Discharged via `subst hg` and `bochner_weitzenboeck`. -/
theorem bochner_weitzenboeck_g
    [IsManifold I 2 M]
    (g : RiemannianMetric I M) (hg : g = hm.metric)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (1 / 2 : ℝ) * Operators.scalarLaplacian g
        (fun y => g.metricInner y (manifoldGradient (I := I) g f y)
                                  (manifoldGradient (I := I) g f y)) x =
      Operators.frobeniusSq (I := I) (M := M) (Operators.hessianBilin (I := I) g f) x
      + g.metricInner x (manifoldGradient (I := I) g f x)
          (manifoldGradient (I := I) g (Operators.scalarLaplacian g f) x)
      + ricciTensor g x (manifoldGradient (I := I) g f x)
                        (manifoldGradient (I := I) g f x) := by
  subst hg
  exact bochner_weitzenboeck f hf x

end Operators
end Riemannian
