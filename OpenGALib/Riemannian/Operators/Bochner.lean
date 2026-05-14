import OpenGALib.Riemannian.Operators.ConnectionLaplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Curvature.Tensoriality
import OpenGALib.Riemannian.Gradient
import OpenGALib.Riemannian.Tensor.SmoothOrthoFrame
import OpenGALib.Riemannian.Tensor.SmoothOrthoFrame.Smoothness
import OpenGALib.Riemannian.Operators.Bochner.HessianExpansion
import OpenGALib.Riemannian.Operators.Bochner.BochnerExpansion
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

set_option linter.unusedSectionVars false

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

/-! ## `mfderiv` distribution over `Finset.sum` -/

/-- **Eng.** `mfderiv` distributes over `Finset.sum` (evaluated at a
tangent vector):
$$\mathrm{d}\Bigl(\sum_{i \in s} g_i\Bigr)(x)(v)
   \;=\; \sum_{i \in s} \mathrm{d}(g_i)(x)(v).$$
Wraps Mathlib's `HasMFDerivAt.sum`. -/
theorem mfderiv_finset_sum_apply
    {ι : Type} (s : Finset ι) (g : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (hg : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (g i) x) :
    (mfderiv I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, g i y) x v : ℝ)
      = ∑ i ∈ s, (mfderiv I 𝓘(ℝ, ℝ) (g i) x v : ℝ) := by
  classical
  have h : HasMFDerivAt I 𝓘(ℝ, ℝ) (∑ i ∈ s, g i) x
      (∑ i ∈ s, mfderiv I 𝓘(ℝ, ℝ) (g i) x) :=
    HasMFDerivAt.sum (fun i hi => (hg i hi).hasMFDerivAt)
  have h' : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, g i y) x
      (∑ i ∈ s, mfderiv I 𝓘(ℝ, ℝ) (g i) x) := by
    convert h using 1
    funext y
    exact (Finset.sum_apply y s g).symm
  rw [h'.mfderiv]
  -- `(∑ i, F i) v = ∑ i, F i v` via Mathlib `ContinuousLinearMap.sum_apply`.
  exact ContinuousLinearMap.sum_apply s _ v

/-! ## `connectionLaplacian` (section-form definition)

Following Mathlib LC PR #36845 (Massot/Rothgang/Macbeth) and the external
`differential-geometry` library, the connection Laplacian is defined in
**section form** using the smooth $g$-orthonormal frame
`smoothOrthoFrame g α` (Gram-Schmidt of chart frame, centered at the
evaluation point $\alpha$).

Section form avoids the Hom-bundle Leibniz bridge between section and
constant forms, which is technically blocked by Lean's
`TangentSpace I x = E` non-reducibility (the same infrastructure issue
Mathlib LC PR works around with `set_option backward.isDefEq.respectTransparency false`).
With section form, the trace identifies directly with the section-form
output of `bochner_per_summand_assembled`, eliminating the bridge entirely. -/

/-- **Math.** **Connection Laplacian** $\Delta_\nabla Z$ on a tangent
vector field $Z$, computed against `smoothOrthoFrame g α`:
$$(\Delta_\nabla Z)(\alpha) \;=\; \sum_i (\nabla^2 Z)(B_i, B_i)(\alpha),$$
where $B_i := \mathrm{smoothOrthoFrame}\,g\,\alpha\,i$.

**Ground truth**: Petersen Ch. 7 §1 Prop 33; do Carmo §6 ex. 12. -/
noncomputable def connectionLaplacian
    (Z : Π x : M, TangentSpace I x) (α : M) : TangentSpace I α :=
  ∑ i, Riemannian.Operators.secondCovDerivSection (I := I) (M := M) Z
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α

/-- **Eng.** Definitional unfolding of `connectionLaplacian`. -/
@[simp] lemma connectionLaplacian_def
    (Z : Π x : M, TangentSpace I x) (α : M) :
    connectionLaplacian (I := I) (M := M) Z α =
      ∑ i, Riemannian.Operators.secondCovDerivSection (I := I) (M := M) Z
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α :=
  rfl

/-- **Math.** The connection Laplacian on the zero vector field is zero. -/
@[simp] theorem connectionLaplacian_zero (α : M) :
    connectionLaplacian (I := I) (M := M)
        (0 : Π x : M, TangentSpace I x) α = 0 := by
  rw [connectionLaplacian_def]
  refine Finset.sum_eq_zero ?_
  intro i _
  show secondCovDerivSection (I := I) (M := M)
        (0 : Π x : M, TangentSpace I x)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α = 0
  unfold secondCovDerivSection
  have h_inner_zero : ∀ y v, covDerivAt (0 : Π x : M, TangentSpace I x) y v = 0 := by
    intro y v
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 y) v = 0
    rw [CovariantDerivative.zero]; rfl
  have h_section_zero : (fun y : M => covDerivAt (0 : Π x : M, TangentSpace I x) y
        ((Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) y))
      = (0 : Π y : M, TangentSpace I y) := by
    funext y; exact h_inner_zero y _
  rw [h_section_zero]
  show ((leviCivitaConnection (I := I) (M := M)).toFun 0 α) _
        - ((leviCivitaConnection (I := I) (M := M)).toFun 0 α) _ = 0
  rw [CovariantDerivative.zero]
  show (0 : TangentSpace I α →L[ℝ] TangentSpace I α) _
      - (0 : TangentSpace I α →L[ℝ] TangentSpace I α) _ = 0
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, sub_zero]

/-! ## Two intermediates (E, G) for the Bochner identity -/

/-- **Math.** **Leibniz trace reduction**: the scalar Laplacian of
$|\nabla f|_g^2$ decomposes as
$$\tfrac{1}{2}\,\Delta_g \, |\nabla f|_g^2 \;=\;
   \langle \Delta_\nabla \nabla f,\, \nabla f \rangle_g
   + |\nabla^2 f|_g^2.$$
Combines `hessian_gradientNormSq_apply_chartFrame` summed over
`stdOrthonormalBasis`, the trace identity for `connectionLaplacian`, and
`OrthonormalBasis.sum_sq_inner_left` for Frobenius². -/
theorem leibniz_trace_reduction
    [IsManifold I 2 M] [T2Space M]
    (f : M → ℝ) (x : M)
    (h_grad : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
              (fun y => (⟨y, manifoldGradient (I := I) f y⟩ : TangentBundle I M))) :
    (1 / 2 : ℝ) * (Δ_g[I] ‖grad_g[I] f‖²_g) x
      = ⟪connectionLaplacian (grad_g[I] f) x, (grad_g[I] f) x⟫_g
        + ‖hess_g[I] f‖²_g x := by
  classical
  show (1 / 2 : ℝ) * Operators.scalarLaplacian (I := I) (M := M) (‖grad_g[I] f‖²_g) x
      = metricInner x
          (connectionLaplacian (I := I) (M := M) (manifoldGradient (I := I) f) x)
          (manifoldGradient (I := I) f x)
        + frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
  -- Wrap `smoothOrthoFrame · x i` as `SmoothVectorField` for `hessian_gradientNormSq_apply_section`.
  let Bi : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i
      smooth := Riemannian.Tensor.smoothOrthoFrame_smooth (I := I) hm.metric x i }
  -- Step 1: convert `scalarLaplacian` from std-basis trace to smoothOrthoFrame trace
  -- via Stage 7 basis-invariance of trace (`sum_diagonal_smoothOrthoFrame_eq_std`).
  have h_scalarLap_eq :
      Operators.scalarLaplacian (I := I) (M := M) (‖grad_g[I] f‖²_g) x
        = ∑ i, hessian (I := I) (M := M) (‖grad_g[I] f‖²_g)
            (Bi i).toFun (Bi i).toFun x := by
    rw [scalarLaplacian_eq_laplacian_hessianBilin]
    show laplacian (I := I) (M := M)
        (hessianBilin (I := I) (‖grad_g[I] f‖²_g)) x = _
    unfold laplacian
    rw [trace_def]
    rw [← Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x
          (hessianBilin (I := I) (‖grad_g[I] f‖²_g) x)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rfl
  rw [h_scalarLap_eq, Finset.mul_sum]
  -- Step 2: per-summand section-form Hess identity (`hessian_gradientNormSq_apply_section`).
  have h_summand : ∀ i,
      (1 / 2 : ℝ) * hessian (I := I) (M := M) (‖grad_g[I] f‖²_g)
        (Bi i).toFun (Bi i).toFun x
      = metricInner x
            (secondCovDerivSection (I := I) (M := M)
              (manifoldGradient (I := I) f) (Bi i).toFun (Bi i).toFun x)
            (manifoldGradient (I := I) f x)
          + metricInner x
              (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x)
              (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x) := by
    intro i
    rw [hessian_gradientNormSq_apply_section f (Bi i) x h_grad]
    ring
  rw [Finset.sum_congr rfl (fun i _ => h_summand i), Finset.sum_add_distrib]
  -- Step 3: identify the two sums.
  congr 1
  · -- First sum: ∑_i ⟨secondCovDerivSection ∇f (Bi · x) (Bi · x) x, ∇f x⟩
    --             = ⟨connectionLaplacian ∇f x, ∇f x⟩ via `sum_inner` + `connectionLaplacian_def`.
    show ∑ i, metricInner x
          (secondCovDerivSection (I := I) (M := M)
            (manifoldGradient (I := I) f) (Bi i).toFun (Bi i).toFun x)
          (manifoldGradient (I := I) f x)
        = metricInner x
            (connectionLaplacian (I := I) (M := M) (manifoldGradient (I := I) f) x)
            (manifoldGradient (I := I) f x)
    rw [connectionLaplacian_def]
    exact (sum_inner Finset.univ
      (fun i => secondCovDerivSection (I := I) (M := M)
        (manifoldGradient (I := I) f) (Bi i).toFun (Bi i).toFun x)
      (manifoldGradient (I := I) f x)).symm
  · -- Second sum: ∑_i ‖∇_{Bi · x x} ∇f x‖² = frobeniusSq (hessianBilin f) x.
    -- Approach: Stage 7 basis-invariance on the bilinear form
    -- `B(v, w) := ⟪covDerivAt ∇f x v, covDerivAt ∇f x w⟫_ℝ` (a `LinearMap.mk₂`),
    -- converts smoothOrthoFrame trace to std-basis trace; then the existing
    -- orthonormal-basis Frobenius identity closes.
    show ∑ i, metricInner x
            (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x)
            (covDeriv (Bi i).toFun (manifoldGradient (I := I) f) x)
        = frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
    -- Construct the bilinear form for Stage 7 swap.
    set B' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ
        (fun v w => @inner ℝ (TangentSpace I x) _
          (covDerivAt (manifoldGradient (I := I) f) x v)
          (covDerivAt (manifoldGradient (I := I) f) x w))
        (fun v₁ v₂ w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x (v₁ + v₂))
              (covDerivAt (manifoldGradient (I := I) f) x w)
            = @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v₁)
                (covDerivAt (manifoldGradient (I := I) f) x w)
              + @inner ℝ (TangentSpace I x) _
                  (covDerivAt (manifoldGradient (I := I) f) x v₂)
                  (covDerivAt (manifoldGradient (I := I) f) x w)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_add, inner_add_left])
        (fun c v w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x (c • v))
              (covDerivAt (manifoldGradient (I := I) f) x w)
            = c • @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v)
                (covDerivAt (manifoldGradient (I := I) f) x w)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_smul,
              real_inner_smul_left]; rfl)
        (fun v w₁ w₂ => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x v)
              (covDerivAt (manifoldGradient (I := I) f) x (w₁ + w₂))
            = @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v)
                (covDerivAt (manifoldGradient (I := I) f) x w₁)
              + @inner ℝ (TangentSpace I x) _
                  (covDerivAt (manifoldGradient (I := I) f) x v)
                  (covDerivAt (manifoldGradient (I := I) f) x w₂)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_add, inner_add_right])
        (fun c v w => by
          show @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x v)
              (covDerivAt (manifoldGradient (I := I) f) x (c • w))
            = c • @inner ℝ (TangentSpace I x) _
                (covDerivAt (manifoldGradient (I := I) f) x v)
                (covDerivAt (manifoldGradient (I := I) f) x w)
          rw [(covDerivAt (manifoldGradient (I := I) f) x).map_smul,
              real_inner_smul_right]; rfl) with hB'_def
    -- Stage 7 swap: ∑_i B'(Bi · x x, Bi · x x) = ∑_i B'(εᵢ, εᵢ).
    have h_stage7 :=
      Riemannian.Tensor.sum_diagonal_smoothOrthoFrame_eq_std (I := I) x B'
    rw [hB'_def] at h_stage7
    simp only [LinearMap.mk₂_apply] at h_stage7
    -- LHS: rewrite `metricInner x (covDeriv (Bi · x) ∇f x) (covDeriv (Bi · x) ∇f x)`
    -- as `⟪covDerivAt ∇f x (Bi · x x), covDerivAt ∇f x (Bi · x x)⟫_ℝ` (def-eq), match h_stage7's LHS.
    show ∑ i, @inner ℝ (TangentSpace I x) _
              (covDerivAt (manifoldGradient (I := I) f) x
                (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
              (covDerivAt (manifoldGradient (I := I) f) x
                (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric x i x))
        = frobeniusSq (I := I) (M := M) (hessianBilin (I := I) f) x
    rw [h_stage7]
    -- Now goal: ∑_i ⟪covDerivAt ∇f x εᵢ, covDerivAt ∇f x εᵢ⟫_ℝ = frobeniusSq.
    -- Existing chain via OrthonormalBasis.sum_sq_inner_left.
    unfold frobeniusSq
    refine Finset.sum_congr rfl ?_
    intro i _
    set b := stdOrthonormalBasis ℝ (TangentSpace I x)
    set v : TangentSpace I x :=
      covDerivAt (manifoldGradient (I := I) f) x (b i)
    have h_hess_unfold : ∀ j, ((hessianBilin (I := I) f x) (b i)) (b j)
                            = metricInner x v (b j) := fun _ => rfl
    simp only [h_hess_unfold]
    calc @inner ℝ (TangentSpace I x) _ v v
        = ⟪v, v⟫_ℝ := rfl
      _ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      _ = ∑ j, ⟪v, b j⟫_ℝ ^ 2 := (b.sum_sq_inner_left v).symm
      _ = ∑ j, (metricInner x v (b j)) ^ 2 := rfl


end Operators
end Riemannian
