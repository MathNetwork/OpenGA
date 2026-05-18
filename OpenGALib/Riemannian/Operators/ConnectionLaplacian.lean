import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Connection Laplacian on tangent vector fields

For a tangent vector field $Z : \Pi x : M, T_x M$ on a Riemannian manifold
$(M, g)$, the **connection Laplacian** (also called the rough or Bochner
Laplacian) is the metric trace of the second covariant derivative,
$$\Delta_\nabla Z \;=\; \mathrm{tr}_g(\nabla\nabla Z).$$
In a $g$-orthonormal frame $\{\varepsilon_i\}$ of $T_xM$ this evaluates to
$$(\Delta_\nabla Z)(x) \;=\; \sum_i
   \bigl(\nabla_{\varepsilon_i}\nabla_{\varepsilon_i} Z
        - \nabla_{(\nabla_{\varepsilon_i}\varepsilon_i)} Z\bigr)(x).$$

The frame is `stdOrthonormalBasis ℝ (TangentSpace I x)`, viewed as a
constant chart-frame extension via `[IsLocallyConstantChartedSpace H M]`
(under which `TangentSpace I _ = E` definitionally on all of $M$).

The connection Laplacian on tangent fields is the linear operator at the
heart of the Bochner–Weitzenböck identity:
$\Delta_\nabla(\nabla f) = \nabla(\Delta_g f) + \mathrm{Ric}^\sharp(\nabla f)$.

## Main definitions

* `connectionLaplacian Z x` — the connection Laplacian on a tangent vector
  field, evaluated at `x` against `stdOrthonormalBasis ℝ (TangentSpace I x)`.

Reference: Petersen, *Riemannian Geometry*, Ch. 7 §1; do Carmo §6.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle
open scoped ContDiff Manifold Bundle Riemannian

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Math.** The **second covariant derivative** of $Z$ at $x$ on
directions $v, w \in T_x M$:
$$(\nabla^2 Z)(v, w)_x \;=\; \nabla_v(\nabla_w Z)|_x \;-\; \nabla_{(\nabla_v w)} Z|_x.$$
$v$ is the outer differentiation direction, $w$ the inner one (Lee §4 /
do Carmo §2). Both are extended as constant chart-frame sections; the
Christoffel-correction term uses the chart-frame extension of $w$. The
connection Laplacian is the metric trace,
$\Delta_\nabla Z = \sum_i (\nabla^2 Z)(\varepsilon_i, \varepsilon_i)$. -/
noncomputable def secondCovDerivAt
    (Z : VectorFieldSection I M) (x : M)
    (v w : TangentSpace I x) : TangentSpace I x :=
  covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y (w : TangentSpace I x)) x v
    - covDerivAt HasMetric.metric Z x (covDerivAt HasMetric.metric (fun _ : M => (w : TangentSpace I x)) x v)

@[simp] lemma secondCovDerivAt_def
    (Z : VectorFieldSection I M) (x : M)
    (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x v w =
      covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y (w : TangentSpace I x)) x v
        - covDerivAt HasMetric.metric Z x
            (covDerivAt HasMetric.metric (fun _ : M => (w : TangentSpace I x)) x v) :=
  rfl

/-- **Math.** $(\nabla^2 Z)(0, w) = 0$. Pure continuous linear map linearity in the outer
direction slot. -/
@[simp] theorem secondCovDerivAt_zero_left
    (Z : VectorFieldSection I M) (x : M) (w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x 0 w = 0 := by
  unfold secondCovDerivAt
  rw [(covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y w) x).map_zero,
      (covDerivAt HasMetric.metric (fun _ : M => w) x).map_zero,
      (covDerivAt HasMetric.metric Z x).map_zero]
  abel

/-- **Math.** $(\nabla^2 Z)(v_1 + v_2, w) = (\nabla^2 Z)(v_1, w) + (\nabla^2 Z)(v_2, w)$. -/
theorem secondCovDerivAt_add_left
    (Z : VectorFieldSection I M) (x : M) (v₁ v₂ w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x (v₁ + v₂) w =
      secondCovDerivAt Z x v₁ w + secondCovDerivAt Z x v₂ w := by
  unfold secondCovDerivAt
  rw [(covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y w) x).map_add,
      (covDerivAt HasMetric.metric (fun _ : M => w) x).map_add,
      (covDerivAt HasMetric.metric Z x).map_add]
  abel

/-- **Math.** $(\nabla^2 Z)(c \cdot v, w) = c \cdot (\nabla^2 Z)(v, w)$. -/
theorem secondCovDerivAt_smul_left
    (Z : VectorFieldSection I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x (c • v) w =
      c • secondCovDerivAt Z x v w := by
  unfold secondCovDerivAt
  rw [(covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y w) x).map_smul,
      (covDerivAt HasMetric.metric (fun _ : M => w) x).map_smul,
      (covDerivAt HasMetric.metric Z x).map_smul]
  rw [smul_sub]

/-! ### Right-slot bilinearity

Right-slot (inner direction) bilinearity is **not** automatic from continuous linear map
properties of $\nabla_v$: the inner $w$ appears inside the section
`fun y => covDerivAt HasMetric.metric Z y w`, and to commute the section sum past the
outer `covDerivAt HasMetric.metric (·) x v` we need `covDeriv_add_field` /
`covDeriv_smul_const_field`, both of which require smoothness of
the section at $x$.

For $Z = \nabla f$ with smooth gradient, the relevant sections
`y ↦ covDerivAt HasMetric.metric Z y w` are smooth at $x$ via
`covDeriv_const_smoothVF_smoothAt` on the
`SmoothVectorField` wrapper around $\nabla f$. We expose the
right-slot lemmas with this smoothness as an explicit hypothesis,
so they are usable for any `Z` whose connection-on-constant-direction
sections are smooth at $x$ — including the heart-of-Bochner setting. -/

/-- **Eng.** Pi-level additivity of the section `y ↦ covDerivAt HasMetric.metric Z y w` in the
constant direction $w$. Pure continuous linear map additivity, no smoothness needed:
$\nabla_y$ is a continuous linear map in its second arg, so the sum splits pointwise. -/
private lemma covDerivAt_const_dir_section_add
    (Z : VectorFieldSection I M) (x : M) (w₁ w₂ : TangentSpace I x) :
    (fun y : M => covDerivAt HasMetric.metric Z y (w₁ + w₂))
      = (fun y : M => covDerivAt HasMetric.metric Z y w₁) + (fun y : M => covDerivAt HasMetric.metric Z y w₂) := by
  funext y
  exact (covDerivAt HasMetric.metric Z y).map_add w₁ w₂

/-- **Eng.** Pi-level scalar multiplication of the section
`y ↦ covDerivAt HasMetric.metric Z y w` in the constant direction $w$. -/
private lemma covDerivAt_const_dir_section_smul
    (Z : VectorFieldSection I M) (x : M) (c : ℝ) (w : TangentSpace I x) :
    (fun y : M => covDerivAt HasMetric.metric Z y (c • w))
      = c • (fun y : M => covDerivAt HasMetric.metric Z y w) := by
  funext y
  exact (covDerivAt HasMetric.metric Z y).map_smul c w

/-- **Math.** $(\nabla^2 Z)(v, 0) = 0$: the second covariant derivative vanishes
when the inner direction is zero. Inner continuous linear map-zero in both occurrences
of $w$. No smoothness hypothesis. -/
@[simp] theorem secondCovDerivAt_zero_right
    (Z : VectorFieldSection I M) (x : M) (v : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x v 0 = 0 := by
  unfold secondCovDerivAt
  -- (fun y => covDerivAt HasMetric.metric Z y 0) = 0 (Pi-zero, by continuous linear map map_zero pointwise).
  have h1 : (fun y : M => covDerivAt HasMetric.metric Z y (0 : TangentSpace I x))
      = (fun _ : M => (0 : TangentSpace I x)) := by
    funext y; exact (covDerivAt HasMetric.metric Z y).map_zero
  rw [h1]
  -- covDerivAt HasMetric.metric of the zero Pi-section at any direction is 0
  -- (`CovariantDerivative.zero` says `lcc.toFun 0 = 0`).
  have hZero : covDerivAt HasMetric.metric (fun _ : M => (0 : TangentSpace I x)) x v = 0 := by
    show ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 x) v = 0
    rw [CovariantDerivative.zero]; rfl
  rw [hZero, (covDerivAt HasMetric.metric Z x).map_zero]
  abel

/-- **Math.** $(\nabla^2 Z)(v, w_1 + w_2) = (\nabla^2 Z)(v, w_1) + (\nabla^2 Z)(v, w_2)$,
under smoothness of $y \mapsto \nabla_y Z(w_i)$ at $x$ for each
$w \in \{w_1, w_2\}$.

The smoothness hypothesis is the natural condition for $Z$ in the
heart-of-Bochner setting: for $Z = \nabla f$ with smooth gradient,
`covDeriv_const_smoothVF_smoothAt` on the `SmoothVectorField`
wrapper supplies it. -/
theorem secondCovDerivAt_add_right
    (Z : VectorFieldSection I M) (x : M) (v w₁ w₂ : TangentSpace I x)
    (h_smooth_dir : ∀ w : TangentSpace I x,
      TangentSmoothAt (fun y : M => covDerivAt HasMetric.metric Z y w) x) :
    secondCovDerivAt (I := I) (M := M) Z x v (w₁ + w₂) =
      secondCovDerivAt Z x v w₁ + secondCovDerivAt Z x v w₂ := by
  unfold secondCovDerivAt
  -- Outer term: distribute via covDeriv_add_field HasMetric.metric on the section sum.
  rw [covDerivAt_const_dir_section_add Z x w₁ w₂]
  -- `covDerivAt HasMetric.metric (s₁ + s₂) x v = covDerivAt HasMetric.metric s₁ x v + covDerivAt HasMetric.metric s₂ x v` via
  -- covDeriv_add_field HasMetric.metric with X := const v.
  have h_outer : covDerivAt HasMetric.metric
        ((fun y : M => covDerivAt HasMetric.metric Z y w₁) + (fun y : M => covDerivAt HasMetric.metric Z y w₂)) x v
      = covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y w₁) x v
        + covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y w₂) x v := by
    have h := covDeriv_add_field HasMetric.metric (fun _ : M => v)
      (fun y : M => covDerivAt HasMetric.metric Z y w₁) (fun y : M => covDerivAt HasMetric.metric Z y w₂) x
      (h_smooth_dir w₁) (h_smooth_dir w₂)
    -- h : (∇[const v] (s₁ + s₂)) x = (∇[const v] s₁) x + (∇[const v] s₂) x
    -- Unfolds to covDerivAt HasMetric.metric _ x v on each side.
    exact h
  rw [h_outer]
  -- Inner-direction term: const(w₁+w₂) = const w₁ + const w₂ pointwise,
  -- and covDerivAt HasMetric.metric (constant section) is continuous linear map in the inner argument.
  -- (fun _ => w₁ + w₂) = (fun _ => w₁) + (fun _ => w₂) (pointwise sum of consts).
  have h_const_add : (fun _ : M => (w₁ + w₂ : TangentSpace I x))
      = (fun _ : M => (w₁ : TangentSpace I x))
          + (fun _ : M => (w₂ : TangentSpace I x)) := by
    funext y; rfl
  rw [h_const_add]
  -- covDerivAt HasMetric.metric (s₁ + s₂) x v = covDerivAt HasMetric.metric s₁ x v + covDerivAt HasMetric.metric s₂ x v on const sums
  -- (smoothness of constant sections is automatic).
  have h_const_w₁_smooth : TangentSmoothAt (fun _ : M => (w₁ : TangentSpace I x)) x :=
    (SmoothVectorField.const (I := I) (M := M) (w₁ : E)).smoothAt x
  have h_const_w₂_smooth : TangentSmoothAt (fun _ : M => (w₂ : TangentSpace I x)) x :=
    (SmoothVectorField.const (I := I) (M := M) (w₂ : E)).smoothAt x
  have h_inner_dir : covDerivAt HasMetric.metric
        ((fun _ : M => (w₁ : TangentSpace I x)) + (fun _ : M => w₂)) x v
      = covDerivAt HasMetric.metric (fun _ : M => (w₁ : TangentSpace I x)) x v
        + covDerivAt HasMetric.metric (fun _ : M => (w₂ : TangentSpace I x)) x v := by
    have h := covDeriv_add_field HasMetric.metric (fun _ : M => v)
      (fun _ : M => (w₁ : TangentSpace I x)) (fun _ : M => (w₂ : TangentSpace I x))
      x h_const_w₁_smooth h_const_w₂_smooth
    exact h
  rw [h_inner_dir, (covDerivAt HasMetric.metric Z x).map_add]
  abel

/-- **Math.** $(\nabla^2 Z)(v, c \cdot w) = c \cdot (\nabla^2 Z)(v, w)$, under
the same smoothness hypothesis as `secondCovDerivAt_add_right`. -/
theorem secondCovDerivAt_smul_right
    (Z : VectorFieldSection I M) (x : M)
    (c : ℝ) (v w : TangentSpace I x)
    (h_smooth_dir : TangentSmoothAt (fun y : M => covDerivAt HasMetric.metric Z y w) x) :
    secondCovDerivAt (I := I) (M := M) Z x v (c • w) =
      c • secondCovDerivAt Z x v w := by
  unfold secondCovDerivAt
  rw [covDerivAt_const_dir_section_smul Z x c w]
  -- covDeriv_smul_const_field HasMetric.metric with field = (fun y => covDerivAt HasMetric.metric Z y w), constant c
  have h_outer : covDerivAt HasMetric.metric (c • (fun y : M => covDerivAt HasMetric.metric Z y w)) x v
      = c • covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y w) x v := by
    exact covDeriv_smul_const_field HasMetric.metric (fun _ : M => v)
      (fun y : M => covDerivAt HasMetric.metric Z y w) x c h_smooth_dir
  rw [h_outer]
  -- Inner-direction: const (c • w) = c • const w (pointwise scalar multiple).
  have h_const_smul : (fun _ : M => (c • w : TangentSpace I x))
      = c • (fun _ : M => (w : TangentSpace I x)) := by
    funext y; rfl
  rw [h_const_smul]
  have h_const_w_smooth : TangentSmoothAt (fun _ : M => (w : TangentSpace I x)) x :=
    (SmoothVectorField.const (I := I) (M := M) (w : E)).smoothAt x
  have h_inner_smul : covDerivAt HasMetric.metric (c • (fun _ : M => (w : TangentSpace I x))) x v
      = c • covDerivAt HasMetric.metric (fun _ : M => (w : TangentSpace I x)) x v :=
    covDeriv_smul_const_field HasMetric.metric (fun _ : M => v)
      (fun _ : M => (w : TangentSpace I x)) x c h_const_w_smooth
  rw [h_inner_smul, (covDerivAt HasMetric.metric Z x).map_smul, smul_sub]

/-- **Math.** $(\nabla^2\,0)(v, w) = 0$: the second covariant derivative of the zero
vector field vanishes identically. -/
@[simp] theorem secondCovDerivAt_zero
    (x : M) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M)
        (0 : VectorFieldSection I M) x v w = 0 := by
  unfold secondCovDerivAt
  have h_inner : (fun y : M => covDerivAt HasMetric.metric (0 : VectorFieldSection I M) y w)
      = (fun _ : M => (0 : TangentSpace I x)) := by
    funext y
    show ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 y) w = 0
    rw [CovariantDerivative.zero]; rfl
  rw [h_inner]
  have h0a : covDerivAt HasMetric.metric (fun _ : M => (0 : TangentSpace I x)) x v = 0 := by
    show ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 x) v = 0
    rw [CovariantDerivative.zero]; rfl
  have h0b : covDerivAt HasMetric.metric (0 : VectorFieldSection I M) x
      (covDerivAt HasMetric.metric (fun _ : M => w) x v) = 0 := by
    show ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 x) _ = 0
    rw [CovariantDerivative.zero]; rfl
  rw [h0a, h0b, sub_zero]

/-- **Math.** **Ricci identity at chart-frame constant directions** (the heart of the
heart-of-Bochner identity):
$$(\nabla^2 Z)(v, w) - (\nabla^2 Z)(w, v) \;=\; R(\tilde v, \tilde w) Z,$$
where $\tilde v, \tilde w$ are the chart-frame constant extensions of $v, w$.
Under `[IsLocallyConstantChartedSpace H M]`, the constant extensions
$\tilde v(y) := v$, $\tilde w(y) := w$ have **vanishing covariant derivative
torsion** at each point, so the antisymmetric part of the second covariant
derivative is exactly the Riemann curvature.

Proof sketch: combines (i) torsion-freeness of Levi-Civita
(`covDeriv_sub_swap_eq_mlieBracket`) applied to the smooth-everywhere constant
sections $\tilde v, \tilde w$, and (ii) ℝ-linearity of `covDerivAt HasMetric.metric Z x` (a continuous linear map)
to lift the bracket through the inner derivative.

**Ground truth**: do Carmo §4 Proposition 2.5 (ii); Lee §11. -/
theorem secondCovDerivAt_sub_swap_eq_riemannCurvature
    (Z : VectorFieldSection I M) (x : M) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x v w
      - secondCovDerivAt (I := I) (M := M) Z x w v
      = riemannCurvature HasMetric.metric
          (fun _ : M => (v : TangentSpace I x))
          (fun _ : M => (w : TangentSpace I x)) Z x := by
  set V : VectorFieldSection I M := fun _ => (v : TangentSpace I x) with hV
  set W : VectorFieldSection I M := fun _ => (w : TangentSpace I x) with hW
  have hVsm : TangentSmoothAt V x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  have hWsm : TangentSmoothAt W x :=
    (SmoothVectorField.const (I := I) (M := M) (w : E)).smoothAt x
  -- Torsion-free identity at x for the constant chart-frame sections
  have h_tor : (∇[V] W) x - (∇[W] V) x = (⟦V, W⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket HasMetric.metric V W x hVsm hWsm
  -- Lift through covDerivAt HasMetric.metric Z x (a continuous linear map, hence ℝ-linear)
  have h_lifted : covDerivAt HasMetric.metric Z x ((∇[V] W) x) - covDerivAt HasMetric.metric Z x ((∇[W] V) x)
      = covDerivAt HasMetric.metric Z x ((⟦V, W⟧) x) := by
    rw [← (covDerivAt HasMetric.metric Z x).map_sub, h_tor]
  rw [riemannCurvature_commutator_form]
  -- After unfolding: both `secondCovDerivAt` reduce to the covDeriv HasMetric.metric pattern (rfl)
  show (covDeriv HasMetric.metric V (covDeriv HasMetric.metric W Z) x - covDerivAt HasMetric.metric Z x ((∇[V] W) x))
       - (covDeriv HasMetric.metric W (covDeriv HasMetric.metric V Z) x - covDerivAt HasMetric.metric Z x ((∇[W] V) x))
       = covDeriv HasMetric.metric V (covDeriv HasMetric.metric W Z) x - covDeriv HasMetric.metric W (covDeriv HasMetric.metric V Z) x
         - covDeriv HasMetric.metric (⟦V, W⟧) Z x
  -- `covDeriv HasMetric.metric (⟦V, W⟧) Z x = covDerivAt HasMetric.metric Z x ((⟦V, W⟧) x)` by definition.
  rw [show covDeriv HasMetric.metric (⟦V, W⟧) Z x = covDerivAt HasMetric.metric Z x ((⟦V, W⟧) x) from rfl]
  rw [← h_lifted]
  abel

/-- **Math.** **Swap form of the Ricci identity at chart-frame constant directions**:
$$(\nabla^2 Z)(w, v) \;=\; (\nabla^2 Z)(v, w) \;-\; R(\tilde v, \tilde w) Z.$$
Direct corollary of `secondCovDerivAt_sub_swap_eq_riemannCurvature`. -/
theorem secondCovDerivAt_swap_eq
    (Z : VectorFieldSection I M) (x : M) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x w v
      = secondCovDerivAt (I := I) (M := M) Z x v w
        - riemannCurvature HasMetric.metric
            (fun _ : M => (v : TangentSpace I x))
            (fun _ : M => (w : TangentSpace I x)) Z x := by
  have h := secondCovDerivAt_sub_swap_eq_riemannCurvature
    (I := I) (M := M) Z x v w
  -- h : sCDA(v,w) - sCDA(w,v) = R(v,w) Z
  -- Goal: sCDA(w,v) = sCDA(v,w) - R(v,w) Z
  rw [← h]; abel

/-! ## Smooth-section second covariant derivative (D.3 layer)

The point-vector `secondCovDerivAt Z x v w` extends both `v, w` as
chart-frame constants. For the heart-of-Bochner derivation, one of the
slots is itself a smooth vector field (typically `∇f`), so we need a
section-form analog `secondCovDerivSection Z V W x` where `V, W` are
smooth tangent fields. The chart-frame constant case recovers
`secondCovDerivAt` definitionally. -/

/-- **Math.** **Smooth-section second covariant derivative** at $x$:
$$(\nabla^2 Z)(V, W)(x) \;=\;
  \nabla_V (\nabla_W Z)\,x \;-\; \nabla_{(\nabla_V W)}\,Z\,x.$$

For $V(y) := v$, $W(y) := w$ (chart-frame constant lifts of vectors at
$x$), this reduces to `secondCovDerivAt Z x v w` definitionally. -/
noncomputable def secondCovDerivSection
    (Z V W : VectorFieldSection I M) (x : M) : TangentSpace I x :=
  covDerivAt HasMetric.metric (fun y : M => covDerivAt HasMetric.metric Z y (W y)) x (V x)
    - covDerivAt HasMetric.metric Z x (covDerivAt HasMetric.metric W x (V x))

/-- **Math.** **D.3 — Smooth-frame Ricci identity**: for smooth tangent fields $V, W$
at $x$ and any tangent field $Z$,
$$(\nabla^2 Z)(V, W)(x) \;-\; (\nabla^2 Z)(W, V)(x) \;=\; R(V, W)\,Z\,(x).$$

Generalises `secondCovDerivAt_sub_swap_eq_riemannCurvature` (D.2): the
constant lifts $\tilde v, \tilde w$ are replaced by arbitrary smooth $V, W$.
The proof is the same algebraic chain — torsion-freeness
(`covDeriv_sub_swap_eq_mlieBracket`) on $V, W$, lifted through the continuous linear map
$\nabla_\bullet Z$ at $x$, then matched against `riemannCurvature_commutator_form`.

**Ground truth**: do Carmo §4 Prop 2.5; Lee §11. -/
theorem secondCovDerivSection_sub_swap_eq_riemannCurvature
    (Z V W : VectorFieldSection I M) (x : M)
    (hV : TangentSmoothAt V x) (hW : TangentSmoothAt W x) :
    secondCovDerivSection (I := I) (M := M) Z V W x
      - secondCovDerivSection (I := I) (M := M) Z W V x
      = riemannCurvature HasMetric.metric V W Z x := by
  -- Torsion-free identity at x for V, W
  have h_tor : (∇[V] W) x - (∇[W] V) x = (⟦V, W⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket HasMetric.metric V W x hV hW
  -- Lift through covDerivAt HasMetric.metric Z x (a continuous linear map, hence ℝ-linear)
  have h_lifted : covDerivAt HasMetric.metric Z x ((∇[V] W) x) - covDerivAt HasMetric.metric Z x ((∇[W] V) x)
      = covDerivAt HasMetric.metric Z x ((⟦V, W⟧) x) := by
    rw [← (covDerivAt HasMetric.metric Z x).map_sub, h_tor]
  rw [riemannCurvature_commutator_form]
  unfold secondCovDerivSection
  -- After unfolding both `secondCovDerivSection`, both sides are in covDeriv HasMetric.metric form
  show (covDeriv HasMetric.metric V (covDeriv HasMetric.metric W Z) x - covDerivAt HasMetric.metric Z x ((∇[V] W) x))
       - (covDeriv HasMetric.metric W (covDeriv HasMetric.metric V Z) x - covDerivAt HasMetric.metric Z x ((∇[W] V) x))
       = covDeriv HasMetric.metric V (covDeriv HasMetric.metric W Z) x - covDeriv HasMetric.metric W (covDeriv HasMetric.metric V Z) x
         - covDeriv HasMetric.metric (⟦V, W⟧) Z x
  rw [show covDeriv HasMetric.metric (⟦V, W⟧) Z x = covDerivAt HasMetric.metric Z x ((⟦V, W⟧) x) from rfl]
  rw [← h_lifted]
  abel

/-- **Math.** **Swap form of D.3** (smooth-frame Ricci identity, swap orientation):
$$(\nabla^2 Z)(W, V)(x) \;=\; (\nabla^2 Z)(V, W)(x) \;-\; R(V, W)\,Z\,(x).$$
Direct corollary of `secondCovDerivSection_sub_swap_eq_riemannCurvature`. -/
theorem secondCovDerivSection_swap_eq
    (Z V W : VectorFieldSection I M) (x : M)
    (hV : TangentSmoothAt V x) (hW : TangentSmoothAt W x) :
    secondCovDerivSection (I := I) (M := M) Z W V x
      = secondCovDerivSection (I := I) (M := M) Z V W x
        - riemannCurvature HasMetric.metric V W Z x := by
  have h := secondCovDerivSection_sub_swap_eq_riemannCurvature
    (I := I) (M := M) Z V W x hV hW
  rw [← h]; abel

/-! ## Connection Laplacian operator

Section-form trace `Δ_∇ Z (α) = ∑ i (∇²Z)(B_i, B_i)(α)` against
`smoothOrthoFrame g α`. Section form (per Mathlib LC PR #36845 and the
external `differential-geometry` library convention) directly composes
with `bochner_per_summand_assembled` — the per-summand chain output —
without needing a Hom-bundle Leibniz bridge between section and constant
forms. -/

/-- **Math.** **Connection Laplacian** $\Delta_\nabla Z$ on a tangent
vector field $Z$, computed against `smoothOrthoFrame g α`:
$$(\Delta_\nabla Z)(\alpha) \;=\; \sum_i (\nabla^2 Z)(B_i, B_i)(\alpha),$$
where $B_i := \mathrm{smoothOrthoFrame}\,g\,\alpha\,i$.

**Ground truth**: Petersen Ch. 7 §1 Prop 33; do Carmo §6 ex. 12. -/
noncomputable def connectionLaplacian
    (Z : VectorFieldSection I M) (α : M) : TangentSpace I α :=
  ∑ i, secondCovDerivSection (I := I) (M := M) Z
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α

/-- **Math.** The connection Laplacian on the zero vector field is zero. -/
@[simp] theorem connectionLaplacian_zero (α : M) :
    connectionLaplacian (I := I) (M := M)
        (0 : VectorFieldSection I M) α = 0 := by
  unfold connectionLaplacian
  refine Finset.sum_eq_zero ?_
  intro i _
  show secondCovDerivSection (I := I) (M := M)
        (0 : VectorFieldSection I M)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i)
        (Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) α = 0
  unfold secondCovDerivSection
  have h_inner_zero : ∀ y v, covDerivAt HasMetric.metric (0 : VectorFieldSection I M) y v = 0 := by
    intro y v
    show ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 y) v = 0
    rw [CovariantDerivative.zero]; rfl
  have h_section_zero : (fun y : M => covDerivAt HasMetric.metric (0 : VectorFieldSection I M) y
        ((Riemannian.Tensor.smoothOrthoFrame (I := I) hm.metric α i) y))
      = (0 : VectorFieldSection I M) := by
    funext y; exact h_inner_zero y _
  rw [h_section_zero]
  show ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 α) _
        - ((leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun 0 α) _ = 0
  rw [CovariantDerivative.zero]
  show (0 : TangentSpace I α →L[ℝ] TangentSpace I α) _
      - (0 : TangentSpace I α →L[ℝ] TangentSpace I α) _ = 0
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, sub_zero]

end Operators
end Riemannian
