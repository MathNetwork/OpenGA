import OpenGALib.Riemannian.Connection
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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- The **second covariant derivative** of a tangent vector field $Z$ at
$x$, evaluated on a pair of directions $v, w \in T_x M$:
$$(\nabla^2 Z)(v, w)_x \;=\; \nabla_v(\nabla_w Z)|_x \;-\; \nabla_{(\nabla_v w)} Z|_x.$$
The convention follows Lee §4 and do Carmo §2: $v$ is the **outer**
differentiation direction, $w$ the inner one. Both directions are extended
as constant chart-frame sections (under `[IsLocallyConstantChartedSpace H M]`,
$T_y M = E$ definitionally on all of $M$), and the formula's "Christoffel
correction" $\nabla_{(\nabla_v w)} Z$ uses the chart-frame extension of $w$.

The expression depends only on $v, w$ at $x$ (tensoriality), but the proof
of tensoriality requires smoothness propagation of $Z$ and is deferred.

The connection Laplacian is the metric trace of this tensor:
$\Delta_\nabla Z = \sum_i (\nabla^2 Z)(\varepsilon_i, \varepsilon_i)$ —
see `connectionLaplacian_eq_sum_secondCovDerivAt` below. -/
noncomputable def secondCovDerivAt
    (Z : Π x : M, TangentSpace I x) (x : M)
    (v w : TangentSpace I x) : TangentSpace I x :=
  covDerivAt (fun y : M => covDerivAt Z y (w : TangentSpace I x)) x v
    - covDerivAt Z x (covDerivAt (fun _ : M => (w : TangentSpace I x)) x v)

@[simp] lemma secondCovDerivAt_def
    (Z : Π x : M, TangentSpace I x) (x : M)
    (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x v w =
      covDerivAt (fun y : M => covDerivAt Z y (w : TangentSpace I x)) x v
        - covDerivAt Z x
            (covDerivAt (fun _ : M => (w : TangentSpace I x)) x v) :=
  rfl

/-- $(\nabla^2 Z)(0, w) = 0$: the second covariant derivative vanishes when
the outer direction is zero. Pure CLM linearity in the outer direction slot;
no smoothness hypothesis. -/
@[simp] theorem secondCovDerivAt_zero_left
    (Z : Π x : M, TangentSpace I x) (x : M) (w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x 0 w = 0 := by
  unfold secondCovDerivAt
  rw [(covDerivAt (fun y : M => covDerivAt Z y w) x).map_zero,
      (covDerivAt (fun _ : M => w) x).map_zero,
      (covDerivAt Z x).map_zero]
  abel

/-- $(\nabla^2 Z)(v_1 + v_2, w) = (\nabla^2 Z)(v_1, w) + (\nabla^2 Z)(v_2, w)$.
Pure CLM linearity in the outer direction slot; no smoothness hypothesis. -/
theorem secondCovDerivAt_add_left
    (Z : Π x : M, TangentSpace I x) (x : M) (v₁ v₂ w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x (v₁ + v₂) w =
      secondCovDerivAt Z x v₁ w + secondCovDerivAt Z x v₂ w := by
  unfold secondCovDerivAt
  rw [(covDerivAt (fun y : M => covDerivAt Z y w) x).map_add,
      (covDerivAt (fun _ : M => w) x).map_add,
      (covDerivAt Z x).map_add]
  abel

/-- $(\nabla^2 Z)(c \cdot v, w) = c \cdot (\nabla^2 Z)(v, w)$.
Pure CLM linearity in the outer direction slot; no smoothness hypothesis. -/
theorem secondCovDerivAt_smul_left
    (Z : Π x : M, TangentSpace I x) (x : M)
    (c : ℝ) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x (c • v) w =
      c • secondCovDerivAt Z x v w := by
  unfold secondCovDerivAt
  rw [(covDerivAt (fun y : M => covDerivAt Z y w) x).map_smul,
      (covDerivAt (fun _ : M => w) x).map_smul,
      (covDerivAt Z x).map_smul]
  rw [smul_sub]

set_option backward.isDefEq.respectTransparency false in
/-- The **connection Laplacian** $\Delta_\nabla Z$ on a tangent vector
field $Z : \Pi x : M, T_x M$, computed against the $g$-orthonormal frame
`stdOrthonormalBasis ℝ (TangentSpace I x)` extended as a constant
chart-frame section:
$$(\Delta_\nabla Z)(x) \;=\; \sum_i \bigl(\nabla_{\varepsilon_i}
   \nabla_{\varepsilon_i} Z - \nabla_{(\nabla_{\varepsilon_i}\varepsilon_i)} Z\bigr)(x).$$

The constant chart-frame extension is $g$-orthonormal at $x$ (where
`stdOrthonormalBasis` is constructed); in general it is *not* $g$-orthonormal
at other points, but the trace identification at $x$ depends only on the
frame at $x$, so this gives the correct geometric trace of $\nabla\nabla Z$
at $x$ — basis-independent among $g$-orthonormal frames of $T_xM$.

**Ground truth**: Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33
(Bochner identity); do Carmo §6 ex. 12. -/
noncomputable def connectionLaplacian
    (Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, (covDerivAt (fun y : M => covDerivAt Z y (e i : TangentSpace I x)) x
          (e i : TangentSpace I x)
        - covDerivAt Z x
            (covDerivAt (fun _ : M => (e i : TangentSpace I x)) x
              (e i : TangentSpace I x)))

@[simp] lemma connectionLaplacian_def
    (Z : Π x : M, TangentSpace I x) (x : M) :
    connectionLaplacian (I := I) (M := M) Z x =
      ∑ i, (covDerivAt (fun y : M =>
                covDerivAt Z y
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x)) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x)
            - covDerivAt Z x
                (covDerivAt (fun _ : M =>
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x)) x
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x))) :=
  rfl

/-- Splits `connectionLaplacian` into its two trace pieces:
the sum of pure second-covariant-derivative terms
$\sum_i \nabla_{\varepsilon_i}\nabla_{\varepsilon_i} Z$, minus the sum of
Christoffel-correction terms $\sum_i \nabla_{(\nabla_{\varepsilon_i}\varepsilon_i)} Z$. -/
theorem connectionLaplacian_eq_sum_sub
    (Z : Π x : M, TangentSpace I x) (x : M) :
    connectionLaplacian (I := I) (M := M) Z x =
      (∑ i, covDerivAt (fun y : M =>
              covDerivAt Z y
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                  : TangentSpace I x)) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x))
        - ∑ i, covDerivAt Z x
                (covDerivAt (fun _ : M =>
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x)) x
                  ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                    : TangentSpace I x)) := by
  simp only [connectionLaplacian_def, Finset.sum_sub_distrib]

/-- The connection Laplacian on the zero vector field is zero:
$\Delta_\nabla 0 = 0$. -/
@[simp] theorem connectionLaplacian_zero (x : M) :
    connectionLaplacian (I := I) (M := M)
        (0 : Π x : M, TangentSpace I x) x = 0 := by
  rw [connectionLaplacian_eq_sum_sub]
  -- inner section `fun y => covDerivAt 0 y v` = `fun _ => 0`
  have h_inner : ∀ v : TangentSpace I x,
      (fun y : M => covDerivAt (0 : Π x : M, TangentSpace I x) y v)
        = (fun _ : M => (0 : TangentSpace I x)) := by
    intro v
    funext y
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 y) v = 0
    rw [CovariantDerivative.zero]; rfl
  -- LHS sum: each term is covDerivAt (fun _ => 0) x (e i) = 0
  have h_lhs :
      ∑ i, covDerivAt (fun y : M =>
              covDerivAt (0 : Π x : M, TangentSpace I x) y
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                  : TangentSpace I x)) x
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                : TangentSpace I x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [h_inner]
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 x) _ = 0
    rw [CovariantDerivative.zero]; rfl
  -- RHS sum: each term is covDerivAt 0 x (...) = 0
  have h_rhs :
      ∑ i, covDerivAt (0 : Π x : M, TangentSpace I x) x
              (covDerivAt (fun _ : M =>
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                  : TangentSpace I x)) x
                ((stdOrthonormalBasis ℝ (TangentSpace I x)) i
                  : TangentSpace I x)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 x) _ = 0
    rw [CovariantDerivative.zero]; rfl
  rw [h_lhs, h_rhs, sub_zero]

/-- **Connection Laplacian as the trace of the second covariant derivative**:
$$\Delta_\nabla Z \;=\; \sum_i (\nabla^2 Z)(\varepsilon_i, \varepsilon_i),$$
where $\{\varepsilon_i\} = \mathrm{stdOrthonormalBasis}\,\mathbb{R}\,(T_xM)$.

This is the textbook identification $\Delta_\nabla = \mathrm{tr}_g(\nabla^2)$.
The two definitions unfold to the same expression — `rfl` holds modulo the
definitional unfolding of both sides. -/
theorem connectionLaplacian_eq_sum_secondCovDerivAt
    (Z : Π x : M, TangentSpace I x) (x : M) :
    connectionLaplacian (I := I) (M := M) Z x =
      ∑ i, secondCovDerivAt (I := I) (M := M) Z x
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x)
        ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x) := by
  rw [connectionLaplacian_def]
  refine Finset.sum_congr rfl ?_
  intro i _
  rfl

/-- $(\nabla^2\,0)(v, w) = 0$: the second covariant derivative of the zero
vector field vanishes identically. -/
@[simp] theorem secondCovDerivAt_zero
    (x : M) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M)
        (0 : Π x : M, TangentSpace I x) x v w = 0 := by
  unfold secondCovDerivAt
  have h_inner : (fun y : M => covDerivAt (0 : Π x : M, TangentSpace I x) y w)
      = (fun _ : M => (0 : TangentSpace I x)) := by
    funext y
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 y) w = 0
    rw [CovariantDerivative.zero]; rfl
  rw [h_inner]
  have h0a : covDerivAt (fun _ : M => (0 : TangentSpace I x)) x v = 0 := by
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 x) v = 0
    rw [CovariantDerivative.zero]; rfl
  have h0b : covDerivAt (0 : Π x : M, TangentSpace I x) x
      (covDerivAt (fun _ : M => w) x v) = 0 := by
    show ((leviCivitaConnection (I := I) (M := M)).toFun 0 x) _ = 0
    rw [CovariantDerivative.zero]; rfl
  rw [h0a, h0b, sub_zero]

/-- **Ricci identity at chart-frame constant directions** (the heart of the
heart-of-Bochner identity):
$$(\nabla^2 Z)(v, w) - (\nabla^2 Z)(w, v) \;=\; R(\tilde v, \tilde w) Z,$$
where $\tilde v, \tilde w$ are the chart-frame constant extensions of $v, w$.
Under `[IsLocallyConstantChartedSpace H M]`, the constant extensions
$\tilde v(y) := v$, $\tilde w(y) := w$ have **vanishing covariant derivative
torsion** at each point, so the antisymmetric part of the second covariant
derivative is exactly the Riemann curvature.

Proof sketch: combines (i) torsion-freeness of Levi-Civita
(`covDeriv_sub_swap_eq_mlieBracket`) applied to the smooth-everywhere constant
sections $\tilde v, \tilde w$, and (ii) ℝ-linearity of `covDerivAt Z x` (a CLM)
to lift the bracket through the inner derivative.

**Ground truth**: do Carmo §4 Proposition 2.5 (ii); Lee §11. -/
theorem secondCovDerivAt_sub_swap_eq_riemannCurvature
    (Z : Π x : M, TangentSpace I x) (x : M) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x v w
      - secondCovDerivAt (I := I) (M := M) Z x w v
      = riemannCurvature
          (fun _ : M => (v : TangentSpace I x))
          (fun _ : M => (w : TangentSpace I x)) Z x := by
  set V : Π y : M, TangentSpace I y := fun _ => (v : TangentSpace I x) with hV
  set W : Π y : M, TangentSpace I y := fun _ => (w : TangentSpace I x) with hW
  have hVsm : TangentSmoothAt V x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  have hWsm : TangentSmoothAt W x :=
    (SmoothVectorField.const (I := I) (M := M) (w : E)).smoothAt x
  -- Torsion-free identity at x for the constant chart-frame sections
  have h_tor : (∇[V] W) x - (∇[W] V) x = (⟦V, W⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket V W x hVsm hWsm
  -- Lift through covDerivAt Z x (a CLM, hence ℝ-linear)
  have h_lifted : covDerivAt Z x ((∇[V] W) x) - covDerivAt Z x ((∇[W] V) x)
      = covDerivAt Z x ((⟦V, W⟧) x) := by
    rw [← (covDerivAt Z x).map_sub, h_tor]
  rw [riemannCurvature_def]
  -- After unfolding: both `secondCovDerivAt` reduce to the covDeriv pattern (rfl)
  show (covDeriv V (covDeriv W Z) x - covDerivAt Z x ((∇[V] W) x))
       - (covDeriv W (covDeriv V Z) x - covDerivAt Z x ((∇[W] V) x))
       = covDeriv V (covDeriv W Z) x - covDeriv W (covDeriv V Z) x
         - covDeriv (⟦V, W⟧) Z x
  -- `covDeriv (⟦V, W⟧) Z x = covDerivAt Z x ((⟦V, W⟧) x)` by definition.
  rw [show covDeriv (⟦V, W⟧) Z x = covDerivAt Z x ((⟦V, W⟧) x) from rfl]
  rw [← h_lifted]
  abel

/-- **Swap form of the Ricci identity at chart-frame constant directions**:
$$(\nabla^2 Z)(w, v) \;=\; (\nabla^2 Z)(v, w) \;-\; R(\tilde v, \tilde w) Z.$$
Direct corollary of `secondCovDerivAt_sub_swap_eq_riemannCurvature`. -/
theorem secondCovDerivAt_swap_eq
    (Z : Π x : M, TangentSpace I x) (x : M) (v w : TangentSpace I x) :
    secondCovDerivAt (I := I) (M := M) Z x w v
      = secondCovDerivAt (I := I) (M := M) Z x v w
        - riemannCurvature
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

/-- **Smooth-section second covariant derivative** at $x$:
$$(\nabla^2 Z)(V, W)(x) \;=\;
  \nabla_V (\nabla_W Z)\,x \;-\; \nabla_{(\nabla_V W)}\,Z\,x.$$

For $V(y) := v$, $W(y) := w$ (chart-frame constant lifts of vectors at
$x$), this reduces to `secondCovDerivAt Z x v w` definitionally
(`secondCovDerivSection_const_const` below). -/
noncomputable def secondCovDerivSection
    (Z V W : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  covDerivAt (fun y : M => covDerivAt Z y (W y)) x (V x)
    - covDerivAt Z x (covDerivAt W x (V x))

/-- Bridge: chart-frame constant lifts of $v, w$ recover `secondCovDerivAt`. -/
theorem secondCovDerivSection_const_const
    (Z : Π x : M, TangentSpace I x) (x : M) (v w : TangentSpace I x) :
    secondCovDerivSection (I := I) (M := M) Z
        (fun _ : M => (v : TangentSpace I x))
        (fun _ : M => (w : TangentSpace I x)) x
      = secondCovDerivAt (I := I) (M := M) Z x v w := rfl

/-- **D.3 — Smooth-frame Ricci identity**: for smooth tangent fields $V, W$
at $x$ and any tangent field $Z$,
$$(\nabla^2 Z)(V, W)(x) \;-\; (\nabla^2 Z)(W, V)(x) \;=\; R(V, W)\,Z\,(x).$$

Generalises `secondCovDerivAt_sub_swap_eq_riemannCurvature` (D.2): the
constant lifts $\tilde v, \tilde w$ are replaced by arbitrary smooth $V, W$.
The proof is the same algebraic chain — torsion-freeness
(`covDeriv_sub_swap_eq_mlieBracket`) on $V, W$, lifted through the CLM
$\nabla_\bullet Z$ at $x$, then matched against `riemannCurvature_def`.

**Ground truth**: do Carmo §4 Prop 2.5; Lee §11. -/
theorem secondCovDerivSection_sub_swap_eq_riemannCurvature
    (Z V W : Π x : M, TangentSpace I x) (x : M)
    (hV : TangentSmoothAt V x) (hW : TangentSmoothAt W x) :
    secondCovDerivSection (I := I) (M := M) Z V W x
      - secondCovDerivSection (I := I) (M := M) Z W V x
      = riemannCurvature V W Z x := by
  -- Torsion-free identity at x for V, W
  have h_tor : (∇[V] W) x - (∇[W] V) x = (⟦V, W⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket V W x hV hW
  -- Lift through covDerivAt Z x (a CLM, hence ℝ-linear)
  have h_lifted : covDerivAt Z x ((∇[V] W) x) - covDerivAt Z x ((∇[W] V) x)
      = covDerivAt Z x ((⟦V, W⟧) x) := by
    rw [← (covDerivAt Z x).map_sub, h_tor]
  rw [riemannCurvature_def]
  unfold secondCovDerivSection
  -- After unfolding both `secondCovDerivSection`, both sides are in covDeriv form
  show (covDeriv V (covDeriv W Z) x - covDerivAt Z x ((∇[V] W) x))
       - (covDeriv W (covDeriv V Z) x - covDerivAt Z x ((∇[W] V) x))
       = covDeriv V (covDeriv W Z) x - covDeriv W (covDeriv V Z) x
         - covDeriv (⟦V, W⟧) Z x
  rw [show covDeriv (⟦V, W⟧) Z x = covDerivAt Z x ((⟦V, W⟧) x) from rfl]
  rw [← h_lifted]
  abel

/-- **Swap form of D.3** (smooth-frame Ricci identity, swap orientation):
$$(\nabla^2 Z)(W, V)(x) \;=\; (\nabla^2 Z)(V, W)(x) \;-\; R(V, W)\,Z\,(x).$$
Direct corollary of `secondCovDerivSection_sub_swap_eq_riemannCurvature`. -/
theorem secondCovDerivSection_swap_eq
    (Z V W : Π x : M, TangentSpace I x) (x : M)
    (hV : TangentSmoothAt V x) (hW : TangentSmoothAt W x) :
    secondCovDerivSection (I := I) (M := M) Z W V x
      = secondCovDerivSection (I := I) (M := M) Z V W x
        - riemannCurvature V W Z x := by
  have h := secondCovDerivSection_sub_swap_eq_riemannCurvature
    (I := I) (M := M) Z V W x hV hW
  rw [← h]; abel

end Operators
end Riemannian
