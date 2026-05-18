import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Riemannian.Operators.HessianLie
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import OpenGALib.Riemannian.Util.CovDerivBridges

/-!
# Hessian on a Riemannian manifold

For smooth $f : M \to \mathbb{R}$ on $(M, g)$, the **Hessian** is the
symmetric $(0,2)$-tensor
$$\operatorname{Hess} f(x)(X, Y) = \langle \nabla_X (\nabla^M f), Y \rangle_g(x)
  = X(Y(f)) - (\nabla_X Y)(f).$$

This file provides the vector-field bilinear form `hessian f X Y x` plus
an abstract pointwise bilinear-form carrier `Bilin I M` carrying the
linear-algebra trace–Frobenius Cauchy-Schwarz inequality
$\bigl(\sum_i B(b_i, b_i)\bigr)^2 \le n \cdot \sum_{i,j} B(b_i, b_j)^2$,
used downstream to bound $(\Delta f)^2 \le n \cdot |\mathrm{Hess}\,f|^2$
after Bochner.

The chart-Christoffel formula and the smoothness of the Hessian as a
section of the $(0,2)$-bundle are out of scope here.

Reference: do Carmo §6 ex. 12.
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
  [hm : HasMetric I M]

/-! ## Vector-field Hessian -/

/-- **Math.** The **Hessian** of a smooth scalar `f` on vector fields:
$$\operatorname{Hess} f(X, Y)(x) = \langle \nabla_X (\nabla^M f), Y \rangle_g(x).$$ -/
noncomputable def hessian
    [IsLocallyConstantChartedSpace H M]
    (g : RiemannianMetric I M)
    (f : M → ℝ) (X Y : VectorFieldSection I M) (x : M) : ℝ :=
  g.metricInner x (covDeriv g X (manifoldGradient g f) x) (Y x)

/-! ## Pointwise bilinear-form carrier -/

variable (I) in
/-- **Math.** Pointwise real-valued bilinear form on the tangent bundle
of $M$ — the abstract carrier for concrete $(0,2)$-tensors. -/
abbrev Bilin :=
  ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ

/-- **Math.** Pointwise symmetry: $B(x)(v, w) = B(x)(w, v)$ for all $x, v, w$. -/
def IsPointwiseSymm (B : Bilin (M := M) I) : Prop :=
  ∀ x : M, ∀ v w : TangentSpace I x, B x v w = B x w v

/-! ## Frobenius and trace, in a $g$-orthonormal frame

`TangentSpace I x = E` definitionally; with `[HasMetric I M]` activating the
`RiemannianBundle` scoped `InnerProductSpace ℝ (TangentSpace I x)` instance,
`stdOrthonormalBasis ℝ (TangentSpace I x)` is a genuine $g$-orthonormal frame
on $T_x M$. Frobenius and trace against this frame are the **geometric**
Hilbert-Schmidt norm and trace of $B$ at $x$ (basis-independent among
$g$-orthonormal frames). -/

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Frobenius squared norm $\sum_{i,j} B(x)(\varepsilon_i, \varepsilon_j)^2$
in the $g$-orthonormal frame. -/
def frobeniusSq (B : Bilin (M := M) I) (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, ∑ j, (B x (e i : TangentSpace I x) (e j : TangentSpace I x))^2

@[simp] lemma frobeniusSq_def (B : Bilin (M := M) I) (x : M) :
    frobeniusSq (I := I) (M := M) B x =
      ∑ i, ∑ j,
        (B x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x)
             ((stdOrthonormalBasis ℝ (TangentSpace I x)) j : TangentSpace I x))^2 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Trace $\sum_i B(x)(\varepsilon_i, \varepsilon_i)$ in the
$g$-orthonormal frame. -/
def trace (B : Bilin (M := M) I) (x : M) : ℝ :=
  let e : OrthonormalBasis _ ℝ (TangentSpace I x) :=
    stdOrthonormalBasis ℝ (TangentSpace I x)
  ∑ i, B x (e i : TangentSpace I x) (e i : TangentSpace I x)

@[simp] lemma trace_def (B : Bilin (M := M) I) (x : M) :
    trace (I := I) (M := M) B x =
      ∑ i,
        B x ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x)
            ((stdOrthonormalBasis ℝ (TangentSpace I x)) i : TangentSpace I x) :=
  rfl

lemma frobeniusSq_nonneg (B : Bilin (M := M) I) (x : M) :
    0 ≤ frobeniusSq (I := I) (M := M) B x := by
  unfold frobeniusSq
  positivity

/-! ## Trace–Frobenius Cauchy-Schwarz -/

/-- **Math.** $\bigl(\sum_i B(v_i, v_i)\bigr)^2 \le |\iota| \cdot \sum_{i,j} B(v_i, v_j)^2$. -/
theorem bilinForm_trace_sq_le_card_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : ι → V) :
    (∑ i : ι, B (v i) (v i))^2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 := by
  classical
  have h_diag :
      (∑ i : ι, B (v i) (v i))^2 ≤
        (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := by
    have h := sq_sum_le_card_mul_sum_sq (α := ℝ) (s := (Finset.univ : Finset ι))
      (f := fun i => B (v i) (v i))
    simpa [Finset.card_univ] using h
  have h_row : ∀ i : ι, (B (v i) (v i))^2 ≤ ∑ j : ι, (B (v i) (v j))^2 := by
    intro i
    exact Finset.single_le_sum
      (f := fun j => (B (v i) (v j))^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h_sum :
      ∑ i : ι, (B (v i) (v i))^2 ≤ ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 :=
    Finset.sum_le_sum (fun i _ => h_row i)
  have h_card_nonneg : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Nat.zero_le _
  calc (∑ i : ι, B (v i) (v i))^2
      ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := h_diag
    _ ≤ (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 :=
        mul_le_mul_of_nonneg_left h_sum h_card_nonneg

/-- **Math.** Specialisation to the canonical basis `Module.finBasis ℝ V`. -/
theorem bilinForm_trace_sq_le_dim_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    (∑ i : Fin (Module.finrank ℝ V), B (b i) (b i))^2 ≤
      (Module.finrank ℝ V : ℝ) *
        ∑ i : Fin (Module.finrank ℝ V),
          ∑ j : Fin (Module.finrank ℝ V), (B (b i) (b j))^2 := by
  have h := bilinForm_trace_sq_le_card_mul_frobenius_sq (V := V)
    (ι := Fin (Module.finrank ℝ V)) B (fun i => b i)
  simpa [Fintype.card_fin] using h

/-- **Math.** $(\operatorname{trace}_g B(x))^2 \le n \cdot \operatorname{frobeniusSq}_g B(x)$
with $n = \dim_\mathbb{R} E$. Cauchy-Schwarz in the $g$-orthonormal frame. -/
theorem trace_sq_le_dim_mul_frobeniusSq
    (B : Bilin (M := M) I) (x : M) :
    (trace (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSq (I := I) (M := M) B x := by
  have h := bilinForm_trace_sq_le_dim_mul_frobenius_sq
    (V := TangentSpace I x) (B := B x)
    (b := (stdOrthonormalBasis ℝ (TangentSpace I x)).toBasis)
  simp only [OrthonormalBasis.coe_toBasis] at h
  exact h

/-- **Math.** The **Hessian as a `Bilin` section**: at each point $x$,
$\operatorname{Hess} f(x)(v, w) = \langle \nabla_{(\text{const }v)}\,\nabla^M f,\,
w\rangle_g(x)$. Tensoriality is built in: the constant extension suffices
since the Levi-Civita connection is C∞-linear in its first slot. -/
noncomputable def hessianBilin
    [IsLocallyConstantChartedSpace H M]
    (g : RiemannianMetric I M)
    (f : M → ℝ) : Bilin (M := M) I := fun x =>
  LinearMap.mk₂ ℝ
    (fun v w => g.metricInner x
      (covDerivAt g (manifoldGradient (I := I) g f) x v) w)
    (fun v₁ v₂ w => by
      show g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x (v₁ + v₂)) w
          = g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x v₁) w
          + g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x v₂) w
      rw [map_add, g.metricInner_add_left])
    (fun c v w => by
      show g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x (c • v)) w
          = c • g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x v) w
      rw [(covDerivAt g (manifoldGradient (I := I) g f) x).map_smul,
          g.metricInner_smul_left]; rfl)
    (fun v w₁ w₂ => g.metricInner_add_right x _ w₁ w₂)
    (fun c v w => by
      show g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x v) (c • w)
          = c • g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x v) w
      rw [g.metricInner_smul_right]; rfl)


/-- **Math.** $(\operatorname{trace} B(x))^2 / n \le \operatorname{frobeniusSq} B(x)$. -/
theorem trace_sq_div_dim_le_frobeniusSq
    (B : Bilin (M := M) I) (x : M) :
    (trace (I := I) (M := M) B x)^2 / (Module.finrank ℝ E : ℝ) ≤
      frobeniusSq (I := I) (M := M) B x := by
  have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  exact (div_le_iff₀ hpos).mpr
    (by linarith [trace_sq_le_dim_mul_frobeniusSq (I := I) (M := M) B x])

/-! ## Bridge: scalar Hessian via iterated `mDirDeriv` -/

variable [IsLocallyConstantChartedSpace H M]

/-- **Math.** **Scalar Hessian as iterated `mDirDeriv` minus Christoffel
correction**. For a smooth scalar $g \colon M \to \mathbb{R}$ with
$\nabla^M g$ smooth at $x$, the connection Hessian admits the textbook
decomposition
$$\mathrm{Hess}\,g(X, Y)(x) \;=\; X(Y(g))(x) \;-\; (\nabla_X Y)(g)(x),$$
i.e. iterated directional differentiation of $g$ along $Y$ then $X$,
minus the Christoffel correction $\nabla_X Y$ acting on $g$. -/
theorem hessian_eq_mDirDeriv_iterate_sub_chris
    (g : RiemannianMetric I M)
    (f : M → ℝ) (X Y : VectorFieldSection I M) (x : M)
    (h_grad_f : TangentSmoothAt (manifoldGradient (I := I) g f) x)
    (hX : TangentSmoothAt X x)
    (hY : TangentSmoothAt Y x) :
    hessian (I := I) g f X Y x =
      mDirDeriv (I := I) (fun y => mDirDeriv (I := I) f y (Y y)) x (X x)
        - mDirDeriv (I := I) f x (covDeriv g X Y x) := by
  -- metric-compat on (X, ∇f, Y) at x
  have h_compat := leviCivitaConnection_metric_compatible g
    X (manifoldGradient (I := I) g f) Y x hX h_grad_f hY
  -- Replace `⟨∇f y, Y y⟩` by `mDirDeriv f y (Y y)` (grad duality)
  have h_lhs :
      (fun y : M => g.metricInner y (manifoldGradient (I := I) g f y) (Y y))
        = (fun y : M => mDirDeriv (I := I) f y (Y y)) := by
    funext y
    exact manifoldGradient_inner_eq g f y (Y y)
  rw [h_lhs] at h_compat
  -- Replace `⟨∇f x, ∇_X Y x⟩` by `mDirDeriv f x (covDeriv g X Y x)`.
  have h_chris_inner :
      g.metricInner x (manifoldGradient (I := I) g f x) (covDeriv g X Y x)
        = mDirDeriv (I := I) f x (covDeriv g X Y x) :=
    manifoldGradient_inner_eq g f x (covDeriv g X Y x)
  rw [h_chris_inner] at h_compat
  change mDirDeriv (I := I) (fun y => mDirDeriv (I := I) f y (Y y)) x (X x)
       = g.metricInner x (covDeriv g X (manifoldGradient (I := I) g f) x) (Y x)
         + mDirDeriv (I := I) f x (covDeriv g X Y x) at h_compat
  show g.metricInner x (covDeriv g X (manifoldGradient (I := I) g f) x) (Y x)
      = mDirDeriv (I := I) (fun y => mDirDeriv (I := I) f y (Y y)) x (X x)
        - mDirDeriv (I := I) f x (covDeriv g X Y x)
  linarith [h_compat]

/-! ## Symmetry of the Hessian on scalar functions -/

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** **Hessian symmetry on scalar functions** (covariant Schwarz / Clairaut):
$$\mathrm{Hess}\,f(x)(v, w) \;=\; \mathrm{Hess}\,f(x)(w, v).$$
For $f \in C^2$ near $x$, with $\nabla^M f$ smooth at $x$ as a tangent
bundle section. The chart-interior hypothesis `h_interior` enables the
manifold scalar Hessian–Lie identity from
`mfderiv_iterate_sub_eq_mlieBracket_apply`.

Proof: combines (i) Levi-Civita's metric-compatibility applied twice (for
constant chart-frame extensions of $v, w$), (ii) torsion-freeness via
`covDeriv_sub_swap_eq_mlieBracket`, (iii) the manifold scalar Hessian–Lie
identity, and (iv) gradient duality `manifoldGradient_inner_eq`. The Lie
bracket of constant chart-frame extensions appears on both sides and
cancels, leaving $\mathrm{Hess}\,f(x)(v, w) - \mathrm{Hess}\,f(x)(w, v) = 0$.

**Ground truth**: do Carmo §2 ex. 7; Lee §4 (symmetry of the Hessian). -/
theorem hessianBilin_symm
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (f : M → ℝ) (x : M)
    (h_interior : extChartAt I x x ∈ closure (interior (Set.range I)))
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x)
    (h_grad : TangentSmoothAt (manifoldGradient (I := I) g f) x)
    (v w : TangentSpace I x) :
    hessianBilin (I := I) g f x v w = hessianBilin (I := I) g f x w v := by
  set V : VectorFieldSection I M := fun _ => (v : TangentSpace I x) with hV_def
  set W : VectorFieldSection I M := fun _ => (w : TangentSpace I x) with hW_def
  have hVsm : TangentSmoothAt V x :=
    (SmoothVectorField.const (I := I) (M := M) (v : E)).smoothAt x
  have hWsm : TangentSmoothAt W x :=
    (SmoothVectorField.const (I := I) (M := M) (w : E)).smoothAt x
  -- Bundle smoothness for HessianLie iterate (need ContMDiffAt 1; have ContMDiff ∞)
  have hV_cmd : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, V y⟩ : TotalSpace E (TangentSpace I))) x :=
    ((SmoothVectorField.const (I := I) (M := M) (v : E)).smooth x).of_le
      (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hW_cmd : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, W y⟩ : TotalSpace E (TangentSpace I))) x :=
    ((SmoothVectorField.const (I := I) (M := M) (w : E)).smooth x).of_le
      (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  -- Torsion-free identity at x; restate in `lcc.toFun` form (def-equal)
  have h_torsion : covDeriv g V W x - covDeriv g W V x = (⟦V, W⟧) x :=
    covDeriv_sub_swap_eq_mlieBracket g V W x hVsm hWsm
  have h_torsion' :
      (leviCivitaConnection (I := I) (M := M) g).toFun W x v
        - (leviCivitaConnection (I := I) (M := M) g).toFun V x w
      = VectorField.mlieBracket I V W x := h_torsion
  -- Metric-compatibility, both directions; bridge ∇ → `.toFun` form for
  -- the downstream `rw [h_hess_lhs/rhs]` matches.
  have h_compat_vw := leviCivitaConnection_metric_compatible g
    V (manifoldGradient (I := I) g f) W x hVsm h_grad hWsm
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h_compat_vw
  have h_compat_wv := leviCivitaConnection_metric_compatible g
    W (manifoldGradient (I := I) g f) V x hWsm h_grad hVsm
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h_compat_wv
  -- Substitute `g.metricInner _ ∇f _ = mDirDeriv f _` to match HessianLie iterate form.
  -- (Use `mDirDeriv` to strip basepoint-dependent typing on the codomain.)
  have h_repl_W :
      (fun y : M => g.metricInner y (manifoldGradient (I := I) g f y) (W y))
        = (fun y : M => mDirDeriv (I := I) f y w) := by
    funext y
    show g.metricInner y (manifoldGradient (I := I) g f y) w
        = mDirDeriv (I := I) f y w
    exact manifoldGradient_inner_eq g f y w
  have h_repl_V :
      (fun y : M => g.metricInner y (manifoldGradient (I := I) g f y) (V y))
        = (fun y : M => mDirDeriv (I := I) f y v) := by
    funext y
    show g.metricInner y (manifoldGradient (I := I) g f y) v
        = mDirDeriv (I := I) f y v
    exact manifoldGradient_inner_eq g f y v
  rw [h_repl_W] at h_compat_vw
  rw [h_repl_V] at h_compat_wv
  -- Lift h_compat_vw / h_compat_wv from `mfderiv ... x (V x)` to `mDirDeriv ... x v`
  have hVx : V x = v := rfl
  have hWx : W x = w := rfl
  rw [hVx] at h_compat_vw
  rw [hWx] at h_compat_wv
  -- h_compat_vw : mfderiv (fun y => mDirDeriv f y w) x v = ...
  -- but `mfderiv g x v = mDirDeriv g x v` definitionally
  change mDirDeriv (fun y => mDirDeriv (I := I) f y w) x v = _ at h_compat_vw
  change mDirDeriv (fun y => mDirDeriv (I := I) f y v) x w = _ at h_compat_wv
  -- HessianLie iterate identity. Normalize the inner `(W y)`/`(V y)` to
  -- the constants `w`/`v` via `change` (definitional, since V, W are constants).
  have h_iter := mfderiv_iterate_sub_eq_mlieBracket_apply
    (I := I) (M := M) f V W x h_interior hf hV_cmd hW_cmd
  rw [hVx, hWx] at h_iter
  change mDirDeriv (fun y => mDirDeriv (I := I) f y w) x v
         - mDirDeriv (fun y => mDirDeriv (I := I) f y v) x w
         = mDirDeriv (I := I) f x ((⟦V, W⟧) x) at h_iter
  -- Convert RHS via gradient duality
  have h_grad_dual :
      mDirDeriv (I := I) f x ((⟦V, W⟧) x)
      = g.metricInner x (manifoldGradient (I := I) g f x) ((⟦V, W⟧) x) :=
    (manifoldGradient_inner_eq g f x ((⟦V, W⟧) x)).symm
  rw [h_grad_dual] at h_iter
  -- Identify the connection-toFun terms in h_compat_vw, h_compat_wv with hessianBilin
  have h_hess_lhs :
      g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun
            (manifoldGradient (I := I) g f) x v) w
        = hessianBilin (I := I) g f x v w := rfl
  have h_hess_rhs :
      g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun
            (manifoldGradient (I := I) g f) x w) v
        = hessianBilin (I := I) g f x w v := rfl
  -- Cast h_compat_vw / h_compat_wv to typeclass `metricInner` form for rw matching.
  change mDirDeriv (fun y => mDirDeriv (I := I) f y w) x v
       = g.metricInner x
           ((leviCivitaConnection (I := I) (M := M) g).toFun
             (manifoldGradient (I := I) g f) x v) w
         + g.metricInner x (manifoldGradient (I := I) g f x)
           ((leviCivitaConnection (I := I) (M := M) g).toFun W x v)
    at h_compat_vw
  change mDirDeriv (fun y => mDirDeriv (I := I) f y v) x w
       = g.metricInner x
           ((leviCivitaConnection (I := I) (M := M) g).toFun
             (manifoldGradient (I := I) g f) x w) v
         + g.metricInner x (manifoldGradient (I := I) g f x)
           ((leviCivitaConnection (I := I) (M := M) g).toFun V x w)
    at h_compat_wv
  rw [h_hess_lhs] at h_compat_vw
  rw [h_hess_rhs] at h_compat_wv
  -- The bracket-correction terms via torsion-free + continuous linear map linearity
  have h_inner_diff :
      g.metricInner x (manifoldGradient (I := I) g f x)
          ((leviCivitaConnection (I := I) (M := M) g).toFun W x v)
        - g.metricInner x (manifoldGradient (I := I) g f x)
          ((leviCivitaConnection (I := I) (M := M) g).toFun V x w)
      = g.metricInner x (manifoldGradient (I := I) g f x) ((⟦V, W⟧) x) := by
    rw [← g.metricInner_sub_right, h_torsion']
  -- Combine: subtract h_compat_vw - h_compat_wv, use h_iter to eliminate LHS,
  -- and h_inner_diff to convert the bracket-correction term
  linarith [h_iter, h_compat_vw, h_compat_wv, h_inner_diff]

end Operators
end Riemannian

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [HasMetric I M]

end Riemannian
