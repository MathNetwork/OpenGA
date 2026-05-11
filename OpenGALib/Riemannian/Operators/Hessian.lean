import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Gradient
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Hessian on a Riemannian manifold

For a smooth scalar $f : M \to \mathbb{R}$ on a Riemannian manifold $(M, g)$,
the **Hessian** is the symmetric $(0,2)$-tensor given by the second covariant
derivative of $f$. Pointwise:
$$\operatorname{Hess} f(x)(X, Y) = \langle \nabla_X (\nabla^M f), Y \rangle_g(x).$$
Equivalently $\operatorname{Hess} f(X, Y) = X(Y(f)) - (\nabla_X Y)(f)$.

This file provides:

1. The vector-field bilinear form `hessian f X Y x`, defined directly via
   `covDeriv`, `manifoldGradient`, `metricInner`.
2. An abstract pointwise bilinear-form carrier `Bilin I M` and the
   pure-linear-algebra trace–Frobenius Cauchy-Schwarz inequality
   $$\bigl(\sum_i B(b_i, b_i)\bigr)^2 \le n \cdot \sum_{i,j} B(b_i, b_j)^2,$$
   the inequality used to bound $(\Delta f)^2 \le n \cdot |\operatorname{Hess} f|^2$
   downstream of the Bochner identity.

The chart-Christoffel formula and the smoothness of the Hessian as a section
of the $(0,2)$-bundle live with the chart machinery and are out of scope here.

## Main definitions

* `hessian f X Y x` — the Hessian on vector fields.
* `Bilin I M` — pointwise bilinear-form carrier on $TM$.
* `IsPointwiseSymm B` — pointwise symmetry predicate.
* `frobeniusSq B x` — the Frobenius norm squared of `B` against the canonical basis.
* `trace B x` — the trace of `B` against the canonical basis.

## Main results

* `bilinForm_trace_sq_le_card_mul_frobenius_sq` — the linear-algebra
  Cauchy-Schwarz bound for any indexing type.
* `trace_sq_le_dim_mul_frobeniusSq` — pointwise specialisation:
  $(\operatorname{trace} B(x))^2 \le n \cdot \operatorname{frobeniusSq} B(x)$.
* `trace_sq_div_dim_le_frobeniusSq` — quotient form.

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hm : HasMetric I M]

/-! ## Vector-field Hessian -/

/-- The **Hessian** of a smooth scalar `f` on vector fields:
$$\operatorname{Hess} f(X, Y)(x) = \langle \nabla_X (\nabla^M f), Y \rangle_g(x).$$ -/
noncomputable def hessian
    [IsLocallyConstantChartedSpace H M]
    (f : M → ℝ) (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  metricInner x (covDeriv X (manifoldGradient f) x) (Y x)

/-! ## Pointwise bilinear-form carrier -/

variable (I) in
/-- Pointwise real-valued bilinear form on the tangent bundle of $M$. Clients
plug a concrete chart-Hessian (or any `(0,2)`-tensor) into this carrier. -/
abbrev Bilin :=
  ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ

/-- Pointwise symmetry: $B(x)(v, w) = B(x)(w, v)$ for all $x, v, w$. -/
def IsPointwiseSymm (B : Bilin (M := M) I) : Prop :=
  ∀ x : M, ∀ v w : TangentSpace I x, B x v w = B x w v

/-! ## Frobenius and trace, in the canonical basis

`TangentSpace I x = E` definitionally, so the canonical `Module.finBasis ℝ E`
is automatically a basis at every point. Computing Frobenius and trace against
this basis gives scalar functions on $M$. They are not basis-independent in
general (would require a $g$-orthonormal frame); the Cauchy-Schwarz inequality
below holds regardless. -/

/-- Frobenius norm squared $\sum_{i,j} B(x)(e_i, e_j)^2$. -/
def frobeniusSq (B : Bilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))^2

@[simp] lemma frobeniusSq_def (B : Bilin (M := M) I) (x : M) :
    frobeniusSq (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))^2 := rfl

/-- Trace $\sum_i B(x)(e_i, e_i)$. -/
def trace (B : Bilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i)

@[simp] lemma trace_def (B : Bilin (M := M) I) (x : M) :
    trace (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) := rfl

lemma frobeniusSq_nonneg (B : Bilin (M := M) I) (x : M) :
    0 ≤ frobeniusSq (I := I) (M := M) B x :=
  Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-! ## Trace–Frobenius Cauchy-Schwarz -/

/-- $\bigl(\sum_i B(v_i, v_i)\bigr)^2 \le |\iota| \cdot \sum_{i,j} B(v_i, v_j)^2$. -/
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

/-- Specialisation to the canonical basis `Module.finBasis ℝ V`. -/
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

/-- $(\operatorname{trace} B(x))^2 \le n \cdot \operatorname{frobeniusSq} B(x)$, where
$n = \dim_\mathbb{R} E$. The Bochner-style bound (orthonormality not needed). -/
theorem trace_sq_le_dim_mul_frobeniusSq
    (B : Bilin (M := M) I) (x : M) :
    (trace (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSq (I := I) (M := M) B x := by
  have h := bilinForm_trace_sq_le_dim_mul_frobenius_sq
    (V := TangentSpace I x) (B := B x) (b := Module.finBasis ℝ E)
  simp only [trace_def, frobeniusSq_def]
  exact h

/-- The **Hessian as a `Bilin` section**: at each point $x$,
$\operatorname{Hess} f(x)(v, w) = \langle \nabla_{(\text{const }v)}\,\nabla^M f,\,
w\rangle_g(x)$. Tensoriality (independence of the choice of vector-field
extension of $v, w$) is built in: the constant extension $\tilde v(y) := v$
suffices because the Levi-Civita connection is C∞-linear in its first slot
and the second slot is just evaluated. -/
noncomputable def hessianBilin
    [IsLocallyConstantChartedSpace H M]
    (f : M → ℝ) : Bilin (M := M) I := fun x =>
  LinearMap.mk₂ ℝ
    (fun v w => metricInner x
      (covDerivAt (manifoldGradient (I := I) f) x v) w)
    (fun v₁ v₂ w => by
      show metricInner x (covDerivAt (manifoldGradient (I := I) f) x (v₁ + v₂)) w
          = metricInner x (covDerivAt (manifoldGradient (I := I) f) x v₁) w
          + metricInner x (covDerivAt (manifoldGradient (I := I) f) x v₂) w
      rw [map_add, metricInner_add_left])
    (fun c v w => by
      show metricInner x (covDerivAt (manifoldGradient (I := I) f) x (c • v)) w
          = c • metricInner x (covDerivAt (manifoldGradient (I := I) f) x v) w
      rw [(covDerivAt (manifoldGradient (I := I) f) x).map_smul,
          metricInner_smul_left]; rfl)
    (fun v w₁ w₂ => metricInner_add_right x _ w₁ w₂)
    (fun c v w => by
      show metricInner x (covDerivAt (manifoldGradient (I := I) f) x v) (c • w)
          = c • metricInner x (covDerivAt (manifoldGradient (I := I) f) x v) w
      rw [metricInner_smul_right]; rfl)

/-- The Hessian as a `(0,2)`-tensor section `hess_g[I] f`. `I` is
bracketed because `f : M → ℝ` does not expose the model with corners.
For the Frobenius squared norm `|∇²f|²_g`, use polymorphic
`‖hess_g[I] f‖²_g` (the Bilin-section instance of `‖·‖²_g`). -/
scoped[Riemannian] notation:max "hess_g[" I "] " f:max =>
  Operators.hessianBilin (I := I) f

/-- $(\operatorname{trace} B(x))^2 / n \le \operatorname{frobeniusSq} B(x)$. -/
theorem trace_sq_div_dim_le_frobeniusSq
    (B : Bilin (M := M) I) (x : M) :
    (trace (I := I) (M := M) B x)^2 / (Module.finrank ℝ E : ℝ) ≤
      frobeniusSq (I := I) (M := M) B x := by
  have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  exact (div_le_iff₀ hpos).mpr
    (by linarith [trace_sq_le_dim_mul_frobeniusSq (I := I) (M := M) B x])

end Operators
end Riemannian

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Frobenius squared norm on `(0,2)`-tensor sections. Closes the
polymorphic squared-norm story: `‖B‖²_g x = ∑_{ij} B(x)(eᵢ, eⱼ)²`. -/
noncomputable instance instMetricNormSqBilin :
    MetricNormSq (Riemannian.Operators.Bilin (M := M) I) (M → ℝ) where
  normSqG B := fun x => Riemannian.Operators.frobeniusSq (I := I) (M := M) B x

end Riemannian
