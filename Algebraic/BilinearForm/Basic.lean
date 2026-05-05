import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Bilinear forms — algebraic core (field-generic)

A field-generic, fully computable algebraic core for symmetric
positive-definite bilinear forms. This is the foundation upon which
the Riemannian metric API (`Riemannian/Metric/`) is built when the
field happens to be `ℝ` and smoothness is required; on a computable
field like `ℚ`, the same operations evaluate to actual numbers.

## Design

This file deliberately avoids:
- Continuous linear maps (which require topology + `RCLike`)
- Smoothness / `ContMDiff` (which require `ℝ` or `ℂ`)
- Any non-computable Mathlib infrastructure

What remains is pure linear algebra: a bilinear form is a
`B : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜`, with computable `inner`, `IsSymm`, and
`IsPosDef` predicates.

## Reusability

The bilinear-form algebra layer is reusable across:
- Riemannian metrics (when 𝕜 = ℝ, with smoothness added)
- Hermitian forms (when 𝕜 = ℂ)
- Quadratic forms in algebra
- Positive-definite forms in optimization
- Matrix calculus over arbitrary fields

**Ground truth**: standard linear algebra of bilinear forms.
-/

namespace OpenGALib.BilinearForm

/-- A bilinear form on `V` over field `𝕜`: a linear map
`V →ₗ[𝕜] V →ₗ[𝕜] 𝕜`. -/
abbrev Form (𝕜 : Type*) [Field 𝕜]
    (V : Type*) [AddCommGroup V] [Module 𝕜 V] :=
  V →ₗ[𝕜] V →ₗ[𝕜] 𝕜

section Algebra

variable {𝕜 : Type*} [Field 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The bilinear form is symmetric. -/
def IsSymm (B : Form 𝕜 V) : Prop :=
  ∀ v w, B v w = B w v

/-- The **inner product** $\langle v, w \rangle_B$ via a bilinear form. -/
def inner (B : Form 𝕜 V) (v w : V) : 𝕜 :=
  B v w

/-- Inner product unfolds to bilinear-form application. -/
@[simp]
theorem inner_def (B : Form 𝕜 V) (v w : V) :
    inner B v w = B v w := rfl

/-! ## Algebra lemmas

These follow directly from `LinearMap` algebra. They form the field-
generic version of the framework's `metricInner_*` lemmas. -/

/-- **Symmetry** (when the form is symmetric). -/
theorem inner_comm {B : Form 𝕜 V} (hB : IsSymm B) (v w : V) :
    inner B v w = inner B w v :=
  hB v w

/-- **Additivity in left argument**. -/
theorem inner_add_left (B : Form 𝕜 V) (v₁ v₂ w : V) :
    inner B (v₁ + v₂) w = inner B v₁ w + inner B v₂ w := by
  simp [inner_def, map_add, LinearMap.add_apply]

/-- **Additivity in right argument**. -/
theorem inner_add_right (B : Form 𝕜 V) (v w₁ w₂ : V) :
    inner B v (w₁ + w₂) = inner B v w₁ + inner B v w₂ := by
  simp [inner_def, map_add]

/-- **Scalar mult in left argument**. -/
theorem inner_smul_left (B : Form 𝕜 V) (c : 𝕜) (v w : V) :
    inner B (c • v) w = c * inner B v w := by
  simp [inner_def, LinearMap.smul_apply, smul_eq_mul]

/-- **Scalar mult in right argument**. -/
theorem inner_smul_right (B : Form 𝕜 V) (c : 𝕜) (v w : V) :
    inner B v (c • w) = c * inner B v w := by
  simp [inner_def, smul_eq_mul]

/-- **Zero in left argument**. -/
@[simp]
theorem inner_zero_left (B : Form 𝕜 V) (w : V) :
    inner B 0 w = 0 := by
  simp [inner_def]

/-- **Zero in right argument**. -/
@[simp]
theorem inner_zero_right (B : Form 𝕜 V) (v : V) :
    inner B v 0 = 0 := by
  simp [inner_def]

/-- **Negation in left argument**. -/
@[simp]
theorem inner_neg_left (B : Form 𝕜 V) (v w : V) :
    inner B (-v) w = -inner B v w := by
  simp [inner_def, map_neg, LinearMap.neg_apply]

/-- **Negation in right argument**. -/
@[simp]
theorem inner_neg_right (B : Form 𝕜 V) (v w : V) :
    inner B v (-w) = -inner B v w := by
  simp [inner_def, map_neg]

/-- **Subtraction in left argument**. -/
@[simp]
theorem inner_sub_left (B : Form 𝕜 V) (v₁ v₂ w : V) :
    inner B (v₁ - v₂) w = inner B v₁ w - inner B v₂ w := by
  rw [sub_eq_add_neg, inner_add_left, inner_neg_left, sub_eq_add_neg]

/-- **Subtraction in right argument**. -/
@[simp]
theorem inner_sub_right (B : Form 𝕜 V) (v w₁ w₂ : V) :
    inner B v (w₁ - w₂) = inner B v w₁ - inner B v w₂ := by
  rw [sub_eq_add_neg, inner_add_right, inner_neg_right, sub_eq_add_neg]

end Algebra

section Order

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The bilinear form is positive-definite. -/
def IsPosDef (B : Form 𝕜 V) : Prop :=
  ∀ v ≠ 0, 0 < B v v

omit [IsStrictOrderedRing 𝕜] in
/-- **Positive-definite** (when the form is positive-definite). -/
theorem inner_self_pos {B : Form 𝕜 V} (hB : IsPosDef B) (v : V) (hv : v ≠ 0) :
    0 < inner B v v :=
  hB v hv

omit [IsStrictOrderedRing 𝕜] in
/-- **Self-inner non-negativity** (when positive-definite). -/
theorem inner_self_nonneg {B : Form 𝕜 V} (hB : IsPosDef B) (v : V) :
    0 ≤ inner B v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, inner_zero_left]
  · exact le_of_lt (inner_self_pos hB v hv)

end Order

end OpenGALib.BilinearForm
