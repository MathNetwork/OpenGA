import Algebraic.BilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Riesz extraction — algebraic core

Field-generic Riesz isomorphism for symmetric positive-definite
bilinear forms on finite-dimensional vector spaces. Given a
positive-definite `B : Form 𝕜 V`, every linear functional
`φ : V →ₗ[𝕜] 𝕜` has a unique vector representative `v` such that
`B v w = φ w` for all `w`.

This is the algebraic substrate of the Riemannian module's
`metricRiesz` operation: when 𝕜 = ℝ and the bilinear form is the
metric tensor, we recover the standard Riemannian Riesz duality
between vectors and 1-forms.

## Reusability

Riesz extraction is not Riemannian-specific. The same construction
applies to:
- Hermitian forms on ℂ-vector spaces (with conjugate)
- Quadratic forms in algebraic optimization
- Inner-product-style dualities in any positive-definite setting

**Ground truth**: standard fact in linear algebra; on a finite-dim
vector space, a positive-definite bilinear form gives a vector-space
isomorphism with the dual space.
-/

namespace OpenGALib.BilinearForm

section Riesz

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- **Forward Riesz**: vector → linear functional via bilinear form.
By definition just the bilinear form itself, viewed as `V →ₗ[𝕜] (V →ₗ[𝕜] 𝕜)`. -/
def toDual (B : Form 𝕜 V) : V →ₗ[𝕜] (V →ₗ[𝕜] 𝕜) := B

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem toDual_apply (B : Form 𝕜 V) (v w : V) :
    toDual B v w = inner B v w := rfl

/-- **Injectivity of forward Riesz**: from positive-definiteness. -/
theorem toDual_injective {B : Form 𝕜 V} (hB : IsPosDef B) :
    Function.Injective (toDual B) := by
  intro v₁ v₂ h
  by_contra hne
  have hsub : v₁ - v₂ ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < inner B (v₁ - v₂) (v₁ - v₂) :=
    inner_self_pos hB _ hsub
  have key : ∀ w, inner B v₁ w = inner B v₂ w := fun w =>
    congrArg (fun (f : V →ₗ[𝕜] 𝕜) => f w) h
  have hzero : inner B (v₁ - v₂) (v₁ - v₂) = 0 := by
    rw [inner_sub_left, key (v₁ - v₂), sub_self]
  linarith

/-- **Vector equality via inner-product equality** (non-degeneracy):
two vectors are equal iff their inner products with all test vectors agree. -/
theorem inner_eq_iff_eq {B : Form 𝕜 V} (hB : IsPosDef B) (v w : V) :
    (∀ z, inner B v z = inner B w z) ↔ v = w := by
  refine ⟨fun h => ?_, fun h _ => by rw [h]⟩
  apply toDual_injective hB
  ext z
  simpa [toDual_apply] using h z

variable [FiniteDimensional 𝕜 V]

/-- **Bijectivity of forward Riesz**: injective + same finrank ⇒ bijective. -/
theorem toDual_bijective {B : Form 𝕜 V} (hB : IsPosDef B) :
    Function.Bijective (toDual B) := by
  refine ⟨toDual_injective hB, ?_⟩
  have h_finrank : Module.finrank 𝕜 (V →ₗ[𝕜] 𝕜) = Module.finrank 𝕜 V :=
    Subspace.dual_finrank_eq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := toDual B) h_finrank.symm).mp (toDual_injective hB)

/-- The Riesz isomorphism as a `LinearEquiv`. -/
noncomputable def toDualEquiv {B : Form 𝕜 V} (hB : IsPosDef B) :
    V ≃ₗ[𝕜] (V →ₗ[𝕜] 𝕜) :=
  LinearEquiv.ofBijective (toDual B) (toDual_bijective hB)

/-- **Inverse Riesz**: linear functional → vector via bilinear form. -/
noncomputable def riesz {B : Form 𝕜 V} (hB : IsPosDef B)
    (φ : V →ₗ[𝕜] 𝕜) : V :=
  (toDualEquiv hB).symm φ

/-- **Riesz defining property**: `inner B (riesz hB φ) v = φ v`. -/
theorem riesz_inner {B : Form 𝕜 V} (hB : IsPosDef B)
    (φ : V →ₗ[𝕜] 𝕜) (v : V) :
    inner B (riesz hB φ) v = φ v := by
  show toDual B (riesz hB φ) v = φ v
  have heq : toDual B ((toDualEquiv hB).symm φ) = φ :=
    (toDualEquiv hB).apply_symm_apply φ
  exact congrArg (fun (f : V →ₗ[𝕜] 𝕜) => f v) heq

/-- **Riesz uniqueness**: if `v` represents `φ`, then `v = riesz hB φ`. -/
theorem riesz_unique {B : Form 𝕜 V} (hB : IsPosDef B) (v : V)
    (φ : V →ₗ[𝕜] 𝕜) (h : ∀ w, inner B v w = φ w) :
    v = riesz hB φ := by
  apply toDual_injective hB
  ext w
  rw [toDual_apply, h w]
  show φ w = toDual B (riesz hB φ) w
  have heq : toDual B ((toDualEquiv hB).symm φ) = φ :=
    (toDualEquiv hB).apply_symm_apply φ
  exact congrArg (fun (f : V →ₗ[𝕜] 𝕜) => f w) heq.symm

end Riesz

end OpenGALib.BilinearForm
