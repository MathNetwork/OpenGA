import Riemannian.Metric.Basic
import Algebraic.BilinearForm.Riesz

/-!
# Framework-owned Riesz extraction

The Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)` via the metric
tensor's positive-definiteness + finite-dim invertibility, providing
the framework's replacement for Mathlib's
`(InnerProductSpace.toDual ℝ _).symm`.

## Architecture

The mathematical content of Riesz extraction is field-generic and
lives in `Algebraic/BilinearForm/Riesz.lean` (works on any positive-
definite bilinear form over a finite-dim vector space, computable
when the field is). This file is the Riemannian-specific wrapper:

  * Translates between the Riemannian `metricInner` / `metricTensor`
    API (uses `→L[ℝ]` continuous linear maps) and the algebraic core
    `BilinearForm.inner` / `BilinearForm.toDual` (uses `→ₗ[ℝ]` linear
    maps), via the `RiemannianMetric.toBilinForm` bridge.
  * Each Riemannian Riesz lemma is a 1-2 line wrapper around the
    algebraic-core lemma plus the bridge.

Public API (`metricToDual`, `metricRiesz`, `metricRiesz_inner`,
`metricRiesz_unique`, `metricInner_eq_iff_eq`) is unchanged.
-/

open scoped ContDiff Manifold Topology

namespace OpenGALib

section RieszExtraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

/-- The bridge form `toBilinForm x` is positive-definite, derived
from the typeclass `posdef` axiom. -/
theorem RiemannianMetric.toBilinForm_isPosDef (x : M) :
    BilinearForm.IsPosDef (RiemannianMetric.toBilinForm (g := g) x) := by
  intro v hv
  show 0 < (RiemannianMetric.toBilinForm (g := g) x) v v
  show 0 < g.metricTensor x v v
  exact g.posdef x v hv

/-- **Forward Riesz**: vector → linear functional via metric (CLM form). -/
noncomputable def metricToDual (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.metricTensor x

@[simp]
theorem metricToDual_apply (x : M) (v w : TangentSpace I x) :
    metricToDual (g := g) x v w = metricInner x v w := by
  rw [metricInner_apply]; rfl

/-- **Injectivity of forward Riesz**: from positive-definiteness.
Inherited via the algebraic core. -/
theorem metricToDual_injective (x : M) :
    Function.Injective (metricToDual (g := g) x) := by
  intro v₁ v₂ h
  apply BilinearForm.toDual_injective (RiemannianMetric.toBilinForm_isPosDef (g := g) x)
  ext w
  show (RiemannianMetric.toBilinForm (g := g) x) v₁ w
      = (RiemannianMetric.toBilinForm (g := g) x) v₂ w
  show g.metricTensor x v₁ w = g.metricTensor x v₂ w
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) h

/-- **Vector equality via inner-product equality** (non-degeneracy).

Inherited from `BilinearForm.inner_eq_iff_eq`. -/
theorem metricInner_eq_iff_eq (x : M) (v w : TangentSpace I x) :
    (∀ Z : TangentSpace I x, metricInner x v Z = metricInner x w Z) ↔ v = w :=
  BilinearForm.inner_eq_iff_eq (RiemannianMetric.toBilinForm_isPosDef (g := g) x) v w

omit g in
/-- finrank of `TangentSpace I x →L[ℝ] ℝ` equals finrank of `TangentSpace I x`. -/
private theorem finrank_clm_dual_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x →L[ℝ] ℝ) =
      Module.finrank ℝ (TangentSpace I x) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  rw [← LinearEquiv.finrank_eq
    (LinearMap.toContinuousLinearMap : (TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _)]
  exact Subspace.dual_finrank_eq

/-- **Bijectivity of forward Riesz**: injective + same `finrank` ⇒ bijective. -/
theorem metricToDual_bijective (x : M) :
    Function.Bijective (metricToDual (g := g) x) := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  haveI : FiniteDimensional ℝ (TangentSpace I x →L[ℝ] ℝ) :=
    Module.Finite.equiv (LinearMap.toContinuousLinearMap :
      (TangentSpace I x →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ))
  refine ⟨metricToDual_injective x, ?_⟩
  have h_finrank := finrank_clm_dual_eq (I := I) (M := M) x
  have hiff := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (metricToDual (g := g) x).toLinearMap) h_finrank.symm
  exact hiff.mp (metricToDual_injective (g := g) x)

/-- The Riesz isomorphism as a `LinearEquiv`. -/
noncomputable def metricToDualEquiv (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.ofBijective (metricToDual (g := g) x).toLinearMap
    (metricToDual_bijective (g := g) x)

/-- **Inverse Riesz**: linear functional → vector via metric. -/
noncomputable def metricRiesz (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x :=
  (metricToDualEquiv (g := g) x).symm φ

/-- **Riesz defining property**: $\langle \text{metricRiesz}\,\varphi, V\rangle_g
= \varphi(V)$. -/
theorem metricRiesz_inner (x : M) (φ : TangentSpace I x →L[ℝ] ℝ)
    (V : TangentSpace I x) :
    metricInner x (metricRiesz (g := g) x φ) V = φ V := by
  rw [metricInner_apply]
  show metricToDual (g := g) x (metricRiesz (g := g) x φ) V = φ V
  have heq : (metricToDual (g := g) x).toLinearMap
      ((metricToDualEquiv (g := g) x).symm φ) = φ :=
    (metricToDualEquiv (g := g) x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f V) heq

/-- **Riesz uniqueness**: if `v` represents `φ`, then `v = metricRiesz x φ`. -/
theorem metricRiesz_unique (x : M) (v : TangentSpace I x)
    (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, metricInner x v w = φ w) :
    v = metricRiesz (g := g) x φ := by
  apply metricToDual_injective (g := g) x
  ext w
  rw [metricToDual_apply, h w]
  show φ w = metricToDual (g := g) x (metricRiesz (g := g) x φ) w
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w)
    ((metricToDualEquiv (g := g) x).apply_symm_apply φ).symm

end RieszExtraction

end OpenGALib
