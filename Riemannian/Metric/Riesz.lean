import Riemannian.Metric.Basic

/-!
# Framework-owned Riesz extraction

Build out the Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)` via the metric
tensor's positive-definiteness + finite-dim invertibility, providing the
framework's replacement for Mathlib's `(InnerProductSpace.toDual ℝ _).symm`.
-/

open scoped ContDiff Manifold Topology

namespace OpenGALib

section RieszExtraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

/-- **Forward Riesz**: vector → linear functional via metric. -/
noncomputable def metricToDual (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.metricTensor x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricToDual_apply (x : M) (v w : TangentSpace I x) :
    metricToDual (g := g) x v w = metricInner x v w :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Injectivity of forward Riesz**: from positive-definiteness. -/
theorem metricToDual_injective (x : M) :
    Function.Injective (metricToDual (g := g) x) := by
  intro v₁ v₂ h
  by_contra hne
  have hsub : v₁ - v₂ ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < metricInner x (v₁ - v₂) (v₁ - v₂) :=
    metricInner_self_pos x _ hsub
  have key : ∀ w, metricInner x v₁ w = metricInner x v₂ w := by
    intro w
    exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) h
  have hzero : metricInner x (v₁ - v₂) (v₁ - v₂) = 0 := by
    rw [metricInner_sub_left, key (v₁ - v₂), sub_self]
  linarith

omit [FiniteDimensional ℝ E] in
/-- **Vector equality via inner-product equality** (non-degeneracy).

Two tangent vectors at $x$ are equal iff their inner products with all
test vectors agree. Direct corollary of `metricToDual_injective`. -/
theorem metricInner_eq_iff_eq (x : M) (v w : TangentSpace I x) :
    (∀ Z : TangentSpace I x, metricInner x v Z = metricInner x w Z) ↔ v = w := by
  refine ⟨fun h => ?_, fun h _ => by rw [h]⟩
  apply metricToDual_injective x
  ext Z
  simpa [metricToDual_apply] using h Z

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
