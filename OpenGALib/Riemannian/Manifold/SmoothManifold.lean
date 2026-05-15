import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.Util.MetricNotation
import OpenGALib.Util.Attributes
import OpenGALib.Riemannian.TangentBundle.LocallyConstant

/-!
# Smooth and Riemannian manifolds — bundled typeclass

A pure-math user reasons about a Riemannian manifold as the data
$(M, g)$; the Mathlib machinery $(E, H, I, \text{ChartedSpace},
\text{IsManifold})$ is implementation detail. The typeclasses here
bundle that machinery:

  * `[SmoothManifold M]` — $(E, H, I)$ + chart machinery + smooth
    structure (one typeclass replaces five parameters).
  * `[RiemannianManifold M]` — extends `[SmoothManifold M]` with a
    Riemannian metric (one typeclass replaces six).

Downstream operators (`metricInner`, `manifoldGradient`, `Δ_g`, `Ric`)
take `[RiemannianManifold M]` and recover everything they need. The
metric lives on the typeclass as a `RiemannianMetric modelI M` field
(data, not nested typeclass), so polymorphic notation can pull it
without `[I]`-bracket workarounds.

Other geometric structures (Lorentzian, Kähler, symplectic, contact)
extend `SmoothManifold M` analogously and provide bridge instances to
their structure-specific typeclasses.

**Ground truth**: do Carmo §1.1; Lee, *Smooth Manifolds*, Ch. 1, 13.
-/

open Bundle
open scoped ContDiff Manifold Bundle

namespace Riemannian

/-- **Math.** A **smooth manifold** as a single bundled typeclass.
Packages `(E, H, modelI)` plus the complete typeclass cascade
(`NormedAddCommGroup E`, `NormedSpace ℝ E`, `FiniteDimensional ℝ E`,
`CompleteSpace E`, `TopologicalSpace H`, `ChartedSpace H M`,
`IsManifold modelI ∞ M`, `IsLocallyConstantChartedSpace H M`) needed by
Riemannian operators. `[SmoothManifold M]` reads "M is a smooth
finite-dimensional manifold" — the textbook setting. -/
class SmoothManifold (M : Type*) [TopologicalSpace M] where
  /-- The model fibre. -/
  E : Type*
  [normedAddCommGroup_E : NormedAddCommGroup E]
  [normedSpace_E : NormedSpace ℝ E]
  [finiteDimensional_E : FiniteDimensional ℝ E]
  [completeSpace_E : CompleteSpace E]
  /-- The model chart codomain. -/
  H : Type*
  [topologicalSpace_H : TopologicalSpace H]
  /-- The model with corners specifying $M$'s smooth structure. -/
  modelI : ModelWithCorners ℝ E H
  [chartedSpace_M : ChartedSpace H M]
  [isManifold_M : IsManifold modelI ∞ M]
  [isLocallyConstantChartedSpace_M : IsLocallyConstantChartedSpace H M]

/-- **Math.** A **Riemannian manifold** $(M, g)$ as a single bundled
typeclass. Extends `SmoothManifold M` with a `metric : RiemannianMetric
modelI M` field (data). Also bundles `[InnerProductSpace ℝ E]` and
`[NeZero (Module.finrank ℝ E)]` so the full cascade for Bochner,
Lichnerowicz, second-variation is provided by `[RiemannianManifold M]`
alone. -/
class RiemannianManifold (M : Type*) [TopologicalSpace M]
    extends SmoothManifold M where
  [innerProductSpace_E : InnerProductSpace ℝ E]
  [neZero_finrank_E : NeZero (Module.finrank ℝ E)]
  /-- The metric on $M$, attached to the inherited `modelI`. -/
  metric : RiemannianMetric modelI M

/-! ## Global instance bridges

Class fields tagged `[...]` are accessible to type-class search only via
parent-chain projection from `[SmoothManifold M]` / `[RiemannianManifold
M]`. Lean's TC engine can occasionally fail to chain these projections at
the right elaboration sites (especially when the projected type appears
under an `outParam` like `E` here). The bridges below promote each
instance field to a top-level instance so synthesis is direct. -/

section SmoothManifoldBridges

variable {M : Type*} [TopologicalSpace M] [s : SmoothManifold M]

instance : NormedAddCommGroup s.E := s.normedAddCommGroup_E
instance : NormedSpace ℝ s.E := s.normedSpace_E
instance : FiniteDimensional ℝ s.E := s.finiteDimensional_E
instance : CompleteSpace s.E := s.completeSpace_E
instance : TopologicalSpace s.H := s.topologicalSpace_H
instance : ChartedSpace s.H M := s.chartedSpace_M
instance : IsManifold s.modelI ∞ M := s.isManifold_M
instance : IsLocallyConstantChartedSpace s.H M := s.isLocallyConstantChartedSpace_M

end SmoothManifoldBridges

section RiemannianManifoldBridges

variable {M : Type*} [TopologicalSpace M] [rm : RiemannianManifold M]

instance : InnerProductSpace ℝ rm.E := rm.innerProductSpace_E
instance : NeZero (Module.finrank ℝ rm.E) := rm.neZero_finrank_E

/-- **Eng.** The metric carried by `[RiemannianManifold M]` induces a
global `Bundle.RiemannianBundle (TangentSpace modelI : M → Type _)`,
activating Mathlib's scoped `NormedAddCommGroup` / `InnerProductSpace ℝ` on each
fibre. Single `NormedAddCommGroup` / `InnerProductSpace` source — sidesteps the
lean4#13063 `NormedAddCommGroup` diamond. -/
noncomputable instance instRiemannianBundleOfRiemannianManifold :
    Bundle.RiemannianBundle (TangentSpace rm.modelI : M → Type _) :=
  ⟨rm.metric.toRiemannianMetric⟩

/-- **Eng.** Bridge: `[RiemannianManifold M] → [HasMetric (SmoothManifold.modelI M) M]`.
Lets every `[HasMetric I M]`-keyed API work uniformly for bundled and
explicit-metric callers. -/
instance instHasMetricOfRiemannianManifold :
    HasMetric rm.modelI M where
  metric := rm.metric

end RiemannianManifoldBridges

/-! ## Math-first metric API

Downstream operator code reads as textbook math when the metric is
carried implicitly by `[HasMetric I M]`:

* `metricInner x v w`           (inner product on `T_xM`, not `g.metricInner`)
* `metricRiesz x φ`             (Riesz dual vector)
* `metricInner_add_left ...`    (algebra lemmas, bare names)

Each wrapper takes `[HasMetric I M]` as instance argument and delegates
to the underlying `RiemannianMetric.X` method on `HasMetric.metric`.
Wrappers are `abbrev` / direct delegations so `g.X`-style proofs still
work via abbrev unfolding, and so the `@[simp]` / `@[metric_simp]` simp
sets unify naturally with the underlying method-form lemmas. -/

section MetricAPI

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hm : HasMetric I M]

/-- **Math.** The **metric inner product** $\langle V, W\rangle_g$ as a
top-level function, sourcing $g$ from `[HasMetric I M]`. -/
noncomputable abbrev metricInner (x : M)
    (v w : TangentSpace I x) : ℝ :=
  hm.metric.metricInner x v w

@[simp]
theorem metricInner_apply (x : M) (v w : TangentSpace I x) :
    metricInner x v w = hm.metric.inner x v w := rfl

/-- **Math.** Symmetry: $\langle V, W\rangle_g = \langle W, V\rangle_g$. -/
theorem metricInner_comm (x : M) (v w : TangentSpace I x) :
    metricInner x v w = metricInner x w v :=
  hm.metric.metricInner_comm x v w

/-- **Math.** Positive-definiteness: $V \ne 0 \Rightarrow \langle V, V\rangle_g > 0$. -/
theorem metricInner_self_pos (x : M) (v : TangentSpace I x)
    (hv : v ≠ 0) : 0 < metricInner x v v :=
  hm.metric.metricInner_self_pos x v hv

@[metric_simp]
theorem metricInner_add_left (x : M) (v₁ v₂ w : TangentSpace I x) :
    metricInner x (v₁ + v₂) w = metricInner x v₁ w + metricInner x v₂ w :=
  hm.metric.metricInner_add_left x v₁ v₂ w

@[metric_simp]
theorem metricInner_add_right (x : M) (v w₁ w₂ : TangentSpace I x) :
    metricInner x v (w₁ + w₂) = metricInner x v w₁ + metricInner x v w₂ :=
  hm.metric.metricInner_add_right x v w₁ w₂

@[metric_simp]
theorem metricInner_smul_left (x : M) (c : ℝ)
    (v w : TangentSpace I x) :
    metricInner x (c • v) w = c * metricInner x v w :=
  hm.metric.metricInner_smul_left x c v w

@[metric_simp]
theorem metricInner_smul_right (x : M) (c : ℝ)
    (v w : TangentSpace I x) :
    metricInner x v (c • w) = c * metricInner x v w :=
  hm.metric.metricInner_smul_right x c v w

@[simp, metric_simp]
theorem metricInner_zero_left (x : M) (w : TangentSpace I x) :
    metricInner x 0 w = 0 :=
  hm.metric.metricInner_zero_left x w

@[simp, metric_simp]
theorem metricInner_zero_right (x : M) (v : TangentSpace I x) :
    metricInner x v 0 = 0 :=
  hm.metric.metricInner_zero_right x v

@[simp, metric_simp]
theorem metricInner_neg_left (x : M) (v w : TangentSpace I x) :
    metricInner x (-v) w = -metricInner x v w :=
  hm.metric.metricInner_neg_left x v w

@[simp, metric_simp]
theorem metricInner_neg_right (x : M) (v w : TangentSpace I x) :
    metricInner x v (-w) = -metricInner x v w :=
  hm.metric.metricInner_neg_right x v w

@[simp, metric_simp]
theorem metricInner_sub_left (x : M) (v₁ v₂ w : TangentSpace I x) :
    metricInner x (v₁ - v₂) w = metricInner x v₁ w - metricInner x v₂ w :=
  hm.metric.metricInner_sub_left x v₁ v₂ w

@[simp, metric_simp]
theorem metricInner_sub_right (x : M) (v w₁ w₂ : TangentSpace I x) :
    metricInner x v (w₁ - w₂) = metricInner x v w₁ - metricInner x v w₂ :=
  hm.metric.metricInner_sub_right x v w₁ w₂

@[simp, metric_simp]
theorem metricInner_self_nonneg (x : M) (v : TangentSpace I x) :
    0 ≤ metricInner x v v :=
  hm.metric.metricInner_self_nonneg x v

/-- **Math.** Non-degeneracy: vectors with equal inner-products against every test
vector are equal. -/
theorem metricInner_eq_iff_eq (x : M) (v w : TangentSpace I x) :
    (∀ z : TangentSpace I x, metricInner x v z = metricInner x w z) ↔
      v = w :=
  hm.metric.metricInner_eq_iff_eq x v w

section RieszSection

variable [FiniteDimensional ℝ E]

/-- **Math.** The **metric-to-dual** continuous linear map $V \mapsto g_x(V, \cdot)$. -/
noncomputable abbrev metricToDual (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  hm.metric.metricToDual x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricToDual_apply (x : M) (v w : TangentSpace I x) :
    metricToDual x v w = metricInner x v w := rfl

omit [FiniteDimensional ℝ E] in
theorem metricToDual_injective (x : M) :
    Function.Injective (metricToDual (I := I) (M := M) x) :=
  hm.metric.metricToDual_injective x

theorem metricToDual_bijective (x : M) :
    Function.Bijective (metricToDual (I := I) (M := M) x) :=
  hm.metric.metricToDual_bijective x

/-- **Math.** Inverse Riesz: $\varphi \mapsto V_\varphi$ such that
$g_x(V_\varphi, W) = \varphi(W)$. -/
noncomputable abbrev metricRiesz (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) : TangentSpace I x :=
  hm.metric.metricRiesz x φ

@[simp]
theorem metricRiesz_inner (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) (v : TangentSpace I x) :
    metricInner x (metricRiesz x φ) v = φ v :=
  hm.metric.metricRiesz_inner x φ v

theorem metricRiesz_unique (x : M) (v : TangentSpace I x)
    (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, metricInner x v w = φ w) :
    v = metricRiesz x φ :=
  hm.metric.metricRiesz_unique x v φ h

/-- **Math.** The Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)`. -/
noncomputable abbrev metricToDualEquiv (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  hm.metric.metricToDualEquiv x

end RieszSection

/-! ## Smoothness of the metric inner product — Math headline

`metricInner y (v y) (w y)` is `ContMDiffWithinAt` whenever the
tangent-bundle sections `v, w` are. The pointwise / set / global parity
variants, the first-order `MDifferentiable*` analog family, and the
`TangentSmoothAt`-form convenience wrapper all live in
`Riemannian/Util/MetricInnerSmoothness.lean`. -/

section Smoothness

variable {v w : ∀ x : M, TangentSpace I x} {s : Set M} {x : M}

variable {n : ℕ∞ω} [hLE : ENat.LEInfty n]

/-- **Math.** $\langle v(\cdot), w(\cdot)\rangle_g$ is `ContMDiffWithinAt`. -/
theorem metricInner_contMDiffWithinAt
    (hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s x)
    (hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s x) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) n
      (fun y => metricInner y (v y) (w y)) s x :=
  hm.metric.metricInner_contMDiffWithinAt hv hw

end Smoothness

end MetricAPI

-- Polymorphic notation `⟪·, ·⟫_g` and `‖·‖²_g` (and the dispatch classes
-- `MetricInnerHom`, `MetricNormSq`) live in
-- `OpenGALib/Riemannian/Util/MetricNotation.lean`; the import below
-- pulls them into scope for every consumer of `SmoothManifold`.

end Riemannian
