import OpenGALib.Riemannian.Manifold.SmoothManifold
import OpenGALib.Riemannian.TangentBundle.TangentSmooth

/-!
# `metricInner` smoothness — pointwise / set / global variants

Engineering parity API expanding the Math headlines

* `Riemannian.RiemannianMetric.metricInner_contMDiffWithinAt`
  (Metric.lean — real proof via `ContMDiffWithinAt.inner_bundle`)
* `Riemannian.metricInner_contMDiffWithinAt`
  (Manifold.lean — typeclass-bound restatement)

into the full `_within_at / _at / _on / _` parity for both the
explicit-metric form `g.metricInner_X` and the typeclass-bound form
`metricInner_X` keyed on `[HasMetric I M]`. Each variant is a pointwise
reduction to the Math headline.
-/

open Bundle
open scoped ContDiff Manifold Bundle

namespace Riemannian.RiemannianMetric

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {v w : ∀ x : M, TangentSpace I x} {s : Set M} {x : M}

/-! ### `ContMDiff` family — smoothness order `n ≤ ∞` -/

variable {n : ℕ∞ω} [hLE : ENat.LEInfty n]

/-- **Eng.** Pointwise variant. -/
theorem metricInner_contMDiffAt
    (g : RiemannianMetric I M)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) x)
    (hw : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) x :=
  g.metricInner_contMDiffWithinAt hv hw

/-- **Eng.** Set-form variant. -/
theorem metricInner_contMDiffOn
    (g : RiemannianMetric I M)
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s)
    (hw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s) :
    ContMDiffOn I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) s :=
  fun y hy => g.metricInner_contMDiffWithinAt (hv y hy) (hw y hy)

/-- **Eng.** Global variant. -/
theorem metricInner_contMDiff
    (g : RiemannianMetric I M)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M))) :
    ContMDiff I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) :=
  fun y => g.metricInner_contMDiffAt (hv y) (hw y)

/-! ### `MDifferentiable` family — first-order differentiability -/

/-- **Eng.** Differentiable-within-at variant. -/
theorem metricInner_mdifferentiableWithinAt
    (g : RiemannianMetric I M)
    (hv : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s x)
    (hw : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s x) :
    MDifferentiableWithinAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) s x := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact MDifferentiableWithinAt.inner_bundle (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _)) (b := fun y => y)
    (v := v) (w := w) (IM := I) hv hw

/-- **Eng.** Pointwise differentiability. -/
theorem metricInner_mdifferentiableAt
    (g : RiemannianMetric I M)
    (hv : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) x)
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) x :=
  g.metricInner_mdifferentiableWithinAt hv hw

/-- **Eng.** Set-form differentiability. -/
theorem metricInner_mdifferentiableOn
    (g : RiemannianMetric I M)
    (hv : MDifferentiableOn I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s)
    (hw : MDifferentiableOn I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s) :
    MDifferentiableOn I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) s :=
  fun y hy => g.metricInner_mdifferentiableWithinAt (hv y hy) (hw y hy)

/-- **Eng.** Global differentiability. -/
theorem metricInner_mdifferentiable
    (g : RiemannianMetric I M)
    (hv : MDifferentiable I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (hw : MDifferentiable I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M))) :
    MDifferentiable I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (v y) (w y)) :=
  fun y => g.metricInner_mdifferentiableAt (hv y) (hw y)

end Smoothness

end Riemannian.RiemannianMetric

namespace Riemannian

section MetricInnerSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hm : HasMetric I M]
  {v w : ∀ x : M, TangentSpace I x} {s : Set M} {x : M}

/-! ### `ContMDiff` family — smoothness order `n ≤ ∞` -/

variable {n : ℕ∞ω} [hLE : ENat.LEInfty n]

/-- **Eng.** Pointwise variant. -/
theorem metricInner_contMDiffAt
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) x)
    (hw : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n
      (fun y => metricInner y (v y) (w y)) x :=
  hm.metric.metricInner_contMDiffAt hv hw

/-- **Eng.** Set-form variant. -/
theorem metricInner_contMDiffOn
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s)
    (hw : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s) :
    ContMDiffOn I 𝓘(ℝ, ℝ) n
      (fun y => metricInner y (v y) (w y)) s :=
  hm.metric.metricInner_contMDiffOn hv hw

/-- **Eng.** Global variant. -/
theorem metricInner_contMDiff
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M))) :
    ContMDiff I 𝓘(ℝ, ℝ) n
      (fun y => metricInner y (v y) (w y)) :=
  hm.metric.metricInner_contMDiff hv hw

/-! ### `MDifferentiable` family — first-order differentiability -/

/-- **Eng.** Differentiable-within-at variant. -/
theorem metricInner_mdifferentiableWithinAt
    (hv : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s x)
    (hw : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s x) :
    MDifferentiableWithinAt I 𝓘(ℝ, ℝ)
      (fun y => metricInner y (v y) (w y)) s x :=
  hm.metric.metricInner_mdifferentiableWithinAt hv hw

/-- **Eng.** Pointwise differentiability. -/
theorem metricInner_mdifferentiableAt
    (hv : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) x)
    (hw : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => metricInner y (v y) (w y)) x :=
  hm.metric.metricInner_mdifferentiableAt hv hw

/-- **Eng.** Set-form differentiability. -/
theorem metricInner_mdifferentiableOn
    (hv : MDifferentiableOn I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s)
    (hw : MDifferentiableOn I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s) :
    MDifferentiableOn I 𝓘(ℝ, ℝ)
      (fun y => metricInner y (v y) (w y)) s :=
  hm.metric.metricInner_mdifferentiableOn hv hw

/-- **Eng.** Global differentiability. -/
theorem metricInner_mdifferentiable
    (hv : MDifferentiable I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, v y⟩ : TangentBundle I M)))
    (hw : MDifferentiable I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, w y⟩ : TangentBundle I M))) :
    MDifferentiable I 𝓘(ℝ, ℝ)
      (fun y => metricInner y (v y) (w y)) :=
  hm.metric.metricInner_mdifferentiable hv hw

/-- **Eng.** `TangentSmoothAt`-form pointwise differentiability — convenience
wrapper that converts the framework's `TangentSmoothAt` predicate to
the underlying `MDifferentiableAt` bundle-section form. -/
theorem metricInner_mdifferentiableAt_of_tangentSmoothAt
    {Y Z : ∀ y : M, TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => metricInner y (Y y) (Z y)) x :=
  metricInner_mdifferentiableAt hY.toBundleSection hZ.toBundleSection

end MetricInnerSmoothness

end Riemannian
