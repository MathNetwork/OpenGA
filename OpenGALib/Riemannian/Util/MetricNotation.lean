import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Polymorphic metric notation — `⟪·, ·⟫_g` and `‖·‖²_g`

Engineering typeclass dispatch for the metric inner product and squared
norm notations so the same syntax works on tangent vectors (yielding `ℝ`)
and on tangent-bundle sections / vector fields (yielding `M → ℝ`).

Reference: do Carmo 1992 §1.2 (inner product).
-/

open scoped ContDiff Manifold

namespace Riemannian

/-- **Eng.** Polymorphic squared norm typeclass dispatch. -/
class MetricNormSq (V : Type*) (R : outParam Type*) where
  /-- The squared norm `‖·‖²_g`. -/
  normSqG : V → R

/-- **Eng.** Polymorphic inner product typeclass dispatch. -/
class MetricInnerHom (V W : Type*) (R : outParam Type*) where
  /-- The inner product `⟪·, ·⟫_g`. -/
  innerG : V → W → R

section MetricNotationInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [HasMetric I M]

/-- **Math.** Pointwise tangent-vector squared norm $\|V\|^2_g$. -/
noncomputable instance instMetricNormSqTangent (x : M) :
    MetricNormSq (TangentSpace I x) ℝ where
  normSqG v := HasMetric.metric.metricInner x v v

/-- **Math.** Section-level squared norm: vector field `V` ↦ scalar function
`y ↦ ⟨V(y), V(y)⟩_g`. -/
noncomputable instance instMetricNormSqSection :
    MetricNormSq ((y : M) → TangentSpace I y) (M → ℝ) where
  normSqG V := fun y => HasMetric.metric.metricInner y (V y) (V y)

/-- **Math.** Pointwise tangent-vector inner product $\langle V, W\rangle_g$. -/
noncomputable instance instMetricInnerHomTangent (x : M) :
    MetricInnerHom (TangentSpace I x) (TangentSpace I x) ℝ where
  innerG v w := HasMetric.metric.metricInner x v w

/-- **Math.** Section-level inner product: pair of vector fields ↦ scalar function
`y ↦ ⟨V(y), W(y)⟩_g`. -/
noncomputable instance instMetricInnerHomSection :
    MetricInnerHom ((y : M) → TangentSpace I y) ((y : M) → TangentSpace I y)
      (M → ℝ) where
  innerG V W := fun y => HasMetric.metric.metricInner y (V y) (W y)

end MetricNotationInstances

/-- **Math.** Notation `⟪V, W⟫_g` for the metric inner product. Pointwise on tangent vectors → `ℝ`;
on two sections → `M → ℝ`. -/
scoped notation:max "⟪" V ", " W "⟫_g" => MetricInnerHom.innerG V W

/-- **Math.** Notation `‖V‖²_g` for the squared norm. Pointwise on a tangent vector → `ℝ`;
on a section → `M → ℝ`. -/
scoped notation:max "‖" V "‖²_g" => MetricNormSq.normSqG V

end Riemannian
