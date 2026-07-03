---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] [I.Boundaryless] [CompleteSpace\
  \ E] {g : Riemannian.RiemannianMetric I M} {α : M}\n  {t₀ : ℝ} {f₁ f₂ : ℝ → TangentBundle\
  \ I M},\n  (f₁ t₀).proj ∈ (chartAt H α).source →\n    IsMIntegralCurveAt f₁ (Riemannian.Geodesic.geodesicVectorFieldChart\
  \ g α) t₀ →\n      IsMIntegralCurveAt f₂ (Riemannian.Geodesic.geodesicVectorFieldChart\
  \ g α) t₀ → f₁ t₀ = f₂ t₀ → f₁ =ᶠ[nhds t₀] f₂"
file: Riemannian/Geodesic/Uniqueness.lean
line: 61
name: Riemannian.Geodesic.isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/Uniqueness.lean
ref:
- 3ab0f72efa6b
sort: theorem
source: lean
state: proven
title: isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
---
