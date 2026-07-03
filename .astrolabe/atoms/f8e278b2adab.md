---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M) (x : M) (V W₁ W₂\
  \ : TangentSpace I x),\n  g.metricInner x V (W₁ + W₂) = g.metricInner x V W₁ + g.metricInner\
  \ x V W₂"
file: Riemannian/Metric/RiemannianMetric.lean
line: 115
name: Riemannian.RiemannianMetric.metricInner_add_right
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Metric/RiemannianMetric.lean
ref:
- f8e278b2adab
sort: theorem
source: lean
state: proven
title: metricInner_add_right
---
