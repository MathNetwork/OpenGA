---
content: "{E : Type u_1} →\n  [inst : NormedAddCommGroup E] →\n    [inst_1 : NormedSpace\
  \ ℝ E] →\n      [FiniteDimensional ℝ E] →\n        {H : Type u_2} →\n          [inst_3\
  \ : TopologicalSpace H] →\n            {I : ModelWithCorners ℝ E H} →\n        \
  \      {M : Type u_3} →\n                [inst_4 : TopologicalSpace M] →\n     \
  \             [inst_5 : ChartedSpace H M] →\n                    [inst_6 : IsManifold\
  \ I (↑⊤) M] →\n                      Riemannian.RiemannianMetric I M → (x : M) →\
  \ (TangentSpace I x →L[ℝ] ℝ) → TangentSpace I x"
file: Riemannian/Metric/RiemannianMetric.lean
line: 281
name: Riemannian.RiemannianMetric.metricRiesz
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Metric/RiemannianMetric.lean
ref:
- df2ae41c2c3f
sort: definition
source: lean
state: proven
title: metricRiesz
---
