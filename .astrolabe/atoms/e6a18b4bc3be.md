---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (x₀ : M), (trivializationAt E (TangentSpace I) x₀).baseSet\
  \ = (chartAt H x₀).source"
file: Riemannian/Connection/ChartChristoffelSmooth.lean
line: 41
name: Riemannian.trivializationAt_baseSet_eq_chartAt_source
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Connection/ChartChristoffelSmooth.lean
ref:
- e6a18b4bc3be
sort: theorem
source: lean
state: proven
title: trivializationAt_baseSet_eq_chartAt_source
---
