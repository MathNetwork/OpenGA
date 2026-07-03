---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric\
  \ I M) (α : M) (w y : E),\n  Riemannian.Geodesic.chartChristoffelContraction g α\
  \ 0 w y = 0"
file: Riemannian/Geodesic/Equation.lean
line: 145
name: Riemannian.Geodesic.chartChristoffelContraction_zero_left
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/Equation.lean
ref:
- eea1ccf5e32c
sort: theorem
source: lean
state: proven
title: chartChristoffelContraction_zero_left
---
