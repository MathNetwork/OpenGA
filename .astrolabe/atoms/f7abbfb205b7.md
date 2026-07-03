---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric\
  \ I M) (α : M) (a : ℝ) (v y : E),\n  Riemannian.Geodesic.chartChristoffelContraction\
  \ g α (a • v) (a • v) y =\n    (a * a) • Riemannian.Geodesic.chartChristoffelContraction\
  \ g α v v y"
file: Riemannian/Geodesic/Equation.lean
line: 163
name: Riemannian.Geodesic.chartChristoffelContraction_smul_smul
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/Equation.lean
ref:
- f7abbfb205b7
sort: theorem
source: lean
state: proven
title: chartChristoffelContraction_smul_smul
---
