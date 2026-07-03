---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric\
  \ I M) (p : M) (v : TangentSpace I p),\n  Riemannian.Exponential.expMap g p v =\
  \ Riemannian.Geodesic.maximalGeodesic g p v 1"
file: Riemannian/Exponential/Defs.lean
line: 73
name: Riemannian.Exponential.expMap_def
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Exponential/Defs.lean
ref:
- f2d0db1afbb2
sort: theorem
source: lean
state: proven
title: expMap_def
---
