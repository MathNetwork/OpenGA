---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] [I.Boundaryless] [CompleteSpace\
  \ E] (g : Riemannian.RiemannianMetric I M) (p : M)\n  (v : TangentSpace I p), IsOpen\
  \ (Riemannian.Geodesic.maximalGeodesicInterval g p v)"
file: Riemannian/Geodesic/MaximalInterval.lean
line: 164
name: Riemannian.Geodesic.maximalGeodesicInterval_isOpen
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/MaximalInterval.lean
ref:
- 9c9dbda5ac48
sort: theorem
source: lean
state: proven
title: maximalGeodesicInterval_isOpen
---
