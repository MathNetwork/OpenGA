---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] {g : Riemannian.RiemannianMetric\
  \ I M} {γ : ℝ → M} {s : Set ℝ} {t : ℝ},\n  Riemannian.Geodesic.IsGeodesicOn g γ\
  \ s → t ∈ s → Riemannian.Geodesic.HasGeodesicEquationAt g γ t"
file: Riemannian/Geodesic/Equation.lean
line: 475
name: Riemannian.Geodesic.IsGeodesicOn.hasGeodesicEquationAt
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/Equation.lean
ref:
- 1cbe0ca29b3d
sort: theorem
source: lean
state: proven
title: hasGeodesicEquationAt
---
