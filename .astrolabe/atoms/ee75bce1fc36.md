---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] {g : Riemannian.RiemannianMetric\
  \ I M} {γ : ℝ → M},\n  Riemannian.Geodesic.IsGeodesic g γ → ∀ (t : ℝ), Riemannian.Geodesic.HasGeodesicEquationAt\
  \ g γ t"
file: Riemannian/Geodesic/Equation.lean
line: 461
name: Riemannian.Geodesic.IsGeodesic.hasGeodesicEquationAt
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/Equation.lean
ref:
- ee75bce1fc36
sort: theorem
source: lean
state: proven
title: hasGeodesicEquationAt
---
