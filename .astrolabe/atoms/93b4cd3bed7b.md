---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric\
  \ I M) (α : M) {c : ℝ × ℝ → E}\n  {Dc : ℝ × ℝ → ℝ × ℝ →L[ℝ] E} {D2c : ℝ × ℝ →L[ℝ]\
  \ ℝ × ℝ →L[ℝ] E} {x : ℝ × ℝ},\n  (∀ (y : ℝ × ℝ), HasFDerivAt c (Dc y) y) →\n   \
  \ HasFDerivAt Dc D2c x →\n      ∀ (v w : ℝ × ℝ),\n        (D2c v) w + Riemannian.Geodesic.chartChristoffelContraction\
  \ g α ((Dc x) v) ((Dc x) w) (c x) =\n          (D2c w) v + Riemannian.Geodesic.chartChristoffelContraction\
  \ g α ((Dc x) w) ((Dc x) v) (c x)"
file: Riemannian/Geodesic/SymmetryLemma.lean
line: 30
name: Riemannian.Geodesic.covariant_sndFDeriv_symm
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/SymmetryLemma.lean
ref:
- 93b4cd3bed7b
sort: theorem
source: lean
state: proven
title: covariant_sndFDeriv_symm
---
