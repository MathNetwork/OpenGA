---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E] [Module.Finite ℝ E]\n  [inst_4 : FiniteDimensional ℝ E]\
  \ [NeZero (Module.finrank ℝ E)] {H : Type u_2} [inst_6 : TopologicalSpace H]\n \
  \ {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_7 : TopologicalSpace M] [inst_8\
  \ : ChartedSpace H M]\n  [inst_9 : IsManifold I (↑⊤) M] [I.Boundaryless] [CompleteSpace\
  \ E] {g : Riemannian.RiemannianMetric I M} {γ : ℝ → M}\n  {s : Set ℝ} {p : M} {v\
  \ : TangentSpace I p} {t : ℝ},\n  Riemannian.Geodesic.IsGeodesicOnWithInitial g\
  \ γ s p v →\n    s ∈ nhds t → γ t ∈ (chartAt H p).source → Riemannian.Geodesic.IsGeodesicAt\
  \ g γ t"
file: Riemannian/Geodesic/MaximalInterval.lean
line: 91
name: Riemannian.Geodesic.IsGeodesicOnWithInitial.isGeodesicAt
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Geodesic/MaximalInterval.lean
ref:
- feb6a21f4c9f
sort: theorem
source: lean
state: proven
title: isGeodesicAt
---
