---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E]\n  [inst_3 : FiniteDimensional ℝ E] [NeZero (Module.finrank\
  \ ℝ E)] {H : Type u_2} [inst_5 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ\
  \ E H} {M : Type u_3} [inst_6 : TopologicalSpace M] [inst_7 : ChartedSpace H M]\n\
  \  [inst_8 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M) (α : M)\
  \ {b : M},\n  b ∈ (trivializationAt E (TangentSpace I) α).baseSet →\n    ∀ (i :\
  \ Fin (Module.finrank ℝ E)), Riemannian.Tensor.chartFrameRawFiber g α b i ≠ 0"
file: Riemannian/TensorBundle/SmoothOrthoFrame/Orthonormality.lean
line: 152
name: Riemannian.Tensor.chartFrameRawFiber_ne_zero
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/TensorBundle/SmoothOrthoFrame/Orthonormality.lean
ref:
- e2c6a2e0aef8
sort: theorem
source: lean
state: proven
title: chartFrameRawFiber_ne_zero
---
