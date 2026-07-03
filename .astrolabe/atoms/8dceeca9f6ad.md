---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E]\n  [inst_3 : FiniteDimensional ℝ E] [NeZero (Module.finrank\
  \ ℝ E)] {H : Type u_2} [inst_5 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ\
  \ E H} {M : Type u_3} [inst_6 : TopologicalSpace M] [inst_7 : ChartedSpace H M]\n\
  \  [inst_8 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M) (α : M)\
  \ {b : M},\n  b ∈ Riemannian.Tensor.smoothOrthoFrameNbhd α →\n    ∀ (i j : Fin (Module.finrank\
  \ ℝ E)),\n      ((g.inner b) (Riemannian.Tensor.smoothOrthoFrame g α i b)) (Riemannian.Tensor.smoothOrthoFrame\
  \ g α j b) =\n        if i = j then 1 else 0"
file: Riemannian/TensorBundle/SmoothOrthoFrame.lean
line: 154
name: Riemannian.Tensor.smoothOrthoFrame_orthonormal
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/TensorBundle/SmoothOrthoFrame.lean
ref:
- 8dceeca9f6ad
sort: theorem
source: lean
state: proven
title: smoothOrthoFrame_orthonormal
---
