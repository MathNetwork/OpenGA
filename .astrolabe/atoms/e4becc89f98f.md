---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E]\n  [inst_3 : FiniteDimensional ℝ E] [NeZero (Module.finrank\
  \ ℝ E)] {H : Type u_2} [inst_5 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ\
  \ E H} {M : Type u_3} [inst_6 : TopologicalSpace M] [inst_7 : ChartedSpace H M]\n\
  \  [inst_8 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M) (α x : M)\
  \ (c : Fin (Module.finrank ℝ E) → ℝ),\n  star c ⬝ᵥ (Riemannian.Tensor.chartGramMatrix\
  \ g α x).mulVec c =\n    ((g.inner x) (∑ i, c i • Riemannian.Tensor.chartBasisVecFiber\
  \ α i x))\n      (∑ j, c j • Riemannian.Tensor.chartBasisVecFiber α j x)"
file: Riemannian/TensorBundle/MusicalIso.lean
line: 88
name: Riemannian.Tensor.chartGramMatrix_dotProduct_mulVec
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/TensorBundle/MusicalIso.lean
ref:
- e4becc89f98f
sort: theorem
source: lean
state: proven
title: chartGramMatrix_dotProduct_mulVec
---
