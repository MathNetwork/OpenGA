---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [InnerProductSpace ℝ E]\n  [inst_3 : FiniteDimensional ℝ E] [NeZero (Module.finrank\
  \ ℝ E)] {H : Type u_2} [inst_5 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ\
  \ E H} {M : Type u_3} [inst_6 : TopologicalSpace M] [inst_7 : ChartedSpace H M]\n\
  \  [inst_8 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M) (α : M)\
  \ {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ},\n  (∀ (j : Fin (Module.finrank ℝ E)),\n\
  \      ContMDiffOn I (modelWithCornersSelf ℝ ℝ) (↑⊤) (fun y => (Φ y) (Riemannian.Tensor.chartBasisVecFiber\
  \ α j y))\n        (trivializationAt E (TangentSpace I) α).baseSet) →\n    ContMDiffOn\
  \ I (I.prod (modelWithCornersSelf ℝ E)) (↑⊤)\n      (fun y =>\n        ⟨y,\n   \
  \       ∑ i,\n            (∑ j, Riemannian.Tensor.chartInvGramMatrix g α y i j *\
  \ (Φ y) (Riemannian.Tensor.chartBasisVecFiber α j y)) •\n              Riemannian.Tensor.chartBasisVecFiber\
  \ α i y⟩)\n      (trivializationAt E (TangentSpace I) α).baseSet"
file: Riemannian/TensorBundle/MusicalIso.lean
line: 508
name: Riemannian.Tensor.metricRiesz_chartLocal_total_contMDiffOn
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/TensorBundle/MusicalIso.lean
ref:
- ff87adaf34af
sort: theorem
source: lean
state: proven
title: metricRiesz_chartLocal_total_contMDiffOn
---
