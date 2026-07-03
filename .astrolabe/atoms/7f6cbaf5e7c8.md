---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_4} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (self : Riemannian.SmoothVectorField I M),\n  ContMDiff\
  \ I (I.prod (modelWithCornersSelf ℝ E)) ↑⊤ fun y => ⟨y, self.toFun y⟩"
file: Riemannian/TangentBundle/TangentSmooth.lean
line: 206
name: Riemannian.SmoothVectorField.smooth
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/TangentBundle/TangentSmooth.lean
ref:
- 7f6cbaf5e7c8
sort: theorem
source: lean
state: proven
title: smooth
---
