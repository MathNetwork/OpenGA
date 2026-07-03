---
content: "∀ {\U0001D55C : Type u_1} [inst : NontriviallyNormedField \U0001D55C] [inst_1\
  \ : CompleteSpace \U0001D55C] {M : Type u_2} {F₁ : Type u_3}\n  [inst_2 : NormedAddCommGroup\
  \ F₁] [inst_3 : NormedSpace \U0001D55C F₁] [inst_4 : FiniteDimensional \U0001D55C\
  \ F₁] {F₂ : Type u_4}\n  [inst_5 : NormedAddCommGroup F₂] [inst_6 : NormedSpace\
  \ \U0001D55C F₂] (T : M → F₁ →L[\U0001D55C] F₂) {ι : Type u_5} [inst_7 : Fintype\
  \ ι]\n  (basis : Module.Basis ι \U0001D55C F₁),\n  T = fun y => ∑ i, (LinearMap.toContinuousLinearMap\
  \ (basis.coord i)).smulRight ((T y) (basis i))"
file: Riemannian/Util/Chart/FlatChartDerivs.lean
line: 145
name: TangentBundle.continuousLinearMap_of_components_decomp
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Util/Chart/FlatChartDerivs.lean
ref:
- 3baad90f14cb
sort: theorem
source: lean
state: proven
title: continuousLinearMap_of_components_decomp
---
