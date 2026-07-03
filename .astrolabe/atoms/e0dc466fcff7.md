---
content: "∀ {ι : Type u_1} {ι' : Type u_2} [inst : Fintype ι] [inst_1 : Fintype ι']\
  \ {V : Type u_3} [inst_2 : NormedAddCommGroup V]\n  [inst_3 : InnerProductSpace\
  \ ℝ V] {W : Type u_4} [inst_4 : AddCommGroup W] [inst_5 : _root_.Module ℝ W]\n \
  \ (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis ι' ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ]\
  \ W),\n  ∑ i, (B (b i)) (b i) = ∑ i, (B (b' i)) (b' i)"
file: Algebraic/Auxiliary/OrthonormalBasisDiagonal.lean
line: 97
name: OrthonormalBasis.sum_apply_diagonal_invariant
path: /Users/moqian/OpenGALib/OpenGALib/Algebraic/Auxiliary/OrthonormalBasisDiagonal.lean
ref:
- e0dc466fcff7
sort: theorem
source: lean
state: proven
title: sum_apply_diagonal_invariant
---
