---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [inst_2 : FiniteDimensional ℝ E]\n  {H : Type u_2} [inst_3 : TopologicalSpace\
  \ H] {I : ModelWithCorners ℝ E H} {M : Type u_3} [inst_4 : TopologicalSpace M]\n\
  \  [inst_5 : ChartedSpace H M] [inst_6 : IsManifold I (↑⊤) M] (g g_1 : Riemannian.RiemannianMetric\
  \ I M),\n  g = g_1 →\n    ∀ (α α_1 : M),\n      α = α_1 →\n        ∀ (i i_1 : Fin\
  \ (Module.finrank ℝ E)),\n          i = i_1 →\n            ∀ (j j_1 : Fin (Module.finrank\
  \ ℝ E)),\n              j = j_1 →\n                ∀ (k k_1 : Fin (Module.finrank\
  \ ℝ E)),\n                  k = k_1 →\n                    ∀ (y y_1 : E),\n    \
  \                  y = y_1 →\n                        Riemannian.chartChristoffel\
  \ g α i j k y = Riemannian.chartChristoffel g_1 α_1 i_1 j_1 k_1 y_1"
file: Riemannian/Connection/ChartChristoffel.lean
line: 0
name: Riemannian.chartChristoffel.congr_simp
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Connection/ChartChristoffel.lean
ref:
- e1c5fee4ded7
sort: theorem
source: lean
state: proven
title: congr_simp
---
