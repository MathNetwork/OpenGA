import Sweepout.Defs

open GeometricMeasureTheory

namespace Sweepout

/-!
# AltRegularity.Sweepout.Interpolation

The interpolation lemma (CLS22, Lemma 1.12; cited as Lemma 2.16 in the
paper). It produces, given two nested sets of finite perimeter close in volume,
an $\mathcal{F}$-continuous one-parameter family connecting them with
controlled perimeter overhead. This is the standard tool for gluing
local modifications into a sweepout-wide family.
-/



variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]


/-- **Interpolation lemma (CLS22 1.12).** Given two nested sets of finite perimeter
sets $\Omega^- \subseteq \Omega^+$ close in volume and a perimeter cap
$P$, there exists an $\mathcal{F}$-continuous nested family
$\{\Omega_t\}_{t \in [0,1]}$ from $\Omega^-$ to $\Omega^+$ with
$\mathrm{Per}(\Omega_t) \le \max(\mathrm{Per}(\Omega^-), \mathrm{Per}(\Omega^+)) + \varepsilon$
for any prescribed $\varepsilon > 0$. -/
theorem interpolation_lemma
    (Ωlo Ωhi : FinitePerimeter M) (hsub : Ωlo.carrier ⊆ Ωhi.carrier)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ family : ℝ → FinitePerimeter M,
      FContinuous family ∧
        family 0 = Ωlo ∧ family 1 = Ωhi ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ((family t).perim : ℝ) ≤ max ((Ωlo.perim : ℝ)) ((Ωhi.perim : ℝ)) + ε := by
  sorry



end Sweepout
