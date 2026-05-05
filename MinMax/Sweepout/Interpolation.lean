import MinMax.Sweepout.Defs

open GeometricMeasureTheory
open MinMax

namespace MinMax.Sweepout

/-!
# AltRegularity.Sweepout.Interpolation

The interpolation lemma (CLS22, Lemma 1.12; cited as Lemma 2.16 in the
paper). It produces, given two nested sets of finite perimeter close in volume,
an $\mathcal{F}$-continuous one-parameter family connecting them with
controlled perimeter overhead. This is the standard tool for gluing
local modifications into a sweepout-wide family.
-/



variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]


/-- **Interpolation lemma** ([CLS22, Lemma 1.12]; reproduced verbatim
as paper §2 Lemma `lem:interpolation`).

Verbatim CLS22/paper §2 statement:
> Fix $L > 0$. For every $\varepsilon > 0$ there exists $\delta > 0$
> such that the following holds. If $\Omega_0, \Omega_1$ are two
> Caccioppoli sets with $\Omega_0 \subset \Omega_1$,
> $\mathrm{Per}(\Omega_i) \leq L$ for $i = 0, 1$, and
> $\mathrm{Vol}(\Omega_1 \setminus \Omega_0) \leq \delta$, then there
> exists a nested $\mathcal{F}$-continuous family
> $\{\partial\Omega_t\}_{t \in [0,1]}$ with
> $\mathrm{Per}(\Omega_t) \leq \max\{\mathrm{Per}(\Omega_0),
>     \mathrm{Per}(\Omega_1)\} + \varepsilon$
> for all $t \in [0,1]$.

The Lean statement strict-aligns: `L` is a perimeter cap fixed first;
for every `ε > 0`, there exists a `δ > 0` (the "magnitude of allowable
volume gap") such that the conclusion holds for any pair of
Caccioppoli sets satisfying the perimeter cap and the volume-gap
hypothesis.

**Volume**: uses `MeasureTheory.volume` from the ambient
`[MeasureTheory.MeasureSpace M]` cascade.

**Used by**: paper §5 cancellation chain (`5-integrality.tex:211`,
applied with perimeter bound $W$ and tolerance $\varepsilon$). -/
theorem interpolation_lemma
    (L : ℝ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (Ωlo Ωhi : FinitePerimeter M),
        Ωlo.carrier ⊆ Ωhi.carrier →
        (Ωlo.perim : ℝ) ≤ L → (Ωhi.perim : ℝ) ≤ L →
        (MeasureTheory.volume (Ωhi.carrier \ Ωlo.carrier)).toReal ≤ δ →
        ∃ family : ℝ → FinitePerimeter M,
          FContinuous family ∧
            family 0 = Ωlo ∧ family 1 = Ωhi ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1,
              ((family t).perim : ℝ) ≤
                max ((Ωlo.perim : ℝ)) ((Ωhi.perim : ℝ)) + ε := by
  sorry



end MinMax.Sweepout
