import GeometricMeasureTheory.FlatDistance

open GeometricMeasureTheory

/-!
# MinMax.Sweepout.Defs

The basic notion of a sweepout (paper Definition 3.1, [CLS22, Def 1.1]):
a 1-parameter family $\Phi : [0,1] \to \mathcal{Z}_n(M; \mathbb{Z}_2)$
continuous in the flat $\mathcal{F}$-topology, with $\Phi(x) = \partial
\Omega(x)$, $\Omega(0) = \varnothing$, $\Omega(1) = M$. The width
$W(\Phi) := \sup_{x \in [0,1]} \mathbf{M}(\Phi(x))$ is the supremum of
slice perimeters.
-/

namespace MinMax.Sweepout

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- A family $t \mapsto \Omega_t$ of finite-perimeter sets is
**flat-continuous** if it is continuous as a function $\mathbb{R} \to
\mathrm{FinitePerimeter}\,M$ in the flat-distance pseudometric on the
codomain. -/
def FContinuous (family : ℝ → FinitePerimeter M) : Prop :=
  ∀ t : ℝ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ s : ℝ, |s - t| < δ →
      FinitePerimeter.flatDist (family s) (family t) < ε

end MinMax.Sweepout

namespace MinMax

/-- A sweepout of $M$ (paper Definition 3.1, [CLS22, Def 1.1]):
a 1-parameter family of finite-perimeter sets indexed by $\mathbb{R}$
(in practice the interval $[0,1]$), continuous in the flat topology,
with empty starting slice and full-volume terminal slice. -/
structure Sweepout (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [MeasureTheory.MeasureSpace M] where
  /-- The slice $\Omega_t$ at parameter $t$. -/
  slice : ℝ → FinitePerimeter M
  /-- Flat continuity of $t \mapsto \Omega_t$ (paper Def 3.1). -/
  isFContinuous : MinMax.Sweepout.FContinuous slice
  /-- $\Omega(0) = \varnothing$ (paper Def 3.1). -/
  slice_zero : (slice 0).carrier = ∅
  /-- $\Omega(1) = M$ (paper Def 3.1). -/
  slice_one : (slice 1).carrier = Set.univ

end MinMax

namespace MinMax.Sweepout

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- **Width** $W(\Phi) := \sup_{t \in [0,1]} \mathbf{M}(\Phi(t))
= \sup_{t \in [0,1]} \mathrm{Per}(\Omega_t)$ (paper Def 3.1). -/
noncomputable def width (Φ : MinMax.Sweepout M) : ℝ :=
  ⨆ t ∈ Set.Icc (0 : ℝ) 1, ((Φ.slice t).perim : ℝ)

end MinMax.Sweepout
