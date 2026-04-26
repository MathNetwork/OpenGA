import AltRegularity.GMT.FlatDistance

/-!
# AltRegularity.Sweepout.Defs

The basic notion of a sweepout (paper Definition 3.1, [CLS22, Def 1.1]):
a 1-parameter family $\Phi : [0,1] \to \mathcal{Z}_n(M; \mathbb{Z}_2)$
continuous in the flat $\mathcal{F}$-topology, with $\Phi(x) = \partial
\Omega(x)$, $\Omega(0) = \varnothing$, $\Omega(1) = M$. The width
$W(\Phi) := \sup_{x \in [0,1]} \mathbf{M}(\Phi(x))$ is the supremum of
slice perimeters.

## Definition style

`Sweepout` is an explicit `structure` carrying:
  * the slice family `slice : ℝ → FinitePerimeter M`,
  * the flat-continuity hypothesis `isFContinuous`,
  * the boundary conditions `slice_zero`, `slice_one`.

`Sweepout.FContinuous` is an explicit `def` in terms of the leaf
primitive `FinitePerimeter.flatDist`. `Sweepout.width` is an explicit
`def` as the iSup of slice perimeters over $[0,1]$.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-- A family $t \mapsto \Omega_t$ of finite-perimeter sets is
**flat-continuous** if it is continuous as a function $\mathbb{R} \to
\mathrm{FinitePerimeter}\,M$ in the flat-distance pseudometric on the
codomain.

Defined explicitly via the standard $\varepsilon$-$\delta$ formulation
using `FinitePerimeter.flatDist`. -/
def FContinuous (family : ℝ → FinitePerimeter M) : Prop :=
  ∀ t : ℝ, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ s : ℝ, |s - t| < δ →
      FinitePerimeter.flatDist (family s) (family t) < ε

end Sweepout

/-- A sweepout of $M$ (paper Definition 3.1, [CLS22, Def 1.1]):
a 1-parameter family of finite-perimeter sets indexed by $\mathbb{R}$
(in practice the interval $[0,1]$), continuous in the flat topology,
with empty starting slice and full-volume terminal slice. -/
structure Sweepout (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] where
  /-- The slice $\Omega_t$ at parameter $t$. -/
  slice : ℝ → FinitePerimeter M
  /-- Flat continuity of $t \mapsto \Omega_t$ (paper Def 3.1). -/
  isFContinuous : Sweepout.FContinuous slice
  /-- $\Omega(0) = \varnothing$ (paper Def 3.1). -/
  slice_zero : (slice 0).carrier = ∅
  /-- $\Omega(1) = M$ (paper Def 3.1). -/
  slice_one : (slice 1).carrier = Set.univ

namespace Sweepout

/-- **Width** $W(\Phi) := \sup_{t \in [0,1]} \mathbf{M}(\Phi(t))
= \sup_{t \in [0,1]} \mathrm{Per}(\Omega_t)$ (paper Def 3.1).

Defined explicitly as the iSup of slice perimeters over $[0,1]$. -/
noncomputable def width (Φ : Sweepout M) : ℝ :=
  ⨆ t ∈ Set.Icc (0 : ℝ) 1, ((Φ.slice t).perim : ℝ)

end Sweepout

end AltRegularity
