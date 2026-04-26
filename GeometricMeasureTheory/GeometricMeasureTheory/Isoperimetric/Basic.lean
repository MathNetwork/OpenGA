import GeometricMeasureTheory.FinitePerimeter

/-!
# GeometricMeasureTheory.Isoperimetric.Basic

Foundation primitives for the isoperimetric inequality and related
geometric variational problems on a metric measure space $M$.

The key primitive is the **volume** $|\Omega|$ of a finite-perimeter
set $\Omega$, defined as the ambient measure of $\Omega$'s carrier:
$$|\Omega| := \mu(\Omega) \in [0, \infty].$$

This file is the minimal foundation; the classical Euclidean isoperimetric
inequality (Maggi 2012 Theorem 14.1) lives downstream in
`GeometricMeasureTheory.Isoperimetric.Euclidean`.

**Ground truth**: Maggi 2012 *Sets of Finite Perimeter and Geometric
Variational Problems*, Definition 12.1 (volume of a measurable set).
-/

namespace GeometricMeasureTheory
namespace Isoperimetric

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

/-- The **volume** $|\Omega|$ of a finite-perimeter set $\Omega \subseteq M$,
defined as the ambient measure $\mu(\Omega)$ of $\Omega$'s carrier set.

Returned as `ℝ≥0∞` to allow the unbounded value when $\Omega$ has infinite
volume (relevant for the unbounded ambient case; the classical isoperimetric
inequality is stated under the side hypothesis `volume Ω < ⊤`).

**Ground truth**: Maggi 2012 Definition 12.1. -/
noncomputable def volume (Ω : FinitePerimeter M) : ENNReal :=
  MeasureTheory.volume Ω.carrier

/-- Volume is non-negative (as an `ℝ≥0∞`-valued quantity). -/
@[simp] theorem volume_nonneg (Ω : FinitePerimeter M) : 0 ≤ volume Ω :=
  zero_le _

/-- The volume equals the ambient measure restricted to the carrier,
applied to the universe. This rewrite is convenient when downstream
arguments work with `MeasureTheory.Measure.restrict`. -/
theorem volume_eq_restrict_univ (Ω : FinitePerimeter M) :
    volume Ω = (MeasureTheory.volume.restrict Ω.carrier) Set.univ := by
  unfold volume
  rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

end Isoperimetric
end GeometricMeasureTheory
