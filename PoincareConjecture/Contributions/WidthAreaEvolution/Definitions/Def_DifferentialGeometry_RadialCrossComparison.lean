/-
Copyright 2026 The DifferentialGeometry contributors.
Licensed under Apache-2.0. Adapted from qinz1yang/differential-geometry,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Only declaration placement and platform imports are changed.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Disjoint

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison



variable {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}

def CrossAnti (R : ℝ) (f g : ℝ → ℝ≥0∞) : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ R → f b * g a ≤ f a * g b







end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
