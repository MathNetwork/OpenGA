/-
Copyright 2026 The DifferentialGeometry contributors.
Licensed under Apache-2.0. Adapted from qinz1yang/differential-geometry,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Only declaration placement and platform imports are changed.
-/

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

def hypSn (q r : ℝ) : ℝ :=
  if q = 0 then r else Real.sinh (q * r) / q

def hypSnDeriv (q r : ℝ) : ℝ :=
  if q = 0 then 1 else Real.cosh (q * r)

def hypDensity (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  hypSn q r ^ d

def hypDensityDeriv (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  (d : ℝ) * hypSn q r ^ (d - 1) * hypSnDeriv q r

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
