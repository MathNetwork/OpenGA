/-
Copyright 2026 The DifferentialGeometry contributors.
Licensed under Apache-2.0. Adapted from qinz1yang/differential-geometry,
commit 1b535dd102b94cc42b107cca27059687888f08b3.
Only declaration placement and platform imports are changed.
-/

import Definitions.Def_DifferentialGeometry_HyperbolicModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

def hypRadVol (q : Real) (d : Nat) (R : Real) : Real :=
  ∫ t in (0 : Real)..R, hypDensity q d t

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
