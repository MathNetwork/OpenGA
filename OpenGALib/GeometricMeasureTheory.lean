/-
GeometricMeasureTheory — basic GMT primitives.

This package provides the GMT foundations used by sweepout-based min-max
regularity arguments: finite-perimeter sets (Caccioppoli), varifolds,
stationary varifolds, second variation, tangent cones, rectifiability.

Mathlib-upstream candidate: this package is intended to be eventually
contributed to Mathlib once the Mathlib-side smooth-manifold and
varifold infrastructure stabilizes.
-/

import OpenGALib.GeometricMeasureTheory.FinitePerimeter
import OpenGALib.GeometricMeasureTheory.FlatDistance
import OpenGALib.GeometricMeasureTheory.Varifold
import OpenGALib.GeometricMeasureTheory.Stationary
import OpenGALib.GeometricMeasureTheory.SecondVariation
import OpenGALib.GeometricMeasureTheory.TangentCone
import OpenGALib.GeometricMeasureTheory.Rectifiability
import OpenGALib.GeometricMeasureTheory.Isoperimetric.Basic
import OpenGALib.GeometricMeasureTheory.Isoperimetric.Euclidean
import OpenGALib.GeometricMeasureTheory.Isoperimetric.ReducedBoundary
import OpenGALib.GeometricMeasureTheory.Isoperimetric.Relative
import OpenGALib.GeometricMeasureTheory.Isoperimetric.BVFunction
import OpenGALib.GeometricMeasureTheory.Isoperimetric.Coarea
import OpenGALib.GeometricMeasureTheory.Isoperimetric.SobolevPoincare
