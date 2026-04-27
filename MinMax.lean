/-
MinMax — min-max theory.

Currently contains the Sweepout sub-namespace (CLS22-style sweepout
machinery: ONVP, non-excessive condition, mass cancellation, homotopic
minimization, interpolation, pull-tight). Future min-max frameworks
(Almgren-Pitts, Marques-Neves, etc.) parallel under `MinMax/`.

Built on top of `GeometricMeasureTheory`.
-/

import MinMax.Sweepout.Defs
import MinMax.Sweepout.ONVP
import MinMax.Sweepout.MassCancellation
import MinMax.Sweepout.MinMaxLimit
import MinMax.Sweepout.PullTight
import MinMax.Sweepout.HomotopicMinimization
import MinMax.Sweepout.Interpolation
import MinMax.Sweepout.NonExcessive
