/-
MinMax — min-max theory.

Currently contains the Sweepout sub-namespace (CLS22-style sweepout
machinery: ONVP, non-excessive condition, mass cancellation, homotopic
minimization, interpolation, pull-tight). Future min-max frameworks
(Almgren-Pitts, Marques-Neves, etc.) parallel under `OpenGALib/MinMax/`.

Built on top of `GeometricMeasureTheory`.
-/

import OpenGALib.MinMax.Sweepout.Defs
import OpenGALib.MinMax.Sweepout.ONVP
import OpenGALib.MinMax.Sweepout.MassCancellation
import OpenGALib.MinMax.Sweepout.MinMaxLimit
import OpenGALib.MinMax.Sweepout.PullTight
import OpenGALib.MinMax.Sweepout.HomotopicMinimization
import OpenGALib.MinMax.Sweepout.Interpolation
import OpenGALib.MinMax.Sweepout.NonExcessive
