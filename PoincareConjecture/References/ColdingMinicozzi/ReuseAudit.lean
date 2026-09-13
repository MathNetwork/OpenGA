import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula
import OpenGALib.Analysis.WidthComparison
import OpenGALib.Analysis.WidthExtinction

/-!
First reuse audit for the Colding-Minicozzi finite-extinction route.

The upstream determinant derivative is a pointwise ingredient for varying
area density. It is not the first-variation theorem for an immersed surface.
The OpenGA declarations below are the existing analytic endpoint; they do not
construct geometric sweepouts or establish compatibility with surgery.

Run from the OpenGA root with `lake env lean` on this file. Source revisions,
mathematical scope, and the reviewed blueprint issues are in `review.json`.
-/

#print axioms DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
#print axioms OpenGA.integral_areaDensity_le_energyDensity
#print axioms OpenGA.eventually_width_slope_lt_of_comparison
#print axioms OpenGA.le_widthExtinctionTime_of_slope_le
#print axioms OpenGA.le_widthExtinctionTime_across_downward_jumps
