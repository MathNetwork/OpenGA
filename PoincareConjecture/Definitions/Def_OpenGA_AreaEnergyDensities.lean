import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Area and energy densities

For the images `v`, `w` of an orthonormal tangent frame under a differential,
the area density is the square root of the Gram determinant and the energy
density is half the sum of the squared norms. The area is bounded by the
energy, with equality precisely for orthogonal vectors of equal norm.

The integral results assume measurable vector fields and integrable energy;
integrability of the area is a conclusion, not an additional assumption.
They apply on any measure space, including a restricted domain measure.
Identifying these fields with a Sobolev differential on a surface remains a
separate geometric interface. No global frame on the sphere is asserted.

Reference: Colding-Minicozzi, *Width and Finite Extinction Time of Ricci Flow*,
arXiv:0707.0108v1, equation (1.4) and the following equality discussion, p. 3.
https://arxiv.org/pdf/0707.0108v1#page=3
-/

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

namespace OpenGA

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Math.** The two-dimensional Jacobian density of a pair of derivative vectors. -/
noncomputable def areaDensity (v w : F) : ℝ :=
  Real.sqrt (‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2)

/-- **Math.** The Dirichlet energy density of a pair of derivative vectors. -/
noncomputable def energyDensity (v w : F) : ℝ :=
  (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2















section Integral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {v w : X → F}







end Integral

end OpenGA
