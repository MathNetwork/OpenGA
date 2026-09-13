import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OpenGA_AreaEnergyDensities

set_option autoImplicit false
open scoped InnerProductSpace
open OpenGA
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem OpenGA.areaDensity_eq_normDet (L : E →ₗ[ℝ] F) (b : OrthonormalBasis (Fin 2) ℝ E) :
    areaDensity (L (b 0)) (L (b 1)) = L.normDet := by sorry
