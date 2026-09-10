import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section

open Matrix

open scoped Matrix BigOperators

namespace DifferentialGeometry
end DifferentialGeometry
open _root_.DifferentialGeometry

namespace DifferentialGeometry.Integral
end DifferentialGeometry.Integral
open _root_.DifferentialGeometry
open _root_.DifferentialGeometry.Integral

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry
open _root_.DifferentialGeometry.Integral
open _root_.DifferentialGeometry.Integral.Measure

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

theorem DifferentialGeometry.Integral.Measure.hasDerivAt_det_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by sorry
