import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Integration.Volume.ChartDensity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import DifferentialGeometry.Analysis.Integration.Measure.Invariance

set_option autoImplicit false









































noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal Matrix

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]






private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩




lemma finBasis_repr_sum
    (L : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    L ((Module.finBasis ℝ E) i) =
      ∑ k, ((Module.finBasis ℝ E).repr (L ((Module.finBasis ℝ E) i)) k)
            • (Module.finBasis ℝ E) k :=
  (((Module.finBasis ℝ E).sum_repr (L ((Module.finBasis ℝ E) i)))).symm




def transitionMatrix_gen (x₀ x₁ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    (Module.finBasis ℝ E).repr
      ((tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i)) k

@[simp] lemma transitionMatrix_apply_gen (x₀ x₁ : M) (x : M)
    (k i : Fin (Module.finrank ℝ E)) :
    transitionMatrix_gen (I := I) x₀ x₁ x k i =
      (Module.finBasis ℝ E).repr
        ((tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i)) k := rfl



lemma tangentCoordChange_finBasis_eq_sum
    (x₀ x₁ : M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (tangentCoordChange I x₁ x₀ x) ((Module.finBasis ℝ E) i) =
      ∑ k, transitionMatrix_gen (I := I) x₀ x₁ x k i • (Module.finBasis ℝ E) k :=
  finBasis_repr_sum (tangentCoordChange I x₁ x₀ x) i

lemma transitionMatrix_det_gen (x₀ x₁ : M) (x : M) :
    (transitionMatrix_gen (I := I) x₀ x₁ x).det =
      (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).det := by
  have hL :
      transitionMatrix_gen (I := I) x₀ x₁ x =
        LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
          (tangentCoordChange I x₁ x₀ x : E →L[ℝ] E).toLinearMap := by
    ext k i
    simp [transitionMatrix_gen, LinearMap.toMatrix_apply]
  rw [hL]
  rw [LinearMap.det_toMatrix]



end DifferentialGeometry.Integral.Measure
