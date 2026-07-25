import DifferentialGeometry.Geometry.Metric.MetricBallMonotone
import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Geometry.Metric.ChartGram

set_option autoImplicit false
































noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]









private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩





private lemma chartGramMatrix_pair_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x ij.1 ij.2)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
  chartGramMatrix_entry_contMDiffOn (I := I) g x₀ ij.1 ij.2



end DifferentialGeometry.Integral.Measure
