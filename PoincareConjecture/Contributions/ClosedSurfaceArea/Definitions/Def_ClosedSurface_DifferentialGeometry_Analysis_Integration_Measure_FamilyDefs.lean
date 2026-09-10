import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyFinite

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix

open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_30 : MeasurableSpace E := borel E

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_31 : BorelSpace E := ⟨rfl⟩

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_32 : MeasurableSpace M := borel M

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs.instance_33 : BorelSpace M := ⟨rfl⟩

def riemannianMeasureFamily
    {P : Type*}
    [T2Space M] [SigmaCompactSpace M]
    (g_fam : P → SmoothRiemannianMetric I M) : P → MeasureTheory.Measure M :=
  fun t => riemannianVolumeMeasure (I := I) (M := M) (g_fam t)

structure MetricFamilyRegularAt
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ) : Prop where
  hasDerivAt_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)) {x : M},
      x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j)
          (deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ x i j) t) t
  continuousOn_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
  continuousOn_deriv_chartGramMatrix :
    ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) x₀ p.2 i j) p.1)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)

structure FunctionRegularAt (f : ℝ → M → ℝ) (t₀ : ℝ) : Prop where
  hasDerivAt_time :
    ∀ (x : M) (t : ℝ), HasDerivAt (fun s : ℝ => f s x) (deriv (fun s : ℝ => f s x) t) t
  continuous_joint : Continuous (fun p : ℝ × M => f p.1 p.2)
  continuous_deriv_joint :
    Continuous (fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)

section ChartDensityFamily

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

def chartGramMatrixFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun t => chartGramMatrix (I := I) (g_fam t) x₀ x

def chartDensityFamily
    (g_fam : ℝ → SmoothRiemannianMetric I M) (x₀ x : M) :
    ℝ → ℝ :=
  fun t => chartDensity (I := I) (g_fam t) x₀ x

end ChartDensityFamily

variable (I) in
def traceTimeDerivMetric
    (g_fam : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M) : ℝ :=
  Matrix.trace ((chartGramMatrix (I := I) (g_fam t) x x)⁻¹ *
    (Matrix.of fun i j =>
      deriv (fun s => chartGramMatrix (I := I) (g_fam s) x x i j) t))

end Measure

end Integral

end DifferentialGeometry

end
