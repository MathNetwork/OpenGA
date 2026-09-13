import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Module.Equiv
import Verified.ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Verified.ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Verified.ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram

noncomputable section

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_21 : MeasurableSpace E := borel E

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_22 : BorelSpace E := ⟨rfl⟩

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_23 : MeasurableSpace M := borel M

 local instance _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure.instance_24 : BorelSpace M := ⟨rfl⟩

variable (I M) in
def chartAtlasPOU [T2Space M] [SigmaCompactSpace M] :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose

variable (I M) in
lemma chartAtlasPOU_isSubordinate [T2Space M] [SigmaCompactSpace M] :
    (chartAtlasPOU I M).IsSubordinate (fun x : M => (chartAt H x).source) :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec

def riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.sum fun α : M =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))

lemma riemannianMeasure_def
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : M =>
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) := rfl

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma measurable_ofReal_pou_weight
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
  have hcont : Continuous (fun x : M => ρ α x) :=
    (ρ α).contMDiff.continuous
  exact ENNReal.measurable_ofReal.comp hcont.measurable

end Measure

end Integral

end DifferentialGeometry

end
