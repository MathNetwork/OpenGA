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
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import DifferentialGeometry.Geometry.Metric.ChartGram


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def chartDensity (g : SmoothRiemannianMetric I M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (chartGramMatrix g x₀ x).det

lemma chartDensity_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < chartDensity g x₀ x :=
  Real.sqrt_pos.mpr (chartGramMatrix_det_pos (I := I) g x₀ hx)
lemma chartDensity_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hx
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g x₀ x hx
  have hpos_ne : (chartGramMatrix (I := I) g x₀ x).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (I := I) g x₀ hx)
  have hsqrt : ContDiffAt ℝ ∞ Real.sqrt
      (chartGramMatrix (I := I) g x₀ x).det :=
    Real.contDiffAt_sqrt hpos_ne
  have := hsqrt.comp_contMDiffWithinAt (f :=
      fun y : M => (chartGramMatrix (I := I) g x₀ y).det) hdet
  exact this

noncomputable def modelHaar : MeasureTheory.Measure E := (chartModelBasis E).addHaar

instance modelHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance

theorem map_toEuclidean_modelHaar_eq_volume :
    MeasureTheory.Measure.map (toEuclidean (E := E)) (modelHaar (E := E)) =
      (MeasureTheory.volume :
        MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have h₁ :
      MeasureTheory.Measure.map (toEuclidean (E := E))
          (modelHaar (E := E)) =
        ((chartModelBasis E).map
            (toEuclidean (E := E)).toLinearEquiv).addHaar := by
    unfold modelHaar
    exact Module.Basis.map_addHaar (chartModelBasis E)
      (toEuclidean (E := E))
  rw [h₁]
  have hcancel :
      (chartModelBasis E).map (toEuclidean (E := E)).toLinearEquiv
        = (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis := by
    refine Module.Basis.eq_of_apply_eq ?_
    intro i
    have hb_i : (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i
        = EuclideanSpace.single i (1 : ℝ) := by
      simp [OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]
    rw [Module.Basis.map_apply, chartModelBasis_apply, hb_i]
    simp
  rw [hcancel]
  exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume

def chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I x₀).symm
    (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))))

lemma chartLocalMeasure_def
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) g x₀ =
      MeasureTheory.Measure.map (extChartAt I x₀).symm
        (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartDensity g x₀ ((extChartAt I x₀).symm y)))) := rfl

end Measure
end Integral
end DifferentialGeometry
