
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
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
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Module.Equiv


section

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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_40

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_41

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_42

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Geometry.Metric.ChartGram.instance_43

export DifferentialGeometry (SmoothRiemannianMetric)

@[simp] lemma chartModelBasis_apply (i : Fin (Module.finrank ℝ E)) :
    chartModelBasis E i =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  with_unfolding_all
    change (toEuclidean (E := E)).symm.toLinearEquiv
        ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i) =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ))
  simp [OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]

end Measure

end Integral

end DifferentialGeometry

end

end

section

noncomputable section

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff ENNReal Matrix

namespace DifferentialGeometry

namespace Integral

namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_28

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_29

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_31

lemma chartModelBasis_repr_sum
    (L : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    L ((chartModelBasis E) i) =
      ∑ k, ((chartModelBasis E).repr (L ((chartModelBasis E) i)) k)
            • (chartModelBasis E) k :=
  (((chartModelBasis E).sum_repr (L ((chartModelBasis E) i)))).symm

lemma tangentCoordChange_chartModelBasis_eq_sum
    (x₀ x₁ : M) (x : M) (i : Fin (Module.finrank ℝ E)) :
    (tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) i) =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i • (chartModelBasis E) k :=
  chartModelBasis_repr_sum (tangentCoordChange I x₁ x₀ x) i

end Measure

end Integral

end DifferentialGeometry

end

end

noncomputable section

open Bundle Manifold Set MeasureTheory

open scoped Manifold Topology ContDiff ENNReal Matrix

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_28

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_29

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Invariance.instance_31

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

lemma solution
    (x₀ x₁ : M) {x : M}
    (hx0 : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx1 : x ∈ (trivializationAt E (TangentSpace I) x₁).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x₁ i x =
      ∑ k, transitionMatrix (I := I) x₀ x₁ x k i •
        chartBasisVecFiber (I := I) x₀ k x := by
  set T₀ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₀
  set T₁ : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) x₁
  have hx0' : x ∈ T₀.baseSet := hx0
  have hx1' : x ∈ T₁.baseSet := hx1
  have hdef1 :
      chartBasisVecFiber (I := I) x₁ i x =
        T₁.symm x ((chartModelBasis E) i) := by
    rw [chartBasisVecFiber, T₁.symmL_apply hx1']
  have hcompeq' :=
    Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := ℝ) (F := E) (E := (TangentSpace I : M → Type _))
      T₁ T₀ (b := x) ⟨hx1', hx0'⟩
  have happ :
      (T₀.continuousLinearEquivAt ℝ x hx0')
          ((T₁.continuousLinearEquivAt ℝ x hx1').symm ((chartModelBasis E) i))
        = (Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
            ((chartModelBasis E) i) := by
    have := congrArg
      (fun L : E ≃L[ℝ] E => L ((chartModelBasis E) i)) hcompeq'
    simpa [ContinuousLinearEquiv.trans_apply] using this
  have hequiv :
      T₁.symm x ((chartModelBasis E) i) =
        T₀.symm x
          ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
            ((chartModelBasis E) i)) := by
    have hL : (T₁.continuousLinearEquivAt ℝ x hx1').symm ((chartModelBasis E) i) =
              T₁.symm x ((chartModelBasis E) i) := rfl
    have hR : (T₀.continuousLinearEquivAt ℝ x hx0').symm
                ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
                  ((chartModelBasis E) i)) =
              T₀.symm x
                ((Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
                  ((chartModelBasis E) i)) := rfl
    have := congrArg (T₀.continuousLinearEquivAt ℝ x hx0').symm happ
    simp only [ContinuousLinearEquiv.symm_apply_apply] at this
    rw [← hL, ← hR]
    exact this
  have hcc :
      (Bundle.Trivialization.coordChangeL (R := ℝ) T₁ T₀ x)
          ((chartModelBasis E) i)
        = (tangentCoordChange I x₁ x₀ x) ((chartModelBasis E) i) := by
    change (Bundle.Trivialization.coordChangeL (R := ℝ)
          ((tangentBundleCore I M).localTriv (achart H x₁))
          ((tangentBundleCore I M).localTriv (achart H x₀)) x)
        ((chartModelBasis E) i) = _
    exact VectorBundleCore.localTriv_coordChange_eq
        (tangentBundleCore I M) (achart H x₁) (achart H x₀) (b := x)
        ⟨hx1', hx0'⟩ _
  rw [hdef1, hequiv, hcc, tangentCoordChange_chartModelBasis_eq_sum (I := I) x₀ x₁ x i]
  have hsymmL : (T₀.symm x : E → TangentSpace I x) =
      (T₀.symmL ℝ x : E →L[ℝ] TangentSpace I x) := by
    funext v
    exact (T₀.symmL_apply hx0' v).symm
  rw [hsymmL]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul]
  rw [chartBasisVecFiber, T₀.symmL_apply hx0']
