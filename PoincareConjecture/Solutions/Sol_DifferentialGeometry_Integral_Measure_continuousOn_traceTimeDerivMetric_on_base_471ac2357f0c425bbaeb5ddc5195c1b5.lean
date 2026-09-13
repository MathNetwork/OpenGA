import Theorems.Thm_DifferentialGeometry_Integral_Measure_chartGramMatrix_posDef
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_ChartDensity
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Family
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDecomposition
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_FamilyDefs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Invariance
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_Properties
import Definitions.Def_ClosedSurface_DifferentialGeometry_Analysis_Integration_Measure_RiemannianMeasure
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Geometry_Metric_ChartGram
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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

lemma chartGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < (chartGramMatrix g x₀ x).det :=
  (chartGramMatrix_posDef (I := I) g x₀ hx).det_pos

end Measure

end Integral

end DifferentialGeometry

end

end

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix

open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

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

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_30

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_31

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_32

attribute [local instance] _root_.OpenGAExport.DifferentialGeometry.Analysis.Integration.Measure.Family.instance_33

variable {g_fam : ℝ → SmoothRiemannianMetric I M}

namespace DifferentialGeometry.Integral.Measure
end DifferentialGeometry.Integral.Measure
open _root_.DifferentialGeometry.Integral.Measure

lemma solution
    {g_fam : ℝ → SmoothRiemannianMetric I M} {t : ℝ}
    (hreg : MetricFamilyRegularAt (I := I) g_fam t)
    (α : M) :
    ContinuousOn
      (fun p : ℝ × M => Matrix.trace
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)))
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  set n := Fin (Module.finrank ℝ E)
  have hG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g_fam p.1) α p.2 i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_chartGramMatrix α i j
  have hdG_joint : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        deriv (fun s : ℝ => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := fun i j =>
    hreg.continuousOn_deriv_chartGramMatrix α i j
  have h_det_cont : ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hexp : (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).det)
        = (fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i, chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i) := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    rw [hexp]
    refine continuousOn_finsetSum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finsetProd _ (fun i _ => ?_)
    exact hG_joint (σ i) i
  have h_adj_cont : ∀ k v : n, ContinuousOn
      (fun p : ℝ × M => (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro k v
    have hform : ∀ p : ℝ × M,
        (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v
          = ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)).det := by
      intro p; rw [adjugate_apply]
    have hexp : ∀ p : ℝ × M,
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v (Pi.single k 1)).det
          = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i : n,
              ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                (Pi.single k 1)) (σ i) i := by
      intro p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
      rfl
    have hfn_eq :
        (fun p : ℝ × M =>
          (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate k v)
          = fun p : ℝ × M =>
            ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i : n,
                ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
                  (Pi.single k 1)) (σ i) i := by
      funext p; rw [hform p, hexp p]
    rw [hfn_eq]
    refine continuousOn_finsetSum _ (fun σ _ => ?_)
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_finsetProd _ (fun i _ => ?_)
    by_cases hiv : σ i = v
    · have hconst :
          (fun p : ℝ × M =>
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun _ => (Pi.single k 1 : n → ℝ) i := by
        funext p
        rw [hiv, Matrix.updateRow_self]
      rw [hconst]; exact continuousOn_const
    · have hnonrow :
          (fun p : ℝ × M =>
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2).updateRow v
              (Pi.single k 1)) (σ i) i)
            = fun p : ℝ × M =>
              chartGramMatrix (I := I) (g_fam p.1) α p.2 (σ i) i := by
        funext p
        rw [Matrix.updateRow_apply]
        exact if_neg hiv
      rw [hnonrow]; exact hG_joint (σ i) i
  have h_det_ne_zero : ∀ p ∈ (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet
        : Set (ℝ × M)),
      (chartGramMatrix (I := I) (g_fam p.1) α p.2).det ≠ 0 := by
    intro p hp
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) (g_fam p.1) α hp.2)
  have h_inv_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M => ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have h_inv_entry : ∀ p : ℝ × M,
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j
          = (chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      intro p
      rw [Matrix.inv_def]
      simp [Matrix.smul_apply, Ring.inverse_eq_inv']
    have hfn_eq :
        (fun p : ℝ × M => ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i j)
          = fun p : ℝ × M =>
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).det⁻¹ *
            (chartGramMatrix (I := I) (g_fam p.1) α p.2).adjugate i j := by
      funext p; exact h_inv_entry p
    rw [hfn_eq]
    refine ContinuousOn.mul ?_ (h_adj_cont i j)
    exact h_det_cont.inv₀ h_det_ne_zero
  have h_prod_cont : ∀ i j : n, ContinuousOn
      (fun p : ℝ × M =>
        ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
      (Set.univ ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    intro i j
    have hfun :
        (fun p : ℝ × M =>
          ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i j)
          = fun p : ℝ × M =>
            ∑ k : n, ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹) i k *
              (deriv (fun s : ℝ =>
                chartGramMatrix (I := I) (g_fam s) α p.2 k j) p.1) := by
      funext p
      rw [Matrix.mul_apply]
      rfl
    rw [hfun]
    refine continuousOn_finsetSum _ (fun k _ => ?_)
    exact (h_inv_cont i k).mul (hdG_joint k j)
  have htrace_eq : ∀ p : ℝ × M,
      Matrix.trace ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1)
        = ∑ i : n,
            ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
              Matrix.of fun i j : n =>
                deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    intro p
    rfl
  have hfun : (fun p : ℝ × M =>
        Matrix.trace ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
          Matrix.of fun i j : n =>
            deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1))
      = fun p : ℝ × M =>
          ∑ i : n, ((chartGramMatrix (I := I) (g_fam p.1) α p.2)⁻¹ *
            Matrix.of fun i j : n =>
              deriv (fun s => chartGramMatrix (I := I) (g_fam s) α p.2 i j) p.1) i i := by
    funext p; exact htrace_eq p
  rw [hfun]
  refine continuousOn_finsetSum _ (fun i _ => h_prod_cont i i)
