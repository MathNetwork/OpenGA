import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Integration.Volume.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Properties
import DifferentialGeometry.Integration.Volume.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import DifferentialGeometry.Integration.Volume.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula


























































noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure












omit [FiniteDimensional ℝ E] in
private lemma extChartAt_symm_mapsTo_baseSet (α : M) :
    Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro y hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  exact hsource

private lemma partialDeriv_contDiffOn_interior
    (i : Fin (Module.finrank ℝ E)) {u : E → ℝ} {s : Set E}
    (hu : ContDiffOn ℝ ∞ u s) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) i u) (interior s) := by

  have hu_int : ContDiffOn ℝ ∞ u (interior s) := hu.mono interior_subset



  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior s) :=
    hu_int.fderiv_of_isOpen isOpen_interior
      (by rw [ENat.coe_top_add_one])

  have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) i)
      (interior s) := contDiffOn_const

  exact hfderiv.clm_apply hconst

private def localDivergenceDomain (α : M) : Set M :=
  (extChartAt I α).source ∩
    (extChartAt I α) ⁻¹' interior (extChartAt I α).target

omit [FiniteDimensional ℝ E] in
private lemma localDivergenceDomain_subset_baseSet (α : M) :
    localDivergenceDomain (I := I) α ⊆
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x hx


  rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
  rw [← extChartAt_source_eq_chartAt_source (I := I)]
  exact hx.1



private lemma localDivergence_summand_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y *
              chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      (localDivergenceDomain (I := I) α) := by

  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) :=
    partialDeriv_chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i

  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        partialDeriv (E := E) i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (interior (extChartAt I α).target) := hpartial.contMDiffOn

  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt


  have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (localDivergenceDomain (I := I) α) := by
    refine hchart.mono ?_
    intro x hx
    have h1 : x ∈ (extChartAt I α).source := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
    exact h1

  have hsubset : localDivergenceDomain (I := I) α ⊆
      (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
    fun _ hx => hx.2
  exact hpartialM.comp hchart' hsubset



private lemma chartDensity_contMDiffOn_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (localDivergenceDomain (I := I) α) :=
  (chartDensity_contMDiffOn (I := I) g α).mono
    (localDivergenceDomain_subset_baseSet (I := I) α)


private lemma chartDensity_ne_zero_on_localDivergenceDomain
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ x ∈ localDivergenceDomain (I := I) α, chartDensity (I := I) g α x ≠ 0 :=
  fun _ hx => ne_of_gt
    (chartDensity_pos (I := I) g α
      (localDivergenceDomain_subset_baseSet (I := I) α hx))


theorem divergence_g_chart_product
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g (I := I) g X x =
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (chartCoeffOnE (I := I) x X i) (extChartAt I x x)) +
        (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) x X i (extChartAt I x x) *
            partialDeriv (E := E) i
              (chartDensityOnE (I := I) g x) (extChartAt I x x)) /
          chartDensity (I := I) g x x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target := by
    simp [hy₀_def, (extChartAt I x).map_source hxsrc]
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target (I := I) x).mem_nhds hy₀_target
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensity (I := I) g x x :=
    chartDensity_pos (I := I) g x hbase
  have hρ_ne : chartDensity (I := I) g x x ≠ 0 := ne_of_gt hρ_pos
  have hsymm : (extChartAt I x).symm y₀ = x := by
    simp [hy₀_def, (extChartAt I x).left_inv hxsrc]
  have hρOnE :
      chartDensityOnE (I := I) g x y₀ = chartDensity (I := I) g x x := by
    change chartDensity (I := I) g x ((extChartAt I x).symm y₀) =
      chartDensity (I := I) g x x
    rw [hsymm]
  have hcoeff_diff :
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentiableAt ℝ (chartCoeffOnE (I := I) x X i) y₀ := by
    intro i
    have hsmooth : ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x X i)
        (extChartAt I x).target :=
      chartCoeffOnE_contDiffOn (I := I) x X i
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hρ_diff :
      DifferentiableAt ℝ (chartDensityOnE (I := I) g x) y₀ := by
    have hsmooth : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x)
        (extChartAt I x).target :=
      chartDensityOnE_contDiffOn (I := I) g x
    exact ((hsmooth y₀ hy₀_target).contDiffAt htarget_nhd).differentiableAt
      (by simp)
  have hprod :
      ∀ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀ =
          partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀ := by
    intro i
    unfold partialDeriv
    have hmul : fderiv ℝ
        (fun y : E =>
          chartCoeffOnE (I := I) x X i y *
            chartDensityOnE (I := I) g x y) y₀ =
        chartCoeffOnE (I := I) x X i y₀ •
          fderiv ℝ (chartDensityOnE (I := I) g x) y₀ +
        chartDensityOnE (I := I) g x y₀ •
          fderiv ℝ (chartCoeffOnE (I := I) x X i) y₀ :=
      fderiv_fun_mul (hcoeff_diff i) hρ_diff
    rw [hmul]
    rw [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [divergence_g_def, localDivergence_def]
  change
    (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) /
      chartDensity (I := I) g x x = _
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i
          (fun y : E =>
            chartCoeffOnE (I := I) x X i y *
              chartDensityOnE (I := I) g x y) y₀) =
        ∑ i : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
            chartDensityOnE (I := I) g x y₀ +
          chartCoeffOnE (I := I) x X i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g x) y₀) by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hprod i]
  rw [Finset.sum_add_distrib]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀ *
          chartDensityOnE (I := I) g x y₀) =
        (∑ i : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) i (chartCoeffOnE (I := I) x X i) y₀) *
          chartDensityOnE (I := I) g x y₀ by
      rw [Finset.sum_mul]]
  rw [hρOnE]
  rw [add_div]
  rw [mul_div_assoc, div_self hρ_ne, mul_one]

end DifferentialGeometry.Integral.DivergenceTheorem
