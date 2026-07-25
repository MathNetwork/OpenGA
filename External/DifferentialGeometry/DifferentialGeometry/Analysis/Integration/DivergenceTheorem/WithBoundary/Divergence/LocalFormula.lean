import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.PartialDerivWithin
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def localDivergenceWithin (g : SmoothRiemannianMetric I M)
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x =>
    (∑ i : Fin (Module.finrank ℝ E),
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      / chartDensity (I := I) g α x

omit [InnerProductSpace ℝ E] in
@[simp] lemma localDivergenceWithin_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    localDivergenceWithin (I := I) g α X x =
      (∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
lemma extChartAt_mem_interior_target_of_isInteriorPoint
    (α : M) {x : M} (hx_src : x ∈ (chartAt H α).source)
    (hx_int : x ∈ I.interior M) :
    extChartAt I α x ∈ interior (extChartAt I α).target := by
  have h := (I.isInteriorPoint_iff_of_mem_atlas (M := M) (n := ∞)
      (e := chartAt H α) (x := x)
      (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))
      (chart_mem_atlas H α) hx_src).1 hx_int
  exact h

omit [InnerProductSpace ℝ E] in
theorem localDivergenceWithin_eq_localDivergence_of_isInteriorPoint
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_src : x ∈ (chartAt H α).source)
    (hx_int : x ∈ I.interior M) :
    localDivergenceWithin (I := I) g α X x =
      localDivergence (I := I) g α X x := by
  classical
  have hy_int : extChartAt I α x ∈ interior (extChartAt I α).target :=
    extChartAt_mem_interior_target_of_isInteriorPoint
      (I := I) α hx_src hx_int
  have hsum :
      (∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
        = ∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i
              (fun y : E =>
                chartCoeffOnE (I := I) α X i y *
                  chartDensityOnE (I := I) g α y)
              (extChartAt I α x) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact partialDerivWithin_extChartAt_target_eq_partialDeriv
      (I := I) (M := M) α i
      (fun y : E =>
        chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      hy_int
  rw [localDivergenceWithin_def, localDivergence_def, hsum]

omit [InnerProductSpace ℝ E] in
lemma partialDerivWithin_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (extChartAt I α).target := by
  have hu : ContDiffOn ℝ ∞
      (fun z : E =>
        chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z)
      (extChartAt I α).target :=
    chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  have hUD : UniqueDiffOn ℝ (extChartAt I α).target :=
    uniqueDiffOn_extChartAt_target (I := I) α
  exact partialDerivWithin_contDiffOn_top_of_uniqueDiffOn (i := i) hu hUD

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma extChartAt_contMDiffOn_chartAt_source (α : M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E) (chartAt H α).source :=
  contMDiffOn_extChartAt (I := I) (x := α)

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma extChartAt_mapsTo_target (α : M) :
    Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source
      (extChartAt I α).target := by
  intro x hx
  have hx' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  exact (extChartAt I α).map_source hx'

omit [InnerProductSpace ℝ E] in
lemma localDivergenceWithin_summand_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun y : E =>
            chartCoeffOnE (I := I) α X i y *
              chartDensityOnE (I := I) g α y)
          (extChartAt I α x))
      (chartAt H α).source := by
  have hpartial : ContDiffOn ℝ ∞
      (fun y : E =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (extChartAt I α).target :=
    partialDerivWithin_chartCoeffOnE_mul_chartDensityOnE_contDiffOn
      (I := I) g α X i
  have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E =>
        partialDerivWithin (E := E) (extChartAt I α).target i
          (fun z : E =>
            chartCoeffOnE (I := I) α X i z *
              chartDensityOnE (I := I) g α z) y)
      (extChartAt I α).target := hpartial.contMDiffOn
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source :=
    extChartAt_contMDiffOn_chartAt_source (I := I) α
  have hsubset : (chartAt H α).source ⊆
      (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target :=
    fun x hx => extChartAt_mapsTo_target (I := I) α hx
  exact hpartialM.comp hchart hsubset

omit [InnerProductSpace ℝ E] in
lemma localDivergenceWithin_numerator_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (chartAt H α).source :=
  contMDiffOn_finset_sum
    (fun i _ => localDivergenceWithin_summand_contMDiffOn (I := I) g α X i)

omit [InnerProductSpace ℝ E] in
private lemma chartDensity_contMDiffOn_chartAt_source
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α) (chartAt H α).source :=
  chartDensity_contMDiffOn (I := I) g α

omit [InnerProductSpace ℝ E] in
private lemma chartDensity_ne_zero_on_chartAt_source
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ x ∈ (chartAt H α).source, chartDensity (I := I) g α x ≠ 0 :=
  fun _ hx => ne_of_gt (chartDensity_pos (I := I) g α hx)

omit [InnerProductSpace ℝ E] in
theorem localDivergenceWithin_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergenceWithin (I := I) g α X)
      (chartAt H α).source := by
  have hnum : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M =>
        ∑ i : Fin (Module.finrank ℝ E),
          partialDerivWithin (E := E) (extChartAt I α).target i
            (fun y : E =>
              chartCoeffOnE (I := I) α X i y *
                chartDensityOnE (I := I) g α y)
            (extChartAt I α x))
      (chartAt H α).source :=
    localDivergenceWithin_numerator_contMDiffOn (I := I) g α X
  have hden : ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g α)
      (chartAt H α).source :=
    chartDensity_contMDiffOn_chartAt_source (I := I) g α
  exact hnum.div₀ hden (chartDensity_ne_zero_on_chartAt_source (I := I) g α)

omit [InnerProductSpace ℝ E] in
theorem localDivergenceWithin_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (localDivergenceWithin (I := I) g α X) (chartAt H α).source :=
  (localDivergenceWithin_contMDiffOn (I := I) g α X).continuousOn

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
