import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.ChartInvariance
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula
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

def divergence_g_with_boundary
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun x => localDivergenceWithin (I := I) g x X x

omit [InnerProductSpace ℝ E] in
@[simp] lemma divergence_g_with_boundary_def
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    divergence_g_with_boundary (I := I) g X x =
      localDivergenceWithin (I := I) g x X x := rfl

omit [InnerProductSpace ℝ E] in
theorem voss_weyl_divergence_with_boundary_formula [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_α : x ∈ (chartAt H α).source) (hx_int : x ∈ I.interior M) :
    divergence_g_with_boundary (I := I) g X x =
      localDivergenceWithin (I := I) g α X x := by
  unfold divergence_g_with_boundary
  exact localDivergenceWithin_chart_invariance
    (I := I) g x α X (mem_chart_source H x) hx_α hx_int

omit [InnerProductSpace ℝ E] in
theorem divergence_g_with_boundary_eq_divergence_g_of_isInteriorPoint
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx_int : x ∈ I.interior M) :
    divergence_g_with_boundary (I := I) g X x = divergence_g (I := I) g X x := by
  unfold divergence_g_with_boundary
  rw [divergence_g_def]
  exact localDivergenceWithin_eq_localDivergence_of_isInteriorPoint
    (I := I) g x X (mem_chart_source H x) hx_int

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma isOpen_interior_M : IsOpen (I.interior M) :=
  I.isOpen_interior (M := M) (n := ∞)
    (by exact (by decide : (∞ : WithTop ℕ∞) ≠ 0))

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E] in
private lemma chart_source_inter_interior_open_nhd (x : M) (hx_int : x ∈ I.interior M) :
    IsOpen ((chartAt H x).source ∩ I.interior M) ∧
      x ∈ (chartAt H x).source ∩ I.interior M := by
  refine ⟨?_, ?_, ?_⟩
  · exact (chartAt H x).open_source.inter isOpen_interior_M
  · exact mem_chart_source H x
  · exact hx_int

omit [InnerProductSpace ℝ E] in
private lemma divergence_g_with_boundary_eq_localDivergenceWithin_on_chart
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    ∀ y ∈ (chartAt H x).source ∩ I.interior M,
      divergence_g_with_boundary (I := I) g X y =
        localDivergenceWithin (I := I) g x X y := by
  intro y hy
  exact voss_weyl_divergence_with_boundary_formula
    (I := I) g x X hy.1 hy.2

omit [InnerProductSpace ℝ E] in
private lemma localDivergenceWithin_contMDiffOn_chart_inter_interior
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (localDivergenceWithin (I := I) g x X)
      ((chartAt H x).source ∩ I.interior M) :=
  (localDivergenceWithin_contMDiffOn (I := I) g x X).mono Set.inter_subset_left

omit [InnerProductSpace ℝ E] in
private lemma divergence_g_with_boundary_contMDiffOn_chart_inter_interior
    [T2Space M] (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (divergence_g_with_boundary (I := I) g X)
      ((chartAt H x).source ∩ I.interior M) := by
  have hsmooth :=
    localDivergenceWithin_contMDiffOn_chart_inter_interior (I := I) g X x
  have hcongr := divergence_g_with_boundary_eq_localDivergenceWithin_on_chart
    (I := I) g X x
  exact hsmooth.congr hcongr

omit [InnerProductSpace ℝ E] in
theorem divergence_g_with_boundary_contMDiffOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ) ∞ (divergence_g_with_boundary (I := I) g X)
      (I.interior M) := by
  refine contMDiffOn_of_locally_contMDiffOn ?_
  intro x hx_int
  refine ⟨(chartAt H x).source, ?_, ?_, ?_⟩
  · exact (chartAt H x).open_source
  · exact mem_chart_source H x
  · have hsm := divergence_g_with_boundary_contMDiffOn_chart_inter_interior
      (I := I) g X x
    have hset_eq : I.interior M ∩ (chartAt H x).source =
        (chartAt H x).source ∩ I.interior M := by
      rw [Set.inter_comm]
    rw [hset_eq]
    exact hsm

omit [InnerProductSpace ℝ E] in
theorem divergence_g_with_boundary_continuousOn_interior [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (divergence_g_with_boundary (I := I) g X) (I.interior M) :=
  (divergence_g_with_boundary_contMDiffOn_interior (I := I) g X).continuousOn

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
