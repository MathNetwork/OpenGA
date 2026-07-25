import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar


noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

class HasSmoothBoundary
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) where

  boundaryE : Type*

  [boundaryENormedGroup : NormedAddCommGroup boundaryE]

  [boundaryENormedSpace : NormedSpace ℝ boundaryE]

  [boundaryEInnerProductSpace : InnerProductSpace ℝ boundaryE]

  [boundaryEFiniteDimensional : FiniteDimensional ℝ boundaryE]

  boundaryH : Type*

  [boundaryHTopologicalSpace : TopologicalSpace boundaryH]

  boundaryI : ModelWithCorners ℝ boundaryE boundaryH

  [boundaryIBoundaryless : boundaryI.Boundaryless]

  inclH : boundaryH → H

  inclH_continuous : Continuous inclH

  inclH_injective : Function.Injective inclH

  inclH_isInducing : IsInducing inclH

  inclH_isClosed_image : IsClosed (Set.range (I ∘ inclH))

  projE : E → boundaryE

  projE_continuous : Continuous projE

  projE_contDiff : ContDiff ℝ ∞ projE

  I_inclH_boundaryI_symm_contDiff : ContDiff ℝ ∞ (I ∘ inclH ∘ boundaryI.symm)

  range_I_inclH : Set.range (I ∘ inclH) = frontier (Set.range I)

  proj_inclH_compat : ∀ x : boundaryH, projE (I (inclH x)) = boundaryI x

  inwardCoordE : E

  inwardCoordE_transverse :
    ∀ y : boundaryE, inwardCoordE ∉ Set.range
      (fderiv ℝ ((I : H → E) ∘ inclH ∘ boundaryI.symm) y)

  range_frontier_basis_addHaar_zero :
    ∀ [_h : FiniteDimensional ℝ E],
      letI : MeasurableSpace E := borel E
      haveI : BorelSpace E := ⟨rfl⟩
      ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
          (frontier (Set.range I)) = 0

  finrank_boundaryE_succ :
    ∀ [_h : FiniteDimensional ℝ E],
      Module.finrank ℝ boundaryE + 1 = Module.finrank ℝ E

instance HasSmoothBoundary.instNormedAddCommGroupBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    NormedAddCommGroup hI.boundaryE := hI.boundaryENormedGroup

instance HasSmoothBoundary.instNormedSpaceBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    NormedSpace ℝ hI.boundaryE := hI.boundaryENormedSpace

instance HasSmoothBoundary.instInnerProductSpaceBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    InnerProductSpace ℝ hI.boundaryE := hI.boundaryEInnerProductSpace

instance HasSmoothBoundary.instFiniteDimensionalBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    FiniteDimensional ℝ hI.boundaryE := hI.boundaryEFiniteDimensional

instance HasSmoothBoundary.instTopologicalSpaceBoundaryH
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    TopologicalSpace hI.boundaryH := hI.boundaryHTopologicalSpace

instance HasSmoothBoundary.instBoundarylessBoundaryI
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    hI.boundaryI.Boundaryless := hI.boundaryIBoundaryless

namespace HasSmoothBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

abbrev boundaryModelE (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Type _ := hI.boundaryE

abbrev boundaryModelH (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Type _ := hI.boundaryH

abbrev boundaryModel
    (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    ModelWithCorners ℝ hI.boundaryE hI.boundaryH := hI.boundaryI

section Inclusion

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem inclH_isEmbedding : IsEmbedding hI.inclH where
  toIsInducing := hI.inclH_isInducing
  injective := hI.inclH_injective

theorem continuous_I_inclH : Continuous (I ∘ hI.inclH) :=
  I.continuous.comp hI.inclH_continuous

theorem injective_I_inclH : Function.Injective (I ∘ hI.inclH) :=
  I.injective.comp hI.inclH_injective

end Inclusion

section Range

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem range_I_inclH_subset_frontier :
    Set.range (I ∘ hI.inclH) ⊆ frontier (Set.range I) := by
  rw [hI.range_I_inclH]

theorem frontier_subset_range_I_inclH :
    frontier (Set.range I) ⊆ Set.range (I ∘ hI.inclH) := by
  rw [hI.range_I_inclH]

theorem mem_frontier_range_iff_exists_inclH (y : E) :
    y ∈ frontier (Set.range I) ↔ ∃ x : hI.boundaryH, y = I (hI.inclH x) := by
  rw [← hI.range_I_inclH]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem frontier_range_eq_range_I_inclH :
    frontier (Set.range I) = Set.range (I ∘ hI.inclH) := hI.range_I_inclH.symm

theorem mem_range_inclH_iff (h : H) :
    (∃ z : hI.boundaryH, hI.inclH z = h) ↔ I h ∈ frontier (Set.range I) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    rw [hI.range_I_inclH.symm]
    exact ⟨z, rfl⟩
  · intro hH
    rw [← hI.range_I_inclH] at hH
    obtain ⟨z, hz⟩ := hH
    refine ⟨z, ?_⟩
    have hz' : I (hI.inclH z) = I h := hz
    exact I.injective hz'

end Range

section Compat

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem proj_inclH_apply (x : hI.boundaryH) :
    hI.projE (I (hI.inclH x)) = hI.boundaryI x := hI.proj_inclH_compat x

theorem projE_comp_I_comp_inclH :
    hI.projE ∘ I ∘ hI.inclH = hI.boundaryI := by
  funext x
  simpa [Function.comp] using hI.proj_inclH_compat x

end Compat

section TopologicalDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem mem_range_I_inclH_iff (y : E) :
    y ∈ Set.range (I ∘ hI.inclH) ↔ ∃ x : hI.boundaryH, I (hI.inclH x) = y := by
  rfl

theorem isClosed_range_I_inclH : IsClosed (Set.range (I ∘ hI.inclH)) :=
  hI.inclH_isClosed_image

omit hI in
theorem isClosed_frontier_range :
    IsClosed (frontier (Set.range I)) := isClosed_frontier

end TopologicalDerived

section EmbeddingDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem isInducing_I_inclH : IsInducing (I ∘ hI.inclH) := by
  have hI_inducing : IsInducing (I : H → E) := I.isClosedEmbedding.isEmbedding.isInducing
  exact hI_inducing.comp hI.inclH_isInducing

theorem isEmbedding_I_inclH : IsEmbedding (I ∘ hI.inclH) where
  toIsInducing := isInducing_I_inclH I
  injective := injective_I_inclH I

theorem isClosedEmbedding_I_inclH : IsClosedEmbedding (I ∘ hI.inclH) where
  toIsEmbedding := isEmbedding_I_inclH I
  isClosed_range := hI.inclH_isClosed_image

end EmbeddingDerived

section SmoothnessDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem projE_contDiff' : ContDiff ℝ ∞ hI.projE := hI.projE_contDiff

theorem I_inclH_boundaryI_symm_contDiff' :
    ContDiff ℝ ∞ ((I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm) :=
  hI.I_inclH_boundaryI_symm_contDiff

theorem projE_contDiffOn (s : Set E) : ContDiffOn ℝ ∞ hI.projE s :=
  hI.projE_contDiff.contDiffOn

theorem I_inclH_boundaryI_symm_contDiffOn (s : Set hI.boundaryE) :
    ContDiffOn ℝ ∞ ((I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm) s :=
  hI.I_inclH_boundaryI_symm_contDiff.contDiffOn

end SmoothnessDerived

section NullSetDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]
variable [FiniteDimensional ℝ E]

theorem range_frontier_basisAddHaar_volume_zero :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
        (frontier (Set.range I)) = 0 := by
  exact hI.range_frontier_basis_addHaar_zero

theorem range_inclH_basisAddHaar_volume_zero :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
        (Set.range ((I : H → E) ∘ hI.inclH)) = 0 := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rw [hI.range_I_inclH]
  exact hI.range_frontier_basis_addHaar_zero

theorem subset_range_frontier_basisAddHaar_volume_zero
    {S : Set E} (hS : S ⊆ frontier (Set.range I)) :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E) S = 0 := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact MeasureTheory.measure_mono_null hS hI.range_frontier_basis_addHaar_zero

end NullSetDerived

section Boundaryless

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem boundaryH_isEmpty_of_boundaryless [I.Boundaryless] :
    IsEmpty hI.boundaryH := by
  refine ⟨fun x => ?_⟩
  have h_in : I (hI.inclH x) ∈ Set.range (I ∘ hI.inclH) := ⟨x, rfl⟩
  rw [hI.range_I_inclH] at h_in
  rw [show frontier (Set.range I) = ∅ from ?_] at h_in
  · exact (Set.notMem_empty _ h_in)
  · rw [I.range_eq_univ, frontier_univ]

end Boundaryless

end HasSmoothBoundary

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
