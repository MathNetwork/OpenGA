import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry
namespace Geometry

def HasFiniteAtlasIndexOnCompact
    (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∀ K : Set M, IsCompact K → (Set.image (chartAt H) K).Finite

namespace HasFiniteAtlasIndexOnCompact

variable {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem finite_image
    (h : HasFiniteAtlasIndexOnCompact H M)
    {K : Set M} (hK : IsCompact K) :
    (Set.image (chartAt H) K).Finite :=
  h K hK

theorem mono
    (h : HasFiniteAtlasIndexOnCompact H M)
    {K K' : Set M} (hK : IsCompact K) (hKK' : K' ⊆ K) (_hK' : IsCompact K') :
    (Set.image (chartAt H) K').Finite :=
  (h K hK).subset (Set.image_mono hKK')

theorem union
    (h : HasFiniteAtlasIndexOnCompact H M)
    {K₁ K₂ : Set M} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    (Set.image (chartAt H) (K₁ ∪ K₂)).Finite := by
  rw [Set.image_union]
  exact (h K₁ hK₁).union (h K₂ hK₂)

theorem image_empty :
    (Set.image (chartAt H) (∅ : Set M)).Finite := by
  rw [Set.image_empty]
  exact Set.finite_empty

end HasFiniteAtlasIndexOnCompact

theorem hasFiniteAtlasIndexOnCompact_self
    (H : Type*) [TopologicalSpace H] :
    HasFiniteAtlasIndexOnCompact H H := by
  intro K _hK
  refine Set.Finite.subset (Set.finite_singleton (OpenPartialHomeomorph.refl H))
    ?_
  rintro e ⟨b, _hb, hbe⟩
  have h_eq : chartAt H b = OpenPartialHomeomorph.refl H := chartAt_self_eq
  rw [← hbe, h_eq]
  exact Set.mem_singleton _

end Geometry
end DifferentialGeometry

end
