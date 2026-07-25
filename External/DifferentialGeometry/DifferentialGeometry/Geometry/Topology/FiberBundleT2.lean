import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false















namespace DifferentialGeometry

open Bundle Set Topology


instance FiberBundle.t2Space_totalSpace
    {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    {E : B → Type*} [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [T2Space B] [T2Space F] :
    T2Space (Bundle.TotalSpace F E) := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases hproj : (π F E) x = (π F E) y
  ·
    set e := trivializationAt F E ((π F E) x) with he
    have hxs : x ∈ e.source := by
      rw [e.mem_source]; exact mem_baseSet_trivializationAt F E _
    have hys : y ∈ e.source := by
      rw [e.mem_source, ← hproj]; exact mem_baseSet_trivializationAt F E _
    have hexy : e x ≠ e y := fun h => hxy (e.toOpenPartialHomeomorph.injOn hxs hys h)
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hexy
    refine ⟨e.source ∩ e ⁻¹' U, e.source ∩ e ⁻¹' V,
      e.toOpenPartialHomeomorph.isOpen_inter_preimage hU,
      e.toOpenPartialHomeomorph.isOpen_inter_preimage hV,
      ⟨hxs, hxU⟩, ⟨hys, hyV⟩, ?_⟩
    exact (hUV.preimage e).mono inter_subset_right inter_subset_right
  ·
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hproj
    refine ⟨(π F E) ⁻¹' U, (π F E) ⁻¹' V,
      hU.preimage (FiberBundle.continuous_proj F E),
      hV.preimage (FiberBundle.continuous_proj F E), hxU, hyV, ?_⟩
    exact hUV.preimage _

end DifferentialGeometry
