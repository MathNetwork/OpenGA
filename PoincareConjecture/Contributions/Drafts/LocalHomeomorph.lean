import Mathlib.Topology.Maps.Proper.Basic
import OpenGALib.Topology.CoveringSpace

/-!
# Proper local homeomorphisms

This draft compiles in its local Lake workspace. It is outside the main
OpenGALib library and is not part of the literature-based extinction route.

A proper local homeomorphism with Hausdorff domain is a covering map.
Its fibers are compact by properness and discrete by local invertibility,
hence finite. Closedness then gives evenly covered neighborhoods.
Over a simply connected, locally path connected base, a connected domain
makes this covering a homeomorphism.

This supplies a local-to-global interface for the covering-space branch of
the Poincare project and for global inverse arguments in geometric analysis.
Constructing the local homeomorphism and proving properness are explicit inputs.

References: Hatcher, *Algebraic Topology*, Section 1.3, Propositions 1.33 and 1.34;
Mathlib `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph` and
`IsProperMap.isCompact_preimage`, revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/

/-- **Math.** A proper local homeomorphism with Hausdorff domain is a covering map.
No surjectivity hypothesis is required by Mathlib's definition of covering map. -/
theorem IsProperMap.isCoveringMap_of_isLocalHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    {p : E → X} (hp : IsProperMap p) (hl : IsLocalHomeomorph p) :
    IsCoveringMap p := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  intro x _
  have hlocal : ∀ e ∈ p ⁻¹' {x},
      ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = p := by
    intro e _
    obtain ⟨φ, he, hφ⟩ := hl e
    exact ⟨φ, he, hφ.symm⟩
  have hfinite : (p ⁻¹' {x}).Finite :=
    (hp.isCompact_preimage isCompact_singleton).finite
      (IsDiscrete.of_openPartialHomeomorph p Set.Subset.rfl hlocal)
  exact hp.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph hfinite hlocal

/-- **Math.** A proper local homeomorphism from a connected Hausdorff space to a
simply connected, locally path connected space is a global homeomorphism. -/
theorem IsProperMap.isHomeomorph_of_isLocalHomeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsProperMap p) (hl : IsLocalHomeomorph p) :
    IsHomeomorph p :=
  (hp.isCoveringMap_of_isLocalHomeomorph hl).isHomeomorph_of_simplyConnectedSpace

/-- **Math.** Compactness supplies properness in the local-to-global theorem
when the codomain is Hausdorff. In particular this applies to maps from a sphere. -/
theorem IsLocalHomeomorph.isHomeomorph_of_compact
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X] [CompactSpace E] [ConnectedSpace E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hl : IsLocalHomeomorph p) : IsHomeomorph p :=
  hl.continuous.isProperMap.isHomeomorph_of_isLocalHomeomorph hl
