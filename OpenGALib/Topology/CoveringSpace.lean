import Mathlib.Topology.Homotopy.Lifting

/-!
# Connected coverings of simply connected spaces

A covering map from a connected space onto a simply connected, locally path connected space
is a homeomorphism. Surjectivity need not be assumed: lift the identity on the base through a
point of the nonempty total space. Uniqueness of lifts makes this section a two-sided inverse.

The statement and lifting argument were contributed by `salim` to the Prove2Me Poincare mission:
theorem `192cef90-169f-4470-b074-8392596cb487`, accepted submission
`bbe6fec0-1a12-4eba-bb85-2c00ebf62342` (2026-09-08). This version exposes `IsHomeomorph`, so callers
can use Mathlib's existing bijectivity and bundled-homeomorphism interfaces.
Source: https://prove2.me/api/v1/submissions/bbe6fec0-1a12-4eba-bb85-2c00ebf62342/solution

Mathematical reference: Hatcher, *Algebraic Topology*, Section 1.3, Propositions 1.33 and 1.34.
-/

/-- **Math.** A covering map from a connected space to a simply connected, locally path connected
space is a homeomorphism. `ConnectedSpace E` includes nonemptiness, which is needed to lift the
identity of the base. No separation, compactness, or manifold hypotheses are required. -/
theorem IsCoveringMap.isHomeomorph_of_simplyConnectedSpace
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (hp : IsCoveringMap p) : IsHomeomorph p := by
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e₀) e₀ rfl
  have hleft : (s : X → E) ∘ p = id := by
    apply hp.eq_of_comp_eq (s.continuous.comp hp.continuous) continuous_id
    · ext e
      exact congrFun hs (p e)
    · exact hs₀
  exact ⟨hp.continuous, hp.isOpenMap,
    Function.LeftInverse.injective (fun e => congrFun hleft e),
    Function.RightInverse.surjective (fun x => congrFun hs x)⟩
