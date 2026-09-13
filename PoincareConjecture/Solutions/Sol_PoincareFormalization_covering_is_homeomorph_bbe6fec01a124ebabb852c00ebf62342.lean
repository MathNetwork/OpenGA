import Mathlib.Topology.Homotopy.Lifting

theorem solution
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (p : E → X) (hp : IsCoveringMap p) :
    ∃ e : E ≃ₜ X, (e : E → X) = p := by
  classical
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  obtain ⟨s, ⟨hs₀, hs⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e₀) e₀ rfl
  have hleft : (s : X → E) ∘ p = id := by
    apply hp.eq_of_comp_eq (s.continuous.comp hp.continuous) continuous_id
    · ext e
      exact congrFun hs (p e)
    · exact hs₀
  have hbij : Function.Bijective p :=
    ⟨Function.LeftInverse.injective (fun e => congrFun hleft e),
     Function.RightInverse.surjective (fun x => congrFun hs x)⟩
  exact ⟨hp.isLocalHomeomorph.toHomeomorphOfBijective hbij, rfl⟩
