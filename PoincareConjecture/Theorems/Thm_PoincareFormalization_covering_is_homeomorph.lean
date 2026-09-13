import Mathlib.Topology.Homotopy.Lifting

theorem PoincareFormalization.covering_is_homeomorph
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [ConnectedSpace E] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (p : E → X) (hp : IsCoveringMap p) :
    ∃ e : E ≃ₜ X, (e : E → X) = p := by sorry
