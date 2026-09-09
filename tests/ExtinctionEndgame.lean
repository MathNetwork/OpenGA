import OpenGALib.Topology.ExtinctionEndgame
import Lean.Util.CollectAxioms

/-! Regression checks for the formal extinction endpoint. -/

open OpenGA

universe u

-- The quotient construction has concrete coordinate balls and an actual gluing.
private def identityBall : CoordinateBall EuclideanThree where
  chart := OpenPartialHomeomorph.refl EuclideanThree
  closedBall_subset_source := Set.subset_univ _

example : IsConnectedSum EuclideanThree EuclideanThree
    (ConnectedSum.Space identityBall identityBall (Homeomorph.refl SphereTwo)) :=
  ⟨identityBall, identityBall, Homeomorph.refl SphereTwo, ⟨Homeomorph.refl _⟩⟩

-- Corresponding boundary points are identified in the quotient, as required.
example (x : SphereTwo) :
    Quot.mk (ConnectedSum.BoundaryIdentification identityBall identityBall
      (Homeomorph.refl SphereTwo)) (Sum.inl (identityBall.boundary x)) =
    Quot.mk (ConnectedSum.BoundaryIdentification identityBall identityBall
      (Homeomorph.refl SphereTwo)) (Sum.inr (identityBall.boundary x)) :=
  Quot.sound ⟨x, rfl, rfl⟩

-- Standard discarded components give a valid one-event extinction record.
example (M : ClosedThreeManifold.{u}) (hM : M.IsStandardFactor) :
    FiniteSurgeryHistory [M] [] := by
  apply FiniteSurgeryHistory.step (middle := []) _ (.refl [])
  intro N hN
  have hNM : N = M := by simpa using hN
  subst N
  exact .factor (Or.inr hM)

-- The same definitions also allow a persistent evolution. Finite extinction
-- is not silently included in the topology data's definition.
private def persistentEvolution (M : ClosedThreeManifold.{u}) : SurgeryTopologyEvolution M where
  components := fun _ => [M]
  initial := rfl
  history := fun _ _ => .refl [M]

example (M : ClosedThreeManifold.{u}) : ¬(persistentEvolution M).FiniteExtinction := by
  rintro ⟨T, _, hT⟩
  have h := hT T le_rfl
  simp [persistentEvolution] at h

-- Consequently a persistent evolution cannot supply the common width bound.
example (M : ClosedThreeManifold.{u}) (W : ℝ) :
    ¬(persistentEvolution M).HasWidthControl W := by
  intro hc
  obtain ⟨T, _, hT⟩ := (persistentEvolution M).finiteExtinction_of_width_control hc
  have h := hT T le_rfl
  simp [persistentEvolution] at h

-- Audit every declaration, including generated instances and private helpers,
-- in the new reusable modules. Custom axioms and proof holes are rejected.
run_cmd do
  let env ← Lean.getEnv
  let modules := #[`OpenGALib.Topology.ConnectedSum,
    `OpenGALib.Topology.SurgeryReconstruction, `OpenGALib.Topology.ExtinctionEndgame,
    `OpenGALib.Analysis.ComparisonExtinction]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless modules.contains mod do continue
    for axiomName in (← Lean.collectAxioms name) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    checked := checked + 1
  if checked == 0 then throwError "No reusable declarations were audited"
  Lean.logInfo m!"Checked {checked} reusable declarations: only standard logical axioms."
