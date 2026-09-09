import OpenGALib.GeometricMeasureTheory
import Lean.Util.CollectAxioms

/-! Mathematical regression checks for the varifold interfaces. -/

noncomputable section

open OpenGA MeasureTheory Set
open scoped ENNReal

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- A dimension label cannot admit a plane larger than its ambient space.
example : IsEmpty (Grassmannian Plane 3) := by
  constructor
  intro P
  have h := Submodule.finrank_le P.plane
  rw [P.finrank_plane] at h
  norm_num [Plane] at h

-- The identity parametrization gives area equal to Lebesgue measure of its domain.
example (K : Set Plane) (hK : IsCompact K) :
    (Varifold.ofParametrization (ContinuousLinearMap.id ℝ Plane)
      (ContinuousLinearMap.id ℝ Plane).contDiff K
      (Varifold.linearSurfaceTangentLift _ Function.injective_id)
      (Varifold.finite_area_of_isCompact (ContinuousLinearMap.id ℝ Plane).contDiff hK)).mass
      = volume K := by
  rw [Varifold.mass_ofParametrization]
  simp [Varifold.surfaceJacobian]
  change (∫⁻ _ in K, (1 : ℝ≥0∞)) = volume K
  simp

-- A constant map has zero area, even if the parameter domain has infinite measure.
example (y x : Plane) : Varifold.surfaceJacobian (fun _ : Plane => y) x = 0 := by
  apply Subtype.ext
  simp [Varifold.surfaceJacobian, Plane]

-- The varifold topology separates position-plane measures with equal spatial weights.
example (x : Plane) (P Q : Grassmannian Plane 1) (hPQ : P ≠ Q) :
    (Varifold.dirac x P).weightMeasure = (Varifold.dirac x Q).weightMeasure ∧
      Varifold.dirac x P ≠ Varifold.dirac x Q := by
  exact ⟨by simp, Varifold.dirac_ne_of_plane_ne x hPQ⟩

-- Check the complete new declaration families, including generated instances,
-- against Lean's standard logical axioms. A proof hole or custom axiom fails the check.
run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`OpenGA.Grassmannian).isPrefixOf name || (`OpenGA.Varifold).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  Lean.logInfo m!"Checked {checked} declarations: only standard logical axioms."
