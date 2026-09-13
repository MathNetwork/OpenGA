import OpenGALib.Riemannian.Surface.Width
import OpenGALib.Analysis.Width.SweepoutProfile

/-! The sweepout and geometric-energy foundation must not use project axioms
or proof holes, including through the imported metric and measure definitions. -/

open Lean in
run_meta do
  for name in [`OpenGA.RicciFlow.SmoothSweepout.const,
      `OpenGA.RicciFlow.sampleFamily,
      `OpenGA.Surface.dirichletDensity_nonneg,
      `OpenGA.Surface.dirichletEnergy_eq_ofReal_integral,
      `OpenGA.Surface.dirichletEnergy_lt_top_of_integrable,
      `OpenGA.Surface.dirichletEnergy_const,
      `OpenGA.RicciFlow.SmoothSweepout.homotopic_refl,
      `OpenGA.RicciFlow.SmoothSweepout.Homotopic.symm,
      `OpenGA.RicciFlow.SmoothSweepout.Homotopic.trans,
      `OpenGA.RicciFlow.SmoothSweepout.homotopyWidth_le_maxEnergy,
      `OpenGA.RicciFlow.SmoothSweepout.homotopyWidth_eq_of_homotopic,
      `OpenGA.RicciFlow.SmoothSweepout.exists_maxEnergy_lt,
      `OpenGA.RicciFlow.SmoothSweepout.homotopyWidth_const,
      `OpenGA.profile_pair_area_eq_energy,
      `OpenGA.profile_pair_area_le_width] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    logInfo m!"{name}: {axioms}"
