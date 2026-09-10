import DifferentialGeometry.Geometry.Boundary.SecondFundamentalForm

/-! This audit checks the existing boundary interface only. Its symmetry
lemma explicitly assumes symmetry of the chart coefficients; it is not an
intrinsic Gauss-equation or Gauss-Bonnet theorem for an immersed surface. -/

open Lean in
run_meta do
  for name in [
    `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.secondFundamentalForm,
    `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.secondFundamentalForm_symm,
    `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.secondFundamentalFormBoundary,
    `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.secondFundamentalFormBoundary_symm] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
  logInfo "Four boundary declarations passed the axiom audit."
