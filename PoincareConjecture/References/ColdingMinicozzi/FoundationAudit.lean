import OpenGALib.Riemannian.Surface.NormalProjection
import Lean

open Lean in
run_meta do
  for name in #[`OpenGA.Surface.tangentPlane, `OpenGA.Surface.normalSpace,
      `OpenGA.Surface.finrank_tangentPlane,
      `OpenGA.Surface.inner_normal_tangent_eq_zero,
      `OpenGA.Surface.tangentPlane_inf_normalSpace,
      `OpenGA.Surface.isCompl_tangentPlane_normalSpace,
      `OpenGA.Surface.finrank_normalSpace,
      `OpenGA.Surface.tangentProjection, `OpenGA.Surface.normalProjection,
      `OpenGA.Surface.tangentProjection_mem, `OpenGA.Surface.normalProjection_mem,
      `OpenGA.Surface.normalProjection_mfderiv,
      `OpenGA.Surface.tangentProjection_add_normalProjection] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
  logInfo "All 13 tangent and normal space declarations passed the axiom audit."
