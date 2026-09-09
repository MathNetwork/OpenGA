import Lean
import LocalHomeomorph

open Lean in
run_meta do
  for declaration in [
      `IsProperMap.isCoveringMap_of_isLocalHomeomorph,
      `IsProperMap.isHomeomorph_of_isLocalHomeomorph,
      `IsLocalHomeomorph.isHomeomorph_of_compact] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains name do
        throwError "Unexpected proof axiom: {name}"
    Lean.logInfo m!"{declaration}: {axioms}"
