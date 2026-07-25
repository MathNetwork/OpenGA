import DifferentialGeometry

/-! # Declaration index generator (`DECLS.ndjson`)

Building this module walks the elaborated environment and writes `DECLS.ndjson`
at the package root: one JSON record per project declaration —
`{name, kind, signature, file, line}`, where `signature` is the fully
ELABORATED signature (ground truth, not parsed source).

It is a navigation aid (fast existence / location search for agents); it is NOT
a source of truth — confirm a declaration at its real `file:line` before citing
it. The module is a default target, so a bare `lake build` regenerates the index
whenever the library changed. The targeted `lake build DifferentialGeometry`
(used by the proof-fill loop) does NOT build this module, so that loop pays no
indexing cost. -/

open Lean Lean.Elab.Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | _ => ""
    if kind == "" then continue
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let mod := env.allImportedModuleNames[idx.toNat]!
      if mod.getRoot != `DifferentialGeometry then continue
      let file := (mod.toString).replace "." "/" ++ ".lean"
      let line := match (← Lean.findDeclarationRanges? n) with
        | some r => r.range.pos.line | none => 0
      let sig ← try
          let fwi ← liftTermElabM (Lean.PrettyPrinter.ppSignature n)
          pure fwi.fmt.pretty
        catch _ => pure ""
      let j := Json.mkObj [("name", Json.str n.toString), ("kind", Json.str kind),
                           ("signature", Json.str sig), ("file", Json.str file), ("line", Json.num line)]
      out := out.push j.compress
  IO.FS.writeFile "DECLS.ndjson" (String.intercalate "\n" out.toList ++ "\n")
  logInfo s!"DECLS.ndjson: {out.size} declarations indexed"
