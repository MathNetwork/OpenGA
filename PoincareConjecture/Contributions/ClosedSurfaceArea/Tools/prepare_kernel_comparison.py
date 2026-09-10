#!/usr/bin/env python3
"""Generate exact kernel conversion checks for source/export expression differences."""
import json
from export_closed_surface import Export, DIRECTORY

e = Export()
differences = json.loads((DIRECTORY / 'Metadata/fingerprint_differences.json').read_text())
inverse = {b: a for a, b in e.renames.items()}
pairs = [(inverse.get(n, n), n) for n in differences]
renames = dict(e.renames)
for name in e.graph:
    roots = [n for n in e.renames if name.startswith(n + '.')]
    if roots:
        old = max(roots, key=len)
        renames[name] = e.renames[old] + name[len(old):]
pair_expr = '[' + ','.join('(' + json.dumps(a) + ',' + json.dumps(b) + ')' for a, b in pairs) + ']'
rename_expr = '[' + ','.join('(' + json.dumps(a) + ',' + json.dumps(b) + ')' for a, b in renames.items()) + ']'
codec = (DIRECTORY / 'Tools/ExpressionCodec.lean').read_text()
original = 'import OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea\n' + codec + r'''

partial def expandAuxiliaryProofs (env : Environment) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n ls =>
      if n.getString!.startsWith "_proof_" then
        match env.find? n with
        | some ci => (ci.value? (allowOpaque := true)).map fun v =>
          expandAuxiliaryProofs env (v.instantiateLevelParams ci.levelParams ls)
        | none => none
      else none
    | _ => none


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
run_meta do
  let pairs : List (String × String) := PAIRS
  let renamePairs : List (String × String) := RENAMES
  let renames := renamePairs.foldl (fun (m : Std.HashMap Name Name) (a,b) => m.insert a.toName b.toName) {}
  let env ← getEnv
  let mut table : ExprTable := {}
  let mut rows : Array Json := #[]
  for (original, exported) in pairs do
    let some ci := env.find? original.toName | throwError "Missing source {original}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"universe_{i}")
    let norm := fun x => exportNormalize renames (expandAuxiliaryProofs env (x.instantiateLevelParams ci.levelParams levels))
    let (typeId, next) := (encodeExpr (norm ci.type)).run table
    table := next
    let mut fields := [("name", toJson exported), ("type", toJson typeId)]
    if let .defnInfo d := ci then
      let (valueId, next) := (encodeExpr (norm d.value)).run table
      table := next
      fields := fields ++ [("value", toJson valueId)]
    rows := rows.push (Json.mkObj fields)
  let out := Json.mkObj [("nodes", Json.arr table.nodes), ("declarations", Json.arr rows)]
  IO.FS.writeFile OUTPUT out.compress
  logInfo m!"Serialized {rows.size} declarations as {table.nodes.size} expression DAG nodes."
'''
original = original.replace('PAIRS', pair_expr).replace('RENAMES', rename_expr).replace('OUTPUT', json.dumps(str(DIRECTORY / 'Metadata/source_expressions.json')))
(DIRECTORY / 'Tools/SerializeOriginal.lean').write_text(original)
exported = 'import Verified.ClosedSurface_OpenGALib_Interoperability_RicciFlow_ClosedSurfaceArea\n' + codec + r'''

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
run_meta do
  let text ← IO.FS.readFile "Metadata/source_expressions.json"
  let data ← ofExcept (Json.parse text)
  let nodes ← ofExcept (data.getObjValAs? (Array Json) "nodes")
  let expressions ← ofExcept (decodeExprTable nodes)
  let rows ← ofExcept (data.getObjValAs? (Array Json) "declarations")
  let mut count : Nat := 0
  for row in rows do
    let name ← ofExcept (row.getObjValAs? String "name")
    let some ci := (← getEnv).find? name.toName | throwError "Missing export {name}"
    let params := ci.levelParams.zipIdx |>.map fun (_, i) => Name.mkSimple s!"universe_{i}"
    let levels := params.map Level.param
    let index ← ofExcept (row.getObjValAs? Nat "type")
    let sourceType := expressions[index]!
    let exportedType := ci.type.instantiateLevelParams ci.levelParams levels
    let equality ← mkEq sourceType exportedType
    let proof ← mkEqRefl exportedType
    addDecl (.thmDecl {
      name := Name.str (Name.mkSimple "ClosedSurfaceExportValidation") s!"type_{count}"
      levelParams := params
      type := equality
      value := proof })
    if let .defnInfo d := ci then
      let index ← ofExcept (row.getObjValAs? Nat "value")
      let sourceValue := expressions[index]!
      let exportedValue := d.value.instantiateLevelParams ci.levelParams levels
      let equality ← mkEq sourceValue exportedValue
      let proof ← mkEqRefl exportedValue
      addDecl (.thmDecl {
        name := Name.str (Name.mkSimple "ClosedSurfaceExportValidation") s!"value_{count}"
        levelParams := params
        type := equality
        value := proof })
    logInfo m!"Kernel conversion passed: {name}"
    count := count + 1
  logInfo m!"All {count} source/export conversion checks passed."
'''
(DIRECTORY / 'Tools/KernelComparison.lean').write_text(exported)
print(f'Generated kernel checks for {len(pairs)} structurally differing declarations.')
