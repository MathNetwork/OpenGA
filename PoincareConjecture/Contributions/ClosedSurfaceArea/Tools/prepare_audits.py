#!/usr/bin/env python3
"""Generate kernel-based source/export and per-solution validation programs."""
import json
from pathlib import Path
from export_closed_surface import DIRECTORY, Export

e = Export()
names = sorted({r['name'] for k in e.selected for r in e.groups[k]['rows']})
pairs = [(n, e.renames.get(n, n)) for n in names]
expanded_renames = dict(e.renames)
for name in e.graph:
    roots = [old for old in e.renames if name.startswith(old + '.')]
    if roots:
        old = max(roots, key=len)
        expanded_renames[name] = e.renames[old] + name[len(old):]
base = r'''
import Lean
open Lean Meta

partial def normalizeExportExpr (renames : Std.HashMap Name Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n ls => some (.const (renames.getD n n) ls)
    | .mdata _ v => some (normalizeExportExpr renames v)
    | .forallE _ t b i => some (.forallE .anonymous (normalizeExportExpr renames t) (normalizeExportExpr renames b) i)
    | .lam _ t b i => some (.lam .anonymous (normalizeExportExpr renames t) (normalizeExportExpr renames b) i)
    | .letE _ t v b n => some (.letE .anonymous (normalizeExportExpr renames t) (normalizeExportExpr renames v) (normalizeExportExpr renames b) n)
    | _ => none

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
run_meta do
  let env ← getEnv
  let pairs : List (String × String) := PAIRS
  let renames : Std.HashMap Name Name := RENAME
  let mut count : Nat := 0
  for (original, exported) in pairs do
    let name := PICK.toName
    let some ci := env.find? name | throwError "Missing declaration {name}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"universe_{i}")
    let norm := fun x => normalizeExportExpr renames (x.instantiateLevelParams ci.levelParams levels)
    let mut fields := [("name", Json.str exported), ("type_fingerprint", Json.str (toString (hash (norm ci.type))))]
    if (NODES : List String).contains exported then
      let shown ← withOptions (fun o => o.setBool `pp.explicit true |>.setBool `pp.fullNames true |>.setBool `pp.universes true) do
        ppExpr (norm ci.type)
      fields := fields ++ [("type", Json.str shown.pretty)]
    if let .defnInfo d := ci then
      fields := fields ++ [("value_fingerprint", Json.str (toString (hash (norm d.value))))]
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "Unexpected axiom in {name}: {axioms}"
    logInfo (Json.mkObj fields).compress
    count := count + 1
  logInfo m!"All {count} declarations passed the axiom audit."
'''
pair_text = '[' + ',\n'.join('(' + json.dumps(a) + ', ' + json.dumps(b) + ')' for a, b in pairs) + ']'
for kind, imp, pick in [('Original', 'OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea', 'original'),
                        ('Exported', 'Verified.ClosedSurface_OpenGALib_Interoperability_RicciFlow_ClosedSurfaceArea', 'exported')]:
    renamed_pairs = '[' + ','.join('(' + json.dumps(a) + ', ' + json.dumps(b) + ')' for a, b in expanded_renames.items()) + ']'
    mapping = '(' + renamed_pairs + ' : List (String × String)).foldl (fun acc (a, b) => acc.insert a.toName b.toName) {}' if kind == 'Original' else '{}'
    text = 'import ' + imp + '\n' + base.replace('PAIRS', pair_text).replace('RENAME', mapping).replace('PICK', pick).replace('NODES', '[' + ','.join(json.dumps(n) for n in e.nodes.values()) + ']')
    (DIRECTORY / 'Tools' / (kind + 'Audit.lean')).write_text(text)
for key, name in e.nodes.items():
    s = name.replace('.', '_')
    text = f'''import Theorems.Thm_{s}
import Solutions.Sol_{s}
import Lean
open Lean in
run_meta do
  let env ← getEnv
  let some target := env.find? `{name} | throwError "Missing target"
  let some proof := env.find? `solution | throwError "Missing solution"
  let levels := target.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"universe_{{i}}")
  unless target.levelParams.length == proof.levelParams.length do
    throwError "Universe arity differs"
  unless ← Meta.isDefEq (target.type.instantiateLevelParams target.levelParams levels)
      (proof.type.instantiateLevelParams proof.levelParams levels) do
    throwError "Solution does not match the exact target type"
  logInfo "Exact solution type passed."
'''
    (DIRECTORY / 'Tools' / ('Audit_' + s + '.lean')).write_text(text)
print(f'Generated source/export audits for {len(pairs)} declarations and {len(e.nodes)} solutions.')
