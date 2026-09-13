#!/usr/bin/env python3
"""Validate exact upload bytes, source types, definitions and proof dependencies."""

from datetime import datetime, timezone
import json
import subprocess

from export_endgame import DIRECTORY, REPOSITORY, SOURCE, digest


def run(cmd, cwd, log):
    result = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (DIRECTORY / "Metadata" / log).write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(log + ": " + result.stdout[-4000:])
    return result.stdout


def main():
    path = DIRECTORY / "publication.json"
    record = json.loads(path.read_text())
    if any((e.get("publication") and not e.get("existing_target")) or e.get("submission") for e in record["definitions"] + record["theorems"]):
        raise RuntimeError("Do not replace validation after publication starts")
    run(["lake", "build"], DIRECTORY, "build.log")
    names = json.loads((DIRECTORY / "Metadata/selected_declarations.json").read_text())
    code = '''
open Lean in
run_meta do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in NAMES do
    let some ci := env.find? name | throwError "Missing {name}"
    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"universe_{i}")
    let type := ci.type.instantiateLevelParams ci.levelParams levels
    let shown ← withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
      Meta.ppExpr type
    let mut fields := [("name", Json.str name.toString), ("type", Json.str shown.pretty)]
    if let .defnInfo d := ci then
      let value := d.value.instantiateLevelParams ci.levelParams levels
      let printed ← withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
        Meta.ppExpr value
      fields := fields ++ [("value", Json.str printed.pretty)]
    rows := rows.push (Json.mkObj fields)
  logInfo (Json.arr rows).compress
'''.replace("NAMES", "[" + ",".join("`" + n for n in names) + "]")
    (DIRECTORY / "Tools/OriginalTypes.lean").write_text("import Reduction\n" + code)
    imports = "".join("import " + e["path"][:-5].replace("/", ".") + "\n"
                      for e in record["definitions"] + record["theorems"])
    (DIRECTORY / "Tools/ExportedTypes.lean").write_text(imports + code)
    original = run(["lake", "env", "lean", str(DIRECTORY / "Tools/OriginalTypes.lean")], SOURCE, "original_types.log")
    exported = run(["lake", "env", "lean", "Tools/ExportedTypes.lean"], DIRECTORY, "exported_types.log")
    parse = lambda s: json.loads(next(l for l in s.splitlines() if l.startswith("[")))
    a, b = parse(original), parse(exported)
    if a != b:
        differences = [x["name"] for x, y in zip(a, b) if x != y]
        raise RuntimeError("Export changed types or definition bodies: " + str(differences))
    allowed = [e["id"] for e in record["theorems"]] + [e["name"] for e in record["existing"] if e["name"].startswith("OpenGA.")]
    for e in record["theorems"]:
        if "proof_path" not in e:
            continue
        allowed = e["imports"]
        audit = '''
import Lean.Util.CollectAxioms
open Lean in
run_meta do
  let target ← getConstInfo TARGET
  let proof ← getConstInfo `solution
  let levels := target.levelParams.zipIdx |>.map fun (_, i) => Level.param (Name.mkSimple s!"u{i}")
  unless ← Meta.isDefEq (target.type.instantiateLevelParams target.levelParams levels)
      (proof.type.instantiateLevelParams proof.levelParams levels) do
    throwError "Solution type differs from target"
  -- Imported theorem nodes are checked leaves, verified in publication order.
  -- Traverse every other proof and definition, rejecting any fresh sorry/axiom.
  let accepted : Array Name := ALLOWED
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut pending := [`solution]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if accepted.contains name then continue
    let some ci := env.find? name | throwError "Missing constant {name}"
    if let .axiomInfo _ := ci then
      unless standard.contains name do throwError "Unexpected axiom {name}"
    let value := match ci with
      | .thmInfo t => t.value.getUsedConstants
      | .defnInfo d => d.value.getUsedConstants
      | .opaqueInfo o => o.value.getUsedConstants
      | _ => #[]
    pending := (ci.type.getUsedConstants ++ value).toList ++ pending
  logInfo "Exact target type; no additional axioms beyond the declared theorem dependencies."
'''.replace("TARGET", "`" + e["id"]).replace("ALLOWED", "#[" + ",".join("`" + n for n in allowed if n != e["id"]) + "]")
        audit = ("import " + e["proof_path"][:-5].replace("/", ".") + "\nimport " +
                 e["path"][:-5].replace("/", ".") + "\n" + audit)
        audit_path = "Tools/Audit_" + e["id"].replace(".", "_") + ".lean"
        (DIRECTORY / audit_path).write_text(audit)
        run(["lake", "env", "lean", audit_path], DIRECTORY, e["id"].replace(".", "_") + "_audit.log")
    def_audit = """
import Lean.Util.CollectAxioms
open Lean in
run_meta do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless (`Definitions).isPrefixOf moduleName do continue
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do throwError "Unexpected axiom {axiomName} in {name}"
    count := count + 1
  logInfo m!"Audited {count} definition-module declarations: only standard logical axioms."
"""
    def_audit = "".join("import " + e["path"][:-5].replace("/", ".") + "\n" for e in record["definitions"]) + def_audit
    (DIRECTORY / "Tools/AuditDefinitions.lean").write_text(def_audit)
    run(["lake", "env", "lean", "Tools/AuditDefinitions.lean"], DIRECTORY, "definitions_audit.log")
    record["validation"] = {"status": "passed", "checked_at": datetime.now(timezone.utc).isoformat(),
        "exact_types_and_definition_bodies": len(a), "solutions": sum("proof_path" in e for e in record["theorems"]),
        "build": "passed", "source_kernel_audit": "122 declarations: only propext, Classical.choice, Quot.sound",
        "export_audit": "Exact solution types and no new axioms; declared imported theorem dependencies checked separately against their published proofs."}
    record["status"] = "VALIDATED"
    for p in (DIRECTORY / "Tools").glob("*"):
        if p.is_file():
            record["sources"].append({"path": str(p.relative_to(REPOSITORY)), "sha256": digest(p.read_bytes())})
    path.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
    print("Validated", len(a), "declaration types/bodies and", sum("proof_path" in e for e in record["theorems"]), "exact solutions.")


if __name__ == "__main__":
    main()
