#!/usr/bin/env python3
"""Check source receipts, build curated modules, and reject nonstandard proof axioms.

Run from the repository: python3 PoincareConjecture/check_curation.py
"""

import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from sync import ROOT, digest, review_status, safe_path


def main():
    snapshot = json.loads((ROOT / "sync.json").read_text())
    curation = json.loads((ROOT / "curation.json").read_text())
    stale = review_status(snapshot, curation)["needs_review"]
    if stale:
        raise RuntimeError("Source reviews need updating: " + ", ".join(stale))
    modules, declarations = set(), set()
    for submission_id, review in curation["reviews"].items():
        source = safe_path(ROOT, snapshot["submissions"][submission_id]["local_path"])
        if digest(source.read_bytes()) != review["source_sha256"]:
            raise RuntimeError("Reviewed source was edited: " + str(source))
        for declaration in review["declarations"]:
            path, name = declaration["path"], declaration["name"]
            if not re.fullmatch(r"OpenGALib(?:/[A-Za-z][A-Za-z0-9_]*)+\.lean", path):
                raise ValueError("Curated modules must be inside OpenGALib: " + path)
            if not safe_path(ROOT.parent, path).is_file():
                raise RuntimeError("Missing curated module: " + path)
            if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*", name):
                raise ValueError("Unsupported declaration name: " + name)
            modules.add(path[:-5].replace("/", "."))
            declarations.add(name)
    if not declarations:
        raise RuntimeError("No curated declarations to check")

    subprocess.run(["lake", "build", *sorted(modules)], cwd=ROOT.parent, check=True)
    source = "import Lean\n" + "".join("import " + module + "\n" for module in sorted(modules))
    source += "\nrun_cmd do\n"
    source += "  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]\n"
    source += "  for name in #[" + ", ".join("`" + name for name in sorted(declarations)) + "] do\n"
    source += '''    unless (← Lean.getEnv).contains name do
      throwError "Missing curated declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    Lean.logInfo m!"{name}: {axioms}"
'''
    with tempfile.TemporaryDirectory(prefix="openga-curation-") as directory:
        check_file = Path(directory) / "CheckCuration.lean"
        check_file.write_text(source)
        subprocess.run(["lake", "env", "lean", str(check_file)], cwd=ROOT.parent, check=True)
    print("Verified {} curated declarations and {} source reviews.".format(
        len(declarations), len(curation["reviews"])))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.CalledProcessError) as error:
        print("Curation check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
