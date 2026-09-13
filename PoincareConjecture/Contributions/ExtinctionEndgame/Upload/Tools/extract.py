from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess

BASE = Path(__file__).resolve().parents[1]
SOURCE = BASE.parent
ROOT = SOURCE.parents[2]
MODULES = {
    "ConnectedSum": ROOT / "OpenGALib/Topology/ConnectedSum.lean",
    "SurgeryReconstruction": ROOT / "OpenGALib/Topology/SurgeryReconstruction.lean",
    "ExtinctionEndgame": ROOT / "OpenGALib/Topology/ExtinctionEndgame.lean",
    "ComparisonExtinction": ROOT / "OpenGALib/Analysis/ComparisonExtinction.lean",
    "WidthExtinction": ROOT / "OpenGALib/Analysis/WidthExtinction.lean",
    "SphereCovering": ROOT / "OpenGALib/Topology/SphereCovering.lean",
    "CoveringSpace": ROOT / "OpenGALib/Topology/CoveringSpace.lean",
    "OpenProblems": SOURCE / "OpenProblems.lean",
    "Reduction": SOURCE / "Reduction.lean",
}

def run(item):
    key, path = item
    result = subprocess.run(["lake", "env", "lean", "--run", str(BASE / "Tools/ExtractSketchInfo.lean"), str(path)],
        cwd=SOURCE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (BASE / "Metadata" / (key + "_facts.jsonl")).write_text(result.stdout)
    if result.returncode: raise RuntimeError(key + ": " + result.stdout[-3000:])
    print("Extracted", key, flush=True)

if __name__ == "__main__":
    with ThreadPoolExecutor(max_workers=3) as pool:
        list(pool.map(run, MODULES.items()))
    result = subprocess.run(["lake", "env", "lean", "Upload/Tools/ExtractDeclarationGraph.lean"],
        cwd=SOURCE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (BASE / "Metadata/declaration_graph.log").write_text(result.stdout)
    if result.returncode: raise RuntimeError(result.stdout[-3000:])
    print(result.stdout, flush=True)
