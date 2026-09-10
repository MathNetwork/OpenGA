"""Stage the uniform-area-evolution reduction without overwriting a ledger."""
import hashlib
import json
import shutil
from pathlib import Path

D = Path(__file__).resolve().parents[1]
R = D.parents[1]
L = R.parent / 'OpenGALib'
if (D / 'publication.json').exists():
    raise RuntimeError('Publication ledger already exists')
for part in ['Definitions', 'Theorems', 'Solutions', 'Metadata']:
    (D / part).mkdir(exist_ok=True)
for f in (R / 'Contributions/MeasuredSurgery/Definitions').glob('*.lean'):
    shutil.copyfile(f, D / 'Definitions' / f.name)
for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain', '.gitignore']:
    shutil.copyfile(R / 'Contributions/MeasuredSurgery' / name, D / name)

rev = '0df444a360eaa60ab8c11dca51a86af692955474'
source_url = 'https://github.com/MathNetwork/OpenGA/blob/feat/prove2me-differential-geometry/OpenGALib/Analysis/Width/AreaEvolution.lean'
record = dict(mission_id='29133a9f-c412-4f19-968e-3deae9a335b5',
    root_theorem_id='7ea2da12-4d1b-4bbc-8257-df87d92f5a8e', mathlib_rev=rev,
    toolchain='leanprover/lean4:v4.33.1', status='PREPARED', source_reviewed=True,
    definitions=[], theorems=[], sources=[], validation={'status': 'pending'},
    external_ids={'area_energy': 'd81e3640-8579-4396-babb-69edac82be33'})

def digest(code):
    return hashlib.sha256(code.encode()).hexdigest()

def write(path, code):
    (D / path).write_text(code)

def definition(name, title, code, description, deps):
    path = 'Definitions/Def_' + name + '.lean'
    write(path, code)
    record['definitions'].append(dict(id=name, path=path, sha256=digest(code), dependencies=deps,
        payload=dict(definition_name=name, definition_title=title, definition=code,
            natural_language_statement=description, source=source_url,
            tags=['finite-extinction', 'width', 'geometric-analysis'], env=rev)))

def theorem(name, title, pre, statement, description, deps, proof=None):
    path = 'Theorems/Thm_' + name.replace('.', '_') + '.lean'
    code = pre + '\n\n' + statement + '\n'
    write(path, code)
    e = dict(id=name, path=path, sha256=digest(code), dependencies=deps,
        payload=dict(theorem_name=name, theorem_title=title, preamble=pre,
            formal_statement=statement, natural_language_statement=description,
            source=source_url, tags=['finite-extinction', 'width'], env=rev))
    if proof:
        pp = 'Solutions/Sol_' + name.replace('.', '_') + '.lean'
        write(pp, proof)
        e.update(proof_path=pp, proof_sha256=digest(proof), expected_verdict='ACCEPTED',
            explanation=description)
    else:
        e['open_problem'] = True
    record['theorems'].append(e)
    return e

common = 'set_option autoImplicit false\nopen Set Filter\nopen scoped Topology\n'
a = (L / 'Analysis/Width/AreaEvolution.lean').read_text()
b = (L / 'Analysis/Width/SurgeryAreaEvolution.lean').read_text()
aid = 'OpenGA_WidthAreaEvolutionData'
bid = 'OpenGA_SurgeryAreaEvolutionData'
an = 'OpenGA.nonempty_widthComparisonData_of_areaEvolution'
bn = 'OpenGA.nonempty_measuredSurgeryComparisonData_of_areaEvolution'
child = 'PoincareFormalization.ExtinctionEndgame.exists_area_evolution_surgery_topology'
parent = 'PoincareFormalization.ExtinctionEndgame.exists_measured_surgery_topology'

apre = 'import Definitions.Def_OpenGA_WidthComparisonData\nimport Mathlib.Analysis.Calculus.Deriv.MeanValue\n' + common
adef = apre + '\nnamespace OpenGA\n\n' + a[a.index('/-- Analytic input'):a.index('/-- Integrating')] + '\nend OpenGA\n'
definition(aid, 'Uniform area evolution for width comparison', adef,
    'Finite-energy comparison fields, a conformal limiting realizer, and time-dependent real area profiles. '
    'The energy caps converge to the initial width. For every positive error, one time interval and one '
    'sequence cutoff work for every slice: the evolved family bounds the width and each area derivative '
    'is at most $-4π-R A_*/2+ε+(A_j-A_{j,p})/δ$, where $A_j$ is the initial slice supremum. '
    'The area gap allows low-area slices to have nonnegative derivative. These are analytic data; their realization by geometric sweepouts '
    'and the uniform derivative estimate are separate open obligations.', [])
bpre = 'import Definitions.Def_' + aid + '\nimport Definitions.Def_OpenGA_MeasuredSurgeryComparisonData\n' + common
bdef = bpre + '\nnamespace OpenGA\n\n' + b[b.index('structure SurgeryAreaEvolutionData'):b.index('noncomputable def')] + '\nend OpenGA\n'
definition(bid, 'Surgery profiles with uniform area evolution', bdef,
    'Measured radial surgery data and scalar/width profiles, with uniform area-evolution data on each '
    'event-free interval. The width comparison inequality is not assumed: it is obtained by integrating '
    'the area derivative estimates. Radial comparison, the removed-volume budget, scalar estimates, '
    'and jump inequalities remain explicit hypotheses.', [aid])

shutil.copyfile(R / 'Theorems/Thm_OpenGA_integral_areaDensity_le_energyDensity.lean',
    D / 'Theorems/Thm_OpenGA_integral_areaDensity_le_energyDensity.lean')
pre = 'import Definitions.Def_' + aid + '\n' + common + 'open OpenGA\n'
statement = 'theorem ' + an + ' {width : ℝ → ℝ} {time scalar : ℝ}\n    (D : WidthAreaEvolutionData width time scalar) :\n    Nonempty (WidthComparisonData width time scalar) := by sorry'
aimpl = a[a.index('noncomputable def WidthAreaEvolutionData.toComparison'):a.index('theorem nonempty_')]
proof = 'import Theorems.Thm_OpenGA_integral_areaDensity_le_energyDensity\n' + pre + '\nnamespace OpenGA\n' + aimpl + '\nend OpenGA\n' + statement.replace(an, 'solution').replace('by sorry', '⟨D.toComparison⟩') + '\n'
theorem(an, 'Uniform area derivatives imply width comparison', pre, statement,
    'Integrate the derivative upper bound on a common short interval using the mean-value inequality. The extra term given by the initial area gap divided by the interval length consumes at most that gap. '
    'The area-energy inequality bounds the initial slice supremum by the finite energy cap. '
    'Taking the supremum of the evolved slices gives exactly the short-time area comparison required '
    'by WidthComparisonData. The common interval and cutoff are essential hypotheses; pointwise '
    'variation of a single surface is insufficient.', [aid], proof)

pre = 'import Definitions.Def_' + bid + '\n' + common + 'open OpenGA\n'
statement = 'theorem ' + bn + ' {W T : ℝ}\n    (D : SurgeryAreaEvolutionData W T) : Nonempty (MeasuredSurgeryComparisonData W T) := by sorry'
bimpl = b[b.index('noncomputable def SurgeryAreaEvolutionData.toMeasured'):b.index('theorem nonempty_')]
proof = 'import Theorems.Thm_' + an.replace('.', '_') + '\n' + pre + '\nnamespace OpenGA\n' + bimpl + '\nend OpenGA\n' + statement.replace(bn, 'solution').replace('by sorry', '⟨D.toMeasured⟩') + '\n'
theorem(bn, 'Construct measured surgery comparison from area evolution', pre, statement,
    'At every time in each event-free interval, integrate the uniform area derivative estimates to '
    'construct the required width comparison datum. Preserve all volume, scalar, continuity, '
    'initial-value and jump conditions. This is a proved analytic adapter, not a construction '
    'of a Ricci flow with surgery.', [bid, an], proof)

nodes = json.loads((R / 'sync.json').read_text())['nodes']
old = next(x for x in nodes.values() if x.get('theorem_name') == parent)
pre = 'import Definitions.Def_' + bid + '\nimport Definitions.Def_OpenGA_ExtinctionWidthControl\n' + common + 'open OpenGA\nuniverse u\n'
statement = old['formal_statement'].replace(parent, child).replace('MeasuredSurgeryComparisonData', 'SurgeryAreaEvolutionData')
theorem(child, 'Construct surgery topology with uniform area evolution', pre, statement,
    'For every closed simply connected topological three-manifold, construct a surgery topology '
    'evolution and one nonnegative initial width bound. For each positive horizon with nonempty '
    'final slice, supply surgery area-evolution data. The remaining geometric tasks include the '
    'admissible sweepout families, their common short-time area estimates, and the actual surgery '
    'and radial volume hypotheses. This open construction refines the measured-data input to '
    'the active extinction endgame.', [bid])
ps = old['formal_statement']
proof = 'import Theorems.Thm_' + child.replace('.', '_') + '\nimport Theorems.Thm_' + bn.replace('.', '_') + '\n' + old['preamble'] + '\n' + ps.replace(parent, 'solution').replace('by sorry', '''by
  obtain ⟨E, W, hW, hdata⟩ := PoincareFormalization.ExtinctionEndgame.exists_area_evolution_surgery_topology M
  refine ⟨E, W, hW, ?_⟩
  intro T hT hnonempty
  obtain ⟨D⟩ := hdata T hT hnonempty
  exact OpenGA.nonempty_measuredSurgeryComparisonData_of_areaEvolution D''') + '\n'
e = theorem(parent, old['theorem_title'], old['preamble'], ps,
    'Keep the existing measured-surgery existence statement unchanged. The open area-evolution '
    'construction supplies data at each nonempty horizon; the proved integration adapter produces '
    'the required measured comparison data. The parent and the Poincare theorem remain open.',
    [child, bn], proof)
e['expected_verdict'] = 'SKETCH_ACCEPTED'
e['publication'] = dict(status='PUBLISHED', theorem_id=old['theorem_id'])
record['root_required'] = [e['id'] for e in record['definitions'] + record['theorems']]

# Complete audit replaces the one external proved leaf by its full implementation.
energy = (L / 'Analysis/AreaEnergy.lean').read_text()
energy = energy[:energy.index('/-- **Math.** The two-dimensional Jacobian')] + energy[energy.index('lemma areaDensity_nonneg'):]
audit = 'import Definitions.Def_' + bid + '\n' + energy + '\n' + common + '\nnamespace OpenGA\n' + a[a.index('noncomputable def'):a.rindex('end OpenGA')] + '\n' + b[b.index('noncomputable def'):b.rindex('end OpenGA')] + '\nend OpenGA\n'
audit += '''open Lean in
run_meta do
  for n in [``OpenGA.nonempty_widthComparisonData_of_areaEvolution,
      ``OpenGA.nonempty_measuredSurgeryComparisonData_of_areaEvolution] do
    let axioms ← collectAxioms n
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"
    logInfo m!"{n}: standard axioms only"
'''
write('Tools/ResolvedAudit.lean', audit)
for index, e in enumerate(record['theorems']):
    if 'proof_path' not in e:
        continue
    audit = 'import ' + e['path'][:-5].replace('/', '.') + '\nimport ' + e['proof_path'][:-5].replace('/', '.') + '\nopen Lean in\nrun_meta do\n  let target ← getConstInfo `' + e['id'] + '\n  let proof ← getConstInfo `solution\n  unless ← Meta.isDefEq target.type proof.type do\n    throwError "Target mismatch"\n  logInfo "Exact target type matched"\n'
    write('Tools/Exact' + str(index) + '.lean', audit)
for path in ['Analysis/Width/AreaEvolution.lean', 'Analysis/Width/SurgeryAreaEvolution.lean']:
    f = L / path
    record['sources'].append(dict(path=str(f.relative_to(R.parent)), sha256=digest(f.read_text())))
write('publication.json', json.dumps(record, ensure_ascii=False, indent=2) + '\n')
