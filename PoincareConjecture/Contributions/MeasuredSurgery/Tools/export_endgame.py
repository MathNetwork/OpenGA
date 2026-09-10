from pathlib import Path
import json,hashlib,shutil
D=Path(__file__).resolve().parents[1];R=D.parents[1];p=D/'publication.json';r=json.loads(p.read_text());ext=json.loads((D/'Metadata/endgame_parent.json').read_text())
child='PoincareFormalization.ExtinctionEndgame.exists_measured_surgery_topology'
if any(e['id']==child for e in r['theorems']):raise RuntimeError('Already staged')
for f in (R/'Contributions/ExtinctionEndgame/Upload/Definitions').glob('*.lean'):
 dest=D/'Definitions'/f.name
 if dest.exists():
  if dest.read_bytes()!=f.read_bytes():raise RuntimeError('Conflicting definition: '+f.name)
 else:shutil.copyfile(f,dest)
trace='OpenGA_nonempty_widthComparisonTrace_of_surgeryComparisonProcess'
shutil.copyfile(R/'Contributions/BishopGromov/Theorems'/('Thm_'+trace+'.lean'),D/'Theorems'/('Thm_'+trace+'.lean'))
pre='import Definitions.Def_OpenGA_MeasuredSurgeryComparisonData\nimport Definitions.Def_OpenGA_ExtinctionWidthControl\n\nset_option autoImplicit false\nopen OpenGA\nuniverse u\n'
stmt='''theorem PoincareFormalization.ExtinctionEndgame.exists_measured_surgery_topology
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧
      ∀ T : ℝ, 0 < T → E.components T ≠ [] →
        Nonempty (MeasuredSurgeryComparisonData W T) := by sorry'''
def add(name,title,pre,stmt,desc,deps,proof=None):
 code=pre+'\n\n'+stmt+'\n';path='Theorems/Thm_'+name.replace('.','_')+'.lean';(D/path).write_text(code)
 e={'id':name,'path':path,'sha256':hashlib.sha256(code.encode()).hexdigest(),'dependencies':deps,'payload':{'theorem_name':name,'theorem_title':title,'preamble':pre,'formal_statement':stmt,'natural_language_statement':desc,'source':'OpenGA measured-reference-ball refinement of the extinction endgame: https://github.com/MathNetwork/OpenGA/blob/feat/prove2me-differential-geometry/PoincareConjecture/Contributions/MeasuredSurgery/Endgame.lean','tags':['poincare-conjecture','finite-extinction','bishop-gromov'],'env':r['mathlib_rev']}}
 if proof:
  pp='Solutions/Sol_'+name.replace('.','_')+'.lean';(D/pp).write_text(proof);e.update(proof_path=pp,proof_sha256=hashlib.sha256(proof.encode()).hexdigest(),expected_verdict='SKETCH_ACCEPTED',explanation='Keep the target statement unchanged. The Open measured-data construction supplies a topology evolution and one initial width bound for every nonempty horizon. At each such horizon, the proved measured-data adapter gives a surgery comparison process, and the proved finite-trace constructor gives the required WidthComparisonTrace. Positivity of its budget anchor is derived from the finite reference-ball measure. The uniform radial bound, actual surgery and width estimates remain in the Open geometric child; the parent and Poincare goal remain Open.')
 else:e['open_problem']=True
 r['theorems'].append(e);return e
add(child,'Construct measured surgery topology for the extinction endgame',pre,stmt,r'For every closed simply connected topological three-manifold $M$, construct an extracted surgery topology $E$ and one $W\ge0$ such that, for every $T>0$ with a nonempty final slice, measured surgery comparison data exist with initial-width bound $W$ and horizon $T$. The reference measure, uniform radial estimates, removed-volume budget and sweepout profiles must be supplied by the geometric construction. This Open statement refines the active width-controlled topology input; it does not claim a construction of a Ricci flow or a proof of finite extinction.', ['OpenGA_MeasuredSurgeryComparisonData'])
proof='import Theorems.Thm_'+child.replace('.','_')+'\nimport Theorems.Thm_OpenGA_nonempty_surgeryComparisonProcess_of_measuredData\nimport Theorems.Thm_'+trace+'\n'+pre+'\n'+'''theorem solution (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M] :
    ∃ (E : SurgeryTopologyEvolution M) (W : ℝ), 0 ≤ W ∧ E.HasWidthControl W := by
  obtain ⟨E, W, hW, hdata⟩ := PoincareFormalization.ExtinctionEndgame.exists_measured_surgery_topology M
  refine ⟨E, W, hW, ?_⟩
  intro T hT hnonempty
  obtain ⟨D⟩ := hdata T hT hnonempty
  obtain ⟨P⟩ := nonempty_surgeryComparisonProcess_of_measuredData D
  exact nonempty_widthComparisonTrace_of_surgeryComparisonProcess P
'''
e=add(ext['theorem_name'],ext['theorem_title'],ext['preamble'],ext['formal_statement'],ext['natural_language_statement'],[child,'OpenGA.nonempty_surgeryComparisonProcess_of_measuredData'],proof)
e['publication']={'status':'PUBLISHED','theorem_id':ext['theorem_id']}
r['root_required']=[x['id'] for x in r['definitions']]+['OpenGA.MeasuredReferenceBall.anchor_pos','OpenGA.nonempty_surgeryComparisonProcess_of_measuredData',child,ext['theorem_name']]
f=D/'Endgame.lean';r['sources'].append({'path':str(f.relative_to(R.parent)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
r['validation']['status']='pending_endgame_audit'
p.write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
audit='import '+e['path'][:-5].replace('/','.')+'\nimport '+e['proof_path'][:-5].replace('/','.')+'\nopen Lean in\nrun_meta do\n  let target ← getConstInfo `'+e['id']+'\n  let proof ← getConstInfo `solution\n  unless ← Meta.isDefEq target.type proof.type do\n    throwError "Target mismatch"\n  logInfo "Active endgame target matched exactly"\n'
(D/'Tools/EndgameType.lean').write_text(audit)
