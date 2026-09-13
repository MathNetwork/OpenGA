import json,hashlib,shutil
from pathlib import Path
D=Path(__file__).resolve().parents[1]; R=D.parents[1]; L=R.parent/'OpenGALib'
if (D/'publication.json').exists(): raise RuntimeError('Do not overwrite a publication ledger')
def digest(b): return hashlib.sha256(b).hexdigest()
def write(path,s):
 p=D/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s);return str(path)
for dirname in ['Definitions','Theorems','Solutions','Metadata','Tools']: (D/dirname).mkdir(exist_ok=True)
for old in ['BishopGromov','ComparisonGeometry']:
 for p in (R/'Contributions'/old/'Definitions').glob('*.lean'): shutil.copyfile(p,D/'Definitions'/p.name)
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain','.gitignore']:
 shutil.copyfile(R/'Contributions/ComparisonGeometry'/name,D/name)
external=json.loads((D/'Metadata/external_items.json').read_text())
for e in external.values():
 write('Theorems/Thm_'+e['theorem_name'].replace('.','_')+'.lean',e['preamble']+'\n\n'+e['formal_statement']+'\n')
source=(L/'ComparisonGeometry/MeasuredSurgery.lean').read_text()
common=source[source.index('set_option'):source.index('namespace OpenGA')]
start=source.index('/-- **Math.** A finite');split=source.index('structure MeasuredRadialSurgeryData');end=source.index('/-- **Math.** The reference ball supplies')
ref='import Definitions.Def_OpenGA_GeodesicBall\nimport Mathlib.MeasureTheory.Measure.Restrict\nimport Mathlib.Analysis.InnerProductSpace.PiL2\n'+common.replace('open DifferentialGeometry.Geometry.Riemannian.VolumeComparison\n','')+'namespace OpenGA\n\n'+source[start:split]+'end OpenGA\n'
data='import Definitions.Def_OpenGA_MeasuredReferenceBall\nimport Definitions.Def_OpenGA_SurgeryComparisonProcess\n'+common+'namespace OpenGA\n\n'+source[split:end]+'end OpenGA\n'
rev='0df444a360eaa60ab8c11dca51a86af692955474';tags=['poincare-conjecture','bishop-gromov','geometric-analysis']
record={'mission_id':'29133a9f-c412-4f19-968e-3deae9a335b5','root_theorem_id':'7ea2da12-4d1b-4bbc-8257-df87d92f5a8e','mathlib_rev':rev,'toolchain':'leanprover/lean4:v4.33.1','status':'PREPARED','source_reviewed':True,'definitions':[],'theorems':[],'sources':[]}
source_url='https://github.com/MathNetwork/OpenGA/blob/feat/prove2me-differential-geometry/OpenGALib/ComparisonGeometry/MeasuredSurgery.lean'
def definition(id,title,code,desc,deps):
 path='Definitions/Def_'+id+'.lean';write(path,code)
 record['definitions'].append({'id':id,'path':path,'sha256':digest(code.encode()),'dependencies':deps,'payload':{'definition_name':id,'definition_title':title,'definition':code,'natural_language_statement':desc,'source':source_url,'tags':tags,'env':rev}})
def theorem(id,title,pre,stmt,proof,desc,deps,explanation='',expected='ACCEPTED'):
 name=id;path='Theorems/Thm_'+id.replace('.','_')+'.lean'; code=pre+'\n\n'+stmt+'\n';write(path,code)
 entry={'id':id,'path':path,'sha256':digest(code.encode()),'dependencies':deps,'payload':{'theorem_name':id,'theorem_title':title,'preamble':pre,'formal_statement':stmt,'natural_language_statement':desc,'source':source_url,'tags':tags,'env':rev}}
 if proof:
  pp='Solutions/Sol_'+id.replace('.','_')+'.lean';write(pp,proof);entry.update(proof_path=pp,proof_sha256=digest(proof.encode()),explanation=explanation,expected_verdict=expected)
 else: entry['open_problem']=True
 record['theorems'].append(entry);return entry
refid='OpenGA_MeasuredReferenceBall';dataid='OpenGA_MeasuredSurgeryComparisonData';anchor='OpenGA.MeasuredReferenceBall.anchor_pos';constructor='OpenGA.nonempty_surgeryComparisonProcess_of_measuredData';child='PoincareFormalization.measured_surgery_data_of_not_homeomorph_sphere'
definition(refid,'A finite measured reference ball',ref,r'A reference ball $B_g(p,r)$ in a smooth Riemannian three-manifold, with $r>0$, a measure $\mu$ positive on nonempty open sets, $\mu(B_g(p,r))<\infty$, and a normalization $v>0$. Define the real anchor by $$a=\mu(B_g(p,r))/v.$$ The measure is abstract; a geometric application must identify it with the appropriate Riemannian volume. This datum contains no surgery flow and does not assert a uniform estimate over event times.',[])
definition(dataid,'Measured data for a surgery comparison process',data,r'Radial densities, removed-volume budgets, and scalar and width profiles on event-free intervals, with the same inequalities as the existing surgery comparison process. The reference constant is the normalized measure of a finite positive-radius reference ball. For every event $t$, the normalized reference radial integral is assumed to be at least this same constant. Uniformity, density comparison, containment, and the total removed-volume budget remain explicit hypotheses. Event finiteness and positivity of the reference constant are not assumed; they follow when this datum is converted to the original process.',[refid])
pre='import Definitions.Def_'+refid+'\n'+common.replace('open DifferentialGeometry.Geometry.Riemannian.VolumeComparison\n','')+'open OpenGA\n'
stmt=f'theorem {anchor} (B : MeasuredReferenceBall) : 0 < B.anchor := by sorry'
body=source[source.index('theorem MeasuredReferenceBall.anchor_pos'):source.index('/-- **Math.** Construct the existing budget')].replace('theorem MeasuredReferenceBall.anchor_pos','theorem solution')
imports='import Theorems.Thm_Riemannian_RiemannianMetric_isOpen_geodesicBall\nimport Theorems.Thm_Riemannian_RiemannianMetric_measure_geodesicBall_pos\n'
theorem(anchor,'The measured reference anchor is positive',pre,stmt,imports+pre+'\n'+body,r'For a measured reference ball with normalization $v>0$, its anchor satisfies $$a=\mu(B_g(p,r))/v>0.$$ Openness and positive radius give strictly positive measure. The finite-measure hypothesis permits passage from extended nonnegative values to a positive real number.',[refid], 'Use geodesic-ball openness and the proved positive-measure theorem. Finiteness makes the real conversion positive; division by the positive normalization preserves positivity.')
pre2='import Definitions.Def_'+dataid+'\n'+common+'open OpenGA\n'
stmt2=f'theorem {constructor} {{W T : ℝ}} (D : MeasuredSurgeryComparisonData W T) : Nonempty (SurgeryComparisonProcess W T) := by sorry'
impl=source[source.index('noncomputable def MeasuredRadialSurgeryData.toBudget'):source.index('theorem nonempty_surgeryComparisonProcess_of_measuredData')]
proof2='import Theorems.Thm_OpenGA_MeasuredReferenceBall_anchor_pos\n'+pre2+'\nnamespace OpenGA\n'+impl+'\nend OpenGA\n\ntheorem solution {W T : ℝ} (D : MeasuredSurgeryComparisonData W T) : Nonempty (SurgeryComparisonProcess W T) := ⟨D.toProcess⟩\n'
theorem(constructor,'Construct a surgery process from measured comparison data',pre2,stmt2,proof2,'Measured radial volume-control data and scalar/width profiles determine a surgery comparison process with the same initial-width bound and final time. The only missing budget field, positivity of its reference anchor, is derived from the measured reference ball. The uniform radial lower bound, density comparison, removed-volume containment and budget are retained as hypotheses. This proves an adapter between analytic interfaces, not the existence of a Ricci flow.',[dataid,anchor],'Construct the radial budget by deriving its anchor positivity from the measured reference ball. Copy the remaining budget fields and event-free scalar/width profile inequalities unchanged into the existing process.')
parent=external['parent']; ps=parent['formal_statement']; childstmt=ps.replace(parent['theorem_name'],child).replace('OpenGA.SurgeryComparisonProcess','OpenGA.MeasuredSurgeryComparisonData')
childpre='import Definitions.Def_'+dataid+'\n'+parent['preamble']
theorem(child,'Construct measured surgery data from a hypothetical counterexample',childpre,childstmt,None,r'For a compact simply connected Hausdorff topological three-manifold $M$ hypothetically not homeomorphic to $S^3$, construct one $W\ge0$ such that for every $T>0$ there are measured surgery comparison data on $[0,T]$. This is an Open geometric construction. It must supply the reference ball and measure, the uniform radial lower bound at every event, density comparison, removed-region containment, a total volume budget, and scalar/sweepout profiles. The intended application must identify the abstract measure with geometric volume. Smoothing, Ricci flow with surgery, and the Colding–Minicozzi estimates remain to be developed.',[dataid])
parentproof='import Theorems.Thm_'+child.replace('.','_')+'\nimport Theorems.Thm_'+constructor.replace('.','_')+'\n'+parent['preamble']+'\n\n'+ps.replace('theorem '+parent['theorem_name'],'theorem solution').replace('by sorry','''by
  obtain ⟨W, hW, hdata⟩ := PoincareFormalization.measured_surgery_data_of_not_homeomorph_sphere M hnot
  refine ⟨W, hW, ?_⟩
  intro T hT
  obtain ⟨D⟩ := hdata T hT
  exact OpenGA.nonempty_surgeryComparisonProcess_of_measuredData D''')+'\n'
e=theorem(parent['theorem_name'],parent['theorem_title'],parent['preamble'],ps,parentproof,parent['natural_language_statement'],[constructor,child],'Reduce the unchanged process-existence statement to the Open measured-data construction. For each horizon apply the proved measured-data adapter, whose budget anchor positivity uses the reference-ball openness and measure-positivity theorems. All geometric and uniform-comparison obligations stay in the new Open child; the parent and Poincare goal remain Open.',expected='SKETCH_ACCEPTED');e['publication']={'status':'PUBLISHED','theorem_id':parent['theorem_id']}
for path in [L/'ComparisonGeometry/MeasuredSurgery.lean',L/'ComparisonGeometry/BallMeasure.lean',R/'Contributions/Drafts/SurgeryGeometry.lean']:
 record['sources'].append({'path':str(path.relative_to(R.parent)),'sha256':digest(path.read_bytes())})
record['external_ids']={k:v['theorem_id'] for k,v in external.items()}
write('publication.json',json.dumps(record,indent=2,ensure_ascii=False)+'\n')
