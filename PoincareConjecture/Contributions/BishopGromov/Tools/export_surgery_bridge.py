#!/usr/bin/env python3
"""Export the volume-loss bridge using Lean declaration and reference spans."""
import json
from pathlib import Path
from export_ratio_integral import DIRECTORY, REPOSITORY, PREFIX, REVISION, ENVIRONMENT, NOTICE, edited, digest

RECORD = DIRECTORY / 'bridge_publication.json'
MODULES = ['SurgeryVolume', 'FiniteEventPartition', 'SurgeryComparison', 'ComparisonTrace', 'SurgeryGeometry']
BASE = ('import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic\n'
        'import Mathlib.MeasureTheory.Integral.Lebesgue.Add\n'
        'import Mathlib.Data.Finset.Sort\n'
        'import Mathlib.Data.Set.Finite.Basic\n'
        'import Mathlib.Algebra.Order.Archimedean.Basic\n'
        'import Mathlib.Algebra.Order.BigOperators.Group.Finset\n'
        'import Mathlib.Tactic.Linarith\n\n'
        'set_option autoImplicit false\nopen MeasureTheory Set Filter\nopen scoped ENNReal BigOperators Topology')
PROOF_NOTICE = ('/-\nIncludes unchanged model-positivity helper proofs from qinz1yang/differential-geometry,\n'
                'Copyright 2026 The DifferentialGeometry contributors, Apache-2.0.\n'
                'Source commit: ' + REVISION + '.\n'
                'The volume-loss and finite-trace arguments are OpenGA results.\n-/\n\n')
BUDGET = 'OpenGA_RadialSurgeryVolumeBudget'
PROCESS = 'OpenGA_SurgeryComparisonProcess'
GEOMETRY = 'PoincareFormalization.surgery_comparison_process_of_not_homeomorph_sphere'
PARENT = 'PoincareFormalization.persistent_comparison_data_of_not_homeomorph_sphere'
NAMES = ['OpenGA.RadialSurgeryVolumeBudget.removedVolume_lower',
         'OpenGA.RadialSurgeryVolumeBudget.events_finite',
         'OpenGA.exists_event_free_partition',
         'OpenGA.nonempty_widthComparisonTrace_of_surgeryComparisonProcess']
KL = 'https://arxiv.org/pdf/math/0605667v5#page=13'
CM = 'https://arxiv.org/pdf/0707.0108v1#page=7'


def main():
    if RECORD.exists() and any((e.get('publication') and not e['publication'].get('existing_target')) or e.get('submission') for es in ('definitions','theorems')
                              for e in json.loads(RECORD.read_text())[es]):
        raise RuntimeError('Refusing to overwrite publication receipts')
    source_paths = {m: REPOSITORY / ('PoincareConjecture/Contributions/Drafts/SurgeryGeometry.lean'
                    if m == 'SurgeryGeometry' else 'OpenGALib/Analysis/' + m + '.lean') for m in MODULES}
    fact_paths = {m: DIRECTORY / ('Metadata/bridge_' + m + '_facts.jsonl') for m in MODULES}
    upstream = REPOSITORY / '.lake/packages/DifferentialGeometry/DifferentialGeometry/Geometry/Comparison/Volume'
    for key, source, facts in [('model','HyperbolicModel.lean','model_model_facts.jsonl'),
                              ('volume','BishopBall.lean','model_volume_facts.jsonl'),
                              ('ratio','RatioIntegral.lean','model_ratio_facts.jsonl')]:
        source_paths[key] = upstream / source
        fact_paths[key] = DIRECTORY / ('Metadata/' + facts)
    source_paths['normalized'] = REPOSITORY / 'OpenGALib/Analysis/IntegralComparison.lean'
    source_paths['model_local'] = REPOSITORY / 'OpenGALib/Analysis/ModelVolume.lean'
    fact_paths['normalized'] = DIRECTORY / 'Metadata/model_normalized_facts.jsonl'
    fact_paths['model_local'] = DIRECTORY / 'Metadata/model_local_facts.jsonl'
    facts = {k: [json.loads(l) for l in p.read_text().splitlines()] for k,p in fact_paths.items()}
    sources = {k:p.read_bytes() for k,p in source_paths.items()}

    def decl(key, name, rename=None, stub=False):
        fact, = [f for f in facts[key] if f['kind']=='decl' and f['nameText']==name]
        start,end = fact['declStart']['offset'],fact['declEnd']['offset']
        changes=[]
        if rename:
            ns = 'PoincareFormalization' if key=='SurgeryGeometry' else (PREFIX if key in ('model','volume','ratio') else 'OpenGA')
            binding, = [f for f in facts[key] if f['kind']=='ref' and f['const']==ns+'.'+name and
                        start <= f['start']['offset'] < f['end']['offset'] <= fact['valStart']['offset']]
            changes.append((binding['start']['offset']-start,binding['end']['offset']-start,rename.encode()))
        if stub:
            end=fact['valStart']['offset']
            if fact['docstring']:
                d=fact['docstring']; changes.append((d['start']['offset']-start,d['end']['offset']-start,b''))
        return edited(sources[key][start:end],changes).decode().strip()+(' := by sorry' if stub else '')

    def save(path, code):
        (DIRECTORY/path).write_text(code)
        return {'path':path,'sha256':digest(code.encode())}

    def imports(defs=(), theorems=()):
        return ''.join('import Definitions.Def_'+d+'\n' for d in defs)+''.join(
            'import Theorems.Thm_'+t.replace('.','_')+'\n' for t in theorems)+BASE+ ('\nopen '+PREFIX if defs else '')

    # Existing public definitions are reused byte for byte, recursively with their imports.
    copied=[]
    def copy_definition(name):
        p=REPOSITORY/'PoincareConjecture/Definitions'/('Def_'+name+'.lean')
        if p in copied:return
        copied.append(p)
        code=p.read_text();save('Definitions/'+p.name,code)
        for line in code.splitlines():
            if line.startswith('import Definitions.Def_'):
                copy_definition(line.removeprefix('import Definitions.Def_'))
    copy_definition('OpenGA_WidthComparisonTrace')
    volume_defs=['DifferentialGeometry_ModelRadialVolume','DifferentialGeometry_RadialCrossComparison']
    common={'env':ENVIRONMENT,'tags':['bishop-gromov','ricci-flow','poincare-conjecture','geometric-analysis']}
    definitions=[]
    specs=[(BUDGET, 'Radial comparison and a surgery volume-loss budget',
        imports(volume_defs)+'\n\nnamespace OpenGA\n\n'+decl('SurgeryVolume','RadialSurgeryVolumeBudget')+'\n\nend OpenGA\n',
        ['model_radial_volume','radial_cross_comparison'],
        r'An arbitrary set of real event times carries nonnegative radial densities with cross-comparison against the three-dimensional model of curvature $-q^2$, where $q\ge0$. Fix $0<r\le R$ and $\kappa>0$. At every event the normalized radial volume at $R$ is at least $\kappa$, and the radial integral at $r$ is bounded by the nonnegative removed volume. Every finite subset of events has total removed volume bounded by a single finite real budget. No finiteness or discreteness of the event set is assumed.'+'\n\n'+
        'This is an analytic interface for the nonaccumulation argument. A geometric application must construct the densities, identify their integrals with contained regions, justify uniform scales and the anchor, and bound all removed volume including allowance for smooth volume growth. It is not a definition of Ricci flow or surgery.'),
       (PROCESS, 'Scalar and width profiles with surgery volume control',
        imports([BUDGET,'OpenGA_WidthComparisonData'])+'\n\nnamespace OpenGA\n\n'+
        decl('SurgeryComparison','EventFreeInterval')+'\n\n'+decl('SurgeryComparison','SurgeryComparisonProcess')+'\n\nend OpenGA\n',
        [BUDGET,'width_comparison_data'],
        r'For an initial width bound $W_0$ and positive horizon $T$, this bundle combines a radial volume-loss budget with event times in $(0,T)$ and scalar/width profiles on every event-free interval. Profiles are continuous on each closed interval, widths are nonnegative, initial scalar is at least $-6$, and initial width is at most $W_0$. The scalar right-slope inequality is $R^\prime\ge\frac23R^2$; each time carries an area-energy width-comparison witness. Adjacent intervals allow upward scalar jumps and downward width jumps.'+'\n\n'+
        'The event set need not be finite by definition. Its finiteness is a theorem derived from volume control. These are conditional analytic data, whose construction from a manifold remains an Open geometric problem.')]
    for name,title,code,deps,description in specs:
        definitions.append(dict(id=name,definitions=deps,**save('Definitions/Def_'+name+'.lean',code),
            payload=dict(common,definition_name=name,definition_title=title,definition=code,
                         natural_language_statement=description,source='OpenGA derived analytic interface. Kleiner-Lott, Section 3.5, p. 13, '+KL+'; radial scale comparison in Sublemma 79.23, p. 157. Colding-Minicozzi width estimates: '+CM)))

    helpers=['hasDerivAt_hypSn','hypSn_continuous','hypSn_pos','hasDerivAt_hypDen','hypDen_continuous','hypDensity_pos']
    helper_code='namespace '+PREFIX+'\n\n'+'\n\n'.join(decl('model',n) for n in helpers)+'\n\n'+decl('volume','hypRadVol_pos')+'\n\nend '+PREFIX+'\n'
    theorem_specs=[
        (NAMES[0],'SurgeryVolume','RadialSurgeryVolumeBudget.removedVolume_lower',[BUDGET],
         ['OpenGA.antitoneOn_lintegral_div_hypRadVol'],helper_code,
         'A uniform positive volume loss from model comparison',
         r'For every event of a radial surgery volume budget, its removed volume is at least $\kappa V_{q,2}(r)>0$, where $\kappa$ is the positive reference-scale anchor and $r$ the positive removal radius. The bound is uniform over all events.',
         'Apply the proved normalized radial integral comparison from the removal radius to the reference radius. Combine the anchor lower bound with containment in the removed material, then clear the positive finite model-volume denominator. This is a conditional analytic consequence; geometric containment and the anchor are inputs.'),
        (NAMES[1],'SurgeryVolume','RadialSurgeryVolumeBudget.events_finite',[BUDGET],[NAMES[0]],helper_code,
         'Finitely many events from a radial volume-loss budget',
         'Every radial surgery volume budget has a finite set of event times. No discreteness hypothesis is needed.',
         'The imported lower-loss theorem gives a uniform positive loss epsilon. An infinite event set would contain a finite subset with more than totalBudget/epsilon elements. Summing their losses contradicts the budget. This formalizes the analytic nonaccumulation mechanism in Kleiner-Lott Section 3.5; constructing a geometric budget is still required.'),
        (NAMES[2],'FiniteEventPartition','exists_event_free_partition',[],[],'',
         'An event-free partition for finitely many event times',
         r'If a finite set of real event times is contained in $(0,T)$ with $T>0$, there is a finite strictly increasing partition $0=t_0<\cdots<t_n=T$, $n>0$, all of whose open subintervals contain no event.',
         'Adjoin the endpoints 0 and T to the finite event set and enumerate the result in increasing order. An event strictly between adjacent partition points would have an index strictly between two consecutive natural numbers.'),
        (NAMES[3],'SurgeryComparison','nonempty_widthComparisonTrace_of_surgeryComparisonProcess',
         [PROCESS,'OpenGA_WidthComparisonTrace'],[NAMES[1],NAMES[2]],'',
         'A finite width comparison trace from volume-controlled profiles',
         'For any initial bound and final horizon, a surgery comparison process yields a finite width comparison trace with the same bounds. The trace satisfies the existing scalar and width interface used by the Poincare width-extinction reduction.',
         'Use volume control to prove event finiteness, then construct an event-free partition. Restrict the supplied profiles to its intervals. Initial bounds, continuity, differential inequalities, area-energy comparison witnesses and jumps transfer directly to the trace. No new geometric theorem is claimed.')]
    theorems=[]
    for name,key,local,defs,deps,helper,title,description,explanation in theorem_specs:
        preamble=imports(defs) + ('\nopen OpenGA' if defs else '')
        statement=decl(key,local,name,stub=True)
        proof=(PROOF_NOTICE if helper else '')+imports(defs,deps)+'\n\n'+helper+ ('\nopen OpenGA in\n' if defs else '\n')+decl(key,local,'solution')+'\n'
        pp='Solutions/Sol_'+name.replace('.','_')+'.lean'; ps=save(pp,proof)
        theorems.append(dict(id=name,definitions=defs,imports=deps,
            **save('Theorems/Thm_'+name.replace('.','_')+'.lean',preamble+'\n\n'+statement+'\n'),
            proof_path=pp,proof_sha256=ps['sha256'],explanation=explanation,
            payload=dict(common,theorem_name=name,theorem_title=title,preamble=preamble,formal_statement=statement,
                         natural_language_statement=description,source='OpenGA, OpenGALib/Analysis/'+key+'.lean. Analytic nonaccumulation mechanism: Kleiner-Lott Section 3.5, p. 13, '+KL+'; comparison of scales in Sublemma 79.23, p. 157.')))
    geometry_imports=('import Mathlib.Geometry.Manifold.ChartedSpace\n'
                      'import Mathlib.Analysis.InnerProductSpace.PiL2\n'
                      'import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected\n')
    preamble=geometry_imports+imports([PROCESS])
    statement=decl('SurgeryGeometry',GEOMETRY.removeprefix('PoincareFormalization.'),GEOMETRY,stub=True)
    theorems.append(dict(id=GEOMETRY,definitions=[PROCESS],imports=[],open_problem=True,
        **save('Theorems/Thm_'+GEOMETRY.replace('.','_')+'.lean',preamble+'\n\n'+statement+'\n'),
        payload=dict(common,theorem_name=GEOMETRY,theorem_title='Volume-controlled width profiles from a hypothetical Poincare counterexample',
            preamble=preamble,formal_statement=statement,
            natural_language_statement=r'Let $M$ be a compact, simply connected, Hausdorff topological three-manifold without boundary, hypothetically not homeomorphic to the unit three-sphere. Construct $W_0\ge0$ such that for every $T>0$ there is a surgery comparison process with initial width bound $W_0$ and final time $T$.'+'\n\n'+
            'Open geometric construction. It must supply all fields of the imported analytic process: smoothability and normalization, suitable surgery flow and uniform radial comparison data, containment of controlled regions in removed material, a finite volume-loss budget allowing smooth volume growth, and scalar/sweepout comparison profiles with the prescribed inequalities and jumps. It does not assume event finiteness; that follows from the separately proved volume argument. This refines the existing comparison-data target. The full Ricci-flow and Bishop-Gromov geometric developments remain open.',
            source='Kleiner-Lott, Section 3.5, p. 13 and Sublemma 79.23, p. 157, '+KL+'; Colding-Minicozzi finite-extinction width argument, '+CM+'. This is a composite OpenGA construction target, not a claim that a single cited lemma supplies all fields.')))
    scout=json.loads(Path('/tmp/bishop-bridge-scout.json').read_text());parent=scout['parent']
    pp='Solutions/Sol_'+PARENT.replace('.','_')+'_surgery_bridge.lean'
    proof=imports(['OpenGA_WidthComparisonTrace'],[GEOMETRY,NAMES[3]])+'\n\nopen PoincareFormalization in\n'+decl('SurgeryGeometry','comparison_trace_of_surgery_geometry','solution')+'\n'
    ps=save(pp,proof)
    payload={k:parent[k] for k in ['theorem_name','theorem_title','preamble','formal_statement','natural_language_statement','source']}
    payload['env']=ENVIRONMENT
    theorems.append(dict(id=PARENT,definitions=[],imports=[GEOMETRY,NAMES[3]],expected_verdict='SKETCH_ACCEPTED',
        publication={'status':'PUBLISHED','theorem_id':parent['theorem_id'],'existing_target':True},
        **save('Theorems/Thm_'+PARENT.replace('.','_')+'.lean',payload['preamble']+'\n\n'+payload['formal_statement']+'\n'),
        proof_path=pp,proof_sha256=ps['sha256'],payload=payload,
        explanation='This reduction retains one Open geometric child: constructing volume-controlled scalar and width profiles from a hypothetical counterexample. Given its data for each horizon, the proved trace constructor derives event finiteness from model radial comparison and the volume-loss budget, sorts the event times and restricts the profiles to a finite trace. Thus the Bishop-Gromov analytic prerequisites enter the existing width route through a proved nonaccumulation step. The geometric child, the parent and the Poincare goal remain Open; this is not a proof of Ricci-flow surgery or of the full geometric Bishop-Gromov theorem.'))

    # Every exported solution is checked against the exact target, independently.
    for i,e in enumerate(theorems):
        if 'proof_path' not in e:continue
        save('Tools/BridgeTypeCheck'+str(i)+'.lean','import Lean\nimport '+e['path'][:-5].replace('/','.')+'\nimport '+e['proof_path'][:-5].replace('/','.')+'\n'+
             'open Lean in\nrun_meta do\n  let a ← Lean.getConstInfo `'+e['id']+'\n  let b ← Lean.getConstInfo `solution\n  unless ← Lean.Meta.isDefEq a.type b.type do\n    throwError "Solution type mismatch"\n  Lean.logInfo "Exact target type checked"\n')
    # Full proof audit replaces all proved stubs with the original complete proofs.
    # A section isolates source implicit variables used by the original integral lemma.
    audit=PROOF_NOTICE+'import Lean\n'+imports([BUDGET,PROCESS,'OpenGA_WidthComparisonTrace'])+'\n\n'+helper_code+'\nsection\nvariable {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞} {R : ℝ}\n'+decl('ratio','lintegral_cross_le',PREFIX+'.lintegral_cross_le')+'\nend\n\n'
    audit+=decl('normalized','antitoneOn_lintegral_Ioc_div','OpenGA.antitoneOn_lintegral_Ioc_div')+'\n\nnamespace OpenGA\n'+decl('model_local','lintegral_hypDensity')+'\n'+decl('model_local','antitoneOn_lintegral_div_hypRadVol')+'\nend OpenGA\n'
    for _,key,local,*_ in theorem_specs:
        audit+='\nnamespace OpenGA\n'+decl(key,local)+'\nend OpenGA\n'
    audit+='\nopen Lean in\nrun_meta do\n  for name in #['+', '.join('`'+n for n in NAMES)+'] do\n    let axioms ← Lean.collectAxioms name\n    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do\n      throwError "Unexpected axiom in {name}: {axioms}"\n    Lean.logInfo m!"{name}: {axioms}"\n'
    save('Tools/BridgeFullProofAudit.lean',audit)

    graph_path=DIRECTORY/'Metadata/declaration_graph.jsonl'
    graph={r['name']:r for r in map(json.loads,graph_path.read_text().splitlines())}
    roots=NAMES+['OpenGA.EventFreeInterval','OpenGA.SurgeryComparisonProcess','OpenGA.RadialSurgeryVolumeBudget','OpenGA.WidthComparisonTrace']
    roots += [r['name'] for r in graph.values() if r.get('isInstance') and r['module'] in ['OpenGALib.Analysis.'+m for m in MODULES]]
    closure=set();pending=roots[:]
    while pending:
        name=pending.pop()
        if name in closure:continue
        closure.add(name);r=graph[name];pending.extend(r['typeDeps']+r['valueDeps'])
    graph_out=DIRECTORY/'Metadata/bridge_declaration_closure.json'
    graph_out.write_text(json.dumps([graph[n] for n in sorted(closure)],indent=2)+'\n')
    # Include constructors and projections when comparing the interface types.
    type_names=sorted(set(NAMES+['OpenGA.EventFreeInterval']+[n for n in graph if any(n==s or n.startswith(s+'.') for s in
        ['OpenGA.RadialSurgeryVolumeBudget','OpenGA.SurgeryComparisonProcess','OpenGA.WidthComparisonTrace'])]))
    type_code='open Lean in\nrun_meta do\n  let env ← Lean.getEnv\n  let mut rows : Array Lean.Json := #[]\n  for name in ['+',\n    '.join('`'+n for n in type_names)+'] do\n    let some ci := env.find? name | throwError "Missing declaration {name}"\n    let levels := ci.levelParams.zipIdx |>.map fun (_, i) => Lean.Level.param (Lean.Name.mkSimple s!"universe_{i}")\n    let type := ci.type.instantiateLevelParams ci.levelParams levels\n    let printed ← Lean.withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do\n      Lean.Meta.ppExpr type\n    let mut fields := [("name", Lean.Json.str name.toString), ("type", Lean.Json.str printed.pretty)]\n    if let .defnInfo d := ci then\n      let value := d.value.instantiateLevelParams ci.levelParams levels\n      let shown ← Lean.withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true) do\n        Lean.Meta.ppExpr value\n      fields := fields ++ [("value", Lean.Json.str shown.pretty)]\n    rows := rows.push (Lean.Json.mkObj fields)\n  Lean.logInfo (Lean.Json.arr rows).compress\n'
    save('Tools/BridgeOriginalTypes.lean','import Lean\nimport OpenGALib.Analysis.SurgeryComparison\n'+type_code)
    save('Tools/BridgeExportedTypes.lean','import Lean\n'+''.join('import '+e['path'][:-5].replace('/','.')+'\n' for e in theorems[:4])+type_code)
    old=json.loads((DIRECTORY/'publication.json').read_text())
    tracked=list(source_paths.values())+list(fact_paths.values())+copied+[graph_out]
    record=dict(batch='surgery_bridge',mission_id=old['mission_id'],milestone_id=old['milestone_id'],
        root_theorem_id='7ea2da12-4d1b-4bbc-8257-df87d92f5a8e',mathlib_rev=ENVIRONMENT,toolchain=old['toolchain'],upstream_revision=REVISION,
        definitions=definitions,theorems=theorems,source_reviewed=True,status='EXPORTED_NOT_VALIDATED',validation={'status':'required'},
        source_review='Two analytic interfaces, four complete analytic proofs, and one explicitly Open geometric construction refine the existing width-comparison target. All edits use Lean spans. No finiteness is assumed for the event set. Actual surgery geometry, polar integration, scale and anchor estimates, volume growth budgets and sweepouts remain geometric obligations. Original DifferentialGeometry positivity helper proofs are reused with exact names and attribution.',
        export_classification={'nodes':NAMES,'inline_helpers':[PREFIX+'.'+n for n in helpers+['hypRadVol_pos']],
                               'note':'The 12-line lower-loss proof has a docstring and is promoted. Finite partition has 55 proof lines; the remaining targets are promoted. Original short model helpers are unchanged.'},
        declaration_graph_sha256=digest(graph_path.read_bytes()),
        sources=[{'path':str(p.relative_to(REPOSITORY)),'sha256':digest(p.read_bytes())} for p in tracked],scout=scout)
    RECORD.write_text(json.dumps(record,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
    print('Exported two definitions, four analytic proofs, one Open geometric child and the main-graph reduction.')

if __name__=='__main__':main()
