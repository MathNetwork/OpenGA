#!/usr/bin/env python3
"""Export the area-coordinate interface using Lean declaration/reference spans."""
import argparse
import hashlib
import json
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parents[1]
REPOSITORY = DIRECTORY.parents[2]
ENVIRONMENT = '0df444a360eaa60ab8c11dca51a86af692955474'
PREFIX = 'OpenGA.RicciFlow.'
NAMES = ['SurfaceParameter', 'surfaceTangent', 'surfaceMetricMatrix', 'surfaceDensity',
         'patchArea', 'surfaceMetricMatrix_comp', 'surfaceDensity_comp', 'patchArea_comp']
TARGETS = ['surfaceDensity_comp', 'patchArea_comp']
IMPORTS = '''import Definitions.Def_DifferentialGeometry_SmoothRiemannianMetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
'''


def digest(data):
    return hashlib.sha256(data).hexdigest()


def edited(source, edits):
    right = len(source)
    for start, end, text in sorted(set(edits), reverse=True):
        if not 0 <= start <= end <= right:
            raise RuntimeError('Overlapping Lean source edits')
        source = source[:start] + text + source[end:]
        right = start
    return source


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-revision', required=True)
    args = parser.parse_args()
    record_path = DIRECTORY / 'publication.json'
    if record_path.exists():
        old = json.loads(record_path.read_text())
        if any(e.get('publication') or e.get('submission') for e in old['definitions'] + old['theorems']):
            raise RuntimeError('Refusing to overwrite publication receipts')
    paths = {'area': REPOSITORY / 'OpenGALib/Interoperability/RicciFlow/SurfaceArea.lean',
             'coordinates': REPOSITORY / 'OpenGALib/Interoperability/RicciFlow/SurfaceAreaCoordinates.lean'}
    sources = {k: p.read_bytes() for k, p in paths.items()}
    facts = {k: [json.loads(l) for l in (DIRECTORY/'Metadata'/f'{k}_facts.jsonl').read_text().splitlines()
                 if l.startswith('{')] for k in paths}
    graph = {r['name']: r for r in map(json.loads, (DIRECTORY/'Metadata/declaration_graph.jsonl').read_text().splitlines())}
    pending = [PREFIX + n for n in NAMES]
    pending += [n for n, r in graph.items() if r['isInstance']]
    closure = set()
    while pending:
        name = pending.pop()
        if name in closure:
            continue
        closure.add(name)
        pending.extend(graph[name]['typeDeps'] + graph[name]['valueDeps'])
        if graph[name]['kind'] == 'inductive':
            pending.extend(n for n, r in graph.items() if r['kind'] == 'ctor' and name in r['typeDeps'])
    expected = {PREFIX + n for n in NAMES} | {'DifferentialGeometry.SmoothRiemannianMetric'}
    survivors = {n for n in closure if graph[n]['startLine'] != 0}
    if survivors != expected:
        raise RuntimeError('Unexpected dependency closure: ' + str(survivors ^ expected))
    (DIRECTORY/'Metadata/selected_declaration_graph.json').write_text(json.dumps([graph[n] for n in sorted(closure)], indent=2)+'\n')

    def declaration(name, rename=None, stub=False):
        key = 'area' if name in NAMES[:5] else 'coordinates'
        row = graph[PREFIX+name]
        fact, = [f for f in facts[key] if f['kind'] == 'decl' and
                 f['declStart']['line'] <= row['startLine'] <= f['declEnd']['line']]
        if fact['nameText'] != name:
            raise RuntimeError('Declaration graph/oracle mismatch')
        start, end = fact['declStart']['offset'], fact['declEnd']['offset']
        if stub:
            end = fact['valStart']['offset']
        edits = []
        if rename:
            binding, = [f for f in facts[key] if f['kind'] == 'ref' and f['const'] == PREFIX+name
                        and start <= f['start']['offset'] < f['end']['offset'] <= fact['valStart']['offset']]
            edits.append((binding['start']['offset']-start,binding['end']['offset']-start,rename.encode()))
        if stub and fact.get('docstring'):
            doc = fact['docstring']
            edits.append((doc['start']['offset']-start,doc['end']['offset']-start,b''))
        return edited(sources[key][start:end],edits).decode().strip() + (' := by sorry' if stub else '')

    def context():
        kinds = {'Lean.Parser.Command.open','Lean.Parser.Command.variable','Lean.Parser.Command.section'}
        return '\n\n'.join(sources['coordinates'][f['start']['offset']:f['end']['offset']].decode()
                            for f in facts['coordinates'] if f['kind']=='command' and f['syntaxKind'] in kinds)

    first = min(f['start']['offset'] for f in facts['area'] if f['kind']=='command')
    definitions = IMPORTS+'\n'+sources['area'][first:].decode()
    base = 'import Definitions.Def_OpenGA_SurfaceArea\nimport Mathlib.MeasureTheory.Function.Jacobian\n\n'+context()+'\n\nopen OpenGA.RicciFlow'
    helper = 'namespace OpenGA.RicciFlow\n\n'+declaration('surfaceMetricMatrix_comp')+'\n\nend OpenGA.RicciFlow\n\n'

    def save(path, text):
        (DIRECTORY/path).parent.mkdir(parents=True,exist_ok=True)
        (DIRECTORY/path).write_text(text)
        return {'path':path, 'sha256':digest(text.encode())}

    def source(name):
        row=graph[PREFIX+name]
        path=str(paths['area' if name in NAMES[:5] else 'coordinates'].relative_to(REPOSITORY))
        return f'https://github.com/MathNetwork/OpenGA/blob/{args.source_revision}/{path}#L{row["startLine"]}-L{row["endLine"]}'

    shared={'env':ENVIRONMENT,'tags':['surface-area','riemannian-geometry','colding-minicozzi','poincare-foundations']}
    definition={'id':'OpenGA_SurfaceArea','definitions':[],**save('Definitions/Def_OpenGA_SurfaceArea.lean',definitions),
        'payload':dict(shared,definition_name='OpenGA_SurfaceArea',definition_title='Area density of a parametrized surface',definition=definitions,
        natural_language_statement=r'''Let $(M,g)$ be a smooth Riemannian manifold and let $f:\mathbb R^2\to M$. For the standard parameter vectors $e_1,e_2$, define

$$G_f(u)_{ij}=g_{f(u)}(df_u(e_i),df_u(e_j)),\qquad J_gf(u)=\sqrt{\det G_f(u)}.$$

For a parameter domain $\Omega$, its area with multiplicity is $\int_\Omega J_gf(u)\,du$ when the density is integrable. The definitions use the actual manifold derivative, with Lean's total derivative convention outside differentiability points, and the Bochner integral. They reuse the existing Mathlib/DifferentialGeometry smooth metric type. Coordinate compatibility and Ricci-flow variation are separate theorems.''',
        source=source('SurfaceParameter')+'; '+source('surfaceTangent')+'; '+source('surfaceMetricMatrix')+'; '+source('surfaceDensity')+'; '+source('patchArea'))}
    metadata={
      'surfaceDensity_comp':('Surface area density under a change of parameters',r'''Let $(M,g)$ be a smooth Riemannian manifold, $f:\mathbb R^2\to M$, and $\varphi:\mathbb R^2\to\mathbb R^2$. Suppose $\varphi$ has derivative $A$ at $u$ and $f$ is differentiable at $\varphi(u)$. Then

$$J_g(f\circ\varphi)(u)=|\det A|\,J_gf(\varphi(u)).$$

The determinant is computed in the standard orthonormal parameter basis. Neither $A$ nor $df$ must be injective; orientation reversal and degenerate derivatives are allowed. This is the pointwise coordinate compatibility of parametrized surface area.''',
      'Apply the manifold chain rule to the actual derivative of the surface map. Expanding in the standard parameter basis gives the congruence G(f composed with phi)=A transpose G(f) A. Take determinants and use sqrt(a squared times b)=abs(a) sqrt(b). The Gram-matrix congruence is included as a proved helper; no immersion or orientation assumption is introduced.'),
      'patchArea_comp':('Surface patch area is invariant under injective reparametrization',r'''Let $(M,g)$ be a smooth Riemannian manifold and $\Omega\subseteq\mathbb R^2$ be measurable. Suppose $\varphi:\mathbb R^2\to\mathbb R^2$ is differentiable at every point of $\Omega$ and injective on $\Omega$, and $f:\mathbb R^2\to M$ is differentiable at every point of $\varphi(\Omega)$. Then

$$\int_\Omega J_g(f\circ\varphi)(u)\,du=\int_{\varphi(\Omega)}J_gf(v)\,dv.$$

These are Bochner integrals; in particular, the identity identifies the usual finite areas whenever the density is integrable. The surface map $f$ need not be injective, so multiplicity is retained. This establishes compatibility of local area integrals under changes of surface coordinates; it does not yet construct an integral on a closed surface.''',
      'Use the proved pointwise density transformation. Mathlib\'s change-of-variables theorem for an injective differentiable map on a measurable set identifies the target-domain integral with the absolute-Jacobian-weighted source integral. Replace the integrands by the pointwise density formula. No global frame on the surface or compactness assumption is used.')}
    theorems=[]
    for n in TARGETS:
        preamble=base
        if n=='patchArea_comp':
            preamble='import Theorems.Thm_OpenGA_RicciFlow_surfaceDensity_comp\n'+preamble
        formal=declaration(n,PREFIX+n,stub=True)
        proof=preamble+'\n\n'+(helper if n=='surfaceDensity_comp' else '')+declaration(n,'solution')+'\n'
        entry={'id':n,'definitions':['OpenGA_SurfaceArea'],'imports':[] if n==TARGETS[0] else [TARGETS[0]],
          **save('Theorems/Thm_'+(PREFIX+n).replace('.','_')+'.lean',preamble+'\n\n'+formal+'\n'),
          'payload':dict(shared,theorem_name=PREFIX+n,theorem_title=metadata[n][0],natural_language_statement=metadata[n][1],preamble=preamble,formal_statement=formal,source=source(n)),
          'explanation':metadata[n][2]}
        receipt=save('Solutions/Sol_'+(PREFIX+n).replace('.','_')+'.lean',proof)
        entry.update(proof_path=receipt['path'],proof_sha256=receipt['sha256']);theorems.append(entry)
        # Independently compile the same proofs under their original names. The
        # only changes are the oracle-resolved binding and a generated import.
        verified_preamble=base if n==TARGETS[0] else 'import Verified.surfaceDensity_comp\n'+base
        save('Verified/'+n+'.lean',verified_preamble+'\n\n'+(helper if n==TARGETS[0] else '')+declaration(n,PREFIX+n)+'\n')
    source_records=[{'path':str(p.relative_to(REPOSITORY)),'sha256':digest(p.read_bytes())} for p in paths.values()]
    source_records += [{'path':str(p.relative_to(REPOSITORY)),'sha256':digest(p.read_bytes())} for p in (DIRECTORY/'Metadata').glob('*_facts.jsonl')]
    metric=DIRECTORY/'Definitions/Def_DifferentialGeometry_SmoothRiemannianMetric.lean'
    source_records.append({'path':str(metric.relative_to(REPOSITORY)),'sha256':digest(metric.read_bytes())})
    record={'schema_version':1,'batch':'surface_area_coordinates','mission_id':'29133a9f-c412-4f19-968e-3deae9a335b5',
        'milestone_id':'33045187-e820-4325-a253-c8ba2c778897','mathlib_rev':ENVIRONMENT,'toolchain':'leanprover/lean4:v4.33.1',
        'source_revision':args.source_revision,'definitions':[definition],'theorems':theorems,'sources':source_records,
        'source_reviewed':True,'status':'STAGED','validation':{'status':'required'},
        'prerequisite':{'theorem_id':'9f78021b-c594-4538-b61f-06a8831433af','path':str(metric.relative_to(DIRECTORY)),'sha256':digest(metric.read_bytes())},
        'scope':'Coordinate compatibility of local surface area. The full Ricci-flow scalar and area-variation batch is still local; closed-surface gluing and the finite-extinction milestone remain open.',
        'transformations':['Preserve all area definitions and their source context. Replace only project imports with the already published metric definition.',
          'Select proof and helper declarations by Lean declaration spans; rename theorem bindings by resolved reference spans.',
          'Keep the Gram congruence as an inline proved helper. Import the density theorem as the genuine dependency of the integral theorem.']}
    record_path.write_text(json.dumps(record,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
    print('Staged one definition bundle and two surface-area theorems.')

if __name__=='__main__':
    main()
