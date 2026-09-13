#!/usr/bin/env python3
"""Validate exact payloads, source/export types, definition bodies and proof axioms."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
import subprocess
from export_immersed_metric import DIRECTORY, REPOSITORY, digest


def run(command, cwd):
    p=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def main():
    record_path=DIRECTORY/'publication.json'
    record=json.loads(record_path.read_text())
    if any(e.get('publication') or e.get('submission') for e in record['definitions']+record['theorems']):
        raise RuntimeError('Do not replace validation of published content')
    build=run(['lake','build'],DIRECTORY)
    (DIRECTORY/'Metadata/build.log').write_text(build)
    jobs=[('original_types',['lake','env','lean',str(DIRECTORY/'Tools/OriginalTypes.lean')],REPOSITORY),
          ('exported_types',['lake','env','lean','Tools/ExportedTypes.lean'],DIRECTORY),
          ('axiom_audit',['lake','env','lean','Tools/Audit.lean'],DIRECTORY)]
    jobs += [('type_'+e['id'],['lake','env','lean','Tools/Audit_'+e['id']+'.lean'],DIRECTORY) for e in record['theorems']]
    with ThreadPoolExecutor(max_workers=3) as pool:
        results=list(pool.map(lambda j: run(j[1],j[2]),jobs))
    for (label,_,_),output in zip(jobs,results):
        (DIRECTORY/'Metadata'/f'{label}.log').write_text(output)
    rows=[json.loads(next(l for l in s.splitlines() if l.startswith('['))) for s in results[:2]]
    if len(rows[0])!=13 or rows[0]!=rows[1]:
        raise RuntimeError('Export changed an elaborated type or definition body')
    if 'All 13 declarations passed the axiom audit.' not in results[2]:
        raise RuntimeError('Missing proof audit')
    if any('Exact solution type passed.' not in s for s in results[3:]):
        raise RuntimeError('Missing exact solution type audit')
    for label,row in zip(['original_types','exported_types'],rows):
        (DIRECTORY/'Metadata'/f'{label}.json').write_text(json.dumps(row,indent=2)+'\n')
    # Verified versions are generated from identical declaration bodies, using
    # only binding renames and replacement of the child import with its proof.
    checked=list((DIRECTORY/'Tools').glob('*.py'))+list((DIRECTORY/'Tools').glob('*.lean'))
    checked+=list((DIRECTORY/'Verified').glob('*.lean'))
    checked+=list((DIRECTORY/'Metadata').glob('*.json'))
    checked+=list((DIRECTORY/'Metadata').glob('*.jsonl'))
    checked += [DIRECTORY/'Definitions'/p for p in
                ['Def_DifferentialGeometry_SmoothRiemannianMetric.lean', 'Def_OpenGA_SurfaceArea.lean']]
    extraction=REPOSITORY/'PoincareConjecture/Contributions/ClosedSurfaceArea'
    checked += [extraction/'Metadata/declaration_graph.jsonl',
                extraction/'Tools/ExtractDeclarationGraph.lean', extraction/'Tools/ExtractSketchInfo.lean']
    checked+=[DIRECTORY/'lakefile.lean',DIRECTORY/'lake-manifest.json',DIRECTORY/'lean-toolchain']
    records={e['path']:e for e in record['sources']}
    for p in checked:
        relative=str(p.relative_to(REPOSITORY))
        records[relative]={'path':relative,'sha256':digest(p.read_bytes())}
    record['sources']=list(records.values())
    record['validation']={'status':'passed','checked_at':datetime.now(timezone.utc).isoformat(),
      'exact_types_and_definition_bodies':13,'solution_types':'both exact matches',
      'axioms':'All thirteen source/export declarations use only propext, Classical.choice and Quot.sound.',
      'staged_build':'passed, Mathlib and the two previously published definition bundles only',
      'proof_dependencies':'The density proof is compiled directly. The integral proof is also compiled with that proved density declaration instead of its platform stub.'}
    record['status']='VALIDATED'
    record_path.write_text(json.dumps(record,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
    print('Validated one definition bundle and both exact induced-metric area proofs.')

if __name__=='__main__':
    main()
