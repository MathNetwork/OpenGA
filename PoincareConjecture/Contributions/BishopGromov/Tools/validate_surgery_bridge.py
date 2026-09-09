#!/usr/bin/env python3
"""Validate exact interfaces, solution types and the complete analytic dependency chain."""
from datetime import datetime, timezone
import hashlib
import json
from validate_exports import DIRECTORY, REPOSITORY, run


def main():
    path=DIRECTORY/'bridge_publication.json'
    record=json.loads(path.read_text())
    for source in record['sources']:
        if hashlib.sha256((REPOSITORY/source['path']).read_bytes()).hexdigest()!=source['sha256']:
            raise RuntimeError('Reviewed source changed: '+source['path'])
    run(['lake','build'],DIRECTORY,'bridge_platform_build.log')
    print('Platform build passed',flush=True)
    original=run(['lake','env','lean',str(DIRECTORY/'Tools/BridgeOriginalTypes.lean')],REPOSITORY,'bridge_original_types.json')
    exported=run(['lake','env','lean','Tools/BridgeExportedTypes.lean'],DIRECTORY,'bridge_exported_types.json')
    if json.loads(original)!=json.loads(exported):
        raise RuntimeError('An interface type or definition body differs from the source')
    print('Exact interface types and definition bodies passed',flush=True)
    checks={}
    for i,e in enumerate(record['theorems']):
        if 'proof_path' not in e:continue
        checks[e['id']]=run(['lake','env','lean','Tools/BridgeTypeCheck'+str(i)+'.lean'],DIRECTORY,'bridge_typecheck_'+str(i)+'.log').strip()
    print('All solution types passed',flush=True)
    audit=run(['lake','env','lean','Tools/BridgeFullProofAudit.lean'],DIRECTORY,'bridge_full_proof_audit.log')
    record['validation']={'status':'passed','checked_at':datetime.now(timezone.utc).isoformat(),
        'build':'Exact Mathlib-only staged sources compiled',
        'interface_equivalence':str(len(json.loads(original)))+' declaration types and available definition bodies match the source, including constructors and projections',
        'solution_types':checks,'complete_proof_audit':audit.strip(),
        'allowed_axioms':['propext','Classical.choice','Quot.sound'],
        'dependency_audit':'All proved imports replaced by exact complete original proofs for the analytic axiom check. The main-graph reduction has one explicitly Open geometric child.',
        'scope':'Conditional radial-volume nonaccumulation and finite comparison trace. No geometric completion.'}
    if record['status']=='EXPORTED_NOT_VALIDATED':record['status']='VALIDATED_READY_TO_PUBLISH'
    path.write_text(json.dumps(record,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
    print('Validated the complete analytic bridge and exact parent reduction.',flush=True)

if __name__=='__main__':main()
