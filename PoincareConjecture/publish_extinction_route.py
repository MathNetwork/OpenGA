#!/usr/bin/env python3
"""Publish the reviewed extinction branch, saving receipts before every write."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request
from uuid import uuid4

from sync import BASE, Client, MISSION_ID, ROOT

RECORD = ROOT / 'Contributions/ExtinctionRoute/publication.json'
SCALAR_ID = '688450a0-1949-4aa1-aeec-4ff61ccf5ddd'

def now():
    return datetime.now(timezone.utc).isoformat()

def save(record):
    temporary = RECORD.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(record, indent=2, ensure_ascii=False) + '\n')
    temporary.replace(RECORD)

def source(entry):
    data = (ROOT.parent / entry['path']).read_bytes()
    if hashlib.sha256(data).hexdigest() != entry['sha256']:
        raise RuntimeError('Source changed after validation: ' + entry['path'])
    return data

def require_status(record, key, status):
    if record['receipts'].get(key, {}).get('status') != status:
        raise RuntimeError(key + ' must have verified status ' + status)

def publish(client, record, key, entry, kind):
    if key in record['receipts']:
        raise RuntimeError('Publication already attempted; poll the saved receipt: ' + key)
    payload = entry['payload']
    name = payload['definition_name' if kind == 'definition' else 'theorem_name']
    matches = client.pages('/theorems', 'theorems', theorem_name=name, env=record['mathlib_rev'])
    if any(t['theorem_name'] == name for t in matches):
        raise RuntimeError('Name already exists; inspect before proceeding: ' + name)
    record['receipts'][key] = {'kind':kind, 'status':'SUBMITTING', 'started_at':now()}
    save(record)
    result = client.request('/submit-definition' if kind == 'definition' else '/submit-problem', payload)
    receipt = record['receipts'][key]
    receipt['response'] = result
    save(record)
    job_id = result.get('job_id')
    if not job_id and len(result.get('jobs', [])) == 1:
        job_id = result['jobs'][0]['job_id']
    if not job_id:
        raise RuntimeError('Missing job ID; inspect the saved response')
    receipt.update(job_id=job_id, status='PENDING')
    save(record)
    print(key, 'queued', job_id, flush=True)

def submit_proof(client, record, key, entry, target):
    if key in record['receipts']:
        raise RuntimeError('Proof already attempted; poll the saved receipt: ' + key)
    code = source(entry)
    boundary = 'openga-' + uuid4().hex
    parts = []
    for name, value in {'theorem_id':target, 'proof_type':'prove', 'explanation':entry['explanation']}.items():
        parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="'+name+'"\r\n\r\n'+value+'\r\n').encode())
    parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()+code+b'\r\n')
    parts.append(('--'+boundary+'--\r\n').encode())
    record['receipts'][key] = {'kind':'proof', 'target':target, 'status':'SUBMITTING', 'started_at':now()}
    save(record)
    request = Request(BASE+'/verify', data=b''.join(parts), method='POST', headers={
        'Authorization':'Bearer '+client.token, 'Accept':'application/json',
        'Content-Type':'multipart/form-data; boundary='+boundary})
    with client.opener.open(request, timeout=60) as response:
        result = json.load(response)
    record['receipts'][key].update(response=result, submission_id=result.get('submission_id'), status=result.get('status'))
    save(record)
    if not result.get('submission_id'):
        raise RuntimeError('Missing submission ID; inspect the saved response')
    print(key, result['status'], result['submission_id'], flush=True)

def poll(client, record):
    for key, receipt in record['receipts'].items():
        if 'job_id' in receipt:
            result = client.request('/publish-jobs/'+receipt['job_id'])
            receipt.update(status=result['status'], result=result, checked_at=now())
            save(record)
            if result['status'] == 'PUBLISHED':
                theorem = client.request('/theorems/'+result['theorem_id'])
                entry = record['definition'] if key == 'definition' else record['problems'][key.removesuffix('_problem')]
                fields = ['definition'] if key == 'definition' else ['formal_statement','preamble','theorem_name']
                for field in fields:
                    if theorem[field].strip() != entry['payload'][field].strip():
                        raise RuntimeError('Published content mismatch: '+key+' '+field)
                if theorem['mathlib_rev'] != record['mathlib_rev']:
                    raise RuntimeError('Published environment mismatch')
                receipt.update(theorem_id=result['theorem_id'], theorem=theorem, verified_at=now())
        elif 'submission_id' in receipt:
            result = client.request('/verify?submission_id='+receipt['submission_id'])
            receipt.update(status=result['status'], result=result, checked_at=now())
            save(record)
            if result['status'] in ('ACCEPTED','SKETCH_ACCEPTED'):
                code = client.request('/submissions/'+receipt['submission_id']+'/solution')['content']
                entry = record['proofs']['width' if key == 'width_proof' else 'root']
                if hashlib.sha256(code.encode()).hexdigest() != entry['sha256']:
                    raise RuntimeError('Accepted proof source mismatch')
                receipt.update(verified_at=now(), accepted_source_sha256=entry['sha256'])
        save(record)
        print(key, receipt['status'], flush=True)
        if receipt['status'] in ('FAILED','ERROR','CE','WA','SORRY'):
            raise RuntimeError(receipt['result'].get('error_message') or key+' failed')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['check','publish_definition','publish_problems','prove_width','submit_reduction','poll','verify_graph'])
    args = parser.parse_args()
    record = json.loads(RECORD.read_text())
    if record['mission_id'] != MISSION_ID or record['validation']['status'] != 'passed':
        raise RuntimeError('Mission or validation mismatch')
    for entry in [record['definition'], *record['problems'].values(), *record['proofs'].values()]:
        source(entry)
    client = Client(json.loads((ROOT/'.credentials.json').read_text())['api_key'])
    root = client.request('/theorems/'+record['root_theorem_id'])
    reference = json.loads((ROOT/'sync.json').read_text())['nodes'][record['root_theorem_id']]
    if root['formal_statement'] != reference['formal_statement'] or root['mathlib_rev'] != record['mathlib_rev']:
        raise RuntimeError('Root statement or environment changed')
    if args.action == 'check':
        graph=client.request('/theorems/'+record['root_theorem_id']+'/graph')
        record['before']={'checked_at':now(),'root_status':root['status'],'graph':graph}
        save(record)
        print('Verified root statement and environment; graph has', len(graph['nodes']), 'nodes.')
    elif args.action == 'publish_definition':
        publish(client,record,'definition',record['definition'],'definition')
    elif args.action == 'publish_problems':
        require_status(record,'definition','PUBLISHED')
        for key, entry in record['problems'].items():
            if key+'_problem' not in record['receipts']:
                publish(client,record,key+'_problem',entry,'problem')
    elif args.action == 'prove_width':
        require_status(record,'width_problem','PUBLISHED')
        submit_proof(client,record,'width_proof',record['proofs']['width'],record['receipts']['width_problem']['theorem_id'])
    elif args.action == 'submit_reduction':
        require_status(record,'width_proof','ACCEPTED')
        require_status(record,'geometry_problem','PUBLISHED')
        scalar=client.request('/theorems/'+SCALAR_ID)
        if scalar['status']!='Proved': raise RuntimeError('Scalar theorem is not proved')
        submit_proof(client,record,'root_reduction',record['proofs']['root'],record['root_theorem_id'])
    elif args.action == 'poll':
        poll(client,record)
    else:
        require_status(record,'root_reduction','SKETCH_ACCEPTED')
        graph=client.request('/theorems/'+record['root_theorem_id']+'/graph')
        sketch='sketch-'+record['receipts']['root_reduction']['submission_id']
        edges={(e['source'],e['target']) for e in graph['edges']}
        expected=[SCALAR_ID,record['receipts']['width_problem']['theorem_id'],record['receipts']['geometry_problem']['theorem_id']]
        for child in expected:
            if (child,sketch) not in edges: raise RuntimeError('Missing proof dependency edge: '+child)
        if (sketch,record['root_theorem_id']) not in edges: raise RuntimeError('Missing edge to root')
        nodes={n.get('theorem_id'):n for n in graph['nodes'] if n.get('theorem_id')}
        if nodes[SCALAR_ID]['status']!='Proved' or nodes[expected[1]]['status']!='Proved' or nodes[expected[2]]['status']!='Open':
            raise RuntimeError('Unexpected graph theorem statuses')
        if root['status']!='Open': raise RuntimeError('Unexpected root status')
        record['graph_verification']={'verified_at':now(),'root_status':root['status'],'graph':graph,
            'checked_dependency_edges':[list(e) for e in sorted(edges) if e[1]==sketch or e[0]==sketch]}
        save(record)
        print('Verified live root graph: scalar Proved + width Proved + geometry Open -> accepted sketch -> Poincare Open.')

if __name__=='__main__':
    try:
        main()
    except HTTPError as error:
        print('Prove2Me HTTP', error.code, file=sys.stderr)
        raise SystemExit(1)
    except (URLError,OSError,RuntimeError,KeyError,ValueError) as error:
        print('Operation stopped:',str(error),file=sys.stderr)
        raise SystemExit(1)
