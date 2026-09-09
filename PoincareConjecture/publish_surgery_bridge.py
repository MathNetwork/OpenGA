"""Publish the validated volume-loss bridge and verify its path to the mission root."""
import json
from urllib.request import Request
from sync import BASE, ROOT, MISSION_ID, expand_dependency_graph, json_bytes, write_atomic


def reachable(edges, source, target):
    seen={source}
    while True:
        more=seen | {e['target'] for e in edges if e['source'] in seen}
        if more==seen:return target in seen
        seen=more


def external_entries(publisher, client, record):
    entries={}
    for filename in ('publication.json','model_publication.json'):
        previous=json.loads((publisher.DIRECTORY/filename).read_text())
        for e in previous['definitions']+previous['theorems']:
            item=publisher.verify_item(client,e)
            expected='Definition' if 'definition' in e['payload'] else 'Proved'
            if item['status']!=expected:raise RuntimeError('External dependency status changed')
            entries[e['id']]=e
            entries[item['theorem_name']]=e
    mirror=json.loads((ROOT/'sync.json').read_text())
    for alias,name in [('width_comparison_data','OpenGA_WidthComparisonData'),
                       ('OpenGA_WidthComparisonTrace','OpenGA_WidthComparisonTrace')]:
        node,=[v for v in mirror['nodes'].values() if v['theorem_name']==name]
        live=client.request('/theorems/'+node['theorem_id'])
        code=(ROOT/'Definitions'/('Def_'+name+'.lean')).read_text()
        if live['status']!='Definition' or live['mathlib_rev']!=record['mathlib_rev'] or live['definition'].strip()!=code.strip():
            raise RuntimeError('Existing width definition changed: '+name)
        entry={'id':alias,'publication':{'theorem_id':live['theorem_id']}}
        entries[alias]=entry;entries[name]=entry
    return entries


def annotate(p,client,record):
    plan_path=ROOT/'milestones.json';plan=json.loads(plan_path.read_text())
    local=next(m for m in plan['milestones'] if m.get('platform_milestone_id')==record['milestone_id'])
    live=next(m for m in client.pages('/missions/'+MISSION_ID+'/milestones','milestones') if m['id']==record['milestone_id'])
    update=record.get('milestone_annotation')
    if update is None:
        if live['milestone_description']!=local['payload']['milestone_description']:
            raise RuntimeError('Review concurrent milestone edits before annotation')
        before=live['milestone_description']
        after=before.replace('The geometric milestone remains open, and this analytic component is not yet a dependency of the Poincare goal theorem.',
                             'The geometric milestone remains open. The analytic component now enters the Poincare width route through the conditional volume-loss nonaccumulation argument linked below.')
        proofs=[e for e in record['theorems'] if 'proof_path' in e and not e.get('expected_verdict')]
        links='; '.join('['+e['payload']['theorem_title']+'](https://prove2.me/theorems/'+e['publication']['theorem_id']+')' for e in proofs)
        child=next(e for e in record['theorems'] if e.get('open_problem'))
        after+='\n\n**Volume-loss bridge to the mission graph.** '+links+'. These proved analytic results transfer a reference-scale volume lower bound to the removal scale, bound the number of events and construct the finite width comparison trace. [The geometric construction](https://prove2.me/theorems/'+child['publication']['theorem_id']+') remains Open: it must supply surgery flow, uniform radial estimates and containment, a removed-volume budget allowing smooth volume growth, and scalar/sweepout profiles. The full geometric Bishop-Gromov milestone remains Open.'
        update=record['milestone_annotation']={'before':before,'after':after,'canonical_theorem':live.get('theorem'),'status':'PREPARED'}
        p.save(record)
    if live['milestone_description']!=update['after']:
        if live['milestone_description']!=update['before'] or live.get('theorem')!=update['canonical_theorem']:
            raise RuntimeError('Concurrent milestone edit; no overwrite performed')
        req=Request(BASE+'/milestones/'+record['milestone_id'],method='PATCH',data=json_bytes({
            'milestone_description':update['after'],'reason':'Record the verified volume-loss dependency path to the Poincare goal while preserving the Open geometric milestone.'}),
            headers={'Authorization':'Bearer '+client.token,'Accept':'application/json','Content-Type':'application/json'})
        with client.opener.open(req,timeout=60) as response:update['response']=json.load(response)
        p.save(record)
        live=next(m for m in client.pages('/missions/'+MISSION_ID+'/milestones','milestones') if m['id']==record['milestone_id'])
    if live['milestone_description']!=update['after'] or live.get('theorem')!=update['canonical_theorem']:
        raise RuntimeError('Milestone readback differs')
    update.update(status='VERIFIED',verified_at=p.now())
    local['payload']['milestone_description']=update['after'];local['platform_verified_at']=p.now()
    local['local_progress']['surgery_bridge_publication_record']=str(p.RECORD.relative_to(ROOT.parent))
    write_atomic(plan_path,json_bytes(plan))
    receipt_path=ROOT/'milestones_published.json';receipt=json.loads(receipt_path.read_text())
    receipt['milestones'][local['id']]=live;receipt['verified_at']=p.now();write_atomic(receipt_path,json_bytes(receipt))
    p.save(record)


def run_bridge(p,client,record):
    entries=external_entries(p,client,record)
    ready={name:True for name in entries}
    for entry in record['definitions']:
        ready[entry['id']]=False;entries[entry['id']]=entry
        if all(ready.get(n,False) for n in entry.get('definitions',[])):
            ready[entry['id']]=p.publish(client,record,entry)
    for entry in record['theorems']:
        ready[entry['id']]=False;entries[entry['id']]=entry
        if not all(ready.get(n,False) for n in entry['definitions']):continue
        if not p.publish(client,record,entry):continue
        if entry.get('open_problem'):
            if p.verify_item(client,entry)['status']!='Open':raise RuntimeError('Open construction unexpectedly changed')
            ready[entry['id']]=True
        elif all(ready.get(n,False) for n in entry['imports']):
            ready[entry['id']]=p.prove(client,record,entry)
    if not all(ready[e['id']] for e in record['definitions']+record['theorems']):return
    root=client.request('/theorems/'+record['root_theorem_id']+'/graph')
    write_atomic(p.DIRECTORY/'Metadata/bridge_platform_default_graph.json',json_bytes(root))
    root=expand_dependency_graph(client,root)
    write_atomic(p.DIRECTORY/'Metadata/bridge_platform_root_graph.json',json_bytes(root))
    required=record['definitions']+record['theorems']+[entries['hyperbolic_model'],entries['model_radial_volume'],
        entries['radial_cross_comparison'],entries['OpenGA.antitoneOn_lintegral_div_hypRadVol']]
    for e in required:
        if not reachable(root['edges'],e['publication']['theorem_id'],record['root_theorem_id']):
            raise RuntimeError('Main graph missing dependency path: '+e['id'])
    for e in record['theorems']:
        if not e.get('open_problem'):
            for dependency in e['imports']+e['definitions']:
                if not reachable(root['edges'],entries[dependency]['publication']['theorem_id'],e['publication']['theorem_id']):
                    raise RuntimeError('Missing intermediate dependency: '+dependency+' -> '+e['id'])
    if client.request('/theorems/'+record['root_theorem_id'])['status']!='Open':
        raise RuntimeError('Unexpected root status; inspect before reporting')
    record.update(status='MAIN_GRAPH_BRIDGE_PUBLISHED',verified_at=p.now(),
                  graph_verification={'root_id':record['root_theorem_id'],'nodes':len(root['nodes']),
                    'required_paths_verified':[e['id'] for e in required],'root_status':'Open'})
    p.save(record);annotate(p,client,record)
    print('Verified both new definitions and all analytic dependencies in the main Poincare graph; geometry remains Open.',flush=True)
