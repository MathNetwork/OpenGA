#!/usr/bin/env python3
"""Publish the verified immersion-metric batch and read back every accepted proof."""
import argparse
import json
import time
from urllib.request import Request

import publish_bishop_gromov as publisher
from sync import BASE, Client, MISSION_ID, ROOT, expand_dependency_graph, json_bytes, write_atomic

DIRECTORY=ROOT/'Contributions/ImmersedSurfaceMetric'
GOAL_ID='7ea2da12-4d1b-4bbc-8257-df87d92f5a8e'


def reachable(graph, start):
    seen={start}
    while True:
        more=seen|{e['target'] for e in graph['edges'] if e['source'] in seen}
        if more==seen:
            return seen
        seen=more


def annotate(client, record):
    live=next(m for m in client.pages('/missions/'+MISSION_ID+'/milestones','milestones') if m['id']==record['milestone_id'])
    update=record.get('milestone_update')
    if update is None:
        links=['['+e['payload'].get('definition_title',e['payload'].get('theorem_title'))+'](https://prove2.me/theorems/'+e['publication']['theorem_id']+')'
               for e in record['definitions']+record['theorems']]
        paragraph=('\n\n**Immersed-surface metric and area compatibility.** '+'; '.join(links)+
          '. A smooth immersion now supplies an actual induced smooth Riemannian metric, with proved agreement between its parameter-patch areas and those of the composed ambient map. '
          'Self-intersections are allowed; branch points are excluded. '
          'The global closed-surface Ricci-flow area variation has been checked in the linked OpenGA source; its full dependency tree is not yet published here. '
          'The minimal-sphere estimate, Gauss-Bonnet step and sweepout construction are not claimed by this batch, and finite-time extinction remains open.')
        update=record['milestone_update']={'before':live['milestone_description'],'after':live['milestone_description']+paragraph,
          'canonical_theorem':live.get('theorem'),'status':'PREPARED'}
        publisher.save(record)
    if live['milestone_description']!=update['after']:
        if live['milestone_description']!=update['before'] or live.get('theorem')!=update['canonical_theorem']:
            raise RuntimeError('Milestone changed concurrently; reconcile before editing')
        req=Request(BASE+'/milestones/'+record['milestone_id'],method='PATCH',
          data=json_bytes({'milestone_description':update['after'],'reason':'Link the verified immersion metric and its area compatibility to the CM infrastructure.'}),
          headers={'Authorization':'Bearer '+client.token,'Content-Type':'application/json','Accept':'application/json'})
        with client.opener.open(req,timeout=60) as response:
            update['response']=json.load(response)
        publisher.save(record)
        live=next(m for m in client.pages('/missions/'+MISSION_ID+'/milestones','milestones') if m['id']==record['milestone_id'])
    if live['milestone_description']!=update['after'] or live.get('theorem')!=update['canonical_theorem']:
        raise RuntimeError('Milestone readback differs')
    update.update(status='VERIFIED',verified_at=publisher.now())
    publisher.save(record)


def finish(client,record):
    graphs={e['id']:expand_dependency_graph(client,client.request('/theorems/'+e['publication']['theorem_id']+'/graph')) for e in record['theorems']}
    write_atomic(DIRECTORY/'Metadata/platform_graphs.json',json_bytes(graphs))
    definitions=record['definitions'][0]['publication']['theorem_id']
    density,area=record['theorems']
    for entry in record['theorems']:
        if entry['publication']['theorem_id'] not in reachable(graphs[entry['id']],definitions):
            raise RuntimeError('Missing surface-area definition edge')
    if area['publication']['theorem_id'] not in reachable(graphs[area['id']],density['publication']['theorem_id']):
        raise RuntimeError('Missing density-to-area proof dependency')
    root=expand_dependency_graph(client,client.request('/theorems/'+GOAL_ID+'/graph'))
    write_atomic(DIRECTORY/'Metadata/mission_graph_after.json',json_bytes(root))
    record['graph']={'local_dependency_chain_verified':True,
      'new_nodes_reaching_mission_goal':[e['id'] for e in record['definitions']+record['theorems']
        if GOAL_ID in reachable(root,e['publication']['theorem_id'])],
      'note':'Milestone references are progress links, not proof dependencies. No artificial edge to the Poincare goal is inserted.'}
    record.update(status='PUBLISHED',verified_at=publisher.now())
    publisher.save(record)
    annotate(client,record)
    print('Published and verified: one immersion-metric definition bundle and two proved area compatibility theorems.',flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--apply',action='store_true');p.add_argument('--watch',action='store_true')
    args=p.parse_args()
    publisher.DIRECTORY=DIRECTORY;publisher.RECORD=DIRECTORY/'publication.json'
    record=json.loads(publisher.RECORD.read_text());publisher.validate(record)
    if not args.apply:
        print('All source and payload hashes match; no network request made.');return
    client=Client(json.loads((ROOT/'.credentials.json').read_text())['api_key'])
    if client.version!='0.9.8':
        raise RuntimeError('Refresh platform skill before publishing')
    envs=client.request('/environments')['environments']
    if not any(e['mathlib_rev']==record['mathlib_rev'] and e['toolchain']==record['toolchain'] for e in envs):
        raise RuntimeError('Platform environment differs')
    for prereq in record['prerequisites']:
        item=client.request('/theorems/'+prereq['theorem_id'])
        if item['mathlib_rev']!=record['mathlib_rev'] or item.get('definition','').strip()!=(DIRECTORY/prereq['path']).read_text().strip():
            raise RuntimeError('An existing platform definition differs')
    if not (DIRECTORY/'Metadata/mission_graph_before.json').exists():
        graph=expand_dependency_graph(client,client.request('/theorems/'+GOAL_ID+'/graph'))
        write_atomic(DIRECTORY/'Metadata/mission_graph_before.json',json_bytes(graph))
    for attempt in range(180 if args.watch else 1):
        ready={}
        for entry in record['definitions']:
            ready[entry['id']]=publisher.publish(client,record,entry)
        for entry in record['theorems']:
            deps=entry['definitions']+entry['imports']
            ready[entry['id']]=(all(ready.get(n,False) for n in deps)
                and publisher.publish(client,record,entry) and publisher.prove(client,record,entry))
        if all(ready.values()):
            finish(client,record);return
        if args.watch:
            time.sleep(10)
    print('Jobs remain pending; rerun to resume without duplicate submissions.',flush=True)

if __name__=='__main__':
    main()
