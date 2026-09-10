#!/usr/bin/env python3
"""Resume the validated measured-reference-ball reduction and verify root reachability."""
import argparse,json,sys,time
import publish_bishop_gromov as p
from sync import Client,ROOT,expand_dependency_graph,json_bytes,write_atomic
from publish_surgery_bridge import reachable
D=ROOT/'Contributions/MeasuredSurgery'
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--apply',action='store_true');parser.add_argument('--watch',action='store_true');args=parser.parse_args()
 p.DIRECTORY=D;p.RECORD=D/'publication.json';r=json.loads(p.RECORD.read_text());p.validate(r)
 if not args.apply: print('Validated exact payloads, source hashes, builds, and proof audits.');return
 c=Client(json.loads((ROOT/'.credentials.json').read_text())['api_key'])
 if c.version!='0.9.9':raise RuntimeError('Refresh platform instructions for changed version')
 envs=c.request('/environments')['environments']
 if not any(x['mathlib_rev']==r['mathlib_rev'] and x['toolchain']==r['toolchain'] for x in envs):raise RuntimeError('Environment mismatch')
 for k in ('measure','openness'):
  x=c.request('/theorems/'+r['external_ids'][k])
  if x['status']!='Proved' or x['mathlib_rev']!=r['mathlib_rev']:raise RuntimeError('External theorem changed: '+k)
 ready={}
 for e in r['definitions']+r['theorems']:
  name=e['id'];ready[name]=False
  if not all(ready.get(dep,False) for dep in e['dependencies']): continue
  if not p.publish(c,r,e): continue
  if e.get('open_problem') or 'definition' in e['payload']:ready[name]=True
  else:ready[name]=p.prove(c,r,e)
 if not all(ready.values()):print('Pending jobs saved; resume with --apply.');return
 default_graph=c.request('/theorems/'+r['root_theorem_id']+'/graph')
 write_atomic(D/'Metadata/root_default_after.json',json_bytes(default_graph))
 graph=expand_dependency_graph(c,default_graph)
 write_atomic(D/'Metadata/root_after.json',json_bytes(graph))
 required={e['id']:e['publication']['theorem_id'] for e in r['definitions']+r['theorems']
           if e['id'] in r.get('root_required',[x['id'] for x in r['definitions']+r['theorems']])}
 required.update({k:r['external_ids'][k] for k in ('measure','openness')})
 for name,tid in required.items():
  if not reachable(graph['edges'],tid,r['root_theorem_id']):raise RuntimeError('Missing root path: '+name)
 root=c.request('/theorems/'+r['root_theorem_id'])
 r.update(status='MAIN_GRAPH_CONNECTED',verified_at=p.now(),graph_verification={'nodes':len(graph['nodes']),'edges':len(graph['edges']),'root_status':root['status'],'verified_paths':required})
 p.save(r);print('Main graph verified:',len(graph['nodes']),'nodes,',len(graph['edges']),'edges; goal',root['status'])
if __name__=='__main__':
 while True:
  main()
  if '--watch' not in sys.argv or '--apply' not in sys.argv: break
  if json.loads((D/'publication.json').read_text()).get('status')=='MAIN_GRAPH_CONNECTED': break
  time.sleep(10)
