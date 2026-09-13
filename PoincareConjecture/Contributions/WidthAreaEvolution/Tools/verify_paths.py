"""Save explicit directed paths from the accepted contribution to the mission goal."""
import json
from collections import defaultdict, deque
from pathlib import Path

D = Path(__file__).resolve().parents[1]
record = json.loads((D / 'publication.json').read_text())
if record['status'] != 'MAIN_GRAPH_CONNECTED':
    raise RuntimeError('Wait for accepted submissions and the graph readback')
graph = json.loads((D / 'Metadata/root_after.json').read_text())
adj = defaultdict(list)
for edge in graph['edges']:
    adj[edge['source']].append(edge['target'])
names = {n.get('theorem_id', n.get('id')): n.get('theorem_name', n.get('id'))
         for n in graph['nodes']}
required = dict(record['graph_verification']['verified_paths'])
paths = {}
for name, start in required.items():
    queue = deque([[start]])
    seen = {start}
    while queue:
        path = queue.popleft()
        if path[-1] == record['root_theorem_id']:
            paths[name] = [dict(id=n, name=names.get(n, n)) for n in path]
            break
        for target in adj[path[-1]]:
            if target not in seen:
                seen.add(target)
                queue.append(path + [target])
    else:
        raise RuntimeError('No directed path to the root: ' + name)
(D / 'Metadata/verified_root_paths.json').write_text(
    json.dumps(paths, ensure_ascii=False, indent=2) + '\n')
print('Verified directed root paths:', len(paths))
