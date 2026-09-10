#!/usr/bin/env python3
"""Read-only platform environment and name-collision check."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
from pathlib import Path
import sys

DIRECTORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(DIRECTORY.parents[1]))
from sync import Client, ROOT

record = json.loads((DIRECTORY / 'publication.json').read_text())
client = Client(json.loads((ROOT / '.credentials.json').read_text())['api_key'])
envs = client.request('/environments')['environments']
assert client.version == '0.9.9', 'Refresh the platform skill'
assert any(e['mathlib_rev'] == record['mathlib_rev'] and e['toolchain'] == record['toolchain'] for e in envs), 'Environment differs'
names = [r['payload'].get('definition_name', r['payload'].get('theorem_name')) for r in record['definitions'] + record['theorems']]

def lookup(name):
    rows = client.pages('/theorems', 'theorems', theorem_name=name, env=record['mathlib_rev'])
    return [dict(name=name, theorem_id=r['theorem_id'], status=r['status']) for r in rows if r['theorem_name'] == name]

with ThreadPoolExecutor(max_workers=4) as executor:
    matches = [r for rows in executor.map(lookup, names) for r in rows]
result = {'checked_at': datetime.now(timezone.utc).isoformat(), 'platform_version': client.version,
          'environment_matches': True, 'checked_names': len(names), 'existing_matches': matches}
(DIRECTORY / 'Metadata/platform_preflight.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
