#!/usr/bin/env python3
"""Compile the exported proof tree in dependency order with bounded memory."""
import json
import argparse
import subprocess
from pathlib import Path

directory = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--start-index', type=int, default=1)
args = parser.parse_args()
plan = json.loads((directory / 'Metadata/export_plan.json').read_text())
targets = []
for module in plan['module_order']:
    slug = 'ClosedSurface_' + module.replace('.', '_')
    if (directory / 'Definitions' / ('Def_' + slug + '.lean')).exists():
        targets.append('Definitions.Def_' + slug)
    targets.append('Verified.' + slug)
remaining = {r['name']: r for r in plan['theorem_files']}
order = []
while remaining:
    ready = sorted(n for n, r in remaining.items() if not set(r['children']).intersection(remaining))
    if not ready:
        raise RuntimeError('The proof graph is cyclic')
    for name in ready:
        order.append(name)
        remaining.pop(name)
for name in order:
    targets.extend(['Theorems.Thm_' + name.replace('.', '_'), 'Solutions.Sol_' + name.replace('.', '_')])
with (directory / 'Metadata/build_sequential.log').open('a' if args.start_index > 1 else 'w') as log:
    for index, target in enumerate(targets):
        if index + 1 < args.start_index:
            continue
        proc = subprocess.run(['lake', 'build', target], cwd=directory, stdout=log, stderr=subprocess.STDOUT)
        log.flush()
        print(f'{index + 1}/{len(targets)} {target}: {proc.returncode}', flush=True)
        if proc.returncode:
            raise SystemExit(proc.returncode)
print('All exported modules compiled successfully.', flush=True)
