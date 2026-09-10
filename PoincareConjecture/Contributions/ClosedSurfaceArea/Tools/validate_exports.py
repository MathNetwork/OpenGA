#!/usr/bin/env python3
"""Validate exact theorem text, solution types, source fingerprints and proof axioms."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

DIRECTORY = Path(__file__).resolve().parents[1]
REPOSITORY = DIRECTORY.parents[2]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(label, args, cwd):
    log = DIRECTORY / 'Metadata' / (label + '.log')
    with log.open('w') as stream:
        proc = subprocess.run(args, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    if proc.returncode:
        raise RuntimeError(label + ' failed; inspect ' + str(log))
    print(label + ': passed', flush=True)
    return log


def rows(path):
    return {r['name']: r for r in (json.loads(line) for line in path.read_text().splitlines() if line.startswith('{'))}


def main():
    record = json.loads((DIRECTORY / 'publication.json').read_text())
    run('final_build', ['lake', 'build'], DIRECTORY)
    logs = [DIRECTORY / 'Metadata/original_fingerprints.log']
    if 'All 802 declarations passed the axiom audit.' not in logs[0].read_text():
        raise RuntimeError('Source audit is missing or incomplete')
    logs.append(run('exported_fingerprints', ['lake', 'env', 'lean', 'Tools/ExportedAudit.lean'], DIRECTORY))
    original, exported = map(rows, logs)
    if set(original) != set(exported):
        raise RuntimeError('Exported declaration set differs')
    differences = {n: [k for k in original[n] if original[n][k] != exported[n].get(k)]
                   for n in original if original[n] != exported[n]}
    (DIRECTORY / 'Metadata/fingerprint_differences.json').write_text(json.dumps(differences, indent=2) + '\n')
    if differences:
        expression_path = DIRECTORY / 'Metadata/source_expressions.json'
        serialized = json.loads(expression_path.read_text())
        if {r['name'] for r in serialized['declarations']} != set(differences):
            raise RuntimeError('Kernel comparison inputs do not cover exactly the differing declarations')
        kernel_log = run('kernel_comparison', ['lake', 'env', 'lean', 'Tools/KernelComparison.lean'], DIRECTORY)
        expected = {f'Kernel conversion passed: {name}' for name in differences}
        if not expected <= set(kernel_log.read_text().splitlines()):
            raise RuntimeError('A source/export kernel conversion check is missing')
        logs += [expression_path, kernel_log]
    if 'All 802 declarations passed the axiom audit.' not in logs[1].read_text():
        raise RuntimeError('Exported proof audit is incomplete')
    def check(entry):
        name = entry['id'].replace('.', '_')
        path = run('solution_type_' + name, ['lake', 'env', 'lean', 'Tools/Audit_' + name + '.lean'], DIRECTORY)
        if 'Exact solution type passed.' not in path.read_text():
            raise RuntimeError('Solution audit did not finish: ' + name)
        return path
    with ThreadPoolExecutor(max_workers=2) as executor:
        logs += list(executor.map(check, record['theorems']))
    compact = {'original': original, 'exported': exported}
    (DIRECTORY / 'Metadata/source_export_comparison.json').write_text(json.dumps(compact, ensure_ascii=False, indent=2) + '\n')
    record['validation'] = {'status': 'passed', 'verified_at': datetime.now(timezone.utc).isoformat(),
                            'compiled_libraries': ['Definitions', 'Theorems', 'Solutions', 'Verified'],
                            'declaration_fingerprints_compared': len(original),
                            'pretty_printed_theorem_types_compared': len(record['theorems']),
                            'exact_solution_types_checked': len(record['theorems']),
                            'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
                            'kernel_conversion_checks': len(differences),
                            'normalization': 'Universe parameters and bound variable names; documented private and anonymous-instance name map. Declaration types and definition bodies are structurally fingerprinted. Every differing expression is checked by kernel-verified reflexive equality after expanding source auxiliary proof constants. This accounts for definitionally equal instance expressions and proof-irrelevant arguments; no mathematical hypotheses are removed.',
                            'logs': [{'path': str(p.relative_to(DIRECTORY)), 'sha256': digest(p.read_bytes())} for p in logs]}
    for p in (DIRECTORY / 'Tools').glob('*.py'):
        source = {'path': str(p.relative_to(REPOSITORY)), 'sha256': digest(p.read_bytes())}
        prior = next((r for r in record['sources'] if r['path'] == source['path']), None)
        if prior is None:
            record['sources'].append(source)
        elif prior != source:
            raise RuntimeError('A preparation source changed after payload generation: ' + str(p))
    (DIRECTORY / 'publication.json').write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')
    print('All publication gates passed.', flush=True)


if __name__ == '__main__':
    main()
