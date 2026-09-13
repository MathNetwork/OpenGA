#!/usr/bin/env python3
"""Publish and verify the complete closed-surface Ricci-flow area variation tree."""
import argparse
import json
import time
from urllib.request import Request

import publish_bishop_gromov as publisher
from publish_immersed_metric import reachable
from sync import BASE, Client, MISSION_ID, ROOT, expand_dependency_graph, json_bytes, write_atomic

DIRECTORY = ROOT / 'Contributions/ClosedSurfaceArea'
TARGET = 'OpenGA.RicciFlow.hasDerivAt_area'
GOAL = '7ea2da12-4d1b-4bbc-8257-df87d92f5a8e'


def recover_uncertain_publications(client, record):
    """Recover timed-out uploads from the owner's exact echoed publish jobs."""
    uncertain = [e for e in record['definitions'] + record['theorems']
                 if e.get('publication', {}).get('status') == 'SUBMITTING'
                 and not e['publication'].get('job_id')]
    if not uncertain:
        return
    jobs, offset = [], 0
    while True:
        page = client.request('/publish-jobs?limit=100&offset=' + str(offset))
        arrays = [value for value in page.values() if isinstance(value, list)
                  and all(isinstance(j, dict) and 'id' in j and 'kind' in j for j in value)]
        if len(arrays) != 1:
            raise RuntimeError('Unexpected publish-job list fields: ' + ', '.join(page))
        batch = arrays[0]
        jobs.extend(batch)
        offset += len(batch)
        total = page.get('total', page.get('count', page.get('pagination', {}).get('total')))
        if not batch or (total is not None and offset >= total):
            break
    for entry in uncertain:
        payload = entry['payload']
        definition = 'definition' in payload
        name = payload['definition_name' if definition else 'theorem_name']
        candidates = [j for j in jobs if j.get('theorem_name') == name
                      and j.get('kind') == ('definition' if definition else 'problem')
                      and j.get('created_at', '') >= entry['publication']['started_at'][:19]]
        matches = []
        for candidate in candidates:
            job = client.request('/publish-jobs/' + candidate['id'])
            if job.get('definitions', '').strip() != payload['definition' if definition else 'preamble'].strip():
                continue
            if not definition and job.get('formal_statement', '').strip() != payload['formal_statement'].strip():
                continue
            if job.get('mathlib_rev', record['mathlib_rev']) != record['mathlib_rev']:
                continue
            matches.append(job)
        if len(matches) != 1:
            raise RuntimeError('Upload outcome still uncertain; found ' + str(len(matches)) + ' exact jobs for ' + name)
        job = matches[0]
        entry['publication'].update(job_id=job['id'], status='PENDING',
                                    recovery={'method': 'exact owner publish-job readback', 'job': job,
                                              'recovered_at': publisher.now()})
        publisher.save(record)
        print('Recovered upload:', name, job['id'], flush=True)


def annotate(client, record):
    live = next(m for m in client.pages('/missions/' + MISSION_ID + '/milestones', 'milestones')
                if m['id'] == record['milestone_id'])
    update = record.get('milestone_update')
    if update is None:
        target = next(e for e in record['theorems'] if e['id'] == TARGET)
        link = 'https://prove2.me/theorems/' + target['publication']['theorem_id']
        before = live['milestone_description']
        old = ('The global closed-surface Ricci-flow area variation has been checked in the linked OpenGA source; '
               'its full dependency tree is not yet published here.')
        replacement = ('The [global closed-surface Ricci-flow area variation](' + link + ') and its full dependency tree are now verified on the platform.')
        after = before.replace(old, replacement)
        paragraph = ('\n\n**Closed-surface area variation.** [' + target['payload']['theorem_title'] + '](' + link + '). '
                     'For a fixed smooth immersion of a compact boundaryless surface, the derivative of its actual induced area '
                     'is the negative integral of the ambient Ricci tensor traced on its tangent plane. '
                     'The proof includes local-in-time metric regularity and differentiation of Riemannian volume, '
                     'reusing the linked DifferentialGeometry definitions and proofs. '
                     'This supplies the smooth area-variation step. The minimal-sphere estimate, including the Gauss-Bonnet and branched-surface steps, '
                     'and the sweepout argument remain separate open tasks.')
        update = record['milestone_update'] = {'before': before, 'after': after + paragraph,
                                              'canonical_theorem': live.get('theorem'), 'status': 'PREPARED'}
        publisher.save(record)
    if live['milestone_description'] != update['after']:
        if live['milestone_description'] != update['before'] or live.get('theorem') != update['canonical_theorem']:
            raise RuntimeError('Milestone changed concurrently; reconcile before editing')
        req = Request(BASE + '/milestones/' + record['milestone_id'], method='PATCH',
                      data=json_bytes({'milestone_description': update['after'],
                                       'reason': 'Record the accepted complete closed-surface area-variation proof and its actual dependency tree.'}),
                      headers={'Authorization': 'Bearer ' + client.token, 'Content-Type': 'application/json', 'Accept': 'application/json'})
        with client.opener.open(req, timeout=60) as response:
            update['response'] = json.load(response)
        publisher.save(record)
        live = next(m for m in client.pages('/missions/' + MISSION_ID + '/milestones', 'milestones')
                    if m['id'] == record['milestone_id'])
    if live['milestone_description'] != update['after'] or live.get('theorem') != update['canonical_theorem']:
        raise RuntimeError('Milestone readback differs')
    update.update(status='VERIFIED', verified_at=publisher.now())
    publisher.save(record)


def finish(client, record):
    target = next(e for e in record['theorems'] if e['id'] == TARGET)
    target_id = target['publication']['theorem_id']
    graph = expand_dependency_graph(client, client.request('/theorems/' + target_id + '/graph'))
    write_atomic(DIRECTORY / 'Metadata/platform_graph.json', json_bytes(graph))
    required = ['OpenGA.RicciFlow.inducedMetric_regularOn', 'OpenGA.RicciFlow.traceTimeDeriv_inducedMetric',
                'OpenGA.hasDerivAt_totalRiemannianVolume', 'DifferentialGeometry.Integral.Measure.volume_variation_formula']
    for name in required:
        entry = next(e for e in record['theorems'] if e['id'] == name)
        if target_id not in reachable(graph, entry['publication']['theorem_id']):
            raise RuntimeError('Missing real proof dependency: ' + name)
    root = expand_dependency_graph(client, client.request('/theorems/' + GOAL + '/graph'))
    write_atomic(DIRECTORY / 'Metadata/mission_graph_after.json', json_bytes(root))
    record['graph'] = {'target_nodes': len(graph['nodes']), 'target_edges': len(graph['edges']),
                       'actual_area_variation_dependencies_verified': True,
                       'target_reaches_poincare_goal': GOAL in reachable(root, target_id),
                       'note': 'Milestone progress links do not create proof dependencies. The bridge through the minimal-sphere and sweepout estimates remains to be proved.'}
    record.update(status='PUBLISHED', verified_at=publisher.now())
    publisher.save(record)
    annotate(client, record)
    print('The complete closed-surface area-variation theorem and all exported prerequisites are published and verified.', flush=True)
    print('Target: https://prove2.me/theorems/' + target_id, flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--watch', action='store_true')
    args = parser.parse_args()
    publisher.DIRECTORY = DIRECTORY
    publisher.RECORD = DIRECTORY / 'publication.json'
    record = json.loads(publisher.RECORD.read_text())
    publisher.validate(record)
    if not args.apply:
        print('All validated source and payload hashes match; no network request made.')
        return
    key = json.loads((ROOT / '.credentials.json').read_text())['api_key']
    client = Client(key)
    refreshed = time.monotonic()
    if client.version != '0.9.9':
        raise RuntimeError('Refresh the platform skill before publishing')
    envs = client.request('/environments')['environments']
    if not any(e['mathlib_rev'] == record['mathlib_rev'] and e['toolchain'] == record['toolchain'] for e in envs):
        raise RuntimeError('Platform environment differs')
    recover_uncertain_publications(client, record)
    for prereq in record['prerequisites']:
        item = client.request('/theorems/' + prereq['theorem_id'])
        if item['mathlib_rev'] != record['mathlib_rev'] or item.get('definition', '').strip() != (DIRECTORY / prereq['path']).read_text().strip():
            raise RuntimeError('An existing platform definition differs')
    before = DIRECTORY / 'Metadata/mission_graph_before.json'
    if not before.exists():
        write_atomic(before, json_bytes(expand_dependency_graph(client, client.request('/theorems/' + GOAL + '/graph'))))
    ready = set()
    for attempt in range(720 if args.watch else 1):
        if time.monotonic() - refreshed > 1200:
            client = Client(key)
            refreshed = time.monotonic()
            if client.version != '0.9.9':
                raise RuntimeError('Platform version changed during publication')
        for entry in record['definitions']:
            if entry['id'] not in ready and set(entry['definitions']) <= ready:
                if publisher.publish(client, record, entry):
                    ready.add(entry['id'])
        for entry in record['theorems']:
            if entry['id'] not in ready and set(entry['definitions'] + entry['imports']) <= ready:
                if publisher.publish(client, record, entry) and publisher.prove(client, record, entry):
                    ready.add(entry['id'])
        print(f'Verified {len(ready)}/{len(record["definitions"]) + len(record["theorems"])} items.', flush=True)
        if len(ready) == len(record['definitions']) + len(record['theorems']):
            finish(client, record)
            return
        if args.watch:
            time.sleep(10)
    print('Jobs remain pending. Rerun to resume from the recorded job IDs.', flush=True)


if __name__ == '__main__':
    main()
