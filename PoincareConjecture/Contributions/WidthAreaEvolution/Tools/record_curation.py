"""Record reviewed proof reuse after the platform mirror has synchronized."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

R = Path(__file__).resolve().parents[3]
snapshot = json.loads((R / 'sync.json').read_text())
p = R / 'curation.json'
curation = json.loads(p.read_text())
modules = {
    'Riemannian.RiemannianMetric.isOpen_geodesicBall': 'ComparisonGeometry/MetricBall',
    'Riemannian.RiemannianMetric.measure_geodesicBall_pos': 'ComparisonGeometry/BallMeasure',
    'OpenGA.MeasuredReferenceBall.anchor_pos': 'ComparisonGeometry/MeasuredSurgery',
    'OpenGA.nonempty_surgeryComparisonProcess_of_measuredData': 'ComparisonGeometry/MeasuredSurgery',
    'OpenGA.nonempty_widthComparisonData_of_areaEvolution': 'Analysis/Width/AreaEvolution',
    'OpenGA.nonempty_measuredSurgeryComparisonData_of_areaEvolution': 'Analysis/Width/SurgeryAreaEvolution',
}
selected = {'0bbeaeb3-bf91-4538-ad63-f4a462576fdd', '5619c87b-44f9-43cd-954d-21a9cf48c14b'}
expected_hashes = {}
for batch in ['MeasuredSurgery', 'WidthAreaEvolution']:
    record = json.loads((R / 'Contributions' / batch / 'publication.json').read_text())
    for e in record['theorems']:
        if 'submission' in e:
            sid = e['submission']['submission_id']
            selected.add(sid)
            expected_hashes[sid] = e['proof_sha256']
for sid in selected:
    sub = snapshot['submissions'][sid]
    node = snapshot['nodes'][sub['theorem_id']]
    sha = hashlib.sha256((R / sub['local_path']).read_bytes()).hexdigest()
    if sha != snapshot['file_hashes'][sub['local_path']] or sha != expected_hashes.get(sid, sha):
        raise RuntimeError('Source mismatch: ' + sid)
    review = dict(source_author=sub['username'], source_mathlib_rev=node['mathlib_rev'],
        source_sha256=sha, source_status=sub['status'], source_theorem_id=sub['theorem_id'],
        source_url='https://prove2.me/api/v1/submissions/' + sid + '/solution')
    if sub['status'] == 'ACCEPTED':
        name = node['theorem_name']
        review.update(status='integrated', declarations=[dict(name=name,
            path='OpenGALib/' + modules[name] + '.lean')],
            scope='Reviewed complete proof, with exact target and standard-axiom checks. '
            'Measured reference-ball positivity and uniform area-evolution adapters are conditional '
            'analytic results. Actual surgery geometry, the uniform radial bound, and geometric '
            'sweepout estimates are not claimed by these results.')
    elif sub['status'] == 'SKETCH_ACCEPTED':
        review.update(status='deferred', declarations=[],
            reason='Accepted reduction retained in the platform workspace. It depends on an Open '
            'geometric construction and is not admitted as a complete theorem in the reusable library.')
    else:
        raise RuntimeError('Unexpected status: ' + sid)
    curation['reviews'][sid] = review
curation['reviewed_at'] = datetime.now(timezone.utc).isoformat()
p.write_text(json.dumps(curation, ensure_ascii=False, indent=2, sort_keys=True) + '\n')
print('Recorded', len(selected), 'reviewed source receipts')
