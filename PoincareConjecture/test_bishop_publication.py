"""Offline checks for staged publication with definition dependencies."""
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import publish_bishop_gromov as publisher


class PublicationOrderingTests(unittest.TestCase):
    def test_pending_definition_blocks_consumers_and_preserves_prior_batch(self):
        for first_ready in (False, True):
            with self.subTest(first_ready=first_ready), TemporaryDirectory() as directory:
                root = Path(directory)
                prior = b'{"batch": "original receipt"}\n'
                (root / 'publication.json').write_bytes(prior)
                (root / '.credentials.json').write_text('{"api_key":"test-only"}')
                record = {'mathlib_rev': 'rev', 'toolchain': 'lean',
                          'definitions': [{'id': 'model'}, {'id': 'volume', 'definitions': ['model']}],
                          'theorems': [{'id': 'comparison', 'definitions': ['volume'], 'imports': []}]}
                (root / 'model_publication.json').write_text(json.dumps(record))
                calls = []

                class FakeClient:
                    version = '0.9.8'
                    def __init__(self, key): pass
                    def request(self, path):
                        return {'environments': [{'mathlib_rev': 'rev', 'toolchain': 'lean'}]}

                def publish(client, current, entry):
                    calls.append(entry['id'])
                    current['last_attempt'] = entry['id']
                    publisher.save(current)
                    return entry['id'] == 'model' and first_ready

                with patch.object(publisher, 'DIRECTORY', root), patch.object(publisher, 'ROOT', root), \
                     patch.object(publisher, 'RECORD', root / 'publication.json'), \
                     patch.object(publisher, 'Client', FakeClient), patch.object(publisher, 'validate'), \
                     patch.object(publisher, 'publish', publish), patch.object(publisher, 'prove') as prove, \
                     patch('sys.argv', ['publish', '--batch', 'model', '--apply']):
                    publisher.main()
                self.assertEqual(calls, ['model', 'volume'] if first_ready else ['model'])
                prove.assert_not_called()
                self.assertEqual((root / 'publication.json').read_bytes(), prior)
                self.assertEqual(json.loads((root / 'model_publication.json').read_text())['last_attempt'], calls[-1])


class SketchPublicationTests(unittest.TestCase):
    def test_accepted_sketch_requires_open_parent_and_exact_source(self):
        from types import SimpleNamespace
        from hashlib import sha256
        code = 'theorem solution : True := by trivial\n'
        entry = {'id': 'parent', 'payload': {}, 'expected_verdict': 'SKETCH_ACCEPTED',
                 'proof_sha256': sha256(code.encode()).hexdigest(),
                 'submission': {'submission_id': 'sketch'},
                 'publication': {'theorem_id': 'parent'}}
        client = SimpleNamespace(request=lambda path:
            {'status': 'SKETCH_ACCEPTED'} if path.startswith('/verify') else {'content': code})
        with patch.object(publisher, 'save'), patch.object(publisher, 'verify_item',
                return_value={'theorem_id': 'parent', 'status': 'Open'}):
            self.assertTrue(publisher.prove(client, {}, entry))
        with patch.object(publisher, 'save'), patch.object(publisher, 'verify_item',
                return_value={'theorem_id': 'parent', 'status': 'Proved'}):
            with self.assertRaisesRegex(RuntimeError, 'theorem status'):
                publisher.prove(client, {}, entry)

    def test_pending_analytic_child_blocks_parent_sketch(self):
        from types import SimpleNamespace
        import publish_surgery_bridge as bridge
        record = {'definitions': [], 'theorems': [
            {'id': 'analytic', 'definitions': [], 'imports': []},
            {'id': 'geometry', 'definitions': [], 'imports': [], 'open_problem': True},
            {'id': 'parent', 'definitions': [], 'imports': ['analytic', 'geometry']}]}
        calls=[]
        p=SimpleNamespace(publish=lambda c,r,e: True,
            prove=lambda c,r,e: calls.append(e['id']) or False,
            verify_item=lambda c,e: {'status':'Open'})
        with patch.object(bridge,'external_entries',return_value={}):
            bridge.run_bridge(p,None,record)
        self.assertEqual(calls,['analytic'])


if __name__ == '__main__':
    unittest.main()
