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


if __name__ == '__main__':
    unittest.main()
