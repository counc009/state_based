"""Real native diagnostic controls; skipped until `dune build` has completed."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'code'))
from evaluate import REPO
from semantic_audit import controls, probe

BINARY=REPO/'_build/default/evaluation/native/effects.exe'


@unittest.skipUnless(BINARY.exists(), 'Build the native effects diagnostic with dune first')
class NativeSemanticsTests(unittest.TestCase):
    def test_compiler_valid_counterexamples_fail_nl_obligations(self):
        rows=controls(BINARY)
        self.assertEqual(len(rows),5)
        self.assertTrue(all(row['control_pass'] for row in rows), rows)
        self.assertTrue(all(row['probe']['status']=='ok' for row in rows))

    def test_empty_query_is_not_counted_as_valid(self):
        result=probe('',BINARY)
        self.assertEqual(result['status'],'empty_query')
        self.assertNotEqual(result['returncode'],0)


if __name__=='__main__':
    unittest.main()
