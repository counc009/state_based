"""Free native controls for the evaluation-only KB boundary."""
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from kb_rescore import diagnose,REPO

class FallbackKBTests(unittest.TestCase):
    def test_probe_only_changes_instantiated_kb(self):
        root=REPO/'evaluation/native'
        self.assertEqual((root/'effects_fallback.ml').read_text().split('\n',1)[1],(root/'effects.ml').read_text().replace('Fql.Knowledge.Example','Fallback_kb'))
        self.assertEqual((root/'query_interp_fallback.ml').read_text().split('\n',1)[1],(REPO/'bin/query_interp.ml').read_text().replace('Fql.Knowledge.Example','Fallback_kb'))
    def test_generic_package(self):
        a=diagnose('install zinc-validation-tool','example');b=diagnose('install zinc-validation-tool','fallback')
        self.assertFalse(a['semantic_accepted']);self.assertTrue(b['semantic_accepted']);self.assertTrue(b['interpreted'])
        self.assertEqual(b['probe']['effects'][0]['packages'],[{'name':'zinc-validation-tool','manager':'system'}])
    def test_generic_service(self):
        a=diagnose('start zinc-validation-daemon service','example');b=diagnose('start zinc-validation-daemon service','fallback')
        self.assertFalse(a['semantic_accepted']);self.assertTrue(b['semantic_accepted']);self.assertTrue(b['interpreted'])
        self.assertEqual(b['probe']['effects'][0]['name'],{'kind':'string','value':'zinc-validation-daemon'})
    def test_known_entry_and_context_error_preserved(self):
        for q in ['install bash','install apache server','start apache server service']:
            a=diagnose(q,'example');b=diagnose(q,'fallback');self.assertEqual(a,b)
    def test_non_package_service_errors_preserved(self):
        for q in ['create database zinc_validation','create file zinc_validation','install','This is commentary.']:
            a=diagnose(q,'example');b=diagnose(q,'fallback');self.assertEqual(a,b)

if __name__=='__main__':unittest.main()
