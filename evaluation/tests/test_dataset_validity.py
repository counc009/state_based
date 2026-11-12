import copy
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
CODE=Path(__file__).resolve().parents[1]/'code';sys.path.insert(0,str(CODE))
from dataset_filter import candidate,normalize,support_hint,module_style
import dataset_validity as d
import dataset_transport as transport

class DatasetValidityTests(unittest.TestCase):
    def test_free_screen_filters_named_styles_jinja_and_generic_objects(self):
        self.assertEqual(normalize('name: Ensure unzip is installed.'),'Ensure unzip is installed.')
        self.assertEqual(candidate({'input':'name: Install {{ package }}'})[1],'unresolved_jinja')
        self.assertEqual(candidate({'input':'name: Install packages'})[1],'no_concrete_object')
        self.assertEqual(candidate({'input':'name: Check nginx','output':'ansible.builtin.assert:\n  that: true\n'})[1],'excluded_task_style')
        self.assertTrue(candidate({'input':'name: Ensure unzip is installed.'})[0])
    def test_unsupported_fql_objects_are_not_filtered(self):
        row={'input':'name: Install quantumwidget'}
        self.assertTrue(candidate(row)[0]);self.assertEqual(support_hint(normalize(row['input'])),'may_require_package_kb_entry')
        self.assertFalse(module_style('block:\n  - debug:\n      msg: hi\n'))
    def test_classifier_contract_and_no_implementation_context(self):
        cell={'label_ids':['n1']}
        valid={'status':'completed','text':'[{"id":"n1","keep":true,"reason":"concrete_self_contained"}]'}
        with patch.object(transport,'request',return_value=valid):self.assertTrue(d.classify_request(cell,{})['labels'][0]['keep'])
        bad={'status':'completed','text':'[{"id":"n1","keep":true,"reason":"missing_path"}]'}
        with patch.object(transport,'request',return_value=bad):self.assertEqual(d.classify_request(cell,{})['error'],'classifier_format_error')
    def test_frozen_generation_has_one_call_per_model_and_exact_demos(self):
        with tempfile.TemporaryDirectory() as tmp:
            run=Path(tmp);p=run/'private';(p/'filter').mkdir(parents=True)
            catalog={m['id']:{'limit':{'output':32768},'cost':{'input':0.1,'output':0.2,'cache_read':0.01,'cache_write':0.1}} for m in d.ev.load(d.ROOT/'configs/models.json')['models'].values() if m['provider']=='agentfanclub'}
            d.save(p/'router-catalog.json',catalog);d.save(p/'sample.json',[{'task_id':'d00001','nl':'Install quantumwidget'}]);d.save(p/'filter/state.json',{'attempts':[]});d.save(p/'filter/manifest.json',{'source':{'file_sha256':'fixture'}})
            with patch('sys.stdout',new=io.StringIO()):m=d.freeze_generation(run)
            self.assertEqual(len(m['cells']),6)
            for c in m['cells']:
                self.assertEqual(c['repeat'],0);self.assertEqual(c['demonstration_ids'],['a13','a02','a03','a19'])
                self.assertEqual(c['messages'][-1],{'role':'user','content':'Install quantumwidget'})
                self.assertEqual(len(c['messages']),10)
            self.assertEqual(m['config']['max_output_tokens'],32768)
            self.assertEqual(m['config']['provider_budgets_usd']['anthropic'],8)
