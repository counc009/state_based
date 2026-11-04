import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

CODE = Path(__file__).resolve().parents[1] / 'code'
sys.path.insert(0, str(CODE))
import evaluate as ev
from import_frozen import convert
from semantic_audit import directory_obligations


class ProtocolTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.messages = [{'role':'system','content':(ev.ROOT/'prompts/compact-v1.txt').read_text()},
                         {'role':'user','content':'Neutral example'}, {'role':'assistant','content':'create directory at /probe'},
                         {'role':'user','content':'Create directory /other'}]
        self.task = {'task_id':'probe','messages':self.messages,'demonstration_ids':['demo']}
        self.data = self.root/'input.json'
        self.data.write_text(json.dumps({'tasks':[self.task]}))

    def tearDown(self):
        self.tmp.cleanup()

    def manifest(self):
        return ev.freeze(self.data, ['sol'], ['compact-v1','handbook-v2'])

    def test_paired_prompts_keep_every_demo_and_target_and_five_repeats(self):
        m = self.manifest()
        self.assertEqual(len(m['cells']), 10)
        for variant in ['compact-v1','handbook-v2']:
            cells = [c for c in m['cells'] if c['variant']==variant]
            self.assertEqual({c['repeat'] for c in cells}, set(range(5)))
            for c in cells:
                self.assertEqual(c['messages'][1:], self.messages[1:])
        baseline = next(c for c in m['cells'] if c['variant']=='compact-v1')
        self.assertEqual(baseline['messages'], self.messages)

    def test_narrow_nl_check_does_not_use_gold_and_abstains_on_other_tasks(self):
        effects = [{'kind':'create_directory','destination':{'path':{'kind':'remote','destination':{'kind':'absolute','value':'/independent'}}}}]
        self.assertEqual(directory_obligations('Create directory /independent', effects)['status'],'specified_obligation_present')
        self.assertEqual(directory_obligations('Create directory /different', effects)['status'],'specified_obligation_missing')
        self.assertEqual(directory_obligations('Delete directory /independent', effects)['status'],'unsupported')

    def test_cache_write_ceiling_uses_documented_higher_input_rate(self):
        config={'max_output_tokens':1000,'models':{'fixture':{'provider':'openai','input_per_million':2,'cache_write_per_million':2.5,'output_per_million':10}}}
        cell={'model':'fixture','messages':[{'role':'user','content':'hello'}]}
        # 38 serialized UTF-8 bytes + 4096 framing, priced at $2.50/MTok; 1000 output at $10/MTok.
        self.assertAlmostEqual(ev.reserve(cell,config),0.020335)

    def test_openai_transport_sends_public_id_and_keeps_returned_identity(self):
        manifest=self.manifest();cell=manifest['cells'][0]
        response={'model':'gpt-6.1-sol','status':'completed','output':[{'content':[{'type':'output_text','text':'query'}]}]}
        with patch.dict('os.environ', {'OPENAI_API_KEY':'fixture'}), patch.object(ev.urllib.request,'urlopen',return_value=io.BytesIO(json.dumps(response).encode())) as mock:
            result=ev.request(cell,manifest['config'])
        req=mock.call_args.args[0]
        body=json.loads(req.data)
        self.assertEqual(req.full_url,'https://api.openai.com/v1/responses')
        self.assertEqual(body['model'],'gpt-6.1-sol')
        self.assertNotIn('tools',body)
        self.assertEqual(result['returned_model'],'gpt-6.1-sol')

    def test_target_leak_rejected(self):
        self.task['demonstration_ids'] = ['probe']
        self.data.write_text(json.dumps({'tasks':[self.task]}))
        with self.assertRaisesRegex(AssertionError, 'leaked'):
            self.manifest()

    def test_budget_reservation_and_resume_do_not_repeat_requests(self):
        m = self.manifest(); out = self.root/'run'
        limit = ev.reserve(m['cells'][0],m['config'])
        with patch.dict('os.environ', {'OPENAI_API_KEY':'fixture'}), patch.object(ev,'request',return_value={'status':'completed','text':'query'}) as req:
            first = ev.run(m,out,limit,10)
            self.assertEqual(first['new_calls'],1)
            second = ev.run(m,out,limit,10)
            self.assertEqual(second['new_calls'],0)
            self.assertEqual(req.call_count,1)
        summary = ev.analyze(out)
        statuses = [v['statuses'] for v in summary['results'].values()]
        self.assertEqual(sum(v.get('missing',0) for v in statuses),9)

    def test_interrupted_receipt_is_not_silently_retried(self):
        m = self.manifest(); out=self.root/'run'; out.mkdir()
        ev.write_new(out/'manifest.json',m)
        cell=m['cells'][0]
        (out/'attempts.jsonl').write_text(json.dumps({'id':cell['id'],'reserved_usd':ev.reserve(cell,m['config'])})+'\n')
        with patch.dict('os.environ', {'OPENAI_API_KEY':'fixture'}), patch.object(ev,'request') as req:
            result=ev.run(m,out,ev.reserve(cell,m['config']),10)
            req.assert_not_called()
        self.assertEqual(result['attempts'],1)

    def test_existing_run_cannot_change_frozen_config(self):
        m=self.manifest();out=self.root/'run';out.mkdir();ev.write_new(out/'manifest.json',m)
        m['config']['max_output_tokens']+=1
        with self.assertRaisesRegex(AssertionError,'manifest changed'):
            ev.run(m,out,1,1)

    def test_import_does_not_include_labels_or_code(self):
        source={'tasks':[dict(self.task,mode='fql',repeat=0,oracle_label='secret'),
                         {'mode':'judge','repeat':0,'code':'excluded'}]}
        rows=convert(source)
        self.assertEqual(set(rows[0]),{'task_id','demonstration_ids','messages'})

    def test_parser_runs_without_shell_and_preserves_raw_fences(self):
        m=self.manifest();out=self.root/'run';out.mkdir();ev.write_new(out/'manifest.json',m)
        ev.write_new(out/'responses'/(m['cells'][0]['id']+'.json'),{'status':'completed','text':'```fql\nquery\n```'})
        fake=self.root/'check.py'
        fake.write_text('import pathlib,sys\nassert pathlib.Path(sys.argv[1]).read_text().startswith("```fql")\n')
        report=ev.analyze(out, f'{sys.executable} {fake} {{query}}')
        self.assertEqual(sum(x['checker_pass'] for x in report['results'].values()),1)


if __name__ == '__main__':
    unittest.main()
