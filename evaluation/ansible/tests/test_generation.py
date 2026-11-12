import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
CODE=Path(__file__).resolve().parents[1]/'code';sys.path.insert(0,str(CODE))
import generate as g

class GenerationTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.data=Path(self.tmp.name)/'tasks.json'
        self.data.write_text(json.dumps([{'id':f'a{i+1:02}','legacy_id':problem,'natural_language':'Create directory /neutral/probe'} for i,problem in enumerate(g.PROBLEMS)]))
    def test_frozen_prompt_layout_and_unique_legacy_ids(self):
        m=g.freeze(self.data)
        self.assertEqual(len(m['cells']),1260)
        self.assertEqual({c['problem'] for c in m['cells']},set(g.PROBLEMS))
        self.assertEqual(len({c['id'] for c in m['cells']}),1260)
        self.assertIn('p11a',g.PROBLEMS);self.assertIn('p11b',g.PROBLEMS)
        for c in m['cells']:
            self.assertEqual(len(c['messages']),1);self.assertEqual(c['messages'][0]['role'],'user')
            t=next(t for t in m['tasks'] if t['task_id']==c['task_id'])
            self.assertEqual(c['messages'][0]['content'],m['prompt_template'].replace('{ task }',t['description']))
    def test_router_stream_usage_and_completion_preserved(self):
        wire=[{'model':'probe','choices':[{'delta':{'reasoning_content':'think'},'finish_reason':None}]},
              {'choices':[{'delta':{'content':'---\n'},'finish_reason':None}]},
              {'choices':[{'delta':{'content':'- hosts: all'},'finish_reason':'stop'}]},
              {'choices':[],'usage':{'prompt_tokens':10,'completion_tokens':20}}]
        data=b''.join(b'data: '+json.dumps(x).encode()+b'\n\n' for x in wire)+b'data: [DONE]\n'
        obj=g.collect_stream(io.BytesIO(data),'probe')
        self.assertEqual(obj['choices'][0]['message']['content'],'---\n- hosts: all')
        self.assertEqual(obj['usage']['completion_tokens'],20)
        self.assertTrue(obj['stream_record']['done_marker'])
        with self.assertRaises(g.urllib.error.URLError):g.collect_stream(io.BytesIO(b'data: {"error":"failed"}\n'),'probe')
    def test_request_settings_have_no_added_system_and_correct_efforts(self):
        m=g.freeze(self.data)
        with patch.dict('os.environ',{'OPENAI_API_KEY':'fixture','ANTHROPIC_API_KEY':'fixture','AGENTFANCLUB_API_KEY':'fixture','AGENTFANCLUB_BASE_URL':'https://api.router.agentfan.club/inference/v1'}):
            for key in m['config']['models']:
                c=next(c for c in m['cells'] if c['model']==key);url,body,headers=g.build(c,m['config'])
                self.assertNotIn('system',body)
                if key=='sol':self.assertEqual(body['reasoning'],{'effort':'high'})
                elif key=='opus':self.assertEqual(body['output_config'],{'effort':'high'})
                else:self.assertEqual(body['reasoning_effort'],'xhigh' if key=='qwen3.8-flash' else 'high');self.assertTrue(body['stream'])
    def test_larger_budget_changes_only_request_token_cap(self):
        import copy
        m=g.freeze(self.data)
        with patch.dict('os.environ',{'AGENTFANCLUB_API_KEY':'fixture','AGENTFANCLUB_BASE_URL':'https://api.router.agentfan.club/inference/v1'}):
            for key in ['deepseek-v4.1-flash','deepseek-v4-flash','qwen3.8-flash']:
                c=next(c for c in m['cells'] if c['model']==key)
                _,before,_=g.build(c,m['config'])
                config=copy.deepcopy(m['config']);config['max_output_tokens']=32768
                _,after,_=g.build(c,config)
                self.assertEqual(before.pop('max_tokens'),4096)
                self.assertEqual(after.pop('max_tokens'),32768)
                self.assertEqual(before,after)
                self.assertNotIn('seed',after)

    @unittest.skipUnless((g.REPO/'_build/default/evaluation/ansible/native/paper_process.exe').exists(),'Build the native processor for integration checks')
    def test_original_processor_retains_tasks_handlers_vars_and_pins_hosts(self):
        import subprocess
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);p=root/'fixture/p11b';p.mkdir(parents=True)
            p.joinpath('raw0.yml').write_text('- hosts: ignored\n  vars:\n    marker: value\n  tasks:\n    - debug:\n        msg: hello\n  handlers:\n    - name: notify\n      debug:\n        msg: handler\n')
            subprocess.run([str(g.REPO/'_build/default/evaluation/ansible/native/paper_process.exe'),'fixture'],cwd=root,check=True,capture_output=True)
            text=p.joinpath('response0.yml').read_text()
            self.assertIn('debian',text);self.assertNotIn('ignored',text);self.assertIn('handlers:',text);self.assertIn('marker:',text)
