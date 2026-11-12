import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
import matrix_run as mr
import evaluate as ev

class MatrixTests(unittest.TestCase):
    def manifest(self):
        c=ev.load(ev.ROOT/'configs/models.json')
        cells=[{'id':f'cell-{i}','model':m,'messages':[{'role':'system','content':'guide'},{'role':'user','content':'query'}]} for i,m in enumerate(['opus','opus','sol'])]
        return {'config':c,'cells':cells}
    def test_retries_and_resumes_without_duplicate_success(self):
        m=self.manifest();m['cells']=m['cells'][:1]
        with tempfile.TemporaryDirectory() as tmp,patch.dict('os.environ',{'ANTHROPIC_API_KEY':'fixture'}),patch.object(mr.time,'sleep'),patch.object(ev,'request',side_effect=[TimeoutError(),{'status':'completed','text':'fql','usage':{'input_tokens':10,'output_tokens':20}}]) as req:
            out=Path(tmp);r=mr.Matrix(m,out);r.run(1)
            self.assertEqual(req.call_count,2)
            self.assertEqual(r.state['attempts'][0]['cost_source'],'conservative_unreported_usage')
            resumed=mr.Matrix(m,out);resumed.run(1)
            self.assertEqual(req.call_count,2)
    def test_anthropic_guard_preserves_remaining_and_allows_sol(self):
        m=self.manifest();cap=ev.reserve(m['cells'][0],m['config'])+.000148
        with tempfile.TemporaryDirectory() as tmp,patch.dict('os.environ',{'ANTHROPIC_API_KEY':'fixture','OPENAI_API_KEY':'fixture'}),patch.object(ev,'request',return_value={'status':'completed','text':'fql','usage':None}) as req:
            out=Path(tmp);r=mr.Matrix(m,out,anthropic=cap);r.run(1)
            self.assertEqual(req.call_count,2)
            self.assertFalse((out/'responses/cell-1.json').exists())
            resumed=mr.Matrix(m,out,anthropic=cap*3);resumed.run(1)
            self.assertEqual(req.call_count,3)
            resumed.run(1);self.assertEqual(req.call_count,3)
    def test_usage_cache_and_output_pricing(self):
        m=self.manifest()['config']['models']['opus']
        cost,source=mr.usage_cost({'usage':{'input_tokens':100,'output_tokens':20,'cache_creation_input_tokens':10,'cache_read_input_tokens':50}},m,10)
        self.assertAlmostEqual(cost,.00086)
        self.assertEqual(source,'reported_tokens_at_frozen_rates')

class ExportTests(unittest.TestCase):
    def test_wilson_is_nonzero_for_perfect_or_zero_small_samples(self):
        from export_matrix import wilson
        lo,hi=wilson(10,10);self.assertAlmostEqual(hi,1);self.assertGreater(lo,.7)
        lo,hi=wilson(0,10);self.assertAlmostEqual(lo,0);self.assertGreater(hi,.2)
    def test_top_level_router_reasoning_and_cache_write_pricing(self):
        from export_matrix import totals
        self.assertEqual(totals([{'usage':{'prompt_tokens':100,'completion_tokens':12,'reasoning_tokens':9}}],'agentfanclub'),(100,12,9))
        m=ev.load(ev.ROOT/'configs/models.json')['models']['sol']
        cost,_=mr.usage_cost({'usage':{'input_tokens':100,'output_tokens':10,'input_tokens_details':{'cached_tokens':50,'cache_write_tokens':20}}},m,1)
        self.assertAlmostEqual(cost,.000215)
    def test_gateway_524_is_transient_and_unreported_usage_stays_charged(self):
        self.assertTrue(mr.retryable({'status':'provider_error','http_status':524}))
        self.assertFalse(mr.retryable({'status':'provider_error','http_status':400}))
        model=ev.load(ev.ROOT/'configs/models.json')['models']['opus']
        self.assertEqual(mr.usage_cost({'usage':None},model,.2),(.2,'conservative_unreported_usage'))
