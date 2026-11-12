"""Offline guards for the separately funded, deadline-bounded open-KB prompt run."""
import io,json,sys,tempfile,threading,time,unittest,urllib.error
from datetime import datetime,timezone,timedelta
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
import openkb_prompt as job
import evaluate as ev
import openkb_analyze as analysis

class OpenKbTests(unittest.TestCase):
 def test_prompt_is_verbatim_base_plus_positive_extension(self):
  base=(job.ROOT/'prompts/handbook-v3.txt').read_bytes();new=(job.ROOT/'prompts/handbook-v3-openkb.txt').read_bytes()
  self.assertTrue(new.startswith(base));self.assertNotEqual(new,base)
  addition=new[len(base):].decode()
  self.assertIn('Unlisted packages and services may be named directly.',addition)
  self.assertIn('Deployments may add package and service entries',addition)
  self.assertTrue(addition.rstrip().endswith('Return only the formal query.'))
  registry=ev.load(job.ROOT/'prompts/registry.json');self.assertEqual(registry['handbook-v3-openkb']['parent_sha256'],ev.digest(base))
 def test_deadline_and_billing_stop_prevent_admission_only_for_affected_model(self):
  runner=job.BoundedMatrix.__new__(job.BoundedMatrix);runner.billing=threading.Event();runner.deadline=time.time()-1
  config={'models':{'opus':{'provider':'anthropic'},'sol':{'provider':'openai'}}}
  with patch.object(job.transport,'build',return_value=('url',{},{}))as build:
   with self.assertRaises(job.AdmissionStopped):runner.build({'model':'opus'},config)
   build.assert_not_called();runner.deadline=time.time()+60;runner.billing.set()
   with self.assertRaises(job.AdmissionStopped):runner.build({'model':'opus'},config)
   self.assertEqual(runner.build({'model':'sol'},config),('url',{},{}))
 def test_billing_error_marks_opus_stopped_and_preserves_error_receipt(self):
  with tempfile.TemporaryDirectory()as tmp:
   runner=job.BoundedMatrix.__new__(job.BoundedMatrix);runner.billing=threading.Event();runner.billing_file=Path(tmp)/'billing.json'
   error=urllib.error.HTTPError('https://api.anthropic.com/v1/messages',400,'bad request',{},io.BytesIO(b'{"error":{"message":"Your credit balance is too low"}}'))
   with patch.object(job.transport,'request',side_effect=error):r=runner.request({'model':'opus'},{'models':{'opus':{'provider':'anthropic'}}})
   self.assertTrue(runner.billing.is_set());self.assertTrue(runner.billing_file.exists());self.assertTrue(r['billing_error']);self.assertEqual(r['usage']['output_tokens'],0)
 def test_interruption_keeps_full_reserve_and_any_partial_attempt_artifact(self):
  with tempfile.TemporaryDirectory()as tmp:
   out=Path(tmp);(out/'attempts').mkdir();state={'attempts':[{'cell_id':'probe','attempt':1,'status':'in_flight','reserved_usd':.4}]};(out/'state.json').write_text(json.dumps(state))
   (out/'attempts/probe--attempt1.json').write_text('{partial')
   result=job.finalize_interrupted(out,{})
   self.assertEqual(result['attempts'][0]['cost_usd'],.4);self.assertEqual(result['attempts'][0]['status'],'interrupted_unknown_billing')
   self.assertEqual((out/'attempts/probe--attempt1.partial-preserved').read_text(),'{partial');self.assertIsNone(ev.load(out/'attempts/probe--attempt1.json')['usage'])
 def test_resume_cannot_reset_expired_wall_clock(self):
  with tempfile.TemporaryDirectory()as tmp:
   root=Path(tmp);private=root/'private';private.mkdir();old=datetime.now(timezone.utc)-timedelta(hours=1);start={'started_at':old.isoformat(),'deadline_at':(old+timedelta(minutes=35)).isoformat()};(private/'job-start.json').write_text(json.dumps(start))
   with patch.object(job,'RUN',root),patch.object(job,'freeze',return_value={}),patch.object(job.subprocess,'Popen')as spawn:job.supervise()
   spawn.assert_not_called();self.assertEqual(ev.load(private/'job-start.json'),start)
 def test_offline_recovers_durable_completed_receipt_without_discarding_old_ledger(self):
  with tempfile.TemporaryDirectory()as tmp:
   root=Path(tmp);out=root/'private/generation';(out/'attempts').mkdir(parents=True)
   state={'attempts':[{'cell_id':'probe','attempt':1,'status':'interrupted_unknown_billing','reserved_usd':.5,'cost_usd':.5,'request_body':{}}]}
   (out/'state.json').write_text(json.dumps(state));(out/'manifest.json').write_text('{}')
   receipt={'cell_id':'probe','attempt':1,'status':'completed','cost_usd':.02,'cost_source':'reported_tokens_at_frozen_rates','request_body':{},'usage':{'input_tokens':1,'output_tokens':1},'text':'create directory at /probe'}
   raw=out/'attempts/probe--attempt1.json';raw.write_text(json.dumps(receipt));original=raw.read_bytes()
   with patch.object(analysis,'RUN',root):result=analysis.recover_receipts()
   self.assertEqual(result['recovered_provider_receipts'],1);self.assertEqual(result['recovered_canonical_files'],1);self.assertEqual(raw.read_bytes(),original)
   self.assertEqual(ev.load(out/'state.json')['attempts'][0]['cost_usd'],.02);self.assertEqual(ev.load(out/'state-before-offline-recovery.json')['attempts'][0]['cost_usd'],.5)
 def test_offline_recovers_missing_canonical_after_state_already_completed(self):
  with tempfile.TemporaryDirectory()as tmp:
   root=Path(tmp);out=root/'private/generation';(out/'attempts').mkdir(parents=True);(out/'responses').mkdir()
   state={'attempts':[{'cell_id':'probe','attempt':1,'status':'completed','reserved_usd':.5,'cost_usd':.02,'request_body':{}}]}
   (out/'state.json').write_text(json.dumps(state));(out/'manifest.json').write_text('{}')
   receipt={'cell_id':'probe','attempt':1,'status':'completed','cost_usd':.02,'cost_source':'reported_tokens_at_frozen_rates','request_body':{},'text':'create directory at /probe'}
   (out/'attempts/probe--attempt1.json').write_text(json.dumps(receipt));(out/'responses/probe.json').write_text('{partial')
   with patch.object(analysis,'RUN',root):result=analysis.recover_receipts()
   self.assertEqual(result['recovered_provider_receipts'],0);self.assertEqual(result['recovered_canonical_files'],1);self.assertEqual(ev.load(out/'responses/probe.json')['text'],receipt['text']);self.assertEqual((out/'responses/probe.partial-preserved').read_text(),'{partial')
 @unittest.skipUnless((job.RUN/'private/generation/manifest.json').exists(),'Private frozen run unavailable')
 def test_frozen_1800_cells_change_only_system_prompt_and_variant(self):
  m=ev.load(job.RUN/'private/generation/manifest.json');base=ev.load(job.BASE/'private/generation/manifest.json');index={c['id']:c for c in base['cells']}
  self.assertEqual(len(m['cells']),1800);self.assertEqual(len({c['task_id']for c in m['cells']}),300)
  self.assertEqual(m['config']['models'],base['config']['models']);self.assertEqual(m['config']['max_output_tokens'],32768);self.assertEqual(m['execution']['max_attempts'],3)
  for c in m['cells']:
   old=index[c['id'].replace('--handbook-v3-openkb--','--handbook-v3--')]
   self.assertEqual(c['messages'][1:],old['messages'][1:]);self.assertEqual(c['demonstration_ids'],old['demonstration_ids'])

if __name__=='__main__':unittest.main()
