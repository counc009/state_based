"""Offline preservation and admission controls for the authorized missing-cell fill."""
import json,sys,tempfile,threading,time,unittest
from datetime import datetime,timezone,timedelta
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
import fill_dataset as job

class FillDatasetTests(unittest.TestCase):
 def test_new_ledger_has_only_the_authorized_guards(self):
  with tempfile.TemporaryDirectory()as tmp:
   m={'config':{'prior_cost_usd':0,'prior_anthropic_cost_usd':0},'cells':[]}
   r=job.FillMatrix(m,Path(tmp),{'deadline_at':(datetime.now(timezone.utc)+timedelta(minutes=40)).isoformat()})
   self.assertEqual((r.total,r.anthropic,r.max_attempts),(6,3,6));self.assertEqual(r.spend(),0)
 def test_expired_or_billing_paused_admission(self):
  r=job.FillMatrix.__new__(job.FillMatrix);r.deadline=time.time()-1;r.billing=threading.Event()
  with patch.object(job.transport,'build',return_value=('url',{},{}))as build:
   with self.assertRaises(job.AdmissionStopped):r.build({'model':'opus'},{})
   build.assert_not_called();r.deadline=time.time()+60;r.billing.set()
   with self.assertRaises(job.AdmissionStopped):r.build({'model':'opus'},{})
   self.assertEqual(r.build({'model':'deepseek-v4-flash'},{}),('url',{},{}))
 def test_expired_resume_does_not_reset_deadline_or_spawn_paid_work(self):
  with tempfile.TemporaryDirectory()as tmp:
   root=Path(tmp);(root/'private').mkdir();old=datetime.now(timezone.utc)-timedelta(hours=2)
   start={'started_at':old.isoformat(),'deadline_at':(old+timedelta(minutes=40)).isoformat()};(root/'private/job-start.json').write_text(json.dumps(start))
   with patch.object(job,'RUN',root),patch.object(job,'freeze',return_value={}),patch.object(job.subprocess,'Popen')as spawn:job.run()
   spawn.assert_not_called();self.assertEqual(job.ev.load(root/'private/job-start.json'),start)
 @unittest.skipUnless((job.RUN/'private/generation/manifest.json').exists(),'Private fill manifest unavailable')
 def test_exact_missing_targets_use_identical_frozen_requests(self):
  m=job.ev.load(job.RUN/'private/generation/manifest.json');before=job.ev.load(job.RUN/'private/completed-before.json')
  self.assertEqual(len(before),3459);self.assertEqual(len(m['cells']),141)
  self.assertEqual(sum(c['model']=='opus'for c in m['cells']),64)
  self.assertEqual(sum(c['model']=='deepseek-v4-flash'for c in m['cells']),77)
  self.assertTrue(all(c['model']=='opus'for c in m['cells'][:64]))
  self.assertEqual(m['config']['max_output_tokens'],32768)
  sources={name:job.ev.load((job.BASE if name=='original'else job.BASE/'openkb-prompt')/'private/generation/manifest.json')for name in ['original','openkb']}
  indexes={name:{c['id']:c for c in source['cells']}for name,source in sources.items()}
  for c in m['cells']:
   origin=m['origins'][c['id']]['run'];self.assertEqual(c,indexes[origin][c['id']]);self.assertNotIn(origin+'/'+c['id'],before)

if __name__=='__main__':unittest.main()
