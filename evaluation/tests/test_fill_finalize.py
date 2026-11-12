"""Free overlay invariants: protected answers, phase costs, monotonic/idempotent history."""
import copy,json,sys,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
import evaluate as ev
import fill_finalize as ff

class FillFinalizeTests(unittest.TestCase):
 def fixture(self,root):
  base=root/'original';opened=root/'openkb';fill=root/'fill';runs={'original':base,'openkb':opened};cells=[];origins={};fresh=[];protected=[]
  for label,run in runs.items():
   (run/'private/generation/responses').mkdir(parents=True);(run/'private/generation/attempts').mkdir();(fill/'pre-fill'/label).mkdir(parents=True);(fill/'private/pre-fill'/label).mkdir(parents=True)
  for i in range(141):
   label='original'if i < 140 else 'openkb';ident=f'probe-{i}';c={'id':ident,'messages':[{'role':'user','content':'neutral'}]};cells.append(c);origins[ident]={'run':label}
   a={'cell_id':ident,'attempt':1,'status':'completed','provider':'agentfanclub','reserved_usd':.01,'cost_usd':.001,'cost_source':'reported_tokens_at_frozen_rates','request_body':{'model':'neutral'}};fresh.append(a)
   raw={**a,'text':'create directory at /neutral'}
   ff.save(fill/'private/generation/attempts'/(ident+'--attempt1.json'),raw);ff.save(fill/'private/generation/responses'/(ident+'.json'),raw)
  for label,run in runs.items():
   selected=[c for c in cells if origins[c['id']]['run']==label];rows=[{'cell_id':c['id'],'output_path':None}for c in selected];old=[]
   if label=='original':
    old=[{'cell_id':'probe-0','attempt':4,'status':'transport_error','provider':'agentfanclub','reserved_usd':.01,'cost_usd':.01,'request_body':{}}]
    ff.save(run/'private/generation/responses/probe-0.json',{'status':'transport_error','text':''})
    (run/'outputs').mkdir();(run/'outputs/kept.txt').write_text('immutable old answer\n');ff.save(run/'private/generation/responses/kept.json',{'status':'completed','text':'immutable old answer\n'})
    protected.append({'run':label,'cell_id':'kept','output_path':'outputs/kept.txt','output_sha256':ev.digest((run/'outputs/kept.txt').read_bytes()),'response_sha256':ev.digest((run/'private/generation/responses/kept.json').read_bytes())})
   ff.save(run/'private/generation/manifest.json',{'cells':selected});ff.save(run/'private/generation/state.json',{'attempts':old});ff.save(fill/'private/pre-fill'/label/'state.json',{'attempts':copy.deepcopy(old)});ff.save(fill/'pre-fill'/label/'per-cell.json',rows)
  ff.save(fill/'private/generation/manifest.json',{'cells':cells,'origins':origins});ff.save(fill/'private/generation/state.json',{'attempts':fresh})
  return base,opened,fill,runs,{'protected_outputs':protected,'public_files':[]}
 def test_import_is_monotonic_idempotent_and_preserves_old_answers_and_errors(self):
  with tempfile.TemporaryDirectory()as tmp:
   base,opened,fill,runs,snap=self.fixture(Path(tmp))
   old_response=(base/'private/generation/responses/probe-0.json').read_bytes();kept=(base/'private/generation/responses/kept.json').read_bytes()
   with patch.multiple(ff,BASE=base,OPEN=opened,FILL=fill,RUNS=runs),patch.object(ff,'snapshot',return_value=snap):
    first=ff.import_attempts();state=ev.load(base/'private/generation/state.json');second=ff.import_attempts();self.assertEqual(state,ev.load(base/'private/generation/state.json'))
   self.assertEqual(len(first),141);self.assertEqual(first,second);new=next(a for a in state['attempts']if a.get('funding_phase')==ff.PHASE and a['cell_id']=='probe-0');self.assertEqual(new['attempt'],5);self.assertEqual(new['phase_attempt'],1)
   self.assertEqual((base/'private/generation/responses/kept.json').read_bytes(),kept);self.assertEqual((base/'private/generation/terminal-history'/('probe-0--before-'+ff.PHASE+'.json')).read_bytes(),old_response)
 def test_preflight_rejects_already_available_target_before_import(self):
  with tempfile.TemporaryDirectory()as tmp:
   base,opened,fill,runs,snap=self.fixture(Path(tmp));rows=ev.load(fill/'pre-fill/original/per-cell.json');rows[1]['output_path']='outputs/already-present.txt';ff.save(fill/'pre-fill/original/per-cell.json',rows);before=(base/'private/generation/state.json').read_bytes()
   with patch.multiple(ff,BASE=base,OPEN=opened,FILL=fill,RUNS=runs),patch.object(ff,'snapshot',return_value=snap):
    with self.assertRaises(AssertionError):ff.import_attempts()
   self.assertEqual((base/'private/generation/state.json').read_bytes(),before);self.assertFalse((base/'private/generation/attempts/probe-0--attempt5.json').exists())
 def test_phase_accounting_counts_classifier_and_fill_once(self):
  with tempfile.TemporaryDirectory()as tmp:
   root=Path(tmp);base=root/'base';fill=root/'fill';old={'cell_id':'old','attempt':1,'provider':'anthropic','status':'completed','reserved_usd':.3,'cost_usd':.3,'cost_source':'reported_tokens_at_frozen_rates'};added={**old,'cell_id':'added','funding_phase':ff.PHASE,'phase_attempt':1,'cost_usd':.1}
   ff.save(base/'private/generation/fill-overlay.json',{});ff.save(base/'private/generation/state.json',{'attempts':[old,added]});ff.save(base/'private/filter/state.json',{'attempts':[{**old,'provider':'agentfanclub','cost_usd':.2}]});ff.save(fill/'private/generation/state.json',{'attempts':[{**added,'attempt':1}]})
   with patch.multiple(ff,BASE=base,FILL=fill):result=ff.phase_accounting(base)
   self.assertAlmostEqual(result['initial']['accounted_usd'],.5);self.assertAlmostEqual(result['fill_allocated_to_run']['accounted_usd'],.1);self.assertAlmostEqual(result['cumulative']['accounted_usd'],.6)

if __name__=='__main__':unittest.main()
