#!/usr/bin/env python3
"""Free dual-KB scoring, four-condition comparisons and provenance checks for openkb prompt."""
import argparse,csv,json,time,hashlib,subprocess
from collections import Counter,defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
from pathlib import Path
import evaluate as ev
from export_matrix import write_csv
import kb_rescore as kb
from openkb_prompt import BASE,RUN,ROOT,export_raw,finalize_interrupted


def save(path,value):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(value,indent=2)+'\n')
def csvrows(path):return list(csv.DictReader(path.open()))


def reported_price(usage,model):
 if not isinstance(usage,dict):return None
 if model['provider']=='anthropic':
  if not {'input_tokens','output_tokens'}<=usage.keys():return None
  return (usage['input_tokens']*model['input_per_million']+usage.get('cache_creation_input_tokens',0)*model.get('cache_write_per_million',model['input_per_million'])+usage.get('cache_read_input_tokens',0)*model.get('cached_input_per_million',model['input_per_million'])+usage['output_tokens']*model['output_per_million'])/1e6
 inp=usage.get('input_tokens',usage.get('prompt_tokens'));out=usage.get('output_tokens',usage.get('completion_tokens'))
 if inp is None or out is None:return None
 detail=usage.get('input_tokens_details')or usage.get('prompt_tokens_details')or{};cached=detail.get('cached_tokens',0)or 0;writes=detail.get('cache_write_tokens',0)or 0
 return ((inp-cached)*model['input_per_million']+cached*model.get('cached_input_per_million',model['input_per_million'])+out*model['output_per_million']+writes*max(0,model.get('cache_write_per_million',model['input_per_million'])-model['input_per_million']))/1e6


def baseline_audit():
 commit='b9e9a06a1b23800fc00ae3c582fdaf579ac36185';repo=ROOT.parent;prefix=str(BASE.relative_to(repo))
 tree=subprocess.run(['git','ls-tree','-r','-z',commit,'--',prefix],cwd=repo,capture_output=True,check=True).stdout
 records=[]
 for entry in tree.split(b'\0'):
  if not entry:continue
  header,name=entry.split(b'\t',1);mode,kind,oid=header.decode().split();path=name.decode();assert kind=='blob'and mode in ('100644','100755')
  data=(repo/path).read_bytes();actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert actual==oid,path
  records.append({'path':path,'sha256':ev.digest(data),'baseline_git_blob':oid})
 result={'baseline_commit':commit,'files':len(records),'all_original_exports_unchanged':True,'aggregate_sha256':ev.digest(records),'file_hashes':records};save(RUN/'baseline-unchanged-audit.json',result);return result


def supervisor_alive():
 path=RUN/'private/supervisor-pid.json'
 if not path.exists():return False
 pid=ev.load(path)['pid']
 try:
  args=Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0');state=Path(f'/proc/{pid}/stat').read_text().split()[2]
  return state!='Z' and any(b'openkb_prompt.py' in arg for arg in args) and b'run' in args
 except FileNotFoundError:return False


def recover_receipts():
 out=RUN/'private/generation';m=ev.load(out/'manifest.json');state=ev.load(out/'state.json');before=ev.digest(state);backup=out/'state-before-offline-recovery.json'
 if not backup.exists():ev.write_new(backup,state)
 previous=ev.load(RUN/'receipt-recovery.json')if(RUN/'receipt-recovery.json').exists()else{};events=previous.get('events',[]);last={a['cell_id']:a for a in state['attempts']};changed=False
 for a in state['attempts']:
  path=out/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json')
  if not path.exists():continue
  try:r=ev.load(path)
  except(ValueError,OSError):continue
  required={'cell_id','attempt','status','cost_usd','cost_source','request_body'}
  if not required<=r.keys()or r['status']not in('completed','incomplete','provider_error','transport_error'):continue
  assert r['cell_id']==a['cell_id']and r['attempt']==a['attempt']and r['request_body']==a['request_body']
  if a['status']in('in_flight','interrupted_unknown_billing'):
   events.append({'cell_id':a['cell_id'],'attempt':a['attempt'],'action':'recover_durable_provider_receipt','prior_status':a['status'],'recovered_status':r['status'],'prior_cost_usd':a.get('cost_usd',a['reserved_usd']),'recovered_cost_usd':r['cost_usd']})
   for key in ['status','cost_usd','cost_source','seconds','http_status']:
    if key in r:a[key]=r[key]
   changed=True
  terminal=out/'responses'/(a['cell_id']+'.json');canonical_valid=False
  if terminal.exists():
   try:ev.load(terminal);canonical_valid=True
   except(ValueError,OSError):
    retained=terminal.with_suffix('.partial-preserved');terminal.rename(retained)
    events.append({'cell_id':a['cell_id'],'attempt':a['attempt'],'action':'preserve_partial_canonical','sha256':ev.digest(retained.read_bytes())})
  final=r['status']in('completed','incomplete')or r['status']=='provider_error'and r.get('http_status',0)not in __import__('matrix_run').TRANSIENT or a['attempt']>=3
  if a is last[a['cell_id']]and final and not canonical_valid:
   ev.write_new(terminal,r);events.append({'cell_id':a['cell_id'],'attempt':a['attempt'],'action':'recover_missing_canonical','status':r['status']})
 if changed:save(out/'state.json',state)
 # Any remaining interrupted operation has no complete provider receipt: preserve full reservation.
 state=finalize_interrupted(out,m)
 result={'checked_receipts':len(state['attempts']),'pre_recovery_state_sha256':before,'reconciled_state_sha256':ev.digest(state),'original_ledger_backup_sha256':ev.digest(backup.read_bytes()),'recovered_provider_receipts':sum(e['action']=='recover_durable_provider_receipt'for e in events),'recovered_canonical_files':sum(e['action']=='recover_missing_canonical'for e in events),'events':events}
 save(RUN/'receipt-recovery.json',result);return result


def analyze(wait=False):
 while True:
  ready=(RUN/'private/supervisor-result.json').exists()and not supervisor_alive()
  if ready:break
  if not wait:raise RuntimeError('Paid supervisor is still active; offline finalization must wait')
  time.sleep(5)
 recovery=recover_receipts();export_raw();manifest=ev.load(RUN/'manifest.json');rows=ev.load(RUN/'per-cell.json');assert len(rows)==1800
 manifest['receipt_recovery']=recovery;save(RUN/'manifest.json',manifest)
 cache=RUN/'private/example-flags';cache.mkdir(parents=True,exist_ok=True)
 texts={r['output_sha256']:(RUN/r['output_path']).read_text()for r in rows if r.get('output_path')}
 def check(item):
  digest,text=item;assert ev.digest(text.encode())==digest;path=cache/(digest+'.json')
  if not path.exists():save(path,kb.diagnose(text,'example'))
 with ThreadPoolExecutor(max_workers=16)as pool:list(pool.map(check,texts.items()))
 for row in rows:
  d=ev.load(cache/(row['output_sha256']+'.json'))if row.get('output_path')else None
  row.update(parsed=d['parsed']if d else None,semantic_accepted=d['semantic_accepted']if d else None,interpreted=d['interpreted']if d else None,interpreter_attempted=d['semantic_accepted']if d else False)
 save(RUN/'per-cell.json',rows);write_csv(RUN/'per-cell.csv',rows)
 evidence=kb.rescore(RUN,RUN/'dual-kb',16)
 manifest['distinct_normalized_descriptions']=len({r['nl_sha256']for r in rows})
 manifest['comparison_sources']={'baseline_per_cell_sha256':ev.digest((BASE/'per-cell.json').read_bytes()),'baseline_dual_summary_sha256':ev.digest((BASE/'extended-kb/model-summary.csv').read_bytes()),'analysis_driver_sha256':ev.digest(Path(__file__).read_bytes()),'current_export_driver_sha256':ev.digest((ROOT/'code/openkb_prompt.py').read_bytes()),'native_binary_sha256':{str(p.relative_to(ROOT.parent)):ev.digest(p.read_bytes())for p in [kb.BIN/'evaluation/native/effects.exe',kb.BIN/'evaluation/native/effects_fallback.exe',kb.BIN/'bin/query_interp.exe',kb.BIN/'evaluation/native/query_interp_fallback.exe']}}
 save(RUN/'manifest.json',manifest)
 original=BASE/'extended-kb';conditions=[];reasons=[];cross=[]
 original_raw=ev.load(BASE/'per-cell.json');raw_indexes={'original':{(r['model'],r['task_id']):r for r in original_raw},'openkb':{(r['model'],r['task_id']):r for r in rows}}
 for name,path in [('original',original),('openkb',RUN/'dual-kb')]:
  for r in csvrows(path/'model-summary.csv'):
   charge=sum(x['cost_usd']for x in raw_indexes[name].values()if x['model']==r['model'])
   conditions.append({'condition':name+'+'+r['kb'],'prompt':name,**{k:int(v)if k not in ('model','kb')else v for k,v in r.items()},'generation_cost_usd':charge,'offline_scoring_cost_usd':0})
  for r in csvrows(path/'rejection-reasons.csv'):reasons.append({'condition':name+'+'+r['kb'],'prompt':name,**{k:int(v)if k=='count'else v for k,v in r.items()}})
  for r in csvrows(path/'cross-model.csv'):cross.append({'condition':name+'+'+r['kb'],'prompt':name,**{k:int(v)if k!='kb'else v for k,v in r.items()}})
 write_csv(RUN/'four-condition-summary.csv',conditions);save(RUN/'four-condition-summary.json',conditions)
 write_csv(RUN/'four-condition-rejection-reasons.csv',reasons);write_csv(RUN/'four-condition-cross-model.csv',cross)
 old=ev.load(original/'per-cell.json');new=ev.load(RUN/'dual-kb/per-cell.json');index_old={(r['model'],r['task_id'],r['kb']):r for r in old};index_new={(r['model'],r['task_id'],r['kb']):r for r in new};paired=[]
 for model in sorted({r['model']for r in rows}):
  ids=[r['task_id']for r in rows if r['model']==model and index_old[(model,r['task_id'],'example')]['response']and index_new[(model,r['task_id'],'example')]['response']]
  for label,index in [('original',index_old),('openkb',index_new)]:
   for which in ['example','fallback']:
    rs=[index[(model,ident,which)]for ident in ids];paired.append({'model':model,'condition':label+'+'+which,'common_responses':len(rs),'parsed':sum(r['parsed']is True for r in rs),'semantic_accepted':sum(r['semantic_accepted']is True for r in rs),'interpreted':sum(r['interpreted']is True for r in rs),'generation_cost_usd_on_common_cells':sum(raw_indexes[label][(model,ident)]['cost_usd']for ident in ids),'offline_scoring_cost_usd':0})
 write_csv(RUN/'paired-available-summary.csv',paired)
 # Separate symbolic-interpretation failures from semantic rejection reasons.
 native=[]
 for prompt,path in [('original',original),('openkb',RUN/'dual-kb')]:
  source=ev.load(path/'per-cell.json')
  for model,which in sorted({(r['model'],r['kb'])for r in source}):
   rs=[r for r in source if r['model']==model and r['kb']==which and r['semantic_accepted']is True and r['interpreted']is not True]
   groups=Counter()
   for r in rs:
    d=ev.load(path/'private/cache'/(which+'-'+r['output_sha256']+'.json'));detail=d.get('native')or {}
    why=detail.get('error')or detail.get('stderr','').strip().split('\n')[0]or 'native query_interp nonzero'
    groups[(why,r.get('native_returncode'))]+=1
   for (why,code),n in groups.items():native.append({'condition':prompt+'+'+which,'model':model,'reason':why,'native_returncode':code,'count':n})
 if native:write_csv(RUN/'native-failures.csv',native)
 validate(rows,manifest,evidence)
 report(conditions,cross,manifest,rows)


def validate(rows,public,evidence):
 private=RUN/'private';m=ev.load(private/'generation/manifest.json');base=ev.load(BASE/'private/generation/manifest.json');oldcells={c['id']:c for c in base['cells']};state=ev.load(private/'generation/state.json')
 start=ev.load(private/'job-start.json');deadline=datetime.fromisoformat(start['deadline_at']);prompt=(ROOT/'prompts/handbook-v3-openkb.txt').read_bytes();oldprompt=(ROOT/'prompts/handbook-v3.txt').read_bytes()
 assert prompt.startswith(oldprompt)and prompt!=oldprompt
 assert m['config']['models']==base['config']['models']and m['config']['max_output_tokens']==base['config']['max_output_tokens']==32768
 assert len(m['cells'])==1800 and len({c['task_id']for c in m['cells']})==300
 assert len(rows)==1800 and len({r['cell_id']for r in rows})==1800
 for row in rows:
  assert not {'nl','input','natural_language','ansible','source_output'} & row.keys()
  if row.get('output_path'):
   response=ev.load(private/'generation/responses'/(row['cell_id']+'.json'))
   assert (RUN/row['output_path']).read_text()==response['text']
 for identity in ev.load(RUN/'sample-ids.json'):assert set(identity)=={'task_id','source_path','repo_path','row_index','input_sha256','nl_sha256'}
 oldsample={r['task_id']:r for r in ev.load(BASE/'private/sample.json')};sample={r['task_id']:r for r in ev.load(private/'sample.json')};assert sample==oldsample
 cells={c['id']:c for c in m['cells']}
 for c in m['cells']:
  old=oldcells[c['id'].replace('--handbook-v3-openkb--','--handbook-v3--')]
  assert c['messages'][0]['content']==prompt.decode()and c['messages'][1:]==old['messages'][1:]and c['demonstration_ids']==old['demonstration_ids']
 attempts=Counter();recomputed_total=0.;conservative_with_usage=0
 for a in state['attempts']:
  attempts[a['cell_id']]+=1;assert attempts[a['cell_id']]<=3 and a['attempt']<=3
  assert datetime.fromisoformat(a['started_at'])<=deadline
  c=cells[a['cell_id']];body=a['request_body'];model=m['config']['models'][c['model']]
  receipt=ev.load(private/'generation/attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json'))
  quoted=reported_price(receipt.get('usage'),model)
  if a['cost_source']=='reported_tokens_at_frozen_rates':assert quoted is not None;expected=quoted
  else:expected=a['reserved_usd'];conservative_with_usage+=quoted is not None
  assert abs(expected-a['cost_usd'])<1e-8;recomputed_total+=expected
  assert body['model']==model['id']and body.get('max_tokens',body.get('max_output_tokens'))==32768 and not {'temperature','top_p','seed'}&body.keys()
  effort=body.get('reasoning_effort',body.get('reasoning',{}).get('effort',body.get('output_config',{}).get('effort')));assert effort==model['reasoning_effort']
  if model['provider']=='openai':assert body['input']==c['messages']
  elif model['provider']=='anthropic':assert body['system']==c['messages'][0]['content']and body['messages']==c['messages'][1:]
  else:assert body['messages']==c['messages']
 assert abs(recomputed_total-public['costs']['accounted_usd'])<1e-8
 original_audit=baseline_audit()
 assert sum(r['cost_usd']for r in rows)<=12+1e-8
 assert sum(r['cost_usd']for r in rows if r['model']=='claude-opus-5-5')<=7+1e-8
 assert abs(sum(r['cost_usd']for r in rows)-public['costs']['accounted_usd'])<1e-8
 assert evidence['original_example_cell_flags_reproduced']and evidence['parse_flags_identical']
 assert evidence['source_hashes']==ev.load(BASE/'extended-kb/validation.json')['source_hashes']
 secrets=list(ev.load('/tmp/astrogator-provider-env.json').values())+[Path('/tmp/astrogator-gh-token').read_text().strip()]
 publicfiles=[p for p in RUN.rglob('*')if p.is_file()and 'private'not in p.relative_to(RUN).parts]
 for p in publicfiles:
  text=p.read_text()
  for value in secrets:
   if len(value)>20 and not value.startswith('https://'):assert value not in text,p
 result={'same_300_sample_rows':True,'distinct_normalized_descriptions':len({r['nl_sha256']for r in rows}),'same_demos_and_non_system_messages':True,'base_prompt_verbatim_prefix':True,'same_models_reasoning_32768_cap_and_seed_free_sampling':True,'all_attempts_within_three_attempt_limit':True,'all_admissions_before_deadline':True,'deadline_at':start['deadline_at'],'paid_cells':len(attempts),'physical_attempts':len(state['attempts']),'public_files_secret_audited':len(publicfiles),'secret_audit_passed':True,'budget_guards_respected':True,'independent_frozen_rate_repricing_passed':True,'recomputed_accounted_usd':recomputed_total,'conservative_receipts_with_reported_usage':conservative_with_usage,'original_export_files_unchanged':original_audit['files'],'baseline_git_commit':original_audit['baseline_commit'],'native_example_flags_reproduced':True,'native_sources_identical_to_offline_benchmark_invariance_audit':True,'parse_flags_identical_across_kbs':True,'known_token_usd':public['costs']['known_token_usd'],'unknown_billing_reserve_usd':public['costs']['unknown_billing_reserve_usd'],'accounted_usd':public['costs']['accounted_usd'],'anthropic_usd':public['costs']['anthropic_usd']}
 billing=private/'generation/anthropic-billing-stop.json'
 if billing.exists():
  try:result['anthropic_billing_stop']=ev.load(billing)
  except ValueError:result['anthropic_billing_stop']={'marker_exists':True,'details':'Partial marker preserved; see per-attempt error history'}
 save(RUN/'validation.json',result);print(json.dumps(result,indent=2),flush=True)


def report(conditions,cross,manifest,rows):
 models=['gpt-6.1-sol','claude-opus-5-5','glm-5.3','deepseek-v4.1-flash','qwen3.8-flash','deepseek-v4-flash'];lookup={(r['model'],r['condition']):r for r in conditions}
 lines=['# Open-KB prompt experiment','','Each cell below is grammar parses / semantic acceptance / native symbolic interpretation, out of the same 300 sampled rows (253 distinct normalized descriptions). These are validity counts, not intent correctness or execution tests. Response availability is reported separately.','','| Model | Original + Example | Original + fallback | Open prompt + Example | Open prompt + fallback |','|---|---:|---:|---:|---:|']
 for model in models:lines.append('| '+model+' | '+' | '.join(str(lookup[(model,c)]['parsed'])+' / '+str(lookup[(model,c)]['semantic_accepted'])+' / '+str(lookup[(model,c)]['interpreted'])for c in ['original+example','original+fallback','openkb+example','openkb+fallback'])+' |')
 availability=[]
 for model in models:
  rs=[r for r in rows if r['model']==model]
  availability.append({'model':model,'n':300,'original_responses':lookup[(model,'original+example')]['responses'],'openkb_responses':sum(bool(r['output_path'])for r in rs),'openkb_api_failures':sum(r['api_failure']for r in rs),'openkb_budget_pending':sum(r['status']=='pending_budget'for r in rs),'openkb_deadline_stopped':sum(r['deadline_stopped']for r in rs),'openkb_billing_pending':sum(r['status']=='pending_billing'for r in rs),'original_generation_cost_usd':lookup[(model,'original+example')]['generation_cost_usd'],'openkb_generation_cost_usd':lookup[(model,'openkb+example')]['generation_cost_usd']})
 write_csv(RUN/'response-availability.csv',availability)
 lines+=['','| Model | Original responses | Open responses | API failures | Budget pending | Deadline stopped | Billing pending |','|---|---:|---:|---:|---:|---:|---:|']
 for r in availability:lines.append('| '+r['model']+' | '+' | '.join(str(r[k])for k in ['original_responses','openkb_responses','openkb_api_failures','openkb_budget_pending','openkb_deadline_stopped','openkb_billing_pending'])+' |')
 lines+=['','| Condition | At least one semantically valid | All responding valid | All six responded and valid |','|---|---:|---:|---:|']
 for r in cross:lines.append(f"| {r['condition']} | {r['at_least_one_semantically_valid']} | {r['all_responding_models_semantically_valid']} | {r['all_six_responded_and_semantically_valid']} |")
 lines+=['',f"Paid generation start: {manifest['started_at']}; hard deadline: {manifest['deadline_at']}. Guard: $12 total / $7 Anthropic, three attempts maximum per cell.",'',f"Accounted USD {manifest['costs']['accounted_usd']:.12f} = known token charges {manifest['costs']['known_token_usd']:.12f} + unknown-billing reservations {manifest['costs']['unknown_billing_reserve_usd']:.12f}; Anthropic {manifest['costs']['anthropic_usd']:.12f}. Accounting at frozen rates is not a provider invoice.",'','The source corpus, NL/Ansible rows, private message manifests and provider reasoning remain private. IDs/hashes, generated formal queries, costs and native validity diagnostics are public. No LLM judge or managed-host runtime tests were used.','']
 (RUN/'report.md').write_text('\n'.join(lines));print('\n'.join(lines),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--wait',action='store_true');a=p.parse_args();analyze(a.wait)
