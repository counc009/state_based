#!/usr/bin/env python3
"""Offline, idempotent overlay of separately funded missing-cell generation."""
import argparse,copy,json,os,shutil,time
from functools import lru_cache
from collections import Counter,defaultdict
from datetime import datetime,timezone,timedelta
from pathlib import Path
import evaluate as ev
from export_matrix import write_csv

ROOT=ev.ROOT;BASE=ROOT/'results/2026-11-12-dataset-validity';OPEN=BASE/'openkb-prompt';FILL=BASE/'fill-in-2026-11-12';PHASE='fill-in-2026-11-12'
RUNS={'original':BASE,'openkb':OPEN}


def save(path,value):
 path.parent.mkdir(parents=True,exist_ok=True);tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2)+'\n');os.replace(tmp,path)
def charged(a):return a.get('cost_usd',a['reserved_usd'])
def split_cost(attempts):
 return {'accounted_usd':sum(charged(a)for a in attempts),'known_token_usd':sum(charged(a)for a in attempts if a.get('cost_source')=='reported_tokens_at_frozen_rates'),'unknown_billing_reserve_usd':sum(charged(a)for a in attempts if a.get('cost_source')!='reported_tokens_at_frozen_rates'),'anthropic_usd':sum(charged(a)for a in attempts if a['provider']=='anthropic'),'attempts':len(attempts)}
def root_for(label):return RUNS[label]


def snapshot():
 marker=FILL/'private/pre-fill-snapshot.json'
 if marker.exists():return ev.load(marker)
 snapshots=[];protected=[]
 before=ev.load(FILL/'private/completed-before.json')
 for label,run in RUNS.items():
  files=[p for p in run.rglob('*')if p.is_file()and 'private'not in p.relative_to(run).parts and not p.is_relative_to(FILL)and not(label=='original'and p.is_relative_to(OPEN))]
  for source in files:
   relative=source.relative_to(run);dest=FILL/'pre-fill'/label/relative;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest)
   snapshots.append({'run':label,'path':str(relative),'sha256':ev.digest(source.read_bytes()),'snapshot_path':str(dest.relative_to(FILL))})
  private=run/'private/generation'
  for name in ['manifest.json','state.json']:
   source=private/name;dest=FILL/'private/pre-fill'/label/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest)
  rows=ev.load(run/'per-cell.json')
  for row in rows:
   if not row.get('output_path'):continue
   source=run/row['output_path'];response=private/'responses'/(row['cell_id']+'.json');key=label+'/'+row['cell_id'];assert key in before
   assert ev.digest(source.read_bytes())==before[key]['text_sha256']and ev.digest(response.read_bytes())==before[key]['response_sha256']
   protected.append({'run':label,'cell_id':row['cell_id'],'output_path':row['output_path'],'output_sha256':ev.digest(source.read_bytes()),'response_sha256':ev.digest(response.read_bytes())})
 assert len(protected)==len(before)==3459
 result={'created_at':datetime.now(timezone.utc).isoformat(),'protected_completed':len(protected),'public_snapshot_files':len(snapshots),'public_files':snapshots,'protected_outputs':protected}
 save(marker,result);save(FILL/'pre-fill/index.json',{'created_at':result['created_at'],'protected_completed':len(protected),'public_snapshot_files':len(snapshots),'public_files':snapshots});save(FILL/'completed-preservation.json',protected)
 print(json.dumps({'snapshot_files':len(snapshots),'protected_completed':len(protected)}),flush=True);return result


def phase_accounting(run):
 marker=run/'private/generation/fill-overlay.json'
 if not marker.exists():return None
 own=ev.load(run/'private/generation/state.json')['attempts'];initial=[a for a in own if a.get('funding_phase')!=PHASE];added=[a for a in own if a.get('funding_phase')==PHASE]
 original=run.resolve()==BASE.resolve()
 classifier=ev.load(BASE/'private/filter/state.json')['attempts']if original else[]
 initial_cost=split_cost(classifier+initial);allocated=split_cost(added);fresh=ev.load(FILL/'private/generation/state.json')['attempts'];fresh_cost=split_cost(fresh)
 assert not any(a['status']=='in_flight'for a in fresh)
 assert fresh_cost['accounted_usd']<=6+1e-8 and fresh_cost['anthropic_usd']<=3+1e-8
 assert initial_cost['accounted_usd']<=(20 if original else 12)+1e-8 and initial_cost['anthropic_usd']<=(8 if original else 7)+1e-8
 assert len({(a['cell_id'],a['phase_attempt'])for a in added})==len(added)
 return {'phase':PHASE,'initial_guard_usd':20 if original else 12,'initial_anthropic_guard_usd':8 if original else 7,'initial':initial_cost,'fill_allocated_to_run':allocated,'fill_shared_guard_usd':6,'fill_shared_anthropic_guard_usd':3,'fill_shared':fresh_cost,'cumulative':split_cost(classifier+own),'note':'Historical guards apply to their original phases. Fill is separately authorized and counted once globally; KB scoring has no generation charge.'}


@lru_cache(maxsize=8)
def _fill_context(root,manifest_mtime,state_mtime):
 folder=Path(root);manifest=ev.load(folder/'private/generation/manifest.json');attempts=ev.load(folder/'private/generation/state.json')['attempts'];grouped=defaultdict(list)
 for a in attempts:grouped[a['cell_id']].append(a)
 return manifest,{c['id']:c for c in manifest['cells']},grouped,split_cost(attempts)


def canonical_response(run,ident,path):
 response=ev.load(path)if path.exists()else {'status':'pending_budget','text':''}
 if not(run/'private/generation/fill-overlay.json').exists()or response.get('status')in('completed','incomplete'):return response
 mp=FILL/'private/generation/manifest.json';sp=FILL/'private/generation/state.json';manifest,cells,grouped,spend=_fill_context(str(FILL),mp.stat().st_mtime_ns,sp.stat().st_mtime_ns)
 if ident not in manifest['origins']:return response
 source=FILL/'private/generation/responses'/(ident+'.json')
 if source.exists():return response
 attempts=grouped[ident];cell=cells[ident];model=manifest['config']['models'][cell['model']]
 billing=model['provider']=='anthropic'and(FILL/'private/generation/anthropic-billing-stop.json').exists()
 blocked=spend['accounted_usd']+ev.reserve(cell,manifest['config'])>6+1e-9 or model['provider']=='anthropic'and spend['anthropic_usd']+ev.reserve(cell,manifest['config'])>3+1e-9
 deadline=datetime.fromisoformat(ev.load(FILL/'private/job-start.json')['deadline_at']).timestamp()<=time.time()
 status='interrupted_deadline'if attempts and attempts[-1]['status']=='interrupted_unknown_billing'else'pending_billing'if billing else'pending_budget'if blocked else'pending_deadline'if deadline else'pending_controller_stop'
 return {'status':status,'text':'','funding_phase':PHASE,'error':'No provider output available when the separately funded fill phase stopped'}


def import_attempts():
 snap=snapshot();m=ev.load(FILL/'private/generation/manifest.json');state=ev.load(FILL/'private/generation/state.json');assert not any(a['status']=='in_flight'for a in state['attempts'])
 byid={c['id']:c for c in m['cells']};origins=m['origins'];assert len(byid)==141
 snapshots={label:ev.load(FILL/'private/pre-fill'/label/'state.json')for label in RUNS}
 imports=[]
 for label,run in RUNS.items():
  oldrows={r['cell_id']:r for r in ev.load(FILL/'pre-fill'/label/'per-cell.json')}
  for ident,origin in origins.items():
   if origin['run']!=label:continue
   assert not oldrows[ident].get('output_path'),'Completed output is outside the fill scope'
   canonical=run/'private/generation/responses'/(ident+'.json')
   if canonical.exists():
    existing_response=ev.load(canonical)
    assert existing_response.get('status')not in('completed','incomplete')or existing_response.get('funding_phase')==PHASE,'Existing completed canonical is protected'
 for label,run in RUNS.items():
  out=run/'private/generation';target=ev.load(out/'state.json');source_manifest=ev.load(out/'manifest.json');targets={c['id']:c for c in source_manifest['cells']}
  oldrows={r['cell_id']:r for r in ev.load(FILL/'pre-fill'/label/'per-cell.json')};existing={(a['cell_id'],a.get('phase_attempt')):a for a in target['attempts']if a.get('funding_phase')==PHASE}
  for a in state['attempts']:
   ident=a['cell_id']
   if origins[ident]['run']!=label:continue
   assert not oldrows[ident].get('output_path'),'Refusing to replace an existing model output'
   assert byid[ident]['messages']==targets[ident]['messages']
   key=(ident,a['attempt']);source=FILL/'private/generation/attempts'/(ident+f'--attempt{a["attempt"]}.json');receipt=ev.load(source)
   assert receipt['request_body']==a['request_body']
   if key in existing:
    new=existing[key];assert new['fill_source_receipt_sha256']==ev.digest(source.read_bytes())
   else:
    index=max([x['attempt']for x in target['attempts']if x['cell_id']==ident]+[0])+1
    metadata={'funding_phase':PHASE,'phase_attempt':a['attempt'],'fill_source_manifest_sha256':ev.digest(m),'fill_source_receipt_sha256':ev.digest(source.read_bytes()),'fill_source_cell_id':ident,'fill_source_run':label}
    new={**copy.deepcopy(a),'attempt':index,**metadata};converted={**copy.deepcopy(receipt),'attempt':index,**metadata}
    dest=out/'attempts'/(ident+f'--attempt{index}.json')
    if dest.exists():assert ev.load(dest)==converted,'Existing attempt collision; no overwrite allowed'
    else:ev.write_new(dest,converted)
    target['attempts'].append(new);existing[key]=new
   imports.append({'run':label,'cell_id':ident,'source_attempt':a['attempt'],'target_attempt':new['attempt'],'source_receipt_sha256':ev.digest(source.read_bytes()),'cost_usd':charged(a),'status':a['status']})
  # Old entries stay byte-for-byte equivalent as JSON objects; new entries only append.
  old=snapshots[label]['attempts'];assert target['attempts'][:len(old)]==old
  save(out/'state.json',target)
  updated=[]
  for ident,origin in origins.items():
   if origin['run']!=label:continue
   source=FILL/'private/generation/responses'/(ident+'.json')
   if not source.exists():continue
   result=ev.load(source);key=(ident,result['attempt']);assert key in existing;new=existing[key]
   canonical=out/'responses'/(ident+'.json');replacement=ev.load(out/'attempts'/(ident+f'--attempt{new["attempt"]}.json'))
   if canonical.exists():
    old_bytes=canonical.read_bytes();prior=ev.load(canonical)
    if prior.get('funding_phase')==PHASE:assert prior==replacement;continue
    assert prior['status']not in('completed','incomplete'),'Existing response protected'
    archive=out/'terminal-history'/(ident+'--before-'+PHASE+'.json');archive.parent.mkdir(exist_ok=True)
    if archive.exists():assert archive.read_bytes()==old_bytes
    else:archive.write_bytes(old_bytes)
   save(canonical,replacement);updated.append({'cell_id':ident,'status':replacement['status'],'attempt':new['attempt']})
  previous=ev.load(out/'fill-overlay.json')if(out/'fill-overlay.json').exists()else{}
  known={(x['cell_id'],x['attempt'])for x in previous.get('canonical_updates',[])}
  updated=previous.get('canonical_updates',[])+[x for x in updated if(x['cell_id'],x['attempt'])not in known]
  save(out/'fill-overlay.json',{'phase':PHASE,'fill_manifest_sha256':ev.digest(m),'initial_state_sha256':ev.digest(snapshots[label]),'initial_attempts':len(old),'imported_attempts':sum(x['run']==label for x in imports),'canonical_updates':updated})
 save(FILL/'import-map.json',imports);verify_completed(snap);return imports


def verify_completed(snap=None):
 snap=snap or ev.load(FILL/'private/pre-fill-snapshot.json')
 for row in snap['protected_outputs']:
  run=RUNS[row['run']];assert ev.digest((run/row['output_path']).read_bytes())==row['output_sha256']
  assert ev.digest((run/'private/generation/responses'/(row['cell_id']+'.json')).read_bytes())==row['response_sha256']
 for row in snap['public_files']:assert ev.digest((FILL/row['snapshot_path']).read_bytes())==row['sha256']
 return len(snap['protected_outputs'])


def snapshot_baseline_audit():
 snap=ev.load(FILL/'private/pre-fill-snapshot.json');old=ev.load(FILL/'pre-fill/openkb/baseline-unchanged-audit.json');verify_completed(snap)
 return {'baseline_commit':old['baseline_commit'],'files':old['files'],'all_original_exports_unchanged':False,'pre_fill_original_exports_preserved':True,'original_exports_intentionally_refreshed':True,'pre_fill_snapshot_index_sha256':ev.digest((FILL/'pre-fill/index.json').read_bytes()),'protected_completed_outputs':len(snap['protected_outputs']),'note':'Historical unchanged audit is frozen under pre-fill/openkb; refreshed exports now include authorized fill responses.'}


def fill_supervisor_alive():
 path=FILL/'private/supervisor-pid.json'
 if not path.exists():return False
 pid=ev.load(path)['supervisor']
 try:
  args=Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\0');state=Path(f'/proc/{pid}/stat').read_text().split()[2]
  return state!='Z'and any(b'fill_dataset.py'in x for x in args)and b'run'in args
 except FileNotFoundError:return False


def reconcile_fill():
 out=FILL/'private/generation';state=ev.load(out/'state.json');backup=out/'state-before-finalization.json'
 if not backup.exists():ev.write_new(backup,state)
 previous=ev.load(FILL/'receipt-recovery.json')if(FILL/'receipt-recovery.json').exists()else{};events=previous.get('events',[]);last={a['cell_id']:a for a in state['attempts']}
 for a in state['attempts']:
  path=out/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json');raw=None
  if path.exists():
   try:raw=ev.load(path)
   except(ValueError,OSError):
    keep=path.with_suffix('.partial-preserved');path.rename(keep);events.append({'cell_id':a['cell_id'],'attempt':a['attempt'],'action':'preserve_partial_attempt','sha256':ev.digest(keep.read_bytes())})
  real=isinstance(raw,dict)and {'cell_id','attempt','status','cost_usd','cost_source','request_body'}<=raw.keys()and raw['status']in('completed','incomplete','provider_error','transport_error')
  if real:
   assert raw['cell_id']==a['cell_id']and raw['attempt']==a['attempt']and raw['request_body']==a['request_body']
   if a['status']in('in_flight','interrupted_unknown_billing'):
    events.append({'cell_id':a['cell_id'],'attempt':a['attempt'],'action':'recover_durable_receipt','prior_status':a['status'],'status':raw['status']})
    for key in ['status','cost_usd','cost_source','seconds','http_status']:
     if key in raw:a[key]=raw[key]
   from matrix_run import retryable
   terminal=raw['status']in('completed','incomplete')or not retryable(raw)or a['attempt']>=6
   canonical=out/'responses'/(a['cell_id']+'.json');valid=False
   if canonical.exists():
    try:ev.load(canonical);valid=True
    except(ValueError,OSError):canonical.rename(canonical.with_suffix('.partial-preserved'))
   if a is last[a['cell_id']]and terminal and not valid:
    ev.write_new(canonical,raw);events.append({'cell_id':a['cell_id'],'attempt':a['attempt'],'action':'recover_canonical','status':raw['status']})
  if a['status']=='in_flight':
   a.update(status='interrupted_unknown_billing',cost_usd=a['reserved_usd'],cost_source='conservative_interrupted_unknown_billing')
   if not path.exists():ev.write_new(path,{**a,'text':'','usage':None,'error':'Fill phase stopped with provider billing/output unknown; full reservation retained'})
 save(out/'state.json',state);result={'attempts':len(state['attempts']),'events':events,'state_sha256':ev.digest(state),'original_state_backup_sha256':ev.digest(backup.read_bytes())};save(FILL/'receipt-recovery.json',result);return result


def audit_all():
 from openkb_analyze import reported_price
 m=ev.load(FILL/'private/generation/manifest.json');fresh=ev.load(FILL/'private/generation/state.json');start=ev.load(FILL/'private/job-start.json');cells={c['id']:c for c in m['cells']};assert len(cells)==141
 count=Counter();quoted_total=0.
 for a in fresh['attempts']:
  count[a['cell_id']]+=1;assert count[a['cell_id']]<=6 and a['attempt']<=6
  assert datetime.fromisoformat(start['started_at'])<=datetime.fromisoformat(a['started_at'])<=datetime.fromisoformat(start['deadline_at'])
  c=cells[a['cell_id']];model=m['config']['models'][c['model']];body=a['request_body'];assert body['model']==model['id']and body.get('max_tokens',body.get('max_output_tokens'))==32768 and not {'temperature','top_p','seed'}&body.keys()
  if model['provider']=='anthropic':assert body['system']==c['messages'][0]['content']and body['messages']==c['messages'][1:]and body['output_config']['effort']=='high'
  else:assert body['messages']==c['messages']and body['reasoning_effort']=='high'
  raw=ev.load(FILL/'private/generation/attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json'));quote=reported_price(raw.get('usage'),model)
  expected=quote if a['cost_source']=='reported_tokens_at_frozen_rates'else a['reserved_usd'];assert expected is not None and abs(expected-charged(a))<1e-8;quoted_total+=expected
 original=phase_accounting(BASE);opened=phase_accounting(OPEN);assert original and opened
 initial=[{'phase':'initial-original',**original['initial']},{'phase':'initial-openkb',**opened['initial']},{'phase':PHASE,**split_cost(fresh['attempts'])}]
 overall={key:sum(x[key]for x in initial)for key in ['accounted_usd','known_token_usd','unknown_billing_reserve_usd','anthropic_usd','attempts']}
 assert abs(overall['accounted_usd']-original['cumulative']['accounted_usd']-opened['cumulative']['accounted_usd'])<1e-8
 added=[a for label,run in RUNS.items()for a in ev.load(run/'private/generation/state.json')['attempts']if a.get('funding_phase')==PHASE]
 assert len(added)==len(fresh['attempts'])and abs(sum(charged(a)for a in added)-quoted_total)<1e-8
 rows=[]
 for label,run in RUNS.items():
  data=ev.load(run/'per-cell.json');rows.extend({'run':label,**r}for r in data);assert len(data)==1800
  ledger=ev.load(run/'private/generation/state.json')['attempts'];byid=defaultdict(list)
  for a in ledger:byid[a['cell_id']].append(a)
  for ident,chain in byid.items():assert [x['attempt']for x in chain]==sorted({x['attempt']for x in chain})
 opus=[a for a in fresh['attempts']if cells[a['cell_id']]['model']=='opus'];ds=[a for a in fresh['attempts']if cells[a['cell_id']]['model']=='deepseek-v4-flash']
 if opus and ds:
  first_ds=min(datetime.fromisoformat(a['started_at'])for a in ds)
  assert all(datetime.fromisoformat(a['started_at'])+timedelta(seconds=a.get('seconds',0))<=first_ds for a in opus)
 protected=verify_completed();assert protected==3459
 filled=[]
 for ident,c in cells.items():
  label=m['origins'][ident]['run'];row=next(r for r in rows if r['run']==label and r['cell_id']==ident);filled.append({'run':label,'cell_id':ident,'model':row['model'],'task_id':row['task_id'],'status':row['status'],'response':bool(row['output_path']),'parsed':row['parsed'],'semantic_accepted':row['semantic_accepted'],'interpreted':row['interpreted'],'output_sha256':row.get('output_sha256'),'canonical_output_path':str((RUNS[label]/row['output_path']).relative_to(BASE))if row.get('output_path')else None,'fill_attempts':count[ident],'fill_cost_usd':sum(charged(a)for a in fresh['attempts']if a['cell_id']==ident)})
 write_csv(FILL/'fill-per-cell.csv',filled);save(FILL/'fill-per-cell.json',filled)
 costs={'phases':initial,'cumulative':overall,'allocations':{'original':original,'openkb':opened},'fill_charge_counted_once':True};save(FILL/'cumulative-accounting.json',costs)
 validation={'protected_completed_outputs':protected,'old_completed_outputs_byte_identical':True,'pre_fill_public_snapshots_preserved':True,'filled_targets':141,'filled_available':sum(r['response']for r in filled),'remaining':sum(not r['response']for r in filled),'fill_physical_attempts':len(fresh['attempts']),'all_fill_attempts_at_most_six':True,'opus_stage_before_deepseek_verified':True,'same_messages_models_32768_high_no_seed':True,'phase_deadlines_respected':True,'independent_fill_repricing_passed':True,'monotonic_target_attempt_indices':True,'shared_fill_guard_usd':6,'shared_anthropic_guard_usd':3,'costs':costs}
 save(FILL/'validation.json',validation);return validation


def run(wait=False):
 snapshot()
 while not(FILL/'private/supervisor-result.json').exists()or fill_supervisor_alive():
  if not wait:raise RuntimeError('Fill supervisor is still active; no overlay allowed')
  time.sleep(5)
 reconcile_fill();import_attempts()
 import dataset_validity as dv
 import kb_rescore as kb
 import validate_dataset_validity as vd
 # Refresh original Example first so all later four-condition comparisons use its filled cohort.
 dv.score(BASE,16);dv.export(BASE);vd.validate(BASE);kb.rescore(BASE,BASE/'extended-kb',16)
 import openkb_analyze as opened
 opened.analyze(False)
 validation=audit_all()
 from dataset_validity import public_attempts
 manifest=ev.load(FILL/'private/generation/manifest.json');attempts=public_attempts(FILL,'generation',manifest)
 for a in attempts:a['funding_phase']=PHASE;a['phase_attempt']=a['attempt'];a['source_run']=manifest['origins'][a['cell_id']]['run']
 write_csv(FILL/'per-attempt.csv',attempts);save(FILL/'per-attempt.json',attempts)
 for source in(FILL/'private/source').glob('*'):
  if source.is_file():target=FILL/'sources'/source.name;target.parent.mkdir(exist_ok=True);shutil.copyfile(source,target)
 report={'experiment':'Separately funded missing-cell fill','started_at':ev.load(FILL/'private/job-start.json')['started_at'],'deadline_at':ev.load(FILL/'private/job-start.json')['deadline_at'],'finished_at':ev.load(FILL/'private/supervisor-result.json')['finished_at'],'execution':manifest['execution'],'sources':manifest['sources'],'models':manifest['config']['models'],'completed_before_unchanged':3459,'validation':validation,'privacy':'Only IDs/hashes, model outputs and prior public exports are published; corpus, source NL/YAML and provider reasoning remain private.'};save(FILL/'manifest.json',report)
 print(json.dumps({'fill_available':validation['filled_available'],'remaining':validation['remaining'],'costs':validation['costs']['cumulative']}),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('command',choices=['snapshot','run']);p.add_argument('--wait',action='store_true');a=p.parse_args();snapshot()if a.command=='snapshot'else run(a.wait)
