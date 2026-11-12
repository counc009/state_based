#!/usr/bin/env python3
"""Separately funded open-KB prompt generation, bounded by a durable 35-minute wall clock."""
import argparse,copy,fcntl,json,os,signal,subprocess,sys,threading,time,urllib.error
from concurrent.futures import ThreadPoolExecutor,as_completed
from datetime import datetime,timezone,timedelta
from pathlib import Path
import evaluate as ev
from matrix_run import Matrix,TRANSIENT
import dataset_transport as transport
from dataset_validity import save,credentials,public_attempts,stop_reason
from export_matrix import totals,write_csv

ROOT=ev.ROOT
BASE=ROOT/'results/2026-11-12-dataset-validity'
RUN=BASE/'openkb-prompt'
ORDER=['opus','sol','glm-5.3','deepseek-v4.1-flash','qwen3.8-flash','deepseek-v4-flash']
WORKERS={'opus':16,'sol':16,'glm-5.3':32,'deepseek-v4.1-flash':64,'qwen3.8-flash':64,'deepseek-v4-flash':64}


def utc():return datetime.now(timezone.utc).isoformat()

def freeze():
 private=RUN/'private';path=private/'generation/manifest.json'
 if path.exists():return ev.load(path)
 source=ev.load(BASE/'private/generation/manifest.json');sample=ev.load(BASE/'private/sample.json')
 assert len(sample)==300 and len(source['cells'])==1800
 base=(ROOT/'prompts/handbook-v3.txt').read_bytes();prompt=(ROOT/'prompts/handbook-v3-openkb.txt').read_bytes()
 assert prompt.startswith(base) and prompt!=base
 m=copy.deepcopy(source);m['created_at']=utc();m['phase']='Open-KB prompt NL-to-FQL generation';m['scope']='Same private 300-case sample; only system prompt changes; parse/semantic/native validity only; no reference comparison or judge.'
 m['config'].update(prior_cost_usd=0,prior_anthropic_cost_usd=0,total_budget_usd=12,provider_budgets_usd={'anthropic':7},generation_model_workers=WORKERS,max_output_tokens=32768)
 for c,old in zip(m['cells'],source['cells']):
  assert c['variant']=='handbook-v3' and c['messages'][0]['content']==base.decode()
  c['id']=c['id'].replace('--handbook-v3--','--handbook-v3-openkb--');c['variant']='handbook-v3-openkb';c['messages'][0]['content']=prompt.decode()
  assert c['messages'][1:]==old['messages'][1:] and c['demonstration_ids']==old['demonstration_ids']
 m['cells'].sort(key=lambda c:(ORDER.index(c['model']),ev.digest(c['id'])))
 m['sources'].update(base_generation_manifest_sha256=ev.digest(source),base_system_sha256=ev.digest(base),handbook_sha256=ev.digest(prompt),openkb_driver_sha256=ev.digest(Path(__file__).read_bytes()),sample_sha256=ev.digest([{k:v for k,v in r.items() if k!='nl'} for r in sample]))
 m['execution']={'wall_clock_minutes':35,'max_attempts':3,'total_guard_usd':12,'anthropic_guard_usd':7,'priority':ORDER,'workers':WORKERS,'billing_policy':'Anthropic billing errors stop new Opus admission only'}
 save(path,m);save(private/'sample.json',sample)
 for sourcefile in [Path(__file__),ROOT/'code/dataset_transport.py',ROOT/'prompts/handbook-v3-openkb.txt',ROOT/'prompts/fixed-fql-demos-v1.json']:
  dest=private/'generation/source'/sourcefile.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(sourcefile.read_bytes())
 print(json.dumps({'planned':1800,'prompt_sha256':ev.digest(prompt),'base_prompt_preserved_verbatim':True,'models':ORDER,'max_output_tokens':32768,'guards':{'total':12,'anthropic':7}}),flush=True)
 return m


class AdmissionStopped(Exception):pass


class BoundedMatrix(Matrix):
 def __init__(self,m,out,start):
  self.deadline=datetime.fromisoformat(start['deadline_at']).timestamp();self.billing_file=out/'anthropic-billing-stop.json';self.billing=threading.Event()
  if self.billing_file.exists():self.billing.set()
  super().__init__(m,out,12,7,3,self.request,self.build)
 def build(self,cell,config):
  if time.time()>=self.deadline:raise AdmissionStopped('wall_clock_deadline')
  if config['models'][cell['model']]['provider']=='anthropic' and self.billing.is_set():raise AdmissionStopped('anthropic_billing_stop')
  return transport.build(cell,config)
 def request(self,cell,config):
  try:return transport.request(cell,config)
  except urllib.error.HTTPError as error:
   if config['models'][cell['model']]['provider']!='anthropic':raise
   body=error.read(10000).decode(errors='replace')
   for k,v in os.environ.items():
    if (k.endswith('_KEY') or k.endswith('_TOKEN')) and v:body=body.replace(v,'[REDACTED]')
   billing=error.code==402 or any(t in body.lower() for t in ('billing_error','credit balance','insufficient credit','insufficient_quota','purchase credits'))
   if billing:
    self.billing.set();save(self.billing_file,{'at':utc(),'http_status':error.code,'reason':'Anthropic billing/credit response; new Opus admission stopped','error':body})
   result={'status':'provider_error','http_status':error.code,'text':'','usage':None,'error':body,'billing_error':billing}
   if billing or error.code not in TRANSIENT:result['usage']={'input_tokens':0,'output_tokens':0}
   return result
 def process(self,cell):
  try:return super().process(cell)
  except AdmissionStopped:return


def child():
 credentials(Path('/tmp/astrogator-provider-env.json'));private=RUN/'private/generation';m=ev.load(private/'manifest.json');start=ev.load(RUN/'private/job-start.json')
 with (private/'.matrix.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);runner=BoundedMatrix(m,private,start)
  def model_loop(model):
   cells=[c for c in m['cells'] if c['model']==model]
   while time.time()<runner.deadline:
    if model=='opus' and runner.billing.is_set():return
    pending=[c for c in cells if not (private/'responses'/(c['id']+'.json')).exists()]
    if not pending:return
    with runner.lock:before=len(runner.state['attempts'])
    with ThreadPoolExecutor(max_workers=WORKERS[model]) as pool:
     for job in as_completed([pool.submit(runner.process,c) for c in pending]):job.result()
    with runner.lock:
     after=len(runner.state['attempts']);inflight=any(a['status']=='in_flight' for a in runner.state['attempts'])
     own_guard=model=='opus' and all(runner.spend('anthropic')+ev.reserve(c,m['config'])>7+1e-9 for c in pending)
     own_inflight=any(a['status']=='in_flight' and a['provider']=='anthropic' for a in runner.state['attempts'])
    if after==before:
     if not inflight or (own_guard and not own_inflight):return
     time.sleep(.5)
  with ThreadPoolExecutor(max_workers=6) as pool:
   jobs=[pool.submit(model_loop,model) for model in ORDER]
   for job in as_completed(jobs):job.result()


def finalize_interrupted(out,m):
 state=ev.load(out/'state.json')
 for a in state['attempts']:
  if a['status']!='in_flight':continue
  a.update(status='interrupted_unknown_billing',cost_usd=a['reserved_usd'],cost_source='conservative_interrupted_unknown_billing')
  path=out/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json')
  if path.exists():
   try:ev.load(path)
   except (ValueError,OSError):path.rename(path.with_suffix('.partial-preserved'))
  if not path.exists():ev.write_new(path,{**a,'text':'','usage':None,'error':'35-minute wall-clock supervisor stopped active request; billing unknown; full reservation retained'})
 save(out/'state.json',state)
 return state


def export_raw():
 private=RUN/'private';out=private/'generation';m=ev.load(out/'manifest.json');state=ev.load(out/'state.json');sample={r['task_id']:r for r in ev.load(private/'sample.json')};start=ev.load(private/'job-start.json')
 grouped={c['id']:[] for c in m['cells']}
 for a in state['attempts']:grouped[a['cell_id']].append(a)
 accounted=sum(a.get('cost_usd',a['reserved_usd']) for a in state['attempts']);anthropic_accounted=sum(a.get('cost_usd',a['reserved_usd']) for a in state['attempts'] if a['provider']=='anthropic')
 supervisor=ev.load(private/'supervisor-result.json') if (private/'supervisor-result.json').exists() else {}
 deadline_reached=supervisor.get('hard_deadline_reached',time.time()>=datetime.fromisoformat(start['deadline_at']).timestamp())
 rows=[]
 for c in m['cells']:
  model=m['config']['models'][c['model']];src=sample[c['task_id']];path=out/'responses'/(c['id']+'.json');receipts=grouped[c['id']]
  budget_blocked=accounted+ev.reserve(c,m['config'])>12+1e-9 or (model['provider']=='anthropic' and anthropic_accounted+ev.reserve(c,m['config'])>7+1e-9)
  missing='pending_billing' if model['provider']=='anthropic' and (out/'anthropic-billing-stop.json').exists() else 'pending_budget' if budget_blocked else 'pending_deadline' if deadline_reached else 'pending_controller_stop'
  interrupted=receipts and receipts[-1]['status']=='interrupted_unknown_billing'
  status=('interrupted_deadline' if deadline_reached else 'interrupted_controller_stop') if interrupted else missing
  response=ev.load(path) if path.exists() else {'status':status,'text':''}
  text=response.get('text','');target=None
  if response['status']in ('completed','incomplete'):
   dest=RUN/'outputs'/model['id']/(c['task_id']+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text);target=str(dest.relative_to(RUN))
  rawrecords=[ev.load(out/'attempts'/(c['id']+f'--attempt{a["attempt"]}.json')) for a in receipts];inp,output,reason=totals(rawrecords,model['provider'])
  raw=response.get('response',{});detail=(raw.get('incomplete_details')or{}).get('reason');finish=(raw.get('choices')or[{}])[0].get('finish_reason')or raw.get('stop_reason')or detail
  rows.append({**{k:src[k] for k in ['task_id','source_path','repo_path','row_index','input_sha256','nl_sha256','fql_support_hint']},'cell_id':c['id'],'model':model['id'],'variant':c['variant'],'repeat':0,'status':response['status'],'stop_reason':stop_reason(response),'output_cap_limited':finish in ('length','max_tokens','max_output_tokens'),'api_failure':response['status']in('provider_error','transport_error'),'deadline_stopped':response['status']in('pending_deadline','interrupted_deadline'),'output_nonempty':bool(text.strip()),'output_path':target,'output_sha256':ev.digest(text.encode())if target else None,'input_tokens':inp,'output_tokens':output,'reasoning_tokens':reason,'cost_usd':sum(a.get('cost_usd',a['reserved_usd'])for a in receipts),'attempts':len(receipts),'latency_s':sum(a['seconds'] for a in receipts) if receipts and all('seconds' in a for a in receipts) else None,'max_output_tokens':32768,'reasoning_effort':model['reasoning_effort'],'returned_model':response.get('returned_model'),'messages_sha256':ev.digest(c['messages']),'error':response.get('error','')})
 rows.sort(key=lambda r:(r['model'],r['row_index']));save(RUN/'per-cell.json',rows);write_csv(RUN/'per-cell.csv',rows)
 attempts=public_attempts(RUN,'generation',m);write_csv(RUN/'per-attempt.csv',attempts);save(RUN/'per-attempt.json',attempts)
 save(RUN/'sample-ids.json',[{k:r[k]for k in ['task_id','source_path','repo_path','row_index','input_sha256','nl_sha256']}for r in sample.values()])
 cost=sum(a.get('cost_usd',a['reserved_usd'])for a in state['attempts']);anthropic=sum(a.get('cost_usd',a['reserved_usd'])for a in state['attempts']if a['provider']=='anthropic');assert cost<=12+1e-8 and anthropic<=7+1e-8
 summary=[]
 for model in m['config']['models'].values():
  rs=[r for r in rows if r['model']==model['id']];summary.append({'model':model['id'],'n':len(rs),'attempted':sum(r['attempts'] > 0 for r in rs),'completed':sum(r['status']=='completed'for r in rs),'incomplete':sum(r['status']=='incomplete'for r in rs),'responses':sum(bool(r['output_path'])for r in rs),'api_failures':sum(r['api_failure']for r in rs),'deadline_stopped':sum(r['deadline_stopped']for r in rs),'pending_billing':sum(r['status']=='pending_billing'for r in rs),'pending_budget':sum(r['status']=='pending_budget'for r in rs),'controller_stopped':sum(r['status']in('pending_controller_stop','interrupted_controller_stop')for r in rs),'cost_usd':sum(r['cost_usd']for r in rs)})
 write_csv(RUN/'generation-summary.csv',summary)
 public={'experiment':'handbook-v3-openkb prompt variant','variant':'handbook-v3-openkb','models':m['config']['models'],'settings':m['execution'],'started_at':start['started_at'],'deadline_at':start['deadline_at'],'finished_at':supervisor.get('finished_at',utc()),'exported_at':utc(),'supervisor':supervisor,'sources':m['sources'],'baseline_manifest_sha256':m['sources']['base_generation_manifest_sha256'],'prompt_sha256':ev.digest((ROOT/'prompts/handbook-v3-openkb.txt').read_bytes()),'sampled':300,'planned':1800,'costs':{'accounted_usd':cost,'anthropic_usd':anthropic,'known_token_usd':sum(a['cost_usd']for a in attempts if a['cost_source']=='reported_tokens_at_frozen_rates'),'unknown_billing_reserve_usd':sum(a['cost_usd']for a in attempts if a['cost_source']!='reported_tokens_at_frozen_rates'),'notes':'Frozen-rate token accounting plus conservative reserves, not invoices.'},'summary':summary,'reference_comparison':False,'output_judge':False,'runtime_execution':False,'privacy':'Original NL, Ansible, full message manifests and provider reasoning stay private; IDs/hashes and model outputs only.'}
 marker=out/'anthropic-billing-stop.json'
 if marker.exists():
  try:public['anthropic_billing_stop']=ev.load(marker)
  except ValueError:public['anthropic_billing_stop']={'marker_exists':True,'details':'Partial marker retained; per-attempt error history preserved'}
 save(RUN/'manifest.json',public);print(json.dumps({'costs':public['costs'],'summary':summary}),flush=True)


def supervise():
 m=freeze();private=RUN/'private';startpath=private/'job-start.json'
 if not startpath.exists():
  now=datetime.now(timezone.utc);ev.write_new(startpath,{'started_at':now.isoformat(),'deadline_at':(now+timedelta(minutes=35)).isoformat(),'wall_clock_minutes':35})
 start=ev.load(startpath);deadline=datetime.fromisoformat(start['deadline_at']).timestamp();remaining=deadline-time.time()
 print(json.dumps({'started_at':start['started_at'],'deadline_at':start['deadline_at'],'max_attempts':3,'guards':{'total':12,'anthropic':7},'priority':ORDER,'workers':WORKERS}),flush=True)
 if remaining>0:
  proc=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'child'],start_new_session=True)
  try:proc.wait(timeout=remaining)
  except subprocess.TimeoutExpired:
   os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
  save(private/'supervisor-result.json',{'finished_at':utc(),'returncode':proc.returncode,'hard_deadline_reached':time.time()>=deadline})
 out=private/'generation'
 if (out/'state.json').exists():finalize_interrupted(out,m);export_raw()

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('command',choices=['freeze','run','child','export']);a=p.parse_args()
 if a.command=='freeze':freeze()
 elif a.command=='run':supervise()
 elif a.command=='child':child()
 else:export_raw()
