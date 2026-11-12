#!/usr/bin/env python3
"""Overlay authorized cap-only reruns, preserving the original ledger and completed files."""
import argparse
import copy
from datetime import datetime,timezone
import json
from pathlib import Path
import shutil
import tempfile
import time
from check_and_package import package
from generate import REPO
from export_matrix import totals,write_csv
import evaluate as ev


def reason(result):
    response=result.get('response',{})
    return response.get('stop_reason') or response.get('status') or (response.get('choices') or [{}])[0].get('finish_reason')


def repackage(run,workers=6):
    base=run/'private';fresh=base/'cap-32768';history=run/'history/cap-4096'
    original=ev.load(history/'manifest.json');m=ev.load(base/'manifest.json');state=ev.load(base/'state.json')
    fm=ev.load(fresh/'manifest.json');fs=ev.load(fresh/'state.json');status=ev.load(fresh/'run-status.json')
    selected=set(fm['refresh']['selected_cell_ids']);assert len(selected)==133
    extra=sum(a.get('cost_usd',a['reserved_usd']) for a in fs['attempts']);assert extra<=5+1e-9
    assert set(a['cell_id'] for a in fs['attempts'])<=selected
    assert all(a['provider']=='agentfanclub' for a in fs['attempts'])
    completed={r['cell_id']:r for r in original['calls'] if r['status']=='completed'}
    assert not selected.intersection(completed)
    for row in completed.values():
        if row['sample_path']:assert ev.digest((run/row['sample_path']).read_bytes())==row['sha256']
    oldattempts={a['cell_id']:a for a in state['attempts']};attempt_history=[];canonical={};phases={}
    with tempfile.TemporaryDirectory(prefix='astrogator-cap-overlay-') as tmp:
        stage=Path(tmp);merged=stage/'private';(merged/'attempts').mkdir(parents=True);(merged/'responses').mkdir()
        combined=copy.deepcopy(state);combined['attempts']=[];manifest=copy.deepcopy(m)
        for a in state['attempts']:
            record=copy.deepcopy(a);record.update(phase='initial-4096',phase_attempt=a['attempt']);combined['attempts'].append(record)
            raw=ev.load(base/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json'))
            ev.write_new(merged/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json'),raw)
        for a in fs['attempts']:
            assert a['request_body']['max_tokens']==32768
            oldbody=copy.deepcopy(oldattempts[a['cell_id']]['request_body']);newbody=copy.deepcopy(a['request_body'])
            assert oldbody.pop('max_tokens')==4096 and newbody.pop('max_tokens')==32768
            assert oldbody==newbody,'Only max_tokens may change in the actual request body'
            record=copy.deepcopy(a);record.update(attempt=a['attempt']+1,phase='cap-refresh-32768',phase_attempt=a['attempt']);combined['attempts'].append(record)
            raw=ev.load(fresh/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json'));raw['attempt']+=1
            ev.write_new(merged/'attempts'/(a['cell_id']+f'--attempt{record["attempt"]}.json'),raw)
        for c in manifest['cells']:
            path=fresh/'responses'/(c['id']+'.json');use_fresh=c['id'] in selected and path.exists()
            result=ev.load(path if use_fresh else base/'responses'/(c['id']+'.json'))
            if use_fresh:result['attempt']+=1
            canonical[c['id']]=result;phases[c['id']]='cap-refresh-32768' if use_fresh else 'initial-4096'
            ev.write_new(merged/'responses'/(c['id']+'.json'),result)
        ev.write_new(merged/'manifest.json',manifest);ev.write_new(merged/'state.json',combined);ev.write_new(merged/'run-status.json',status)
        # No paid calls: original paper extraction plus format/syntax checks only.
        package(stage,workers)
        public=ev.load(stage/'manifest.json');rows=public['calls'];models=public['models']
        for row in rows:
            result=canonical[row['cell_id']];phase=phases[row['cell_id']];cap=32768 if phase=='cap-refresh-32768' else 4096
            usage=totals([result],models[row['model_key']]['provider'])
            row.update(canonical_phase=phase,canonical_attempt=result['attempt'],max_output_tokens=cap,
                canonical_input_tokens=usage[0],canonical_output_tokens=usage[1],canonical_reasoning_tokens=usage[2],
                still_at_cap=reason(result) in ('length','max_tokens') and usage[1]==cap,
                originally_length_limited=row['cell_id'] in selected,refresh_pending=row['cell_id'] in selected and phase=='initial-4096')
            # Publish only authorized replacements; untouched files must still match exactly.
            dest=run/(row['sample_path'] or f'{row["model"]}/{row["problem"]}/response{row["sample"]}.yml')
            if phase=='cap-refresh-32768':
                if row['sample_path']:
                    dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((stage/row['sample_path']).read_bytes())
                elif dest.exists():
                    old=next(r for r in original['calls'] if r['cell_id']==row['cell_id'])
                    assert old['sample_path'] and (history/'selected-old-samples'/old['sample_path']).exists()
                    dest.unlink()
            elif row['sample_path']:assert dest.read_bytes()==(stage/row['sample_path']).read_bytes()
        for row in completed.values():
            new=next(r for r in rows if r['cell_id']==row['cell_id'])
            assert all(new[k]==row[k] for k in ['status','raw_text_sha256','sample_path','sha256','cost_usd','attempts'])
            if row['sample_path']:assert ev.digest((run/row['sample_path']).read_bytes())==row['sha256']
        for a in public['attempts']:
            raw=ev.load(merged/'attempts'/(a['cell_id']+f'--attempt{a["attempt"]}.json'))
            cap=raw['request_body'].get('max_tokens',raw['request_body'].get('max_output_tokens'))
            inp,out,reasoning=totals([raw],a['provider']);text=raw.get('text','') if raw['status'] in ('completed','incomplete') else ''
            a.update(max_output_tokens=cap,stop_reason=reason(raw),raw_text_sha256=ev.digest(text.encode()))
            attempt_history.append({'cell_id':a['cell_id'],'model':raw['request_body']['model'],'attempt':a['attempt'],
              'phase':a['phase'],'phase_attempt':a['phase_attempt'],'max_output_tokens':cap,'status':a['status'],
              'stop_reason':reason(raw),'input_tokens':inp,'output_tokens':out,'reasoning_tokens':reasoning,
              'cost_usd':a['cost_usd'],'cost_source':a['cost_source'],'raw_text_sha256':a['raw_text_sha256'],
              'started_at':a['started_at'],'latency_s':a['seconds'],'error':raw.get('error',''),'text':text})
        for summary in public['summary']:
            rs=[r for r in rows if r['model']==summary['model']]
            summary.update(original_length_limited=sum(r['originally_length_limited'] for r in rs),
              cap_refresh_completed=sum(r['canonical_phase']=='cap-refresh-32768' and r['status']=='completed' for r in rs),
              still_at_cap=sum(r['still_at_cap'] for r in rs),
              additional_cost_usd=sum(a['cost_usd'] for a in attempt_history if a['model']==summary['model'] and a['phase']=='cap-refresh-32768'))
        public['settings'].update(max_output_tokens=4096,output_cap_policy='4096 for original completed cells; 32768 for the 133 authorized cap-only reruns',
            output_cap_overrides={r['cell_id']:r['max_output_tokens'] for r in rows if r['canonical_phase']=='cap-refresh-32768'})
        public['refresh']={**fm['refresh'],'run_status':status,'additional_cost_accounted_usd':extra,
            'unknown_billing_reserve_usd':sum(a['cost_usd'] for a in fs['attempts'] if a.get('cost_source')!='reported_tokens_at_frozen_rates'),
            'canonical_replacements':sum(r['canonical_phase']=='cap-refresh-32768' for r in rows),
            'completed_cells_preserved':len(completed),'completed_extracted_files_preserved':sum(bool(r['sample_path']) for r in completed.values()),
            'still_at_cap_cell_ids':[r['cell_id'] for r in rows if r['still_at_cap']],
            'repackager_sha256':ev.digest(Path(__file__).read_bytes())}
        public['budget_guards']['cap_refresh_extra_usd']=5
        assert abs(public['cost_accounted_usd']-(original['cost_accounted_usd']+extra))<1e-8
        assert public['cost_accounted_usd']<=original['cost_accounted_usd']+5+1e-8
        public['audit_trail']='history/cap-4096 preserves the original exports/raw answers; attempt-history.csv/jsonl include every original and rerun attempt; canonical rows include cumulative usage/cost plus separate canonical usage/cap'
        (run/'manifest.json').write_text(json.dumps(public,indent=2)+'\n')
        write_csv(run/'offline-checks.csv',[{**r,'error':r['error'].replace('\r','\\r').replace('\n','\\n'),'yaml_error':r['yaml_error'].replace('\r','\\r').replace('\n','\\n')} for r in rows])
        write_csv(run/'model-summary.csv',public['summary'])
        write_csv(run/'attempt-history.csv',[{k:(v.replace('\r','\\r').replace('\n','\\n') if isinstance(v,str) else v) for k,v in a.items() if k!='text'} for a in attempt_history])
        (run/'attempt-history.jsonl').write_text(''.join(json.dumps(a)+'\n' for a in attempt_history))
        raw=[json.loads(line) for line in (stage/'raw-completions.jsonl').read_text().splitlines()]
        for answer in raw:
            row=next(r for r in rows if r['cell_id']==answer['cell_id']);answer.update(max_output_tokens=row['max_output_tokens'],canonical_phase=row['canonical_phase'])
        (run/'raw-completions.jsonl').write_text(''.join(json.dumps(a)+'\n' for a in raw))
        # Keep the second-stage diagnostic log separate from the original private run.
        shutil.copytree(merged/'syntax-diagnostics',fresh/'syntax-diagnostics',dirs_exist_ok=True)
        print(json.dumps({'additional_cost_usd':extra,'cumulative_cost_usd':public['cost_accounted_usd'],'summary':public['summary']},indent=2),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=Path,required=True);p.add_argument('--workers',type=int,default=6);p.add_argument('--wait',action='store_true');a=p.parse_args()
    if a.wait:
        while not (a.run/'private/cap-32768/run-status.json').exists():time.sleep(10)
    repackage(a.run,a.workers)
