#!/usr/bin/env python3
"""Offline post-hoc sensitivity of four disputed tasks; no network or model calls."""
import argparse
from collections import Counter
import copy
import difflib
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from evaluate import REPO,digest,load
from export_matrix import summarize,write_csv
from semantic_audit import probe
from reference_verifier_audit import verify

WORLDS=('Debian','Ubuntu','RedHat','OtherDebianFamily','OtherRedHatFamily','Other')
REVIEWED={'a03','a18','a20','a21'}


def os_true(condition,world):
    if condition.get('kind')!='os':raise ValueError('Non-OS condition is outside reviewed normalizer')
    val=condition['value']
    if val=='DebianFamily':return world in ('Debian','Ubuntu','OtherDebianFamily')
    if val=='RedHatFamily':return world in ('RedHat','OtherRedHatFamily')
    if val not in ('Debian','Ubuntu','RedHat'):raise ValueError('Unknown OS predicate')
    return world==val


def trace(effects,world):
    result=[]
    for action in effects:
        if action['kind']=='conditional':result.extend(trace(action['then'] if os_true(action['condition'],world) else action['else'],world))
        else:result.append(copy.deepcopy(action))
    return result


def traces(effects):return {world:trace(effects,world) for world in WORLDS}


def reviewed_match(task,actual,expected):
    if task=='a03':return actual==expected
    if task=='a20':
        # This is a scoped NL obligation, not full-state equivalence.
        actions=copy.deepcopy(actual)
        if actions and actions[0]=={'kind':'create_group','name':'wheel'}:actions.pop(0)
        if len(actions)!=2 or actions[0]!=expected[0]:return False
        user=actions[1]
        if user.get('kind')!='create_user' or user.get('name')!='ansible':return False
        primary=user.get('primary_group');supplemental=user.get('supplemental_groups')
        if primary not in (None,'wheel') or not set(supplemental or []).issubset({'wheel'}):return False
        return primary=='wheel' or 'wheel' in (supplemental or [])
    if task not in ('a18','a21'):return actual==expected
    try:actual_worlds=traces(actual);expected_worlds=traces(expected)
    except (ValueError,KeyError):return False
    for world,want in expected_worlds.items():
        got=actual_worlds[world]
        if len(got)!=len(want):return False
        for a,e in zip(got,want):
            if task=='a18' and e['kind']=='copy_file':
                # Only the unspecified backup destination may be concretized.
                p=a.get('destination',{}).get('path',{})
                dest=p.get('destination',{});value=dest.get('value')
                valid_unknown=isinstance(value,dict) and set(value)=={'unknown'}
                valid_literal=isinstance(value,str) and value.startswith('/') and value!='/etc/postfix/main.cf'
                if p.get('kind')!='remote' or dest.get('kind')!='absolute' or not (valid_unknown or valid_literal):return False
                a['destination']['path']=copy.deepcopy(e['destination']['path'])
            if a!=e:return False
    return True


def patch(original,changed,path=''):
    """Exact JSON-pointer replace/add/remove diff; arrays compared positionally."""
    if type(original)!=type(changed):return [{'op':'replace','path':path,'before':original,'after':changed}]
    if isinstance(original,dict):
        out=[]
        for k in sorted(set(original)|set(changed)):
            p=path+'/'+k.replace('~','~0').replace('/','~1')
            if k not in original:out.append({'op':'add','path':p,'after':changed[k]})
            elif k not in changed:out.append({'op':'remove','path':p,'before':original[k]})
            else:out.extend(patch(original[k],changed[k],p))
        return out
    if isinstance(original,list):
        out=[]
        for i in range(min(len(original),len(changed))):out.extend(patch(original[i],changed[i],path+'/'+str(i)))
        for i in range(len(original)-1,len(changed)-1,-1):out.append({'op':'remove','path':path+'/'+str(i),'before':original[i]})
        for i in range(len(original),len(changed)):out.append({'op':'add','path':path+'/'+str(i),'after':changed[i]})
        return out
    return [] if original==changed else [{'op':'replace','path':path,'before':original,'after':changed}]


def controls(review,binary,verifier):
    result={'reference_queries':{},'original_playbook_diagnostics':{},'proposed_playbook_diagnostics':{},'sudoers_whitespace':[]}
    for task,ref in review.items():
        q=probe(ref['proposed_formal_query'],binary);assert q['status']=='ok'
        result['reference_queries'][task]=q
        result['original_playbook_diagnostics'][task]=verify(ref['original_formal_query'],ref['original_reference_solution'],verifier)
        result['proposed_playbook_diagnostics'][task]=verify(ref['proposed_formal_query'],ref['proposed_reference_solution'],verifier)
    for label,separator in [('eight_spaces','        '),('tab','\t')]:
        text='%wheel'+separator+'ALL=(ALL:ALL) NOPASSWD:ALL\n'
        with tempfile.NamedTemporaryFile('w',suffix='.sudoers') as f:
            f.write(text);f.flush();p=subprocess.run(['/usr/sbin/visudo','-cf',f.name],capture_output=True,text=True)
        result['sudoers_whitespace'].append({'form':label,'text':text,'returncode':p.returncode,'stdout':p.stdout.replace(f.name,'{temporary_sudoers_file}'),'stderr':p.stderr.replace(f.name,'{temporary_sudoers_file}')})
        assert p.returncode==0
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',type=Path,required=True);p.add_argument('--review',type=Path,default=REPO/'evaluation/references/reference-review-v2.json');a=p.parse_args()
    run=a.run;out=run/'rescore';out.mkdir(exist_ok=True)
    version=load(a.review);review={r['task_id']:r for r in version['tasks']}
    original_rows=load(run/'per-call.json');diag=load(run/'diagnostics-private.json')
    binary=REPO/'_build/default/evaluation/native/effects.exe';verifier=REPO/'_build/default/bin/verify.exe'
    native=controls(review,binary,verifier)
    corrected_probes=native['reference_queries']
    strict_rows=copy.deepcopy(original_rows);corrected_rows=copy.deepcopy(original_rows);diffrows=[]
    for original,strict,new in zip(original_rows,strict_rows,corrected_rows):
        task=original['task_id']
        if task not in REVIEWED:continue
        g=diag['query_diagnostics'].get(original['output_sha256'],{}).get('probe',{})
        if original['semantic_accepted'] is True:
            actual=g['effects'];expected=corrected_probes[task]['effects']
            strict['ref_match']=actual==expected
            new['ref_match']=reviewed_match(task,actual,expected)
        reason='unchanged_original_metric'
        trace_delta=None
        if original['semantic_accepted'] is not True:reason='no_supported_effects: '+original['status']
        elif new['ref_match'] is True and original['ref_match'] is not True:reason='accepted_by_'+review[task]['policy']
        elif new['ref_match'] is not True and task in ('a18','a21'):
            try:
                actual_traces=traces(actual);expected_traces=traces(expected)
                trace_delta=patch(expected_traces,actual_traces)
                missing_latest=task=='a18' and any(x.get('version')!='latest' for acts in actual_traces.values() for x in acts if x['kind']=='install')
                reason='genuine_missing_latest_version' if missing_latest else 'remaining_os_scope_action_or_path_difference'
            except ValueError:reason='unsupported_non_os_condition_requires_review'
        elif new['ref_match'] is not True and task=='a03':reason='parent_reconstruction_not_equated_to_contents_deletion'
        elif new['ref_match'] is not True:reason='remaining_account_or_action_difference'
        diffrows.append({'model':original['model'],'variant':original['variant'],'task_id':task,'repeat':original['repeat'],
          'status':original['status'],'parsed':original['parsed'],'interpreted':original['interpreted'],
          'original_ref_match':original['ref_match'],'strict_corrected_ref_match':strict['ref_match'],
          'corrected_review_match':new['ref_match'],'policy':review[task]['policy'],'reason':reason})
    excluded=[r for r in original_rows if r['task_id'] not in REVIEWED]
    groups={'a-original':original_rows,'b-corrected':corrected_rows,'b-strict-reference-only':strict_rows,'c-exclude-four':excluded}
    for name,rows in groups.items():
        summary=summarize(rows,['model','variant']);write_csv(out/(name+'-model-variant-summary.csv'),summary)
        write_csv(out/(name+'-task-model-variant.csv'),summarize(rows,['task_id','model','variant']))
    assert (out/'a-original-model-variant-summary.csv').read_bytes()==(run/'model-variant-summary.csv').read_bytes(),'Original metric changed'
    write_csv(out/'per-cell-diff.csv',diffrows)
    taskrows=[]
    for task in sorted(REVIEWED):
        for variant in ['compact-v1','handbook-v3']:
            for model in sorted({r['model'] for r in original_rows}):
                rs=[r for r in diffrows if (r['task_id'],r['variant'],r['model'])==(task,variant,model)]
                taskrows.append({'task_id':task,'model':model,'variant':variant,'n':len(rs),
                  'original_correct':sum(r['original_ref_match'] is True for r in rs),
                  'strict_corrected_correct':sum(r['strict_corrected_ref_match'] is True for r in rs),
                  'corrected_correct':sum(r['corrected_review_match'] is True for r in rs),
                  'gained':sum(r['corrected_review_match'] is True and r['original_ref_match'] is not True for r in rs),
                  'lost':sum(r['corrected_review_match'] is not True and r['original_ref_match'] is True for r in rs),
                  'interpreted':sum(r['interpreted'] is True for r in rs),
                  'policy':review[task]['policy'],'rationale':review[task]['rationale']})
    write_csv(out/'per-task-diff-summary.csv',taskrows)
    picks={'a03':['sol--handbook-v3--a03--r0','deepseek-v4-flash--handbook-v3--a03--r1','glm-5.3--handbook-v3--a03--r0'],
      'a18':['sol--handbook-v3--a18--r0','opus--handbook-v3--a18--r0','glm-5.3--handbook-v3--a18--r2'],
      'a20':['opus--handbook-v3--a20--r0','sol--handbook-v3--a20--r0','opus--handbook-v3--a20--r5'],
      'a21':['opus--handbook-v3--a21--r0','deepseek-v4-flash--handbook-v3--a21--r3','deepseek-v4-flash--handbook-v3--a21--r8']}
    evidence={}
    for task,ids in picks.items():
        old=diag['reference_probes'][task]['effects'];new=corrected_probes[task]['effects'];samples=[]
        for ident in ids:
            raw=load(run/'responses'/(ident+'.json'));probe_result=diag['query_diagnostics'][digest(raw['text'].encode())]['probe'];actual=probe_result.get('effects')
            samples.append({'cell_id':ident,'output':raw['text'],'probe':probe_result,
               'original_effect_diff':patch(old,actual),'corrected_effect_diff':patch(new,actual),
               'original_trace_diff':patch(traces(old),traces(actual)) if task in ('a18','a21') else None,
               'reviewed_match':reviewed_match(task,actual,new)})
        evidence[task]={'natural_language':review[task]['natural_language'],'original_reference_fql':review[task]['original_formal_query'],
          'proposed_reference_fql':review[task]['proposed_formal_query'],'original_effects':old,'proposed_effects':new,
          'reference_effect_diff':patch(old,new),'representative_outputs':samples}
    (out/'effect-diffs.json').write_text(json.dumps(evidence,indent=2)+'\n')
    (out/'native-reference-controls.json').write_text(json.dumps(native,indent=2)+'\n')
    metadata={'review_version':version['version'],'review_sha256':digest(a.review.read_bytes()),'script_sha256':digest(Path(__file__).read_bytes()),
      'original_references_sha256':version['original_references_sha256'],'original_per_call_sha256':digest((run/'per-call.json').read_bytes()),
      'native_binary_sha256':digest(binary.read_bytes()),'new_paid_calls':0,'charts':False,
      'conditions':{'a-original':'Original references and original structural comparator, byte-identical summary',
        'b-corrected':'Proposed v2 references plus declared scoped post-hoc matching policies on four tasks only',
        'b-strict-reference-only':'Single proposed canonical FQL per task, original structural comparator; isolates reference change from normalization',
        'c-exclude-four':'Original comparator, excluding a03/a18/a20/a21; 170 planned cells/group'},
      'summary_reference_flags':'discrepant_reference_cells/n_without_discrepant_references retain the original a03/a20 flags; c-exclude-four explicitly removes all four reviewed tasks',
      'counts':{k:{'cells':len(rs),'matches':sum(r['ref_match'] is True for r in rs)} for k,rs in groups.items()},
      'limits':'Post-hoc proposals informed by observed outputs, not independently adjudicated gold. a03 remains unresolved in full NL generality. Corrected matching is scoped, not a general equivalence or intent oracle. Costs/latencies are historical and copied, not new spending.'}
    (out/'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2))

if __name__=='__main__':main()
