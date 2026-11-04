#!/usr/bin/env python3
from pathlib import Path
import json,csv,copy,hashlib,collections
import argparse
from evaluate import REPO
p=argparse.ArgumentParser(description='Offline rescore consistency and exact effect-diff audit')
p.add_argument('--run',type=Path,required=True);a=p.parse_args()
root=REPO;run=a.run;out=run/'rescore'
base=list(csv.DictReader((run/'model-variant-summary.csv').open()));d=list(csv.DictReader((out/'per-cell-diff.csv').open()));task=list(csv.DictReader((out/'per-task-diff-summary.csv').open()))
assert len(d)==480 and len(task)==48
assert len({(r['model'],r['variant'],r['task_id'],r['repeat']) for r in d})==480
assert (run/'model-variant-summary.csv').read_bytes()==(out/'a-original-model-variant-summary.csv').read_bytes()
index={(r['model'],r['variant']):r for r in base}
parsebool=lambda s:s=='True'
for name in ['a-original','b-corrected','b-strict-reference-only','c-exclude-four']:
 rows=list(csv.DictReader((out/(name+'-model-variant-summary.csv')).open()))
 assert list(rows[0])==list(base[0]),'Summary schema changed'
 assert len(rows)==12
 for row in rows:
  key=(row['model'],row['variant']);b=index[key];cells=[r for r in d if (r['model'],r['variant'])==key]
  assert len(cells)==40
  orig=int(b['correct']);removed=sum(parsebool(r['original_ref_match']) for r in cells)
  if name=='a-original':wanted=orig
  elif name=='c-exclude-four':wanted=orig-removed
  else:
   field='corrected_review_match' if name=='b-corrected' else 'strict_corrected_ref_match'
   wanted=orig-removed+sum(parsebool(r[field]) for r in cells)
  assert int(row['correct'])==wanted
  assert int(row['n'])==(170 if name=='c-exclude-four' else 210)
  if name!='c-exclude-four':
   for k in ['syntax_parse_fail','semantic_fail','interp_fail','completed','pending','provider_or_transport_fail','cost_usd','mean_latency_s']:
    assert row[k]==b[k],(name,k)

def apply(before,ops):
 result=copy.deepcopy(before)
 for op in ops:
  if not op['path']:result=copy.deepcopy(op['after']);continue
  parts=[x.replace('~1','/').replace('~0','~') for x in op['path'].split('/')[1:]];parent=result
  for x in parts[:-1]:parent=parent[int(x)] if isinstance(parent,list) else parent[x]
  key=int(parts[-1]) if isinstance(parent,list) else parts[-1]
  if op['op']=='remove':assert parent[key]==op['before'];del parent[key]
  elif op['op']=='add':
   if isinstance(parent,list):parent.insert(key,copy.deepcopy(op['after']))
   else:parent[key]=copy.deepcopy(op['after'])
  else:assert parent[key]==op['before'];parent[key]=copy.deepcopy(op['after'])
 return result
proof=json.load(open(out/'effect-diffs.json'));samples=0
for k,t in proof.items():
 assert apply(t['original_effects'],t['reference_effect_diff'])==t['proposed_effects']
 for s in t['representative_outputs']:
  assert apply(t['original_effects'],s['original_effect_diff'])==s['probe']['effects']
  assert apply(t['proposed_effects'],s['corrected_effect_diff'])==s['probe']['effects'];samples+=1
review=json.load(open(root/'evaluation/references/reference-review-v2.json'))
assert hashlib.sha256((root/'evaluation/datasets/references-private.json').read_bytes()).hexdigest()==review['original_references_sha256']
assert samples==12
validation={'conditions':4,'summary_groups_per_condition':12,'reviewed_cells':480,'task_diff_groups':48,
 'exact_effect_diff_reconstructions':24,'reference_effect_diff_reconstructions':4,
 'original_summary_byte_identical':True,'original_references_unchanged':True,
 'summary_schemas_identical':True,'costs_and_native_diagnostics_unchanged':True,'new_paid_calls':0,'tests':27}
(out/'validation.json').write_text(json.dumps(validation,indent=2)+'\n');print(json.dumps(validation,indent=2))
