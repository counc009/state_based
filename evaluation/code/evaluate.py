#!/usr/bin/env python3
"""Frozen five-repeat NL-to-FQL experiments; standard library only, no tools in requests."""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def digest(value):
    data = value if isinstance(value, bytes) else json.dumps(value, sort_keys=True).encode()
    return hashlib.sha256(data).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def write_new(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')


def freeze(dataset, models, variants, cases=None):
    config = load(ROOT / 'configs/models.json')
    assert config['repetitions'] == 5, 'Protocol requires five repetitions'
    registry = load(ROOT / 'prompts/registry.json')
    tasks = load(dataset)['tasks']
    selected = [t for t in tasks if cases is None or t['task_id'] in cases]
    assert selected, 'No tasks selected'
    assert len({t['task_id'] for t in selected}) == len(selected), 'Expected one source row per task'
    if cases:
        assert set(cases) == {t['task_id'] for t in selected}, 'Unknown case'
    cells = []
    sources = {'dataset': digest(Path(dataset).read_bytes()), 'runner': digest(Path(__file__).read_bytes()),
               'models': digest(config), 'registry': digest(registry)}
    for variant in variants:
        prompt = (ROOT / 'prompts' / registry[variant]['file']).read_text()
        sources[variant] = digest(prompt.encode())
        for task in selected:
            assert task['task_id'] not in task['demonstration_ids'], 'Target leaked into demonstrations'
            messages = task['messages']
            assert messages[0]['role'] == 'system' and messages[-1]['role'] == 'user'
            assert all(set(m) == {'role', 'content'} for m in messages), 'Unexpected input fields'
            assert all(isinstance(m['content'], str) for m in messages)
            assert all(m['role'] in {'system','user','assistant'} for m in messages)
            if variant == 'compact-v1':
                assert messages[0]['content'] == prompt, 'Recovered baseline prompt differs'
            revised = [{'role':'system', 'content':prompt}] + messages[1:]
            assert revised[1:] == messages[1:], 'Demonstrations or target changed'
            for model in models:
                for repeat in range(5):
                    cells.append({'id':f'{model}--{variant}--{task["task_id"]}--r{repeat}',
                                  'model':model, 'variant':variant, 'task_id':task['task_id'],
                                  'repeat':repeat, 'demonstration_ids':task['demonstration_ids'],
                                  'messages':revised})
    return {'schema_version':1, 'repetitions':5, 'sources':sources, 'config':config,
            'cells':sorted(cells, key=lambda c:digest(c['id'])),
            'scope':'Development suite; no unseen-task or user-intent correctness claim'}


def reserve(cell, config):
    """Conservative input envelope: UTF-8 bytes plus 4K framing tokens, no discounts."""
    model = config['models'][cell['model']]
    if model['provider'] == 'local':
        return 0.0
    size = len(json.dumps(cell['messages'], ensure_ascii=False).encode()) + 4096
    return (size * model['input_per_million'] +
            config['max_output_tokens'] * model['output_per_million']) / 1_000_000


def estimate(manifest):
    config = manifest['config']
    by_model = {}
    for model in {c['model'] for c in manifest['cells']}:
        cells = [c for c in manifest['cells'] if c['model'] == model]
        by_model[model] = {'calls':len(cells), 'usd_envelope':round(sum(reserve(c, config) for c in cells), 6)}
    return {'calls':len(manifest['cells']), 'by_model':by_model,
            'usd_envelope':round(sum(reserve(c, config) for c in manifest['cells']), 6),
            'notes':'Standard token rates only; local compute excluded. No automatic retries. Reprice before a full run.'}


def request(cell, config):
    model = config['models'][cell['model']]
    provider = model['provider']
    headers = {'Content-Type':'application/json'}
    if provider == 'openai':
        url = 'https://api.openai.com/v1/responses'
        headers['Authorization'] = 'Bearer ' + os.environ['OPENAI_API_KEY']
        payload = {'model':model['id'], 'input':cell['messages'], 'store':False,
                   'max_output_tokens':config['max_output_tokens'],
                   'reasoning':{'effort':config['reasoning_effort']}}
    elif provider == 'anthropic':
        url = 'https://api.anthropic.com/v1/messages'
        headers.update({'x-api-key':os.environ['ANTHROPIC_API_KEY'], 'anthropic-version':'2023-06-01'})
        payload = {'model':model['id'], 'system':cell['messages'][0]['content'],
                   'messages':cell['messages'][1:], 'max_tokens':config['max_output_tokens']}
    else:
        # Operator must provide a pinned local model server. Never download or start one implicitly.
        url = os.environ['EVALUATION_LOCAL_URL'].rstrip('/') + '/chat/completions'
        payload = {'model':model['id'], 'messages':cell['messages'],
                   'max_tokens':config['max_output_tokens'], 'stream':False}
    req = urllib.request.Request(url, data=json.dumps(payload).encode(), headers=headers)
    with urllib.request.urlopen(req, timeout=180) as response:
        raw = json.load(response)
    if provider == 'openai':
        text = '\n'.join(p['text'] for item in raw.get('output', [])
                         for p in item.get('content', []) if p.get('type') == 'output_text')
        completed = raw.get('status') == 'completed'
    elif provider == 'anthropic':
        text = '\n'.join(p['text'] for p in raw.get('content', []) if p['type'] == 'text')
        completed = raw.get('stop_reason') == 'end_turn'
    else:
        text = raw['choices'][0]['message'].get('content') or ''
        completed = raw['choices'][0]['finish_reason'] == 'stop'
    return {'status':'completed' if completed else 'incomplete', 'text':text,
            'response':raw, 'requested_model':model['id'], 'returned_model':raw.get('model'),
            'usage':raw.get('usage'), 'request_body':payload}


def run(manifest, out, budget, max_calls):
    # One writer and one immutable freeze per run. Reserved attempts survive interrupted requests.
    out.mkdir(parents=True, exist_ok=True)
    with (out / '.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        frozen = out / 'manifest.json'
        if frozen.exists():
            assert load(frozen) == manifest, 'Run manifest changed; use a new output directory'
        else:
            write_new(frozen, manifest)
        ledger = out / 'attempts.jsonl'
        attempts = [json.loads(l) for l in ledger.read_text().splitlines()] if ledger.exists() else []
        seen = {a['id'] for a in attempts}
        spent = sum(a['reserved_usd'] for a in attempts)
        calls = 0
        for cell in manifest['cells']:
            if cell['id'] in seen:
                continue
            if calls >= max_calls:
                break
            cost = reserve(cell, manifest['config'])
            if spent + cost > budget + 1e-9:
                break
            provider = manifest['config']['models'][cell['model']]['provider']
            needed = {'openai':'OPENAI_API_KEY','anthropic':'ANTHROPIC_API_KEY','local':'EVALUATION_LOCAL_URL'}[provider]
            if not os.environ.get(needed):
                raise RuntimeError('Missing environment variable: ' + needed)
            receipt = {'id':cell['id'], 'reserved_usd':cost, 'started_at':datetime.now(timezone.utc).isoformat()}
            with ledger.open('a') as f:
                f.write(json.dumps(receipt)+'\n'); f.flush(); os.fsync(f.fileno())
            start = time.monotonic()
            try:
                result = request(cell, manifest['config'])
            except urllib.error.HTTPError as e:
                result = {'status':'provider_error', 'http_status':e.code}
            except Exception as e:
                # Do not serialize exception strings, headers or key values.
                result = {'status':'transport_error', 'error_type':type(e).__name__}
            result.update(cell_id=cell['id'], manifest_sha256=digest(manifest),
                          seconds=round(time.monotonic()-start, 3))
            write_new(out / 'responses' / (cell['id']+'.json'), result)
            spent += cost; calls += 1
            print(json.dumps({'cell':cell['id'], 'status':result['status']}), flush=True)
        return {'new_calls':calls, 'reserved_usd':round(spent, 6),
                'attempts':len(seen)+calls, 'planned_cells':len(manifest['cells'])}


def analyze(out, checker=None):
    manifest = load(out / 'manifest.json')
    groups = defaultdict(list)
    for cell in manifest['cells']:
        path = out / 'responses' / (cell['id']+'.json')
        result = load(path) if path.exists() else {'status':'missing'}
        row = {'cell':cell['id'], 'task_id':cell['task_id'], 'repeat':cell['repeat'],
               'status':result['status'], 'text_sha256':digest(result.get('text','').encode())}
        if checker and result['status'] == 'completed':
            with tempfile.TemporaryDirectory() as tmp:
                query = Path(tmp) / 'query.txt'
                # Keep raw text intact: no repairs or silent fence stripping.
                query.write_text(result['text'])
                argv = [a.replace('{query}', str(query)).replace('{repo}', str(REPO)) for a in shlex.split(checker)]
                p = subprocess.run(argv, capture_output=True, timeout=60)
                row['checker_returncode'] = p.returncode
                row['checker_stdout'] = p.stdout.decode(errors='replace')
                row['checker_stderr'] = p.stderr.decode(errors='replace')
        groups[cell['model']+' / '+cell['variant']].append(row)
    summary = {}
    for name, rows in groups.items():
        texts = [r['text_sha256'] for r in rows if r['status'] == 'completed']
        summary[name] = {'planned':len(rows), 'statuses':dict(Counter(r['status'] for r in rows)),
                         'distinct_completed_outputs':len(set(texts)),
                         'checker_pass':sum(r.get('checker_returncode') == 0 for r in rows),
                         'per_cell':rows}
    return {'scope':manifest['scope'], 'results':summary,
            'warning':'Checker success and output diversity do not measure user intent. No semantic-fidelity labels supplied.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    f = sub.add_parser('freeze')
    f.add_argument('--dataset', type=Path, required=True)
    f.add_argument('--models', nargs='+', required=True)
    f.add_argument('--variants', nargs='+', default=['compact-v1','handbook-v2'])
    f.add_argument('--cases', nargs='+')
    f.add_argument('--output', type=Path, required=True)
    for name in ['estimate','run','analyze']:
        c = sub.add_parser(name)
        c.add_argument('--manifest', type=Path, required=name != 'analyze')
        if name != 'estimate': c.add_argument('--output', type=Path, required=True)
        if name == 'run':
            c.add_argument('--budget-usd', type=float, required=True)
            c.add_argument('--max-calls', type=int, required=True)
        if name == 'analyze': c.add_argument('--checker', help='Trusted argv template, {query} and {repo}; no shell')
    a = p.parse_args()
    if a.command == 'freeze':
        m = freeze(a.dataset, a.models, a.variants, a.cases)
        write_new(a.output, m)
        result = estimate(m)
    elif a.command == 'estimate': result = estimate(load(a.manifest))
    elif a.command == 'run':
        if a.budget_usd < 0 or a.max_calls < 1: p.error('Invalid run bounds')
        result = run(load(a.manifest), a.output, a.budget_usd, a.max_calls)
    else: result = analyze(a.output, a.checker)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
