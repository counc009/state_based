"""Shared provider requests with router streaming; no model tools or output repair."""
import importlib.util
import json
from pathlib import Path
import urllib.request
import urllib.error
import evaluate as ev

spec=importlib.util.spec_from_file_location('ansible_stream_reader',Path(__file__).parents[1]/'ansible/code/generate.py')
reader=importlib.util.module_from_spec(spec);spec.loader.exec_module(reader)


def build(cell,config):
    url,body,headers=ev.build_request(cell,config)
    if config['models'][cell['model']]['provider']=='agentfanclub':
        body.update(stream=True,stream_options={'include_usage':True})
    return url,body,headers


def request(cell,config):
    model=config['models'][cell['model']];url,body,headers=build(cell,config)
    req=urllib.request.Request(url,data=json.dumps(body).encode(),headers=headers)
    try:
        with urllib.request.urlopen(req,timeout=180) as response:
            raw=reader.collect_stream(response,model['id'],config.get('stream_deadline_s',3600)) if body.get('stream') else json.load(response)
    except urllib.error.HTTPError:raise
    except urllib.error.URLError as error:
        return {'status':'transport_error','text':'','usage':None,'error':'URLError: '+str(error.reason)}
    provider=model['provider']
    if provider=='openai':
        text='\n'.join(p['text'] for item in raw.get('output',[]) for p in item.get('content',[]) if p.get('type')=='output_text');completed=raw.get('status')=='completed'
    elif provider=='anthropic':
        text='\n'.join(p['text'] for p in raw.get('content',[]) if p['type']=='text');completed=raw.get('stop_reason')=='end_turn'
    else:
        text=raw['choices'][0]['message'].get('content') or '';completed=raw['choices'][0]['finish_reason']=='stop'
    return {'status':'completed' if completed else 'incomplete','text':text,'response':raw,'usage':raw.get('usage'),
            'requested_model':model['id'],'returned_model':raw.get('model')}
