#!/usr/bin/python3
import pandas as pd

models = {'deepseek': 'deepseek-coder-6 7b',
          'gpt': 'gpt-4o',
          'granite': 'granite-8b-code',
          'llama': 'llama3 1-8b',
          'qwen': 'qwen2 5-coder-3b',
          'starcoder': 'starcoder2-15b' }
benchmarks = [('p01', 'all'), ('p02', 'all'), ('p03', 'all'), ('p04', 'all'),
              ('p05', 'all'), ('p06', 'all'), ('p07', 'all'), ('p08', 'all'),
              ('p09', 'all'), ('p10', 'all'), ('p11a', 'all'), ('p11b', 'all'),
              ('p12', 'all'), ('p13', 'all'), ('p14', 'debian'),
              ('p15', 'all'), ('p16', 'all'), ('p17', 'redhat,ubuntu'),
              ('p18', 'redhat'), ('p19', 'all'), ('p20', 'redhat,debian')]
responses = {'Response 1': 'raw1.yml', 'Response 2': 'raw2.yml',
             'Response 3': 'raw3.yml', 'Response 4': 'raw4.yml',
             'Response 5': 'raw5.yml', 'Response 6': 'raw6.yml',
             'Response 7': 'raw7.yml', 'Response 8': 'raw8.yml',
             'Response 9': 'raw9.yml', 'Response 10': 'raw0.yml'}

sheets = [tab for (_, tab) in models.items()]
data = pd.read_excel('benchmark.xlsx', sheet_name=sheets)

for (model, tab) in models.items():
  model_res = data[tab]

  for ((query, _), model_responses) in zip(benchmarks, model_res.iloc):
    for (col, file) in responses.items():
      path = f'{model}/{query}/{file}'
      response = model_responses[col]
      if not isinstance(response, str):
        response = ""
      with open(path, 'w') as f:
        f.write(response)
