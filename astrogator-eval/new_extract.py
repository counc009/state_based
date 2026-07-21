#!/usr/bin/python3
import os
import pandas as pd
import re

models = {'gpt-5-mini': 'gpt-5-mini',
          'gpt-oss': 'gpt-oss-20b',
          'ministral': 'Ministral-3-14B-Reasoning-2512',
          'qwen3': 'Qwen3.5-9B',
          'qwen-coder': 'Qwen3-Coder-30B-A3B-Instruct' }
benchmarks = [('p01', 'all'), ('p02', 'all'), ('p03', 'all'), ('p04', 'all'),
              ('p05', 'all'), ('p06', 'all'), ('p07', 'all'), ('p08', 'all'),
              ('p09', 'all'), ('p10', 'all'), ('p11a', 'all'), ('p11b', 'all'),
              ('p12', 'all'), ('p13', 'all'), ('p14', 'debian'),
              ('p15', 'all'), ('p16', 'all'), ('p17', 'redhat,ubuntu'),
              ('p18', 'redhat'), ('p19', 'all'), ('p20', 'redhat,debian')]

md_regex = re.compile('^```(yaml)?$', flags=re.MULTILINE)

for (model, file) in models.items():
  data = pd.read_csv(f'raw_results/{file}.csv')
  col = data.keys()[2]

  idx = 0

  for i in range(0, 10):
    for (query, _) in benchmarks:
      path = f'{model}/{query}/raw{i}.yml'
      os.makedirs(os.path.dirname(path), exist_ok=True)

      response = data.iloc[idx][col]
      result = re.sub(md_regex, '', response)

      with open(path, 'w') as f:
        f.write(result)

      idx = idx + 1
