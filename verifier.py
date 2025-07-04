#!/usr/bin/python3
import os
import re
import subprocess

problems = ['01', '02', '03', '04', '05', '06', '07', '08', '09', '10', '11a',
            '11b', '12', '13', '14', '15', '16', '17', '18', '19', '20']
models = ['deepseek', 'gpt', 'granite', 'llama', 'qwen', 'starcoder']

modules = ['modules/' + f for f in os.listdir('modules')]

cmd = ['dune', 'exec', 'ansible-verify', '--', 'QUERY', 'ANSIBLE',
       '--'] + modules
QUERY = 4
ANSIBLE = 5

results = { p : { m : {} for m in models } for p in problems }

ansible_error = re.compile('ERROR in ansible: (.*)')

for problem in problems:
  for model in models:
    for i in range(1, 11):
      n = i % 10
      path = f'/home/aaron/ansible/{model}/p{problem}/response{n}.yml'
      if os.path.isfile(path):
        cmd[QUERY] = f'playbooks/bench/query{problem}.txt'
        cmd[ANSIBLE] = path

        res = subprocess.run(cmd, capture_output=True)
        retcode = res.returncode

        result = 'ERROR'
        if retcode == 0:
          result = 'Correct'
        elif retcode == 1:
          result = 'ERROR (modules)'
        elif retcode == 2:
          result = 'ERROR (query)'
        elif retcode == 3:
          msg = ansible_error.search(res.stdout.decode()).group(1)
          result = f'Ansible Error {msg}'
        elif retcode == 4:
          result = 'Verification Failure'

        results[problem][model][i] = result
        print(f'Model {model}, Problem {problem}, Response {i} - {result}')
      else:
        results[problem][model][i] = 'Syntax Error'
        print(f'Model {model}, Problem {problem}, Response {i} - Syntax Error')

with open('results.csv', 'w') as f:
  f.write('Problem,Model,Response,Result\n')
  for problem in problems:
    for model in models:
      for i in range(1, 11):
        res = results[problem][model][i]
        f.write(f'{problem},{model},{i},{res}\n')
