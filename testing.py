#!/usr/bin/python3
import pandas as pd
import subprocess
import glob
import os

from tqdm import tqdm

errors = {}
success = 0

def log_error(err):
  if err in errors:
    errors[err] += 1
  else:
    errors[err] = 1

modules = glob.glob('modules/*')

data = pd.read_csv('prompts.csv')

for row in tqdm(data['original']):
  with open('ansible.yml', 'w') as f:
    f.write(row)
  res = subprocess.run(
      ['dune', 'exec', 'ansible-interp', '--', 'ansible.yml', '--'] + modules,
      capture_output=True)

  out = res.stdout
  if b'ERROR' in res.stdout:
    for error in out.splitlines()[2:]:
      log_error(error)
  else:
    success += 1

os.remove('ansible.yml')

error_list = sorted(errors, key=lambda e: errors[e], reverse=True)

print(f'Succeeded: {success}')
for error in error_list:
  print(f'{errors[error]:3} {error}')
