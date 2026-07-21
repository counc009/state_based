#!/usr/bin/python3
import os
import re
import subprocess

import argparse
parser = argparse.ArgumentParser()
parser.add_argument('-u', '--users', action='store_true')
parser.add_argument('-p', '--pkgs', action='store_true')
parser.add_argument('-f', '--files', action='store_true')
parser.add_argument('-F', '--strict-files', action='store_true')
parser.add_argument('-r', '--reboot', action='store_true')
parser.add_argument('-w', '--writes', action='store_true')
args = parser.parse_args()

problems = [
    ('01', ('users.txt', 'groups.txt', 'files01.txt', 'all')),
    ('02', ('users.txt', 'groups.txt', 'files02.txt', 'all')),
    ('03', ('users03.txt', 'groups03.txt', 'files03.txt', 'all')),
    ('04', ('users.txt', 'groups.txt', 'files.txt', 'all')),
    ('05', ('users05.txt', 'groups05.txt', 'files.txt', 'all')),
    ('06', ('users.txt', 'groups.txt', 'files.txt', 'all')),
    ('07', ('users.txt', 'groups.txt', 'files07.txt', 'all')),
    ('08', ('users.txt', 'groups.txt', 'files.txt', 'all')),
    ('09', ('users09.txt', 'groups09.txt', 'files.txt', 'all')),
    ('10', ('users10.txt', 'groups10.txt', 'files.txt', 'all')),
    ('11a', ('users.txt', 'groups.txt', 'files11a.txt', 'all')),
    ('11b', ('users.txt', 'groups.txt', 'files11b.txt', 'debian')),
    ('12', ('users12.txt', 'groups12.txt', 'files.txt', 'all')),
    ('13', ('users.txt', 'groups.txt', 'files.txt', 'all')),
    ('14', ('users.txt', 'groups.txt', 'files.txt', 'debian')),
    ('15', ('users15.txt', 'groups15.txt', 'files.txt', 'all')),
    ('16', ('users16.txt', 'groups16.txt', 'files.txt', 'all')),
    ('17', ('users.txt', 'groups.txt', 'files.txt', 'redhat,ubuntu')),
    ('18', ('users.txt', 'groups.txt', 'files18.txt', 'redhat')),
    ('19', ('users19.txt', 'groups19.txt', 'files19.txt', 'all')),
    ('20', ('users20.txt', 'groups20.txt', 'files.txt', 'redhat,ubuntu'))]
models = ['deepseek', 'gpt', 'granite', 'llama', 'qwen', 'starcoder',
          'gpt-5-mini', 'gpt-oss', 'ministral', 'qwen3', 'qwen-coder']

modules = ['modules/' + f for f in os.listdir('modules')]

cmd = ['dune', 'exec', 'ansible-verify', '--']

if args.users:
  USERS = len(cmd) + 1
  GROUPS = len(cmd) + 3
  cmd += ['--users', 'USERS', '--groups', 'GROUPS']
if args.pkgs:
  cmd += ['--pkgs', 'heuristics/packages.txt']
if args.files:
  FILES = len(cmd) + 1
  cmd += ['--files', 'FILES']
if args.strict_files:
  STRICT_FILES = len(cmd) + 1
  cmd += ['--strict-files', 'FILES']
if args.reboot:
  REBOOT_HOSTS = len(cmd) + 1
  cmd += ['--reboot', 'HOSTS']
if args.writes:
  WRITE_HOSTS = len(cmd) + 1
  cmd += ['--writes', 'HOSTS']

QUERY = len(cmd)
ANSIBLE = len(cmd) + 1
cmd += ['QUERY', 'ANSIBLE', '--'] + modules

results = { p : { m : {} for m in models } for (p, _) in problems }

ansible_error = re.compile('ERROR: While lowering Ansible, encountered\n(.*)')

for (problem, (users, groups, files, hosts)) in problems:
  if args.users:
    cmd[USERS] = 'heuristics/' + users
    cmd[GROUPS] = 'heuristics/' + groups
  if args.files:
    cmd[FILES] = 'heuristics/' + files
  if args.strict_files:
    cmd[STRICT_FILES] = 'heuristics/' + files
  if args.reboot:
    cmd[REBOOT_HOSTS] = hosts
  if args.writes:
    cmd[WRITE_HOSTS] = hosts

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
        elif retcode == 1 or retcode == 2:
          result = 'ERROR (modules)'
        elif retcode == 3:
          result = 'ERROR (query)'
        elif retcode == 4:
          msg = res.stdout.decode().split('\n')[2]
          result = f'Ansible Error - {msg}'
        elif retcode == 5:
          result = 'Verification Failure'
        elif retcode == 7:
          result = 'Heuristic Rejection'

        results[problem][model][i] = result
        print(f'Model {model}, Problem {problem}, Response {i} - {result}')
      else:
        results[problem][model][i] = 'Syntax Error'
        print(f'Model {model}, Problem {problem}, Response {i} - Syntax Error')

with open('results.csv', 'w') as f:
  f.write('Problem;Model;Response;Result\n')
  for (problem, _) in problems:
    for model in models:
      for i in range(1, 11):
        res = results[problem][model][i]
        f.write(f'{problem};{model};{i};{res}\n')
