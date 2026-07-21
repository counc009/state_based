#!/usr/bin/python3
import os
import pwd
import re
import subprocess
import time

assert os.getuid() == 0

debian = 'debian12.11.0'
redhat = 'rhel9.6'
ubuntu = 'ubuntu24.04.2'

snapshot = 'snapshot-2026-06-26'

vms = [debian, redhat, ubuntu]

def run_root(cmds):
  return subprocess.run(cmds, capture_output=True)

class AnsibleResult:
  def __init__(self, ret=1, out=b'', err=b'', *, timeout=False):
    self.timeout = timeout
    self.returncode = ret
    self.stdout = out
    self.stderr = err

# Returns false if the process times out
def communicate_timeout(proc, timeout):
  if timeout is None:
    proc.communicate()
    return True
  else:
    end_time = time.time() + timeout

    while time.time() < end_time:
      if proc.poll() is not None:
        return True
      time.sleep(0.1)
    else:
      proc.kill()
      return False

def run_ansible(cmds, timeout=None):
  user_record = pwd.getpwnam('ansible')
  user_name     = user_record.pw_name
  user_home_dir = user_record.pw_dir
  user_uid      = user_record.pw_uid
  user_gid      = user_record.pw_gid
  env = os.environ.copy()
  env['HOME']    = user_home_dir
  env['LOGNAME'] = user_name
  env['USER']    = user_name
  process = subprocess.Popen(
      cmds, preexec_fn=lambda: demote(user_uid, user_gid), env=env,
      stdout=subprocess.PIPE, stderr=subprocess.PIPE)

  if communicate_timeout(process, timeout):
    stdout, stderr = process.communicate()
    return AnsibleResult(process.returncode, stdout, stderr)
  else:
    return AnsibleResult(timeout=True)

def demote(uid, gid):
  os.setgid(gid)
  os.setuid(uid)

def reset_vms(names):
  for name in names:
    run_root(["/usr/bin/virsh", "shutdown", name])

  cnt = 0
  done = False
  while not done:
    time.sleep(1)
    done = True
    for name in names:
      if 'running' in run_root(['/usr/bin/virsh', 'domstate', name]).stdout.decode():
        done = False
        cnt += 1
    if not done:
      cnt += 1
      if cnt == 10:
        print(f'Having issues getting VMs to shut down')
        cnt = 0
        for name in names:
          run_root(["/usr/bin/virsh", "shutdown", name])

  for name in names:
    assert run_root(["/usr/bin/virsh", "snapshot-revert", name,
                "--snapshotname", snapshot]).returncode == 0

  # I'd really like to somehow wait for the system to come online enough for
  # ssh (maybe you can do this https://serverfault.com/a/545408) but for the
  # second I'm just going to wait
  time.sleep(5)

failed_regexp = re.compile('aaron@([^\\s]*).*failed=[^0]')
ip_lookup = {'192.168.122.129': 'debian',
             '192.168.122.149': 'ubuntu',
             '192.168.122.246': 'redhat'}

models = ['deepseek', 'gpt', 'granite', 'llama', 'qwen', 'starcoder',
          'gpt-5-mini', 'gpt-oss', 'ministral', 'qwen3', 'qwen-coder']
# NOTE: problem 20's verification doesn't check that the packages were
# installed or the service started, all it will check is that the packages
# exist and that the ssh key generation is performed; manual inspection is
# needed to ensure those pieces.

# NOTE: proble 17's reqruirement of not overwriting the backup file is not
# feasible to test (since we don't specify where the backup is) and so is
# checked by manual inspection

problems = [('p01', vms, 2, None), ('p02', vms, 2, None),
            ('p03', vms, 1, None), ('p04', vms, 2, None),
            ('p05', vms, 1, None), ('p06', vms, 1, None),
            ('p07', vms, 1, None), ('p08', vms, 1, None),
            ('p09', vms, 1, None), ('p10', vms, 1, None),
            ('p11a', vms, 1, None), ('p11b', [debian], 1, None),
            ('p12', vms, 1, None), ('p13', vms, 2, None),
            ('p14', [debian], 2, None), ('p15', vms, 1, None),
            ('p16', vms, 1, None), ('p17', [redhat,ubuntu], 1, None),
            ('p18', [redhat], 2, None), ('p19', vms, 1, None),
            ('p20', [debian,redhat], 1, 60)]
problems = [('p19', vms, 1, None)]

results = { p : { m : {} for m in models } for (p, _, _, _) in problems}

for output in ['results.csv', 'results-2.csv']:
  for (problem, vms, insts, timeout) in problems:
    for model in models:
      for i in range(1, 11):
        n = i % 10
        path = f'{model}/{problem}/response{n}.yml'
        if os.path.isfile(path):
          result = 'Correct'

          for j in range(0, insts):
            # Reset VMs
            reset_vms(vms)

            # Run setup
            setup = run_ansible(['/usr/bin/ansible-playbook', f'reference/{problem}/setup{j}.yml'])
            assert not setup.timeout and setup.returncode == 0

            # Run the candidate playbook
            candidate = run_ansible(['/usr/bin/ansible-playbook', path], timeout=timeout)
            if candidate.timeout:
              result = f'Timed Out (inst {j})'
              break
            elif candidate.returncode != 0:
              # The playbook execution failed, use the stdout to identify hosts
              ips = failed_regexp.findall(candidate.stdout.decode())
              which = ' '.join(map(lambda i: ip_lookup[i], ips))
              result = f'Exec Failed (inst {j}) {which}'
              break

            # Run the verifier
            verify = run_ansible(['/usr/bin/ansible-playbook', f'reference/{problem}/verify{j}.yml'])
            assert not verify.timeout
            if verify.returncode != 0:
              # The verifier failed
              ips = failed_regexp.findall(verify.stdout.decode())
              which = ' '.join(map(lambda i: ip_lookup[i], ips))
              result = f'Verification Failed (inst {j}) {which}'
              break

          # Finally, log the result
          results[problem][model][i] = result
          print(f'Model {model}, Problem {problem}, Response {i} - {result}')
        elif os.path.isfile(path + '.bad'):
          results[problem][model][i] = 'Does Not Terminate'
          print(f'Model {model}, Problem {problem}, Response {i} - Does Not Terminate')
        else:
          results[problem][model][i] = 'Syntax Error'
          print(f'Model {model}, Problem {problem}, Response {i} - Syntax Error')

  with open(output, 'w') as f:
    f.write('Problem,Model,Response,Result\n')
    for (problem, _, _, _) in problems:
      for model in models:
        for i in range(1, 11):
          res = results[problem][model][i]
          f.write(f'{problem},{model},{i},{res}\n')
