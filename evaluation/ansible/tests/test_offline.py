import sys,tempfile,subprocess
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from check_and_package import extract,parse_yaml,forbidden,syntax_check,REPO

class OfflineTests(unittest.TestCase):
    def test_original_fence_rule_is_exact(self):
        self.assertEqual(extract('```yaml\n- debug: {}\n```'),'\n- debug: {}\n')
        self.assertIn('```yml',extract('```yml\n- debug: {}\n```'))
    def test_module_scan_checks_tasks_and_actions_not_variable_names(self):
        ok,doc,_=parse_yaml('- hosts: all\n  vars:\n    command: harmless\n  pre_tasks:\n    - ansible.builtin.shell: echo test\n  tasks:\n    - block:\n        - local_action: {module: raw, args: echo test}\n    - action: ansible.builtin.command echo test\n  handlers:\n    - script: sample.py\n')
        self.assertTrue(ok);self.assertEqual(forbidden(doc),['command','raw','script','shell'])
    def test_yaml_error_and_isolated_syntax_check_are_not_execution(self):
        self.assertFalse(parse_yaml('- bad: [\n')[0])
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'probe.yml';witness=Path(tmp)/'must-not-exist'
            p.write_text('- hosts: all\n  tasks:\n    - ansible.builtin.command: touch '+str(witness)+'\n')
            self.assertTrue(syntax_check(p)['syntax_check_pass']);self.assertFalse(witness.exists())
