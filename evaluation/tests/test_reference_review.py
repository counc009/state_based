import copy
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from review_rescore import patch,trace,traces,reviewed_match
from semantic_audit import probe
from evaluate import REPO


class ReviewTests(unittest.TestCase):
    def q(self,text):
        p=probe(text,REPO/'_build/default/evaluation/native/effects.exe')
        self.assertEqual(p['status'],'ok');return p['effects']
    def test_os_trace_preserves_scope_and_order_with_equivalent_branching(self):
        a=self.q('if os is Debian or os is RedHat then install postfix; reboot')
        b=self.q('if os is Debian then install postfix; reboot. if os is RedHat then install postfix; reboot')
        self.assertEqual(traces(a),traces(b))
        self.assertNotEqual(traces(a),traces(self.q('if os is Debian or os is RedHat then reboot; install postfix')))
        self.assertNotEqual(traces(a),traces(self.q('if os is Debian based or os is RedHat based then install postfix; reboot')))
        self.assertNotEqual(traces(a),traces(self.q('if os is Debian then install postfix; reboot; if os is RedHat then install postfix; reboot')))
    def test_a18_does_not_relax_latest_urls_copy_order_or_backup_system(self):
        ref=self.q('if os is Ubuntu then install postfix with version="latest"; copy file from "/etc/postfix/main.cf" to ?backup; download file from "https://neutral.example/cfg" to "/etc/postfix/main.cf"')
        actual=self.q('if os is Ubuntu then install postfix with version="latest"; copy file from "/etc/postfix/main.cf" to "/neutral/backup"; download file from "https://neutral.example/cfg" to "/etc/postfix/main.cf"')
        self.assertTrue(reviewed_match('a18',actual,ref))
        for mutation in ['version','url','order','same_path','controller']:
            bad=copy.deepcopy(actual);actions=bad[0]['then']
            if mutation=='version':actions[0]['version']=None
            if mutation=='url':actions[2]['source']='https://neutral.example/wrong'
            if mutation=='order':actions[1],actions[2]=actions[2],actions[1]
            if mutation=='same_path':actions[1]['destination']['path']=copy.deepcopy(actions[1]['source'])
            if mutation=='controller':actions[1]['destination']['path']['kind']='controller'
            self.assertFalse(reviewed_match('a18',bad,ref),mutation)
    def test_group_membership_is_declared_nl_obligation_not_generic_user_relaxation(self):
        ref=self.q('enable passwordless sudo for group="wheel"; create user with name="ansible", supplemental groups="wheel"')
        primary=self.q('create group with name="wheel"; enable passwordless sudo for group="wheel"; create user with name="ansible", primary group="wheel"')
        self.assertTrue(reviewed_match('a20',primary,ref));self.assertNotEqual(primary,ref)
        for text in ['enable sudo for group="wheel"; create user with name="ansible", supplemental groups="wheel"',
                     'enable passwordless sudo for group="wheel"; create user with name="other", supplemental groups="wheel"',
                     'enable passwordless sudo for group="wheel"; create user with name="ansible"',
                     'create group with name="other"; enable passwordless sudo for group="wheel"; create user with name="ansible", supplemental groups="wheel"']:
            self.assertFalse(reviewed_match('a20',self.q(text),ref))
    def test_literal_key_path_does_not_equal_home_relative(self):
        a=self.q('create ssh key for user="probe" at "/.ssh/key"');b=self.q('create ssh key for user="probe" with name="key"')
        self.assertFalse(reviewed_match('a21',a,b));self.assertTrue(reviewed_match('a21',a,a))
    def test_exact_json_pointer_diff_reconstructs_arrays_and_types(self):
        before={'a':[{'x':1},2,3],'b':'before','c':True};after={'a':[{'x':[4]}],'b':'after','d':None}
        result=copy.deepcopy(before)
        for op in patch(before,after):
            parts=[p.replace('~1','/').replace('~0','~') for p in op['path'].split('/')[1:]];parent=result
            for part in parts[:-1]:parent=parent[int(part)] if isinstance(parent,list) else parent[part]
            key=int(parts[-1]) if isinstance(parent,list) else parts[-1]
            if op['op']=='remove':del parent[key]
            elif isinstance(parent,list) and op['op']=='add':parent.insert(key,copy.deepcopy(op['after']))
            else:parent[key]=copy.deepcopy(op['after'])
        self.assertEqual(result,after)
