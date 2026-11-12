"""NL-detail candidate screen; Ansible text is used only for excluded task-style modules."""
import re

STYLES={'debug','assert','include','include_tasks','include_role','include_vars','import_tasks','import_role','import_playbook','set_fact','setup','gather_facts','meta','vars_files'}
STYLE_NL=re.compile(r'\b(debug|assert|assertion|include|import|set[ _-]+facts?|gather[ _-]+facts?|load[ _-]+vars|display|print|show)\b',re.I)
GENERIC=set('a an the this that these those all any some each other new old existing current default required necessary optional proper correct specific desired appropriate latest absent present installed removed enabled disabled started stopped running system global local remote source destination target ensure ensures make sure add adds adding remove removes removing delete deletes deleting create creates creating install installs installing uninstall update updates updating upgrade upgrades upgrading configure configures configuring setup set sets setting enable enables enabling disable disables disabling start starts starting stop stops stopping restart reload reboot copy copies copying move moves moving download downloads downloading fetch get find check checks checking verify validate perform manage apply run execute command commands task tasks step steps debug assert include import fact facts gather load print display show package packages software dependency dependencies service services daemon daemons file files directory directories folder folders path paths symlink symlinks link links symbolic content contents configuration configurations config configs setting settings option options value values variable variables environment key keys ssh public private password passwords user users account accounts group groups permission permissions mode owner ownership name names repo repository repositories server servers client clients application applications app apps database databases version versions template templates from to at in on into under with without for of and or as is are be been has have not if when then only using use via it its them their based by also get data information message messages yes no true false'.split())

GENERIC.update("network networks networking image images container containers volume volumes role roles module modules handler handlers playbook playbooks credential credentials token tokens certificate certificates tls ssl port ports firewall rule rules disk disks partition partitions mount mounts filesystem filesystems storage cluster clusters node nodes host hosts machine machines instance instances resource resources cron crontab job jobs entry entries record records line lines linesinfile default defaults secure security required necessary init initialize initialization initialized enablement installable updated configured started stopped cleaned clean cleanup prepare preparation generate generated creation deletion removal configuration provisioning provision bootstrap apply applied basic common custom additional available availability ensure that enable debug logging log logs backup backups symlinking symbolic destination source associated related dependent setting parameters parameter argument arguments argumentsfor enabledfor passwordless sudo access database db schema tables table authentication authorization context detail details output input result results content mode modes managed unmanaged configurationfile configurationfiles".split())

def normalize(value):
    return re.sub(r'^\s*name\s*:\s*','',value,flags=re.I).strip()


def module_style(output):
    if not isinstance(output,str):return False
    matches=[]
    for line in output.splitlines():
        m=re.match(r'^(\s*)(?:-\s+)?([A-Za-z][\w.]*)\s*:',line)
        if m:matches.append((len(m[1]),m[2].split('.')[-1]))
    if not matches:return False
    minimum=min(n for n,_ in matches)
    return any(n==minimum and key in STYLES for n,key in matches)


def candidate(row):
    raw=row.get('input')
    if not isinstance(raw,str):return False,'invalid_input',''
    nl=normalize(raw)
    if not nl:return False,'empty_input',nl
    if re.search(r'{{|}}|{%|%}',nl):return False,'unresolved_jinja',nl
    if STYLE_NL.search(nl) or module_style(row.get('output')):return False,'excluded_task_style',nl
    words=re.findall(r'[\w][\w.+@:/-]*',nl.lower())
    concrete=[w for w in words if w not in GENERIC and len(w)>1]
    if not concrete:return False,'no_concrete_object',nl
    return True,'heuristic_survivor',nl


def support_hint(nl):
    """Conservative lexical hint only; never used to exclude a row."""
    text=nl.lower()
    if re.search(r'\b(install|uninstall|remove|upgrade|package)\b',text):
        return 'known_kb_package_candidate' if re.search(r'\b(bash|zsh|postfix|apache|numpy|ssh)\b',text) else 'may_require_package_kb_entry'
    if re.search(r'\b(start|stop|restart|service)\b',text):
        return 'known_kb_service_candidate' if re.search(r'\b(postfix|apache|ssh)\b',text) else 'may_require_service_kb_entry'
    if re.search(r'\b(file|directory|folder|user|group|permission|environment|git|clone)\b',text):return 'primitive_action_candidate'
    return 'unknown'
