# Aaron: NL-to-FQL follow-up facts

Source: evaluation/nl-fql-refresh at 8926470618ce6fea0e26c0126829cbd8241d7d76, matching the public fork branch. No paid calls or builds were needed for these answers.

## 1. Demonstrations

There is no fixed global set of four. Each target has four frozen demonstrations; both variants use exactly the same four for that target, in the same order. Across the 21 targets there are 37 distinct demonstrations: 19 exact benchmark tasks and 18 expansion tasks. No target appears in its own prompt. Demonstrations are stored in ignored recovered/imported input files, not inside either system-prompt text file. The imported message contents and every set were checked against the actual full-run frozen manifest. These input files are local recovered artifacts, not committed files on PR #35.

All NL/FQL line numbers below refer to `/home/user/workspaces/state_based/evaluation/datasets/imported-private.json`. Benchmark matches are exact NL and exact original reference FQL; all outside-pool entries are not one of the 21 benchmark tasks.

**a01** — exact benchmark p01. NL line 552; FQL line 556.
- NL: Create directory /srv/www
- FQL: `create directory at /srv/www`

**a02** — exact benchmark p05. NL line 26; FQL line 30.
- NL: Delete the directory /home/mydata/web
- FQL: `delete directory at /home/mydata/web`

**a03** — exact benchmark p15. NL line 34; FQL line 38.
- NL: Delete the contents of the /home/mydata/web directory
- FQL: `delete files in /home/mydata/web`

**a04** — exact benchmark p03. NL line 222; FQL line 226.
- NL: Copy the file /scratch/file.txt to /home/user/data.txt
- FQL: `copy file from "/scratch/file.txt" to "/home/user/data.txt"`

**a05** — exact benchmark p12. NL line 171; FQL line 175.
- NL: Move the file at /scratch/file.txt to /home/user/data.txt
- FQL: `move file from "/scratch/file.txt" to "/home/user/data.txt"`

**a06** — exact benchmark p13. NL line 179; FQL line 183.
- NL: Create the file /etc/file.txt with the contents ``beginning'' if it does not already exist
- FQL: `if file "/etc/file.txt" not exists then create file at "/etc/file.txt" with content="beginning"`

**a07** — exact benchmark p11a. NL line 375; FQL line 379.
- NL: Copy all .war files from /backup on the controller into /tmp on the remote
- FQL: `copy files with glob="*.war" from controller /backup to remote /tmp`

**a08** — exact benchmark p11b. NL line 324; FQL line 328.
- NL: Copy all .war files from /tmp on the remote machine into /backup on the controller
- FQL: `copy files with glob="*.war" from remote /tmp to controller /backup`

**a09** — exact benchmark p07. NL line 1003; FQL line 1007.
- NL: Clone the release1.8.4 branch from the ansible/ansible github repo to /ansible using https
- FQL: `clone github repository with name=ansible/ansible, branch="release1.8.4" into /ansible via https`

**a10** — exact benchmark p02. NL line 595; FQL line 599.
- NL: Permanently set the environment variable LC_ALL to ``C'' system-wide
- FQL: `set environment variable LC_ALL to "C"`

**a12** — exact benchmark p14. NL line 477; FQL line 481.
- NL: For Debian, restart the system if it is needed
- FQL: `if os is Debian and reboot required then reboot`

**a13** — exact benchmark p04. NL line 18; FQL line 22.
- NL: Set permissions for the files and directories under /srv/path so that all users can list and read all files but only the owner can write
- FQL: `set file permissions in /srv/path to read=all, write=owner, list directory=all`

**a14** — exact benchmark p06. NL line 238; FQL line 242.
- NL: Create a Python 3.10 virtual environment at /user/home/venv and install numpy in it
- FQL: `create virtual environment with python="3.10" in /user/home/venv; install numpy in virtual environment at /user/home/venv`

**a15** — exact benchmark p08. NL line 587; FQL line 591.
- NL: For Debian and RedHat based systems, install numpy
- FQL: `if os is Debian based or os is RedHat based then install numpy`

**a16** — exact benchmark p16. NL line 195; FQL line 199.
- NL: Install zsh, set it as the user `dev''s default shell, and ensure its configuration file exists
- FQL: `install zsh; set default shell for user="dev" to zsh; if zsh configuration file for user="dev" not exists then create zsh configuration file for user="dev"`

**a18** — exact benchmark p17. NL line 791; FQL line 795.
- NL: For RedHat and Ubuntu, install the lastest version of postfix, backup its default configuration file, and download the configuration file from http://example.com/cfg.ubuntu for Ubuntu and http://example.com/cfg.redhat for RedHat
- FQL: `if os is RedHat or os is Ubuntu then install postfix with version=latest; copy postfix configuration file to ?backup. if os is Ubuntu then download postfix configuration file from "http://example.com/cfg.ubuntu". if os is "RedHat" then download postfix configuration file from "http://example.com/cfg.redhat"`

**a19** — exact benchmark p18. NL line 42; FQL line 46.
- NL: For RedHat, install apache server, ensure the home page exists, and create a `webdev' user
- FQL: `if os is RedHat then install apache server; create user with name=webdev; if apache server html home page file not exists then create apache server html home page file`

**a20** — exact benchmark p19. NL line 434; FQL line 438.
- NL: Enable passwordless sudo for a `wheel' group and create an `ansible' user in that group
- FQL: `enable passwordless sudo for group=wheel; create user with name=ansible in supplemental groups=wheel`

**a21** — exact benchmark p20. NL line 748; FQL line 752.
- NL: For Debian and RedHat, install and start an ssh client and server and generated an ssh key for `fizbaz' at /.ssh/fizbaz_rsa
- FQL: `if os is Debian or os is RedHat then install ssh client; install ssh server; start ssh server service; create ssh key for user="fizbaz", name="fizbaz_rsa"`

**a22** — outside the 21-task benchmark; not an exact benchmark task. NL line 144; FQL line 148.
- NL: Ensure /work/private is a directory accessible only by its owner (mode 0700), preserving any existing contents.
- FQL: `create directory at /work/private with read=owner, write=owner, list directory=owner`

**a27** — outside the 21-task benchmark; not an exact benchmark task. NL line 187; FQL line 191.
- NL: Copy the remote file /work/source to /work/dest/data, creating the destination directory if needed and keeping the source.
- FQL: `create directory at /work/dest; copy file from remote /work/source to remote /work/dest/data`

**a31** — outside the 21-task benchmark; not an exact benchmark task. NL line 340; FQL line 344.
- NL: Delete only top-level regular files matching *.tmp in /work/cache, including hidden matches. Preserve directories, nested files, and nonmatches.
- FQL: `delete files in /work/cache with glob="*.tmp"`

**a32** — outside the 21-task benchmark; not an exact benchmark task. NL line 630; FQL line 634.
- NL: For /work/tree and its contents, grant owner read/write and everyone read; grant directory traversal without making initially nonexecutable regular files executable.
- FQL: `set file permissions in /work/tree to read=all, write=owner, list directory=all`

**a40** — outside the 21-task benchmark; not an exact benchmark task. NL line 93; FQL line 97.
- NL: Ensure the deploy group exists and the app user exists with deploy as its primary group and a home directory.
- FQL: `create group with name=deploy; create user with name=app in primary group=deploy`

**a42** — outside the 21-task benchmark; not an exact benchmark task. NL line 85; FQL line 89.
- NL: Set the existing app user primary group to deploy, preserving its existing home directory and its contents.
- FQL: `create user with name=app in primary group=deploy`

**a43** — outside the 21-task benchmark; not an exact benchmark task. NL line 799; FQL line 803.
- NL: Set the existing app user login shell to /bin/bash without changing its UID or home contents.
- FQL: `set default shell for user=app to bash`

**a44** — outside the 21-task benchmark; not an exact benchmark task. NL line 858; FQL line 862.
- NL: Remove the retired user account, retaining /home/retired and all its contents.
- FQL: `delete user with name=retired`

**a45** — outside the 21-task benchmark; not an exact benchmark task. NL line 77; FQL line 81.
- NL: Remove the retired user and its home directory /home/retired while preserving /home/active.
- FQL: `delete user with name=retired; delete directory at /home/retired`

**a46** — outside the 21-task benchmark; not an exact benchmark task. NL line 834; FQL line 838.
- NL: Lock password authentication for the existing app user without replacing its stored password hash; retain the account.
- FQL: `disable password for user=app`

**a52** — outside the 21-task benchmark; not an exact benchmark task. NL line 426; FQL line 430.
- NL: Clone /fixtures/repo into /work/checkout and check out its release branch; update an existing checkout from main if present.
- FQL: `clone git repository from /fixtures/repo with branch=release into /work/checkout`

**a53** — outside the 21-task benchmark; not an exact benchmark task. NL line 442; FQL line 446.
- NL: Clone main from /fixtures/repo to /work/checkout if absent. If a checkout already exists, preserve its current commit even if main has advanced.
- FQL: `if directory /work/checkout not exists then clone git repository from /fixtures/repo with branch=main into /work/checkout`

**a54** — outside the 21-task benchmark; not an exact benchmark task. NL line 450; FQL line 454.
- NL: Ensure /work/checkout is checked out at tag v1 from /fixtures/repo, even when an existing checkout follows main.
- FQL: `clone git repository from /fixtures/repo with tag=v1 into /work/checkout`

**a62** — outside the 21-task benchmark; not an exact benchmark task. NL line 987; FQL line 991.
- NL: Remove the unused obsolete group if it exists, preserving the active group and its GID.
- FQL: `delete group with name=obsolete`

**a65** — outside the 21-task benchmark; not an exact benchmark task. NL line 536; FQL line 540.
- NL: Ensure export ASTRO=1 is the last line of /work/profile, preserving existing lines. The setting is initially absent or already last.
- FQL: `write "export ASTRO=1" to /work/profile at position=end`

**a66** — outside the 21-task benchmark; not an exact benchmark task. NL line 544; FQL line 548.
- NL: Ensure # managed is the first line of /work/header, retaining all original body lines. The header is initially absent or already first.
- FQL: `write "# managed" to /work/header at position=start`

**a68** — outside the 21-task benchmark; not an exact benchmark task. NL line 289; FQL line 293.
- NL: Create /work/cache only if the marker file /work/enabled exists. The cache is initially absent and must remain absent without the marker.
- FQL: `if file /work/enabled exists then create directory at /work/cache`

**a70** — outside the 21-task benchmark; not an exact benchmark task. NL line 332; FQL line 336.
- NL: Copy the contents of remote /work/source into /work/dest, preserving hidden files, nested structure, the source, and unrelated destination files. Both directories exist.
- FQL: `copy directory from remote /work/source to remote /work/dest`

Frozen target → demonstration IDs (order preserved):

| Target | Four demonstrations |
|---|---|
| a01 | a13, a02, a03, a19 |
| a02 | a03, a45, a42, a40 |
| a03 | a02, a45, a42, a22 |
| a04 | a05, a06, a27, a16 |
| a05 | a04, a06, a14, a27 |
| a06 | a04, a05, a68, a27 |
| a07 | a08, a70, a31, a13 |
| a08 | a07, a70, a31, a13 |
| a09 | a52, a20, a53, a54 |
| a10 | a12, a14, a13, a42 |
| a11 | a16, a65, a66, a01 |
| a12 | a27, a15, a10, a53 |
| a13 | a32, a31, a07, a08 |
| a14 | a15, a19, a05, a45 |
| a15 | a14, a19, a21, a12 |
| a16 | a40, a18, a43, a19 |
| a17 | a46, a19, a42, a44 |
| a18 | a16, a15, a19, a04 |
| a19 | a14, a15, a40, a16 |
| a20 | a62, a40, a09, a42 |
| a21 | a15, a19, a14, a12 |

Counts below are original-reference effect-tree matches, baseline/v3, each out of 10; columns use the six model IDs in the header. API failures and incomplete outputs stay in the denominator.

| Task/paper | gpt-6.1-sol | claude-opus-5-5 | deepseek-v4.1-flash | deepseek-v4-flash | glm-5.3 | qwen3.8-flash |
|---|---:|---:|---:|---:|---:|---:|
| a01/p01 | 10/10 | 10/10 | 10/10 | 9/10 | 9/10 | 10/10 |
| a02/p05 | 10/10 | 10/10 | 10/10 | 10/10 | 8/10 | 10/9 |
| a03/p15 | 0/10 | 0/10 | 0/10 | 0/9 | 2/9 | 0/10 |
| a04/p03 | 10/10 | 10/10 | 10/10 | 9/10 | 9/10 | 9/10 |
| a05/p12 | 10/10 | 10/10 | 10/10 | 8/10 | 9/10 | 4/10 |
| a06/p13 | 10/10 | 10/10 | 9/8 | 3/9 | 7/8 | 7/9 |
| a07/p11a | 10/10 | 10/10 | 10/10 | 10/10 | 10/10 | 9/10 |
| a08/p11b | 10/10 | 10/10 | 10/10 | 10/10 | 10/10 | 9/9 |
| a09/p07 | 0/10 | 0/10 | 0/6 | 0/10 | 0/0 | 0/7 |
| a10/p02 | 0/10 | 0/10 | 0/10 | 0/10 | 0/10 | 0/10 |
| a12/p14 | 0/10 | 0/9 | 0/10 | 0/10 | 0/10 | 0/8 |
| a13/p04 | 0/10 | 10/10 | 6/6 | 1/5 | 8/6 | 6/7 |
| a14/p06 | 0/10 | 0/10 | 0/10 | 0/10 | 0/10 | 0/9 |
| a15/p08 | 8/9 | 0/5 | 0/9 | 0/8 | 0/1 | 0/8 |
| a16/p16 | 0/10 | 0/10 | 0/7 | 1/10 | 0/9 | 0/9 |
| a18/p17 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 |
| a19/p18 | 0/6 | 0/8 | 0/0 | 0/0 | 0/0 | 0/0 |
| a20/p19 | 0/5 | 0/9 | 0/9 | 0/4 | 0/6 | 0/1 |
| a21/p20 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 | 0/0 |

The strict-reference-only correction changes only a21 in this table: baseline stays 0 for all models; v3 becomes 10,10,3,6,10,7 in the header model order. All other cells are unchanged. Task-scoped relaxed matching is not used here.

Removing all benchmark tasks that occur as a demonstration leaves only a11/p09 and a17/p10: 20 calls per model/variant. Starting with all 21 tasks or the 19-task set excluding a18/a21 leaves the same two tasks, since a18 and a21 are themselves demo-used tasks. Results are identical under original and strict-reference-only scoring.

| Model | From 21 tasks: baseline | From 21 tasks: v3 | From 19 tasks: baseline | From 19 tasks: v3 |
|---|---:|---:|---:|---:|
| gpt-6.1-sol | 10/20 (50%) | 20/20 (100%) | 10/20 (50%) | 20/20 (100%) |
| claude-opus-5-5 | 5/20 (25%) | 20/20 (100%) | 5/20 (25%) | 20/20 (100%) |
| deepseek-v4.1-flash | 10/20 (50%) | 20/20 (100%) | 10/20 (50%) | 20/20 (100%) |
| deepseek-v4-flash | 10/20 (50%) | 20/20 (100%) | 10/20 (50%) | 20/20 (100%) |
| glm-5.3 | 10/20 (50%) | 20/20 (100%) | 10/20 (50%) | 20/20 (100%) |
| qwen3.8-flash | 10/20 (50%) | 18/20 (90%) | 10/20 (50%) | 18/20 (90%) |

These 2-task subsets are small and do not establish held-out generalization. The frozen prompts exclude their own target but contain other benchmark targets as demonstrations.

## 2. Code paths

- Prompt assembly: evaluation/code/import_frozen.py:convert (line 8) copies recovered messages; evaluation/code/evaluate.py:freeze (line 38) replaces only the system guide, preserves demonstrations/target, expands repetitions and rejects target-ID inclusion.
- Generation: evaluation/code/matrix_run.py:Matrix.process (line 86)/run (line 140) reserves, retries and checkpoints; evaluation/code/evaluate.py:build_request (line 103)/request (line 140) sends the provider request and extracts raw text.
- Parse: evaluation/native/effects.ml top-level driver (lines 122–132), calling Fql.Parser.query / Fql.Lexer.token at line 126; grammar lib/fql/parser.mly:query line 22, lexer lib/fql/lexer.mll:token line 5.
- Semantic processing: lib/fql/semant.ml:Semant.analyze_top line 908 (analyze_base line 898, analyze_atom line 198); resolves actions/arguments/KB/OS context into the semantic AST; invoked by effects.ml line 129.
- Native interpretation: bin/query_interp.ml top-level driver line 16, semantic lowering at lines 38–40 and Interp.interpret at line 47; parses module specs, lowers FQL and symbolically interprets possible behaviors. It does not run managed-host commands.
- Reference-effect comparison: evaluation/code/export_matrix.py:export line 68, probe/driver bridge evaluation/code/semantic_audit.py:probe line 14; original comparison at export_matrix.py line 101 is semantic acceptance plus exact equality of serialized effect trees. evaluation/native/effects.ml:sequence line 116 flattens sequences/retains conditionals, and serializers normalize unknown/bound names and supplemental-group ordering. Strict corrected-reference rescoring uses evaluation/code/review_rescore.py:main lines 108/123; reviewed_match line 41 is the separately declared relaxed sensitivity.
- Aggregation: evaluation/code/export_matrix.py:summarize line 46, called near lines 165–166 for model×variant/task×model×variant summaries; counts ref_match true, retains planned denominators and computes Wilson intervals.

## 3. Arbitrary NL input / validity-only mode

At the start of this turn there is no one-command raw-NL-list importer or pure parsing-only CLI. evaluate.py freeze accepts tasks with task_id, demonstration_ids and full messages, not a JSON list of descriptions. The fixed frozen demonstration inputs are private recovered data; no online retrieval implementation is committed. Generation itself is Python standard-library code and needs no native build.

Existing command shape after preparing that schema:

```sh
python3 evaluation/code/evaluate.py freeze --dataset /path/aaron-inputs.json --models sol --variants handbook-v3 --output /tmp/aaron-manifest.json
python3 evaluation/code/evaluate.py estimate --manifest /tmp/aaron-manifest.json
# A funded run would use matrix_run.py with an explicit total/provider guard.
```

The native diagnostic needs `opam exec -- dune build evaluation/native/effects.exe` in a fresh checkout. That binary reports the separate parsed flag, but also runs semantics and serializes effects. Its exit code 0 means more than parsing. Counting nonempty parsed=true counts syntax only, including semantic_error; counting status=ok counts the supported parse+semantic+serializer path. The existing check_query.py uses dune exec query-interp, so it is not a parser-only checker. evaluate.py analyze runs --checker only on completed API responses, and checker_pass counts exit zero; it does not inspect the native JSON parsed flag automatically.

The later instruction in this turn now authorizes building an arbitrary-dataset adapter and running separate parse/semantic/native-interpretation counts. Those implementation/run results will be reported separately; they were not already an existing command.


Subsequent authorized implementation: `dataset_validity.py` now provides the separate prior-work dataset validity experiment. The historical facts above describe the original matrix before that new implementation.
