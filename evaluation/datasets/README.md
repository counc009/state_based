# Input contract

Import existing FQL messages with `../code/import_frozen.py`. Private dataset files end in `-private.json` and are ignored by Git. The importer copies repetition-zero FQL tasks and hashes the complete source without modifying it. It excludes code-judgment tasks and top-level outcome fields.

Each `tasks` entry has `task_id`, `demonstration_ids`, and `messages` (only `role` and string `content`). The first message is the system guide; the last is the target NL request. Preserve the intervening demonstration messages in exact order. Do not include the target reference FQL, oracle labels or candidate programs in those messages. Target IDs cannot appear in demonstration IDs. This ID check cannot detect paraphrased leakage; inspect demonstration construction separately.

The recovered suite has 21 original tasks, four retrieved demonstrations per task, target excluded, and examples from the original plus supported authored expansion pool. It is an existing development suite with same-family examples, not an independently held-out benchmark. Historical source files remain on the VPS; no private corpus or raw outputs are redistributed in Git.
