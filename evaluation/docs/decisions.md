# Darsh's evaluation decisions

## Decisions

- Use a new handbook-v3 improved variant with positive syntax/path/metadata/action/condition/KB reference content, removing defensive instructions and self-checks; retain v2, preserve compact-v1, and keep demonstrations identical.

- Main lineup: OpenAI gpt-6.1-sol; newest Claude Opus through ANTHROPIC_API_KEY; router deepseek-v4.1-flash, deepseek-v4-flash, glm-5.3 and qwen3.8-flash. Drop GPT-5.5, Astra, Fable, Sonnet and local Qwen 4B/9B from the main matrix.
- Use HIGH reasoning for every model that supports it and record the parameters actually sent.
- Use ten repeats per task/model/prompt variant, replacing five, to match the count in paper section 6.3.
- Keep Claude Opus pending/skippable until its key arrives; it must not block the other models.
- Show full prompt texts and updated costs before a paid matrix run; do not start that matrix until Darsh approves.
- Allow only one or two single-call connectivity checks per new model before matrix approval.
- Preserve the original baseline as a named version; track prompt improvements separately, avoid test-data leakage, preserve historical work, and organize the repository for discoverability.

PR #35 exists at https://github.com/counc009/state_based/pull/35; decisions are also recorded under `## Decisions` in its local PR fixes notes.

- Darsh: Anthropic provider cap is $22 until a top-up; retain resumability and continue other models when Claude reaches its cap. Anthropic key is now available and latest Opus is enabled. No paid matrix until V3 approval.

- Darsh APPROVES the full six-model × both-variant × 21-task × ten-repeat paid matrix; keep Anthropic cumulative accounting at $22 and all accounting at $110.
- Run durably in the background with resume and bounded transient-error retries/backoff; keep failure records and all planned cells in reported denominators.
- Primary “correct” is normalized reference-effect match; separately flag the two discrepant supplied references, and score native parse/semantics, interpretation and applicable NL obligations.
- Produce no charts. Publish per-call CSV/JSON, model×variant and task×model×variant CSVs plus original paper baseline counts on the fork branch; report exact raw URLs and the summary table.
