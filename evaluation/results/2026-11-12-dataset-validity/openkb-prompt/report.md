# Open-KB prompt experiment

Each cell below is grammar parses / semantic acceptance / native symbolic interpretation, out of the same 300 sampled rows (253 distinct normalized descriptions). These are validity counts, not intent correctness or execution tests. Response availability is reported separately.

| Model | Original + Example | Original + fallback | Open prompt + Example | Open prompt + fallback |
|---|---:|---:|---:|---:|
| gpt-6.1-sol | 250 / 67 / 65 | 250 / 212 / 208 | 255 / 55 / 55 | 255 / 227 / 221 |
| claude-opus-5-5 | 66 / 54 / 52 | 66 / 61 / 58 | 231 / 49 / 49 | 231 / 225 / 220 |
| glm-5.3 | 218 / 52 / 52 | 218 / 205 / 200 | 243 / 43 / 42 | 243 / 226 / 220 |
| deepseek-v4.1-flash | 253 / 61 / 60 | 253 / 232 / 228 | 256 / 54 / 54 | 256 / 237 / 230 |
| qwen3.8-flash | 219 / 50 / 50 | 219 / 200 / 192 | 231 / 53 / 52 | 231 / 214 / 205 |
| deepseek-v4-flash | 274 / 77 / 74 | 274 / 264 / 252 | 287 / 69 / 68 | 287 / 279 / 270 |

| Model | Original responses | Open responses | API failures | Budget pending | Deadline stopped | Billing pending |
|---|---:|---:|---:|---:|---:|---:|
| gpt-6.1-sol | 300 | 300 | 0 | 0 | 0 | 0 |
| claude-opus-5-5 | 300 | 300 | 0 | 0 | 0 | 0 |
| glm-5.3 | 300 | 300 | 0 | 0 | 0 | 0 |
| deepseek-v4.1-flash | 300 | 300 | 0 | 0 | 0 | 0 |
| qwen3.8-flash | 300 | 300 | 0 | 0 | 0 | 0 |
| deepseek-v4-flash | 300 | 300 | 0 | 0 | 0 | 0 |

| Condition | At least one semantically valid | All responding valid | All six responded and valid |
|---|---:|---:|---:|
| original+example | 93 | 32 | 32 |
| original+fallback | 275 | 42 | 42 |
| openkb+example | 83 | 34 | 34 |
| openkb+fallback | 290 | 182 | 182 |

Historical initial guard $12/$7 applies to the original35-minute phase only. The separately authorized40-minute fill has a shared $6/$3 guard; this prompt received $1.422328066761 of the fill cost. Cumulative prompt costs below include that allocation once. Pre-fill exports are preserved under fill-in-2026-11-12/pre-fill.

Initial generation start: 2026-11-12T22:09:28.745335+00:00; hard deadline: 2026-11-12T22:44:28.745335+00:00. Guard: $12 total / $7 Anthropic, three attempts maximum per cell.

Accounted USD 12.922466721274 = known token charges 8.014768391897 + unknown-billing reservations 4.907698329377; Anthropic 5.382204000000. Accounting at frozen rates is not a provider invoice.

The source corpus, NL/Ansible rows, private message manifests and provider reasoning remain private. IDs/hashes, generated formal queries, costs and native validity diagnostics are public. No LLM judge or managed-host runtime tests were used.
