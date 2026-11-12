# Open-KB prompt experiment

Each cell below is grammar parses / semantic acceptance / native symbolic interpretation, out of the same 300 sampled rows (253 distinct normalized descriptions). These are validity counts, not intent correctness or execution tests. Response availability is reported separately.

| Model | Original + Example | Original + fallback | Open prompt + Example | Open prompt + fallback |
|---|---:|---:|---:|---:|
| gpt-6.1-sol | 250 / 67 / 65 | 250 / 212 / 208 | 255 / 55 / 55 | 255 / 227 / 221 |
| claude-opus-5-5 | 66 / 54 / 52 | 66 / 61 / 58 | 182 / 38 / 38 | 182 / 176 / 173 |
| glm-5.3 | 218 / 52 / 52 | 218 / 205 / 200 | 243 / 43 / 42 | 243 / 226 / 220 |
| deepseek-v4.1-flash | 253 / 61 / 60 | 253 / 232 / 228 | 256 / 54 / 54 | 256 / 237 / 230 |
| qwen3.8-flash | 219 / 50 / 50 | 219 / 200 / 192 | 231 / 53 / 52 | 231 / 214 / 205 |
| deepseek-v4-flash | 245 / 64 / 61 | 245 / 239 / 228 | 252 / 57 / 56 | 252 / 246 / 237 |

| Model | Original responses | Open responses | API failures | Budget pending | Deadline stopped | Billing pending |
|---|---:|---:|---:|---:|---:|---:|
| gpt-6.1-sol | 300 | 300 | 0 | 0 | 0 | 0 |
| claude-opus-5-5 | 300 | 236 | 0 | 64 | 0 | 0 |
| glm-5.3 | 300 | 300 | 0 | 0 | 0 | 0 |
| deepseek-v4.1-flash | 300 | 300 | 0 | 0 | 0 | 0 |
| qwen3.8-flash | 300 | 300 | 0 | 0 | 0 | 0 |
| deepseek-v4-flash | 261 | 262 | 0 | 0 | 38 | 0 |

| Condition | At least one semantically valid | All responding valid | All six responded and valid |
|---|---:|---:|---:|
| original+example | 89 | 32 | 32 |
| original+fallback | 267 | 42 | 42 |
| openkb+example | 81 | 34 | 25 |
| openkb+fallback | 284 | 183 | 130 |

Paid generation start: 2026-11-12T22:09:28.745335+00:00; hard deadline: 2026-11-12T22:44:28.745335+00:00. Guard: $12 total / $7 Anthropic, three attempts maximum per cell.

Accounted USD 11.500138654513 = known token charges 6.792664830311 + unknown-billing reservations 4.707473824202; Anthropic 4.241164000000. Accounting at frozen rates is not a provider invoice.

The source corpus, NL/Ansible rows, private message manifests and provider reasoning remain private. IDs/hashes, generated formal queries, costs and native validity diagnostics are public. No LLM judge or managed-host runtime tests were used.
