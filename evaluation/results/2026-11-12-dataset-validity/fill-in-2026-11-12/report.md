# Completed missing-cell fill

All **141/141** missing cells now have completed responses. Each prompt now has **1,800/1,800** responses: 300 per model. All **3,459** previously completed text files and canonical provider-response files are byte-identical. No invalid-but-existing answer was rerun.

Fresh generation stopped naturally at 2026-11-12T23:45:13.484576+00:00, before the immutable 2026-11-12T23:59:04.742142+00:00 deadline. The 64 Opus cells completed before the 77 DeepSeek cells were admitted. There are 183 physical requests: 141 completed and 42 transport-error receipts; none remain active.

## Costs counted once

| Phase | Accounted USD | Known-token USD | Unknown-billing reserve USD | Anthropic USD |
|---|---:|---:|---:|---:|
| initial-original | 19.985888492705 | 9.459852820346 | 10.526035672359 | 6.290804000000 |
| initial-openkb | 11.500138654513 | 6.792664830311 | 4.707473824202 | 4.241164000000 |
| fill-in-2026-11-12 | 1.961241648367 | 1.361642539608 | 0.599599108759 | 1.141040000000 |
| Cumulative | 33.447268795585 | 17.614160190265 | 15.833108605320 | 11.673008000000 |

The original classifier is included once in the initial-original phase. Fill charges are allocated between source runs once; rescoring under a second KB adds no paid calls. Historical $20/$8 and $12/$7 guards remain frozen phase limits, with the fresh $6/$3 fill independently audited. These are local frozen-rate accounting values, not invoices.

## Current four-condition validity counts

Each entry is grammar parses / semantic acceptance / native interpretation, out of the same 300 sampled rows (253 distinct normalized descriptions). “Original” means handbook-v3 including its filled responses; “open” means handbook-v3-openkb including its filled responses. Initial partial reports are frozen under pre-fill/.

| Model | Original + Example | Original + fallback | Open + Example | Open + fallback |
|---|---:|---:|---:|---:|
| gpt-6.1-sol | 250/67/65 | 250/212/208 | 255/55/55 | 255/227/221 |
| claude-opus-5-5 | 66/54/52 | 66/61/58 | 231/49/49 | 231/225/220 |
| deepseek-v4.1-flash | 253/61/60 | 253/232/228 | 256/54/54 | 256/237/230 |
| deepseek-v4-flash | 274/77/74 | 274/264/252 | 287/69/68 | 287/279/270 |
| glm-5.3 | 218/52/52 | 218/205/200 | 243/43/42 | 243/226/220 |
| qwen3.8-flash | 219/50/50 | 219/200/192 | 231/53/52 | 231/214/205 |

| Condition | At least one semantically valid | All responding valid | Strictly all six responded and valid |
|---|---:|---:|---:|
| original+example | 93 | 32 | 32 |
| original+fallback | 275 | 42 | 42 |
| openkb+example | 83 | 34 | 34 |
| openkb+fallback | 290 | 182 | 182 |

All six models now responded in both prompt conditions; the two all-model columns therefore coincide. These counts measure formal validity, not user-intent correctness. No judge, VM or managed-host execution was used.

## Preservation and provenance

All 3,518 pre-fill public files are preserved with hashes. Old private manifests/ledgers and all previous attempt files remain intact; new target indices increase monotonically with fill-phase/source-attempt/hash provenance. Public snapshots contain already-published artifacts only. Corpus files, source NL/Ansible rows, private message manifests and provider reasoning remain private.
