# Offline reference review and rescore — 2026-11-04

No new model/API calls or charts. Original references and full-matrix results are unchanged. This is a **post-hoc sensitivity analysis informed by observed outputs**, not independent gold adjudication or a replacement for the original result.

## Conditions and scoring separation

- **a-original:** original references, original structural comparator. The model/variant summary is byte-identical to the published original.
- **b-strict-reference-only:** only the proposed canonical FQL change (a21's literal path), with original structural matching. This isolates reference correction from changes to comparison.
- **b-corrected / reviewed v2:** separate versioned references plus explicitly scoped comparison policies: OS action traces for a18/a21, backup-slot refinement only for a18, and the stated group-membership obligation for a20. a03 stays unchanged and unresolved. No other task's comparator changes.
- **c-exclude-four:** original matching, with a03/a18/a20/a21 removed; 17 tasks and 170 planned cells per model/variant.

Every summary CSV has exactly the original `model-variant-summary.csv` schema, including Wilson intervals, failure counts, historical cost and latency. Costs describe the retained historical cells, not additional spending. The extra discrepancy-count fields retain the original a03/a20 flags; the separate exclusion condition explicitly removes all four reviewed tasks. Failed/empty/incomplete cells are not dropped. Reviewed matching does not turn failed parsing into success.

| Model | Prompt | Original /210 | Strict refs only /210 | Reviewed v2 /210 | Exclude four /170 |
|---|---|---:|---:|---:|---:|
| claude-opus-5-5 | baseline | 85 (40.5%) | 85 (40.5%) | 85 (40.5%) | 85 (50.0%) |
| claude-opus-5-5 | v3 | 181 (86.2%) | 191 (91.0%) | 197 (93.8%) | 162 (95.3%) |
| deepseek-v4-flash | baseline | 71 (33.8%) | 71 (33.8%) | 73 (34.8%) | 71 (41.8%) |
| deepseek-v4-flash | v3 | 165 (78.6%) | 171 (81.4%) | 177 (84.3%) | 152 (89.4%) |
| deepseek-v4.1-flash | baseline | 85 (40.5%) | 85 (40.5%) | 85 (40.5%) | 85 (50.0%) |
| deepseek-v4.1-flash | v3 | 165 (78.6%) | 168 (80.0%) | 168 (80.0%) | 146 (85.9%) |
| glm-5.3 | baseline | 82 (39.0%) | 82 (39.0%) | 82 (39.0%) | 80 (47.1%) |
| glm-5.3 | v3 | 149 (71.0%) | 159 (75.7%) | 165 (78.6%) | 134 (78.8%) |
| gpt-6.1-sol | baseline | 88 (41.9%) | 88 (41.9%) | 88 (41.9%) | 88 (51.8%) |
| gpt-6.1-sol | v3 | 180 (85.7%) | 190 (90.5%) | 204 (97.1%) | 165 (97.1%) |
| qwen3.8-flash | baseline | 74 (35.2%) | 74 (35.2%) | 74 (35.2%) | 74 (43.5%) |
| qwen3.8-flash | v3 | 154 (73.3%) | 161 (76.7%) | 169 (80.5%) | 143 (84.1%) |

The totals are 1,479 original matches, 1,525 with strict reference correction only, 1,567 with reviewed v2 policies, and 1,385/2,040 after exclusion. All original and corrected runs retain 2,520 planned cells. These rates use different definitions/denominators; Wilson intervals are descriptive and do not adjust for task/repeat correlation.

## Native and documentation evidence

[Ansible user documentation](https://docs.ansible.com/projects/ansible/latest/collections/ansible/builtin/user_module.html) distinguishes primary `group`, supplemental `groups`, and home-relative SSH filenames. [Ansible find documentation](https://docs.ansible.com/projects/ansible/latest/collections/ansible/builtin/find_module.html) documents `file_type:any`, hidden inclusion and nonrecursive enumeration. Native compiler/module source and all four query trees are included by path and hash. Candidate playbooks are **not executed**. Proposed a18/a20/a21 query/playbook pairs symbolically verify with possible assumptions/residual effects; a03's proposed `hidden` argument is unsupported. Both sudoers whitespace forms pass local read-only `visudo -cf` syntax checks.

## Task investigations

### a03

**NL request (verbatim):**

```text
Delete the contents of the /home/mydata/web directory
```

**Original reference FQL (verbatim):**

```text
delete files in /home/mydata/web
```

**Decision: unresolved reference/language adequacy, not a quotation normalizer bug.** The 58/60 V3 matches are valid matches to the supplied FQL, but `DeleteFiles(InPath)` asserts `is_file` on each child (`lib/fql/codegen.ml:535`; `modules/fs.type:21`), so the query is not a general description of arbitrary contents including subdirectories/symlinks. The supplied playbook deletes/recreates the parent, potentially losing its metadata, and its templated state fails native lowering. The two model delete/recreate outputs are not credited as equivalent parent-preserving deletion. V3 teaches the same supported `delete files` form as the reference.

Proposed separate playbook: `find file_type:any, hidden:true, recurse:false`, then remove each returned path. This keeps the parent and targets hidden files/directories too, but it has not been executed. Native validation rejects its `hidden` argument because the pinned module model lacks it. No fully faithful replacement FQL is claimed. V2 therefore retains the original FQL score as a limited-domain control and keeps a03 flagged; the exclusion analysis is the clean sensitivity.

**Proposed canonical FQL (separate v2 file; unchanged where no FQL correction is justified):**

```text
delete files in /home/mydata/web
```

**Exact original-to-proposed reference effect diff:**

```json
[]
```

**Representative output:** `sol--handbook-v3--a03--r0`

```text
delete files in "/home/mydata/web".
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[]
```

**Representative output:** `deepseek-v4-flash--handbook-v3--a03--r1`

```text
delete directory at "/home/mydata/web"; create directory at "/home/mydata/web"
```

Reviewed policy accepts: **False**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "replace",
    "path": "/0/kind",
    "before": "delete_files",
    "after": "delete_directory"
  },
  {
    "op": "add",
    "path": "/0/path",
    "after": {
      "kind": "remote",
      "destination": {
        "kind": "absolute",
        "value": "/home/mydata/web"
      }
    }
  },
  {
    "op": "remove",
    "path": "/0/paths",
    "before": {
      "kind": "in_path",
      "path": {
        "kind": "remote",
        "destination": {
          "kind": "absolute",
          "value": "/home/mydata/web"
        }
      }
    }
  },
  {
    "op": "add",
    "path": "/1",
    "after": {
      "kind": "create_directory",
      "destination": {
        "path": {
          "kind": "remote",
          "destination": {
            "kind": "absolute",
            "value": "/home/mydata/web"
          }
        },
        "owner": null,
        "group": null,
        "permissions": {
          "read": null,
          "write": null,
          "execute": null,
          "list_directory": null,
          "setuid": null,
          "setgid": null,
          "sticky": null
        }
      }
    }
  }
]
```

**Representative output:** `glm-5.3--handbook-v3--a03--r0`

```text
delete files in "/home/mydata/web"
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[]
```

**Proposed playbook candidate (not executed):**

```yaml
---
- name: Empty directory while preserving its parent
  hosts: all
  become: true
  tasks:
    - name: List immediate entries including hidden files and directories
      ansible.builtin.find:
        paths: /home/mydata/web
        file_type: any
        hidden: true
        recurse: false
      register: contents
    - name: Remove each entry while retaining the parent directory
      ansible.builtin.file:
        path: "{{ item.path }}"
        state: absent
      loop: "{{ contents.files }}"

```

Native original query/playbook status: `program_lowering_error`; proposed pair: `program_lowering_error`.

### a18

**NL request (verbatim):**

```text
For RedHat and Ubuntu, install the lastest version of postfix, backup its default configuration file, and download the configuration file from http://example.com/cfg.ubuntu for Ubuntu and http://example.com/cfg.redhat for RedHat
```

**Original reference FQL (verbatim):**

```text
if os is RedHat or os is Ubuntu then install postfix with version=latest; copy postfix configuration file to ?backup. if os is Ubuntu then download postfix configuration file from "http://example.com/cfg.ubuntu". if os is "RedHat" then download postfix configuration file from "http://example.com/cfg.redhat"
```

**Decision: structural comparator/refinement is too strict for 18 valid V3 outputs; 12 other valid outputs genuinely omit latest.** The original FQL's separate guarded download statements and the models' nested conditional forms yield the same ordered actions per OS. The symbolic backup destination is intentionally unspecified; a distinct concrete remote absolute backup path is an allowed refinement, not literal-tree equality. Other paths, metadata, URLs, package version and action order remain exact. V3 permits nested conditionals and explicit download paths, so it encourages valid forms absent from the reference's spelling; the native analyzer already normalizes named versus explicit configuration-file paths.

Of 60 V3 cells: 30 produce supported/interpreted trees. The reviewed policy accepts 18 (Sol 9, Opus 5, GLM 4). All 12 remaining supported trees omit `version="latest"`; the other 30 cells are invalid/empty/provider failures and remain failures. Reference-only correction changes no a18 score. `lib/fql/codegen.ml:742` distinguishes latest from an omitted version.

**Proposed canonical FQL (separate v2 file; unchanged where no FQL correction is justified):**

```text
if os is RedHat or os is Ubuntu then install postfix with version=latest; copy postfix configuration file to ?backup. if os is Ubuntu then download postfix configuration file from "http://example.com/cfg.ubuntu". if os is "RedHat" then download postfix configuration file from "http://example.com/cfg.redhat"
```

**Exact original-to-proposed reference effect diff:**

```json
[]
```

**Representative output:** `sol--handbook-v3--a18--r0`

```text
if os is RedHat or os is Ubuntu then install postfix with version="latest"; copy postfix configuration file to ?path; if os is Ubuntu then download file from "http://example.com/cfg.ubuntu" to "/etc/postfix/main.cf" otherwise download file from "http://example.com/cfg.redhat" to "/etc/postfix/main.cf"
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "add",
    "path": "/0/else/0/then/2",
    "after": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "Ubuntu"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.ubuntu",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.redhat",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ]
    }
  },
  {
    "op": "add",
    "path": "/0/then/2",
    "after": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "Ubuntu"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.ubuntu",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.redhat",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ]
    }
  },
  {
    "op": "remove",
    "path": "/2",
    "before": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "RedHat"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.redhat",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": []
    }
  },
  {
    "op": "remove",
    "path": "/1",
    "before": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "Ubuntu"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.ubuntu",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": []
    }
  }
]
```

Additional exact per-OS ordered-trace diff (control-flow spelling removed, all action values retained):

```json
[]
```

**Representative output:** `opus--handbook-v3--a18--r0`

```text
if os is Ubuntu or os is RedHat then install postfix; copy postfix configuration file to ?backup; if os is Ubuntu then download file from "http://example.com/cfg.ubuntu" to "/etc/postfix/main.cf" otherwise if os is RedHat then download file from "http://example.com/cfg.redhat" to "/etc/postfix/main.cf"
```

Reviewed policy accepts: **False**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "replace",
    "path": "/0/condition/value",
    "before": "RedHat",
    "after": "Ubuntu"
  },
  {
    "op": "replace",
    "path": "/0/else/0/condition/value",
    "before": "Ubuntu",
    "after": "RedHat"
  },
  {
    "op": "replace",
    "path": "/0/else/0/then/0/version",
    "before": "latest",
    "after": null
  },
  {
    "op": "add",
    "path": "/0/else/0/then/2",
    "after": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "Ubuntu"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.ubuntu",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": [
        {
          "kind": "conditional",
          "condition": {
            "kind": "os",
            "value": "RedHat"
          },
          "then": [
            {
              "kind": "download",
              "source": "http://example.com/cfg.redhat",
              "destination": {
                "path": {
                  "kind": "remote",
                  "destination": {
                    "kind": "absolute",
                    "value": "/etc/postfix/main.cf"
                  }
                },
                "owner": null,
                "group": null,
                "permissions": {
                  "read": null,
                  "write": null,
                  "execute": null,
                  "list_directory": null,
                  "setuid": null,
                  "setgid": null,
                  "sticky": null
                }
              }
            }
          ],
          "else": []
        }
      ]
    }
  },
  {
    "op": "replace",
    "path": "/0/then/0/version",
    "before": "latest",
    "after": null
  },
  {
    "op": "add",
    "path": "/0/then/2",
    "after": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "Ubuntu"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.ubuntu",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": [
        {
          "kind": "conditional",
          "condition": {
            "kind": "os",
            "value": "RedHat"
          },
          "then": [
            {
              "kind": "download",
              "source": "http://example.com/cfg.redhat",
              "destination": {
                "path": {
                  "kind": "remote",
                  "destination": {
                    "kind": "absolute",
                    "value": "/etc/postfix/main.cf"
                  }
                },
                "owner": null,
                "group": null,
                "permissions": {
                  "read": null,
                  "write": null,
                  "execute": null,
                  "list_directory": null,
                  "setuid": null,
                  "setgid": null,
                  "sticky": null
                }
              }
            }
          ],
          "else": []
        }
      ]
    }
  },
  {
    "op": "remove",
    "path": "/2",
    "before": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "RedHat"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.redhat",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": []
    }
  },
  {
    "op": "remove",
    "path": "/1",
    "before": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "Ubuntu"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.ubuntu",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": []
    }
  }
]
```

Additional exact per-OS ordered-trace diff (control-flow spelling removed, all action values retained):

```json
[
  {
    "op": "replace",
    "path": "/RedHat/0/version",
    "before": "latest",
    "after": null
  },
  {
    "op": "replace",
    "path": "/Ubuntu/0/version",
    "before": "latest",
    "after": null
  }
]
```

**Representative output:** `glm-5.3--handbook-v3--a18--r2`

```text
if os is Ubuntu then install postfix with version="latest"; copy postfix configuration file to "/etc/postfix/main.cf.bak"; download file from "http://example.com/cfg.ubuntu" to "/etc/postfix/main.cf". if os is RedHat then install postfix with version="latest"; copy postfix configuration file to "/etc/postfix/main.cf.bak"; download file from "http://example.com/cfg.redhat" to "/etc/postfix/main.cf".
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "replace",
    "path": "/0/condition/value",
    "before": "RedHat",
    "after": "Ubuntu"
  },
  {
    "op": "remove",
    "path": "/0/else/0",
    "before": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "Ubuntu"
      },
      "then": [
        {
          "kind": "install",
          "packages": [
            {
              "name": "postfix",
              "manager": "system"
            }
          ],
          "version": "latest"
        },
        {
          "kind": "copy_file",
          "source": {
            "kind": "remote",
            "destination": {
              "kind": "absolute",
              "value": "/etc/postfix/main.cf"
            }
          },
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": {
                  "unknown": 0
                }
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": []
    }
  },
  {
    "op": "replace",
    "path": "/0/then/1/destination/path/destination/value",
    "before": {
      "unknown": 0
    },
    "after": "/etc/postfix/main.cf.bak"
  },
  {
    "op": "add",
    "path": "/0/then/2",
    "after": {
      "kind": "download",
      "source": "http://example.com/cfg.ubuntu",
      "destination": {
        "path": {
          "kind": "remote",
          "destination": {
            "kind": "absolute",
            "value": "/etc/postfix/main.cf"
          }
        },
        "owner": null,
        "group": null,
        "permissions": {
          "read": null,
          "write": null,
          "execute": null,
          "list_directory": null,
          "setuid": null,
          "setgid": null,
          "sticky": null
        }
      }
    }
  },
  {
    "op": "replace",
    "path": "/1/condition/value",
    "before": "Ubuntu",
    "after": "RedHat"
  },
  {
    "op": "remove",
    "path": "/1/then/0/destination",
    "before": {
      "path": {
        "kind": "remote",
        "destination": {
          "kind": "absolute",
          "value": "/etc/postfix/main.cf"
        }
      },
      "owner": null,
      "group": null,
      "permissions": {
        "read": null,
        "write": null,
        "execute": null,
        "list_directory": null,
        "setuid": null,
        "setgid": null,
        "sticky": null
      }
    }
  },
  {
    "op": "replace",
    "path": "/1/then/0/kind",
    "before": "download",
    "after": "install"
  },
  {
    "op": "add",
    "path": "/1/then/0/packages",
    "after": [
      {
        "name": "postfix",
        "manager": "system"
      }
    ]
  },
  {
    "op": "remove",
    "path": "/1/then/0/source",
    "before": "http://example.com/cfg.ubuntu"
  },
  {
    "op": "add",
    "path": "/1/then/0/version",
    "after": "latest"
  },
  {
    "op": "add",
    "path": "/1/then/1",
    "after": {
      "kind": "copy_file",
      "source": {
        "kind": "remote",
        "destination": {
          "kind": "absolute",
          "value": "/etc/postfix/main.cf"
        }
      },
      "destination": {
        "path": {
          "kind": "remote",
          "destination": {
            "kind": "absolute",
            "value": "/etc/postfix/main.cf.bak"
          }
        },
        "owner": null,
        "group": null,
        "permissions": {
          "read": null,
          "write": null,
          "execute": null,
          "list_directory": null,
          "setuid": null,
          "setgid": null,
          "sticky": null
        }
      }
    }
  },
  {
    "op": "add",
    "path": "/1/then/2",
    "after": {
      "kind": "download",
      "source": "http://example.com/cfg.redhat",
      "destination": {
        "path": {
          "kind": "remote",
          "destination": {
            "kind": "absolute",
            "value": "/etc/postfix/main.cf"
          }
        },
        "owner": null,
        "group": null,
        "permissions": {
          "read": null,
          "write": null,
          "execute": null,
          "list_directory": null,
          "setuid": null,
          "setgid": null,
          "sticky": null
        }
      }
    }
  },
  {
    "op": "remove",
    "path": "/2",
    "before": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "RedHat"
      },
      "then": [
        {
          "kind": "download",
          "source": "http://example.com/cfg.redhat",
          "destination": {
            "path": {
              "kind": "remote",
              "destination": {
                "kind": "absolute",
                "value": "/etc/postfix/main.cf"
              }
            },
            "owner": null,
            "group": null,
            "permissions": {
              "read": null,
              "write": null,
              "execute": null,
              "list_directory": null,
              "setuid": null,
              "setgid": null,
              "sticky": null
            }
          }
        }
      ],
      "else": []
    }
  }
]
```

Additional exact per-OS ordered-trace diff (control-flow spelling removed, all action values retained):

```json
[
  {
    "op": "replace",
    "path": "/RedHat/1/destination/path/destination/value",
    "before": {
      "unknown": 0
    },
    "after": "/etc/postfix/main.cf.bak"
  },
  {
    "op": "replace",
    "path": "/Ubuntu/1/destination/path/destination/value",
    "before": {
      "unknown": 0
    },
    "after": "/etc/postfix/main.cf.bak"
  }
]
```

**Proposed playbook candidate (not executed):**

```yaml
---
- name: Various postfix configuration tasks
  hosts: redhat,ubuntu
  become: true
  tasks:
    - name: Install postfix
      ansible.builtin.package:
        name: postfix
        state: latest
    - name: Backup original main.cf
      ansible.builtin.copy:
        src: /etc/postfix/main.cf
        dest: /etc/postfix/main.bak
        force: false
        remote_src: true
    - name: Download main.cf
      ansible.builtin.get_url:
        url: "http://example.com/cfg.{{ ansible_distribution | lower }}"
        dest: /etc/postfix/main.cf
        #validate_certs: false
        mode: '644'
        owner: root
        group: root
        force: true

```

Native original query/playbook status: `accepted_with_possible_assumptions_or_residuals`; proposed pair: `accepted_with_possible_assumptions_or_residuals`.

### a20

**NL request (verbatim):**

```text
Enable passwordless sudo for a `wheel' group and create an `ansible' user in that group
```

**Original reference FQL (verbatim):**

```text
enable passwordless sudo for group=wheel; create user with name=ansible in supplemental groups=wheel
```

**Decision: two distinct comparison limitations, not evidence that every model is wrong.** The original FQL chooses supplemental membership, while the NL only says the ansible user is in wheel. Primary membership, supplemental membership, or both meet that stated membership obligation, although their complete system effects differ. The V3 handbook documents both forms. The scoped reviewed policy accepts either/both for this exact account/group, and a single leading wheel-group creation (already present as a prerequisite in the source playbook); it rejects wrong subjects, password-required sudo, missing membership and other actions. All 55 supported V3 trees meet this scoped obligation (versus 34 original structural matches); two baseline outputs are additionally recovered.

Separately, the reference playbook's eight-space sudoers separator is syntactically valid: local `visudo -cf` accepts both spaces and tab. Native code compares a tab-containing string (`lib/fql/codegen.ml:635`, including its own spacing TODO), so the verifier rejection is a modeling false negative. The proposed tab-spelling playbook merely accommodates the verifier and passes its symbolic check; this does not make the original spaces wrong. The original FQL is retained as the canonical spelling. No general primary/supplemental effect equivalence is asserted.

**Proposed canonical FQL (separate v2 file; unchanged where no FQL correction is justified):**

```text
enable passwordless sudo for group=wheel; create user with name=ansible in supplemental groups=wheel
```

**Exact original-to-proposed reference effect diff:**

```json
[]
```

**Representative output:** `opus--handbook-v3--a20--r0`

```text
enable passwordless sudo for group="wheel"; create user with name="ansible", supplemental groups="wheel".
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[]
```

**Representative output:** `sol--handbook-v3--a20--r0`

```text
enable passwordless sudo for group="wheel"; create user with name="ansible", primary group="wheel"
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "replace",
    "path": "/1/primary_group",
    "before": null,
    "after": "wheel"
  },
  {
    "op": "replace",
    "path": "/1/supplemental_groups",
    "before": [
      "wheel"
    ],
    "after": null
  }
]
```

**Representative output:** `opus--handbook-v3--a20--r5`

```text
create group with name="wheel"; enable passwordless sudo for group="wheel"; create user with name="ansible", supplemental groups="wheel".
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "remove",
    "path": "/0/account",
    "before": {
      "kind": "group",
      "name": "wheel"
    }
  },
  {
    "op": "replace",
    "path": "/0/kind",
    "before": "enable_sudo",
    "after": "create_group"
  },
  {
    "op": "add",
    "path": "/0/name",
    "after": "wheel"
  },
  {
    "op": "remove",
    "path": "/0/passwordless",
    "before": true
  },
  {
    "op": "add",
    "path": "/1/account",
    "after": {
      "kind": "group",
      "name": "wheel"
    }
  },
  {
    "op": "replace",
    "path": "/1/kind",
    "before": "create_user",
    "after": "enable_sudo"
  },
  {
    "op": "remove",
    "path": "/1/name",
    "before": "ansible"
  },
  {
    "op": "add",
    "path": "/1/passwordless",
    "after": true
  },
  {
    "op": "remove",
    "path": "/1/primary_group",
    "before": null
  },
  {
    "op": "remove",
    "path": "/1/supplemental_groups",
    "before": [
      "wheel"
    ]
  },
  {
    "op": "add",
    "path": "/2",
    "after": {
      "kind": "create_user",
      "name": "ansible",
      "primary_group": null,
      "supplemental_groups": [
        "wheel"
      ]
    }
  }
]
```

**Proposed playbook candidate (not executed):**

```yaml
---
- name: Enable passwordless sudo for wheel and create an ansible user in that group
  hosts: all
  become: true
  tasks:
    - name: Install sudo
      ansible.builtin.package:
        name: sudo
        state: present
    - name: Wheel group
      ansible.builtin.group:
        name: wheel
        system: true
        state: present
    - name: Ansible user
      ansible.builtin.user:
        name: ansible
        comment: Ansible User
        groups:
          - wheel
        state: present
    - name: Allow group wheel to sudo
      ansible.builtin.lineinfile:
        path: "/etc/sudoers"
        line: "%wheel\tALL=(ALL:ALL) NOPASSWD:ALL"
        regexp: "^%wheel"
        owner: root
        group: root
        mode: "640"
        state: present

```

Native original query/playbook status: `rejected`; proposed pair: `accepted_with_possible_assumptions_or_residuals`.

### a21

**NL request (verbatim):**

```text
For Debian and RedHat, install and start an ssh client and server and generated an ssh key for `fizbaz' at /.ssh/fizbaz_rsa
```

**Original reference FQL (verbatim):**

```text
if os is Debian or os is RedHat then install ssh client; install ssh server; start ssh server service; create ssh key for user="fizbaz", name="fizbaz_rsa"
```

**Decision: the reference conflicts with the literal NL path; most V3 models follow the NL.** The reference `name="fizbaz_rsa"` resolves to a key in user fizbaz's home, `.ssh/fizbaz_rsa` (`lib/fql/semant.ml:451`). The request says `/.ssh/fizbaz_rsa`, an absolute root path. V3 explicitly teaches `at "PATH"`, which models use correctly for that literal request. The proposed reference uses that explicit absolute path. Author confirmation is still needed if the publication intended a home-relative path instead.

Of 60 V3 cells, 51 produce supported/interpreted trees. Correcting only the reference recovers 46 matches; equivalent exact-OS branch normalization recovers one more. Four supported trees remain mismatches: two broaden exact distributions to OS families, one creates the key outside the requested OS scope, and one nests RedHat inside Debian so RedHat never executes. Nine other cells have no valid tree. The six-world audit exposes these scope differences rather than erasing them.

The phrase “start an ssh client” lacks a target/session and has no supported client service in the KB. Also, for an explicit-path key, the native `CreateSshKey` AST retains the path but drops the user argument (`lib/fql/semant.ml:465`); its ownership/user adequacy is not established by this score. The correction is therefore a literal-path sensitivity, not independently adjudicated full intent gold.

**Proposed canonical FQL (separate v2 file; unchanged where no FQL correction is justified):**

```text
if os is Debian or os is RedHat then install ssh client; install ssh server; start ssh server service; create ssh key for user="fizbaz" at "/.ssh/fizbaz_rsa"
```

**Exact original-to-proposed reference effect diff:**

```json
[
  {
    "op": "replace",
    "path": "/0/else/0/then/3/path/destination/kind",
    "before": "in_home",
    "after": "absolute"
  },
  {
    "op": "remove",
    "path": "/0/else/0/then/3/path/destination/user",
    "before": "fizbaz"
  },
  {
    "op": "replace",
    "path": "/0/else/0/then/3/path/destination/value",
    "before": ".ssh/fizbaz_rsa",
    "after": "/.ssh/fizbaz_rsa"
  },
  {
    "op": "replace",
    "path": "/0/then/3/path/destination/kind",
    "before": "in_home",
    "after": "absolute"
  },
  {
    "op": "remove",
    "path": "/0/then/3/path/destination/user",
    "before": "fizbaz"
  },
  {
    "op": "replace",
    "path": "/0/then/3/path/destination/value",
    "before": ".ssh/fizbaz_rsa",
    "after": "/.ssh/fizbaz_rsa"
  }
]
```

**Representative output:** `opus--handbook-v3--a21--r0`

```text
if os is Debian or os is RedHat then install ssh client; install ssh server; start ssh server service; create ssh key for user="fizbaz" at "/.ssh/fizbaz_rsa".
```

Reviewed policy accepts: **True**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "replace",
    "path": "/0/else/0/then/3/path/destination/kind",
    "before": "in_home",
    "after": "absolute"
  },
  {
    "op": "remove",
    "path": "/0/else/0/then/3/path/destination/user",
    "before": "fizbaz"
  },
  {
    "op": "replace",
    "path": "/0/else/0/then/3/path/destination/value",
    "before": ".ssh/fizbaz_rsa",
    "after": "/.ssh/fizbaz_rsa"
  },
  {
    "op": "replace",
    "path": "/0/then/3/path/destination/kind",
    "before": "in_home",
    "after": "absolute"
  },
  {
    "op": "remove",
    "path": "/0/then/3/path/destination/user",
    "before": "fizbaz"
  },
  {
    "op": "replace",
    "path": "/0/then/3/path/destination/value",
    "before": ".ssh/fizbaz_rsa",
    "after": "/.ssh/fizbaz_rsa"
  }
]
```

**Representative output:** `deepseek-v4-flash--handbook-v3--a21--r3`

```text
if os is Debian then install ssh client; install ssh server; start ssh server service. if os is RedHat then install ssh client; install ssh server; start ssh server service. create ssh key for user="fizbaz" at "/.ssh/fizbaz_rsa"
```

Reviewed policy accepts: **False**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "remove",
    "path": "/0/else/0",
    "before": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "RedHat"
      },
      "then": [
        {
          "kind": "install",
          "packages": [
            {
              "name": "openssh-clients",
              "manager": "dnf"
            }
          ],
          "version": null
        },
        {
          "kind": "install",
          "packages": [
            {
              "name": "openssh-server",
              "manager": "system"
            }
          ],
          "version": null
        },
        {
          "kind": "start_service",
          "name": {
            "kind": "existential",
            "type": "string",
            "binder": "__kb_bound_0",
            "predicate": {
              "kind": "or",
              "left": {
                "kind": "eq",
                "left": {
                  "kind": "id",
                  "name": "__kb_bound_0"
                },
                "right": {
                  "kind": "string",
                  "value": "ssh"
                }
              },
              "right": {
                "kind": "or",
                "left": {
                  "kind": "eq",
                  "left": {
                    "kind": "id",
                    "name": "__kb_bound_0"
                  },
                  "right": {
                    "kind": "string",
                    "value": "sshd"
                  }
                },
                "right": {
                  "kind": "bool",
                  "value": false
                }
              }
            }
          }
        },
        {
          "kind": "create_ssh_key",
          "path": {
            "kind": "remote",
            "destination": {
              "kind": "in_home",
              "user": "fizbaz",
              "value": ".ssh/fizbaz_rsa"
            }
          }
        }
      ],
      "else": []
    }
  },
  {
    "op": "remove",
    "path": "/0/then/3",
    "before": {
      "kind": "create_ssh_key",
      "path": {
        "kind": "remote",
        "destination": {
          "kind": "in_home",
          "user": "fizbaz",
          "value": ".ssh/fizbaz_rsa"
        }
      }
    }
  },
  {
    "op": "add",
    "path": "/1",
    "after": {
      "kind": "conditional",
      "condition": {
        "kind": "os",
        "value": "RedHat"
      },
      "then": [
        {
          "kind": "install",
          "packages": [
            {
              "name": "openssh-clients",
              "manager": "dnf"
            }
          ],
          "version": null
        },
        {
          "kind": "install",
          "packages": [
            {
              "name": "openssh-server",
              "manager": "system"
            }
          ],
          "version": null
        },
        {
          "kind": "start_service",
          "name": {
            "kind": "existential",
            "type": "string",
            "binder": "__kb_bound_0",
            "predicate": {
              "kind": "or",
              "left": {
                "kind": "eq",
                "left": {
                  "kind": "id",
                  "name": "__kb_bound_0"
                },
                "right": {
                  "kind": "string",
                  "value": "ssh"
                }
              },
              "right": {
                "kind": "or",
                "left": {
                  "kind": "eq",
                  "left": {
                    "kind": "id",
                    "name": "__kb_bound_0"
                  },
                  "right": {
                    "kind": "string",
                    "value": "sshd"
                  }
                },
                "right": {
                  "kind": "bool",
                  "value": false
                }
              }
            }
          }
        }
      ],
      "else": []
    }
  },
  {
    "op": "add",
    "path": "/2",
    "after": {
      "kind": "create_ssh_key",
      "path": {
        "kind": "remote",
        "destination": {
          "kind": "absolute",
          "value": "/.ssh/fizbaz_rsa"
        }
      }
    }
  }
]
```

**Representative output:** `deepseek-v4-flash--handbook-v3--a21--r8`

```text
if os is Debian based or os is RedHat based then install ssh client; install ssh server; start ssh server service; create ssh key for user="fizbaz" at "/.ssh/fizbaz_rsa"
```

Reviewed policy accepts: **False**. Exact original-reference-to-output effect diff (JSON-pointer paths, complete before/after values):

```json
[
  {
    "op": "replace",
    "path": "/0/condition/value",
    "before": "Debian",
    "after": "DebianFamily"
  },
  {
    "op": "replace",
    "path": "/0/else/0/condition/value",
    "before": "RedHat",
    "after": "RedHatFamily"
  },
  {
    "op": "replace",
    "path": "/0/else/0/then/3/path/destination/kind",
    "before": "in_home",
    "after": "absolute"
  },
  {
    "op": "remove",
    "path": "/0/else/0/then/3/path/destination/user",
    "before": "fizbaz"
  },
  {
    "op": "replace",
    "path": "/0/else/0/then/3/path/destination/value",
    "before": ".ssh/fizbaz_rsa",
    "after": "/.ssh/fizbaz_rsa"
  },
  {
    "op": "replace",
    "path": "/0/then/3/path/destination/kind",
    "before": "in_home",
    "after": "absolute"
  },
  {
    "op": "remove",
    "path": "/0/then/3/path/destination/user",
    "before": "fizbaz"
  },
  {
    "op": "replace",
    "path": "/0/then/3/path/destination/value",
    "before": ".ssh/fizbaz_rsa",
    "after": "/.ssh/fizbaz_rsa"
  }
]
```

**Proposed playbook candidate (not executed):**

```yaml
---
- name: Install and start ssh client and server and generate an ssh key for fizbaz
  hosts: debian,redhat
  become: true
  tasks:
    - name: Install SSH (Debian)
      ansible.builtin.package:
        name:
          - openssh-client
          - openssh-server
        state: present
      when: ansible_os_family == "Debian"
    - name: Install SSH (RedHat)
      ansible.builtin.package:
        name:
          - openssh-server
          - openssh-clients
        state: present
      when: ansible_os_family == "RedHat"
    - name: Create SSH key
      ansible.builtin.user:
        name: "fizbaz"
        generate_ssh_key: true
        ssh_key_file: "/.ssh/fizbaz_rsa"
    - name: Enable SSH server
      ansible.builtin.service:
        name: sshd
        state: started

```

Native original query/playbook status: `accepted_with_possible_assumptions_or_residuals`; proposed pair: `accepted_with_possible_assumptions_or_residuals`.

## Reproduce and inspect

```sh
python3 evaluation/code/review_rescore.py --run evaluation/results/2026-11-04-full-matrix
python3 evaluation/code/validate_rescore.py --run evaluation/results/2026-11-04-full-matrix
python3 -m unittest discover -s evaluation/tests -v
```

The offline script needs the preserved private `diagnostics-private.json`, full raw responses and the unchanged native binaries. It never imports an API client or calls a model. Public `effect-diffs.json` includes all four original/proposed trees and all twelve output trees and exact diffs; `per-cell-diff.csv` records the four tasks' 480 cell decisions; `per-task-diff-summary.csv` gives 48 model/variant/task breakdowns. The original full-run exports remain at their prior paths.

Source proposals are versioned at `evaluation/references/reference-review-v2.json`; a copy accompanies this report. The primary original CSV remains immutable. These post-hoc proposals need author/human review before promotion to a new confirmatory benchmark. In particular, a03 lacks a demonstrated faithful FQL, and a21's literal path versus intended home path and user/client semantics remain caveats. No compiler or prompt changes were made.
