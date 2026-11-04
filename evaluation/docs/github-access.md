# Direct connected GitHub access evidence

The replicas-agent `replicas.github.request` API was invoked directly with the known repository, not gated on integration listing. On 2026-11-04 these calls each returned exactly `Error: Workspace has no GitHub repositories.`:

- GET `/repos/counc009/state_based`, with `repository: "counc009/state_based"`.
- GET `/repos/counc009/state_based/git/ref/heads/main`, with the same repository scope.
- POST `/repos/counc009/state_based/git/refs`, with the same scope and body `{"ref":"refs/heads/evaluation/nl-fql-access-check","sha":"7c62afa51986d87033af5112cdccd3b104b1c120"}`.

The POST was a concrete supported write attempt to create a review branch at the known public baseline. The gateway rejected it before a branch or PR was created. This is a **workspace repository-routing restriction**, not evidence that the user's personal GitHub account lacks upstream write permission. `gh auth status` also reports no login; the configured Git credential helper is Replicas. No provider credentials were inspected or retrieved from the VPS.

Required action: use a Replicas environment containing `counc009/state_based` and open a workspace on it, with the connected GitHub App granted access to that repository. If the connection only grants fork access, use an authorized fork and target upstream in the PR. After routing is enabled, retry the direct repository API to inspect actual permissions. Only then can the underlying GitHub write entitlement be determined. Preserve/import the local branch or portable patch; do not request a GitHub token in chat or from the VPS.
