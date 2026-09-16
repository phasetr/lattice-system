## Scope

- Target phase / claim:
- Out of scope:

## Verification

- [ ] The relevant build and checks pass.
- [ ] No legacy implementation, API, status, docs, TeX, or scripts were carried forward.

## Hard merge gate

This gate applies to every pull request in the rewrite program, including PR #5480, with no phase or branch
exception. Merge is forbidden until the user currently and explicitly confirms the target PR number and its
current exact head SHA and authorizes merging that head. Auto-merge, merge queue use, direct push, and force
push are forbidden. CI GREEN, review APPROVE, past approval, and approval for another PR are not merge
authority. If the head changes, approval is invalid and must be obtained again for the new exact SHA.

- [ ] **USER ONLY:** I currently and explicitly authorize merging PR #________ at its current exact head SHA
      `________________________________________`.

Agents must leave the USER ONLY checkbox unchecked and must not infer merge permission.
