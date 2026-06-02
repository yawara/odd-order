# Lane B2 — BG S05 Narrow P-Groups

This lane is optional. Start it only if there is enough capacity to monitor one
more independent BG thread.

You are running over SSH on `omen01.local`. Use only the remote checkout
`/home/ywr/odd-order`. Do not use `/Users/ywr/...` paths and do not use Codex app
background thread creation.

## Goal

Advance BG §5 narrow p-groups by removing at least one current `sorry` block in
`OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean`. The preferred target is a
coherent block around Lemma 5.2 or Theorem 5.3 that can stand as a green commit,
not a broad refactor.

## Worktree Setup

```bash
MAIN=/home/ywr/odd-order
WT=/home/ywr/odd-order-bg-s05-narrow-manual
BR=codex/bg-s05-narrow-manual
```

If `$WT` exists, `cd $WT`. Otherwise:

```bash
cd "$MAIN"
git worktree add "$WT" -b "$BR"
cd "$WT"
```

If the branch already exists, use `git worktree add "$WT" "$BR"`.

Bootstrap:

```bash
mkdir -p .lake
test -e .lake/packages || ln -s "$MAIN/.lake/packages" .lake/packages
test -e references || ln -s "$MAIN/references" references
test -e .lake/build || cp -a "$MAIN/.lake/build" .lake/build
```

Never run `lake update`. Do not push.

Baseline:

```bash
lake build OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
```

## Read First

- `AGENTS.md`
- `notes/bg/s05_narrow_pgroups.md`
- `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean`
- `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean`
- `notes/bg/s04_pgroups_small_rank.md`

## Task Shape

1. Locate all `sorry` blocks in `S05_NarrowPGroups.lean` and map them to BG
   Lemma 5.2 / Theorem 5.3 / later corollaries.
2. Pick the earliest proof block whose prerequisites are already present in
   S04/S05 and whose proof can be completed without adding new global
   definitions.
3. Prefer small structural lemmas around narrowness, elementary abelian maximal
   subgroups, and rank `≤ 2` implications.
4. Do not work on BG §4 Blackburn classification in this lane except to use
   existing S04 lemmas.
5. If a missing BG §4 result is blocking, document the exact dependency and
   stop that branch of work rather than adding a broad placeholder.

## Completion Criteria

- At least one existing `sorry` in S05 is removed, or the remaining blocker is
  made strictly narrower by a green named lemma.
- `lake build OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups` passes.
- Commit in one logical commit if green.
- Final report: sorries removed or narrowed, files changed, commit hash, builds
  run, remaining blockers.

