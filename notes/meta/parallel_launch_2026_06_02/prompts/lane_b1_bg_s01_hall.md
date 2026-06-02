# Lane B1 — BG S01 A-Invariant Hall Framework

You are running over SSH on `omen01.local`. Use only the remote checkout
`/home/ywr/odd-order`. Do not use `/Users/ywr/...` paths and do not use Codex app
background thread creation.

## Goal

Advance issue `0012`: BG §1 Prop 1.5 A-invariant Hall framework. The goal is to
turn the current Sylow-specialized/operator-action facts into a usable Hall
`π` framework for BG §1, unblocking issue `0011` Prop 1.4.

The best outcome is a green commit proving at least Prop 1.5(a)-(c) in a
faithful Hall form, or a smaller but complete Hall-existence/conjugacy block
that S01 can consume directly.

## Worktree Setup

```bash
MAIN=/home/ywr/odd-order
WT=/home/ywr/odd-order-bg-s01-hall
BR=codex/bg-s01-hall
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
lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable
lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main
```

## Read First

- `AGENTS.md`
- `issues/0012-bg-s01-prop-1-5-hall.md`
- `issues/0011-bg-s01-prop-1-2-1-4-fitting.md`, Prop 1.4 dependency notes
- `notes/bg/s01_solvable.md`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`
- `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean`

## Task Shape

1. Confirm current `IsHallSubgroup` API in Isaacs Ch03:
   `hall_exists_of_piSeparable`, conjugacy, containment, quotient mapping, and
   `Subgroup.IsPiGroup` helpers.
2. Confirm current A-invariant Sylow API in Ch04:
   `exists_aInvariant_sylow`, `aInvariant_sylow_conj`,
   `glauberman_fixed_point_exists`, `glauberman_fixed_points_conj`.
3. In S01, avoid pure wrappers. Add BG-facing theorems only when they adapt
   conventions, specialize hypotheses, or are used more than once.
4. Implement the smallest reusable Hall block:
   - A-invariant Hall existence under the exact solvable/coprime hypotheses
     needed by BG Prop 1.5.
   - A-invariant Hall conjugacy if existence is already available.
   - A containment/normalization lemma if Prop 1.5(e) is the true blocker.
5. If Prop 1.5(e) is too broad, make its statement precise and create/update a
   sub-issue instead of silently changing the theorem.

## Completion Criteria

- No new `sorry` or project axioms unless explicitly documented as a temporary
  forward statement with issue linkage.
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` passes.
- `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` passes if Ch03 changed.
- Commit in one logical commit if green.
- Final report: which Prop 1.5 parts are proved, files changed, commit hash,
  builds run, remaining blocker for issue 0011 Prop 1.4.

