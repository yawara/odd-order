# Lane P3 — Peterfalvi S09 Character Estimates

You are running over SSH on `omen01.local`. Use only the remote checkout
`/home/ywr/odd-order`. Do not use `/Users/ywr/...` paths and do not use Codex app
background thread creation.

## Goal

Advance issue `0044` by constructing more of the (7.8) estimate package and the
`FrobeniusFamily.CharacterEstimateData` bridge. The best outcome is to reduce
`card_G0_lower_bound` to named inputs from (6.8), (7.8), and (7.9), with at
least one previously missing (7.8.a/b) proof component closed sorry-free.

Stay in S09 and directly supporting character-estimate lemmas. Do not edit S08
capstone or Brauer Layer C.

## Worktree Setup

```bash
MAIN=/home/ywr/odd-order
WT=/home/ywr/odd-order-pf-s09-estimates
BR=codex/pf-s09-estimates
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
lake build OddOrder.Peterfalvi.S09_NonexistenceCertain
```

## Read First

- `AGENTS.md`
- `issues/0044-peterfalvi-s09-card-g0-lower-bound.md`
- `notes/peterfalvi/s09_nonexistence_certain.md`
- `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
- `OddOrder/Peterfalvi/S07_Coherence.lean`
- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`

## Task Shape

Start by locating these names in `S09_NonexistenceCertain.lean`:

- `Hypothesis78.weightedNuSum`
- `Hypothesis78.BetaDecomp`
- `Hypothesis78.NormEstimates`
- `Hypothesis78.betaNormSq_eq_complementIndex_add_one`
- `FrobeniusFamily.CharacterEstimateData`
- `lowerBoundTerm_of_characterEstimateData`
- `card_G0_lower_bound`

Then choose the highest-leverage local target:

1. Close a missing source-side character computation feeding
   `betaNormSq_eq_complementIndex_add_one`.
2. Prove a bridge from `(7.7.b)/(7.8.a)` data to the `u,v,w` quadratic form.
3. Construct more of `CharacterEstimateData` from existing `Hypothesis78` and
   `Hypothesis79` fields.
4. If direct proof is blocked, add a named theorem that exactly states the
   remaining mathematical input, then use it to simplify `card_G0_lower_bound`.

Avoid adding fields to existing hypothesis structures unless there is no other
clean API. Prefer standalone target theorems and constructors.

## Completion Criteria

- No new `sorry` or project axioms.
- `lake build OddOrder.Peterfalvi.S09_NonexistenceCertain` passes.
- If you touch shared S07/S08 APIs, also run their leaf builds.
- Commit in one logical commit if green.
- Final report: which (7.8)/(7.10) component advanced, files changed, commit
  hash, builds run, remaining blockers.

