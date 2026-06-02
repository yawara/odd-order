# Lane B6 -- BG S07-S09 Uniqueness Spine

You are working over SSH on `omen01.local`.

## Worktree Setup

Use:

- main checkout: `/home/ywr/odd-order`
- worktree: `/home/ywr/odd-order-bg-s07-s09-spine`
- branch: `codex/bg-s07-s09-spine`

Setup commands:

```bash
cd /home/ywr/odd-order
git worktree add -b codex/bg-s07-s09-spine /home/ywr/odd-order-bg-s07-s09-spine main
cd /home/ywr/odd-order-bg-s07-s09-spine
mkdir -p .lake
test -e .lake/packages || ln -s /home/ywr/odd-order/.lake/packages .lake/packages
test -e references || ln -s /home/ywr/odd-order/references references
test -d .lake/build || cp -a /home/ywr/odd-order/.lake/build .lake/build
```

Do not run `lake update`. Do not push.

## Explicit Goal

Set this as your goal at the start:

> Build the faithful BG §7-§9 uniqueness spine: create or refine the concrete
> setup definitions for the minimal odd counterexample, maximal subgroup
> families, uniqueness predicate, and H-invariant subgroup notation; then remove
> every tractable `sorry` in `S07_Transitivity`, `S08_FittingOfMaximal`, and
> `S09_Uniqueness` without hoisting hard content. Continue until the spine is
> proof-ready and all constructible proofs in §7-§9 are landed.

If a goal tool is available, call it with that objective.

## Ownership

Primary:

- `OddOrder/BG/Ch2_Uniqueness/S07_Transitivity.lean`
- `OddOrder/BG/Ch2_Uniqueness/S08_FittingOfMaximal.lean`
- `OddOrder/BG/Ch2_Uniqueness/S09_Uniqueness.lean`
- shared setup modules needed for these files, for example:
  - `OddOrder/GroupTheory/MaximalSubgroup.lean`
  - `OddOrder/BG/Ch2_Uniqueness/Setup.lean`
  - `OddOrder/BG/Ch1_Preliminary/PLength.lean`

Avoid editing BG §10-§13 except for import compatibility. B7 owns those.

## Context To Read First

- `notes/bg/scaffold_feasibility_2026_06_01.md`
- `notes/bg/s07_transitivity.md`
- `notes/bg/s08_fitting_max.md`
- `notes/bg/s09_uniqueness.md`
- current Lean files under `OddOrder/BG/Ch2_Uniqueness/`
- `OddOrder/BG/AppB_Thm62.lean` and BG §6 files for normal-J inputs.

## Work Program

This lane is a spine-building lane, not a single-theorem lane.

1. Audit current S07/S08/S09 definitions and `sorry` statements.
2. Implement faithful shared definitions:
   - maximal subgroup set/family;
   - uniqueness predicate `U` / uniquely maximal objects;
   - `H_H(A; pi)` / starred maximal A-invariant pi-subgroups, if absent;
   - fixed minimal simple odd setup bundle if needed.
3. Replace opaque placeholders with real definitions where possible.
4. Prove low-level definitional lemmas and any theorem whose dependencies are
   already constructible from §1-§6, App.B, and Isaacs Ch07.
5. Leave hard §7 transitivity or §9 uniqueness results as `sorry` only if their
   proof genuinely needs unlanded BG local analysis. Document exact blockers.
6. Update section notes with the actual Lean API and statement inventory.

Recommended broad commit boundaries. Combine adjacent items when they form one
coherent spine increment; avoid single-helper or proof-step commits:

- shared setup definitions and basic lemmas;
- S07 transitivity setup/proof-ready API;
- S08 Fitting-of-maximal proof-ready API and easy lemmas;
- S09 uniqueness chain cleanup and tractable proof blocks;
- notes/issues cleanup.

## Anti-Scaffold Rule

Do not create fields like `theorem_7_6_holds : ...` just to make downstream
theorems easy. The setup bundle may encode the standing minimal counterexample
hypotheses, but not the theorem conclusions being proved.

## Verification

Run focused builds:

```bash
lake build OddOrder.BG.Ch2_Uniqueness.S07_Transitivity
lake build OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal
lake build OddOrder.BG.Ch2_Uniqueness.S09_Uniqueness
```

Before final, run `lake build OddOrder` if feasible.

Final response must include commit hashes, remaining sorries in S07-S09, build
commands run, and exact blockers.

