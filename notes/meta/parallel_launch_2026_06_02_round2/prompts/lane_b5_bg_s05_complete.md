# Lane B5 -- BG S05 Narrow p-Groups Complete

You are working over SSH on `omen01.local`.

## Worktree Setup

Use:

- main checkout: `/home/ywr/odd-order`
- worktree: `/home/ywr/odd-order-bg-s05-complete`
- branch: `codex/bg-s05-complete`

Setup commands:

```bash
cd /home/ywr/odd-order
git worktree add -b codex/bg-s05-complete /home/ywr/odd-order-bg-s05-complete main
cd /home/ywr/odd-order-bg-s05-complete
mkdir -p .lake
test -e .lake/packages || ln -s /home/ywr/odd-order/.lake/packages .lake/packages
test -e references || ln -s /home/ywr/odd-order/references references
test -d .lake/build || cp -a /home/ywr/odd-order/.lake/build .lake/build
```

Do not run `lake update`. Do not push.

## Explicit Goal

Set this as your goal at the start:

> Complete BG §5 Narrow p-groups as a section: remove all constructible remaining
> `sorry` blocks in `S05_NarrowPGroups.lean`, especially Theorem 5.3,
> Corollary 5.4, and Theorems 5.5--5.7, with genuine proofs or exact blockers;
> commit multiple section-level milestones and continue until the section is
> complete or the only remaining blockers are non-hoisted upstream facts.

If a goal tool is available, call it with that objective.

## Ownership

Primary:

- `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean`
- `OddOrder/GroupTheory/NarrowPGroup.lean`
- `notes/bg/s05_design_2026_05_30.md`
- `notes/bg/s05_narrow_pgroups.md`

Avoid editing BG §1. That lane remains active separately.

## Context To Read First

- `notes/bg/s05_design_2026_05_30.md`
- `notes/bg/s05_narrow_pgroups.md`
- `notes/bg/autonomous_prove_queue.md`
- `OddOrder/BG/Ch1_Preliminary/S04f_Blackburn.lean`
- `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean`

Current important facts from prior work:

- Lemma 5.1(a) is closed.
- Lemma 5.2 is closed.
- `exists_narrow_witness_of_three_le_pRank` exists as safe support.
- Remaining S05 frontier is Theorem 5.3 onward. Do not hoist Theorem 5.3.

## Work Program

This lane is intentionally large. Do not stop after the first removed `sorry`.

1. Inventory all current bare `sorry` blocks in S05.
2. Complete Theorem 5.3's genuine narrow characterization if constructible from
   Lemma 5.2 and the current §4/Blackburn support.
3. Complete Corollary 5.4 from Theorem 5.3.
4. Continue to Theorems 5.5, 5.6, and 5.7:
   - isolate reusable automorphism-control lemmas;
   - keep statements faithful to BG;
   - do not smuggle hard BG facts as assumptions.
5. Update the S05 notes with exact status and downstream API names.

Recommended broad commit boundaries. Combine adjacent items when they build
green together; avoid single-helper or proof-step commits:

- Thm 5.3 support and main theorem.
- Cor 5.4 plus witness/centralizer rank helpers.
- Thm 5.5 automorphism-control block.
- Thm 5.6/5.7 global solvable applications.
- Notes/issues cleanup.

## Anti-Scaffold Rule

For Thm 5.3 and Thm 5.5, hypothesis constructibility is the done criterion.
A proof that assumes the needed centralizer decomposition, automorphism control,
or narrow characterization is not complete.

## Verification

Run focused builds after each milestone:

```bash
lake build OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
```

Before final, run if feasible:

```bash
lake build OddOrder
```

Final response must include:

- commit hashes;
- remaining `sorry` count in S05, if any;
- build commands run;
- exact blockers with file/line references.

