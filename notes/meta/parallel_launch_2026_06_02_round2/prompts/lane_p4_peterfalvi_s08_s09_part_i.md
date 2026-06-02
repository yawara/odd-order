# Lane P4 -- Peterfalvi S08-S09 Part-I Capstone

You are working over SSH on `omen01.local`.

## Worktree Setup

Use:

- main checkout: `/home/ywr/odd-order`
- worktree: `/home/ywr/odd-order-pf-part-i-capstone`
- branch: `codex/pf-part-i-capstone`

Setup commands:

```bash
cd /home/ywr/odd-order
git worktree add -b codex/pf-part-i-capstone /home/ywr/odd-order-pf-part-i-capstone main
cd /home/ywr/odd-order-pf-part-i-capstone
mkdir -p .lake
test -e .lake/packages || ln -s /home/ywr/odd-order/.lake/packages .lake/packages
test -e references || ln -s /home/ywr/odd-order/references references
test -d .lake/build || cp -a /home/ywr/odd-order/.lake/build .lake/build
```

Do not run `lake update`. Do not push.

## Explicit Goal

Set this as your goal at the start:

> Complete Peterfalvi Part I capstone through §9: discharge
> `sibleySetup_is_coherent` in §8 and `card_G0_lower_bound` in §9 if
> constructible; otherwise land every missing prerequisite needed to make the
> remaining blocker exact, with no hard content hoisted into hypotheses. Continue
> past the first prerequisite commit until the §8-§9 capstone is complete or
> precisely blocked.

If a goal tool is available, call it with that objective.

## Ownership

Primary:

- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`
- `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
- `issues/0046-peterfalvi-s08-6-8-coherence.md`
- `issues/0044-peterfalvi-s09-card-g0-lower-bound.md`
- `notes/peterfalvi/s08_coherence_theorems.md`
- `notes/peterfalvi/s09_nonexistence_certain.md`

Secondary if necessary:

- `OddOrder/Peterfalvi/S07_Coherence.lean`
- representation-theory files, but coordinate with R1 and keep commits isolated.

## Context To Read First

- `issues/0046-peterfalvi-s08-6-8-coherence.md`
- `issues/0044-peterfalvi-s09-card-g0-lower-bound.md`
- `notes/peterfalvi/autonomous_prove_queue.md`
- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`
- `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`

Current capstone blockers:

- §8 `(6.8)`: `sibleySetup_is_coherent`
- §9 `(7.10)`: `card_G0_lower_bound`, currently missing the assembly of
  `F.CharacterEstimateData`.

## Work Program

This lane is intentionally large.

1. Re-audit the current line numbers and statement names for the two capstone
   sorries.
2. For `(6.8)`, complete the largest possible contiguous proof path:
   - equal-degree family construction for `Y = S(H')`;
   - case A/B wiring;
   - final coherent union and `CoherenceTarget`.
3. For `(7.10)`, assemble `CharacterEstimateData` from the already landed
   `7.5`, `7.8`, `7.9`, and `(6.8)` interfaces.
4. If `(6.8)` genuinely requires missing infrastructure, land that
   infrastructure in broad coherent commits and update issue 0046, then
   continue.
5. Once `card_G0_lower_bound` is available, confirm `not_trivial_G0` still builds.

Recommended broad commit boundaries. Combine adjacent items when they build
green together; avoid single-helper or proof-step commits:

- `(6.8)` prerequisites and setup-specific character family data.
- `(6.8)` coherent target proof.
- `(7.10)` character estimate data assembly.
- `(7.10)` lower bound and `(7.11)` final consumer.
- issue/note cleanup.

## Anti-Scaffold Rule

Do not add fields to `SibleySetup`, `FrobeniusFamily`, `Hypothesis78`, or
`CharacterEstimateData` just to encode the missing theorem. Producer data must
be derived from existing definitions or from faithful book hypotheses.

## Verification

Focused builds:

```bash
lake build OddOrder.Peterfalvi.S08_CoherenceTheorems
lake build OddOrder.Peterfalvi.S09_NonexistenceCertain
```

Before final, run `lake build OddOrder` if feasible.

Final response must include commit hashes, whether the two capstone sorries are
gone, build commands, and exact remaining blockers if any.

