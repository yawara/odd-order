# Parallel lane handoff (2026-06-02)

Purpose: run the FT mainline lanes in parallel without creating new worktrees or
re-downloading mathlib.

## Global constraints

- Use the existing worktrees below. Do not create another worktree unless the
  coordinator explicitly asks.
- Do not run `lake update`, `lake exe cache get`, or any dependency download.
- `.lake/packages` and `references` are symlinks to `/home/ywr/odd-order`.
- `.lake/build` is an independent copy in each worktree. Builds are isolated.
- Commit small logical units on the lane branch. Do not touch unrelated dirty
  files in `/home/ywr/odd-order` (`CLAUDE.md` is currently dirty on main).
- Verify with the lane leaf target first; run `lake build OddOrder` only after a
  meaningful change lands.
- Anti-scaffold rule: do not replace hard content with fresh unconstructible
  hypotheses just to make a theorem compile.

Current worktrees:

| lane | path | branch | starting commit |
|---|---|---|---|
| BG §4 Blackburn | `/home/ywr/odd-order-bg-s04-blackburn` | `codex/bg-s04-blackburn` | `528efc2` |
| BG §5 narrow p-groups | `/home/ywr/odd-order-bg-s05-narrow` | `codex/bg-s05-narrow` | `c7c8d13` |
| BG §7-§16 interface | `/home/ywr/odd-order-bg-s07-s16-interface` | `codex/bg-s07-s16-interface` | `c7c8d13` |
| Peterfalvi §8-§9 | `/home/ywr/odd-order-peterfalvi-s08-s09` | `codex/peterfalvi-s08-s09` | `c7c8d13` |

## Lane A: BG §4 Blackburn

Start in:

```bash
cd /home/ywr/odd-order-bg-s04-blackburn
```

First target:

```bash
lake build OddOrder.BG.Ch1_Preliminary.S04f_Blackburn
```

Context:

- `S04f_Blackburn.lean` was created to avoid an import cycle. The final
  Blackburn endpoint must live downstream of both `S04d_GorThm415` and
  `S04e_GorThm37`.
- Visible `sorry` in the lane:
  - `dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty`
  - `dvd_half_prime_add_or_sub_of_prime_dvd_aut_of_scn3_empty`
  - `blackburnRankTwoClassification`

First useful goal:

Prove BG Lemma 4.13, or land one genuine sorry-free intermediate lemma needed
for it.

Read first:

- `notes/bg/s04_lem413_gorenstein_precursors.md`
- `OddOrder/BG/Ch1_Preliminary/S04f_Blackburn.lean`
- `OddOrder/BG/Ch1_Preliminary/S04d_GorThm415.lean`
- `OddOrder/BG/Ch1_Preliminary/S04e_GorThm37.lean`
- `OddOrder/GroupTheory/PRank.lean`

Known usable gates:

- `pRank_le_two_of_scn3_empty`
- `exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction`
- PRank automorphism order bounds around
  `orderOf_dvd_prime_sq_sub_one_and_lt_of_card_le_prime_sq`

Do not:

- Replace `SCN₃(R)=∅` by a theorem hypothesis `pRank R p ≤ 2`.
- Add `q ∣ p^2 - 1`, `q < p`, or the minimal special subgroup as assumptions to
  Lemma 4.13.
- Move the final theorem back into `S04_PGroupsSmallRank.lean`.

## Lane B: BG §5 narrow p-groups

Start in:

```bash
cd /home/ywr/odd-order-bg-s05-narrow
```

First target:

```bash
lake build OddOrder.BG.Ch1_Preliminary.S05_NarrowPGroups
```

Context:

- This branch starts at `c7c8d13`, so it does not contain the S04f routing commit.
  Avoid touching S04 routing here unless main has merged Lane A.
- §5 has 8 visible `sorry` and is mathematically downstream of §4, but some
  statement cleanup and independent narrow-p-group infrastructure can proceed.

First useful goal:

Make one §5 theorem statement more faithful or prove one independent support
lemma that does not require the unfinished BG Thm 4.16 proof.

Read first:

- `notes/bg/s05_design_2026_05_30.md`
- `OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean`
- `OddOrder/GroupTheory/NarrowPGroup.lean`
- `issues/0051-bg-s04-thm-4-16-blackburn.md`

Good candidates:

- Tighten the dependencies of Lemma 5.1(a)/(b) without adding unconstructible
  assumptions.
- Factor reusable narrow-p-group helpers into `OddOrder/GroupTheory/NarrowPGroup.lean`
  only if they are proof-relevant and not pure wrappers.
- Keep changes independent of `S04f_Blackburn.lean` until Lane A merges.

## Lane C: BG §7-§16 interface

Start in:

```bash
cd /home/ywr/odd-order-bg-s07-s16-interface
```

First target:

```bash
lake build OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults
```

Context:

- This is an interface/skeleton lane, not a proof-fill free-for-all.
- BG §7-§16 is the dominant serial spine, but proof work should wait for §4/§5
  gates where required.

First useful goal:

Improve faithful statements, notation, and dependency comments for one section
without adding new mathematical assumptions that will later be impossible to
construct.

Read first:

- `notes/bg/s07_transitivity.md`
- `notes/bg/s08_fitting_max.md`
- `notes/bg/s09_uniqueness.md`
- `notes/bg/s16_main_results.md`
- `notes/meta/log/ft_mainline_dependency_closure_2026_06_02.md`
- `OddOrder/BG/Ch2_Uniqueness/S07_Transitivity.lean`
- `OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean`

Good candidates:

- Identify which S07/S08/S09 theorem statements consume BG §4 Lem 4.13/4.16 or
  §5 narrow results.
- Replace vague placeholder comments with precise BG theorem numbers and source
  page/mmd line references.
- Add a missing faithful statement only if its dependencies are explicit and
  named.

Do not:

- Make Peterfalvi §10-style type classification assumptions appear as BG §16
  hypotheses just to satisfy downstream files.
- Hide BG §4/§5 obligations behind fields in a structure unless the fields are
  exactly the BG theorem interface to be proved later.

## Lane D: Peterfalvi §8-§9

Start in:

```bash
cd /home/ywr/odd-order-peterfalvi-s08-s09
```

First target:

```bash
lake build OddOrder.Peterfalvi.S09_NonexistenceCertain
```

Context:

- This lane is independent of BG §16 until Peterfalvi §10.
- Current mainline bottom blockers are S08 `(6.8)` coherence and S09 `(7.10)`.

First useful goal:

Either reduce the S08/S09 `sorry` count by one, or land a genuine intermediate
lemma for S09 `(7.8.a/b)`, `(7.9)`, or `(7.10)`.

Read first:

- `issues/0046-peterfalvi-s08-6-8-coherence.md`
- `issues/0044-peterfalvi-s09-card-g0-lower-bound.md`
- `notes/peterfalvi/s08_coherence_theorems.md`
- `notes/peterfalvi/s08_6_8_assembly_plan.md`
- `notes/peterfalvi/s09_nonexistence_certain.md`
- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`
- `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`

Good candidates:

- State missing Peterfalvi `(7.8.a)`, `(7.8.b)`, or `(7.9)` faithfully if still
  absent.
- Prove arithmetic or inner-product sublemmas used by `(7.10)` without changing
  the global hypothesis structures.
- If touching S08, keep the class-sum/coherence assumptions honest and tied to
  existing `S07_Coherence` interfaces.

Do not:

- Start Peterfalvi §10-§16 proof filling before BG §16 supplies real inputs.
- Replace Dade/coherence content with opaque proposition fields unless the field
  already corresponds to a named Peterfalvi theorem being tracked as a `sorry`.

## Merge protocol

Preferred merge order:

1. Lane A small commits into main.
2. Lane B rebases/merges main after Lane A if it needs S04f or Lem 4.13/4.14.
3. Lane C can merge interface-only changes independently if it does not touch
   §4/§5 files.
4. Lane D can merge independently while it stays in Peterfalvi §8-§9.

Before merging any lane:

```bash
git status --short
lake build <lane target>
git diff --check
```

For substantial Lean changes, also run:

```bash
lake build OddOrder
```

Record any new visible `sorry` deliberately in the relevant issue or `notes/`
handoff. Do not leave untracked Lean files unimported unless they are scratch
files outside `OddOrder/`.
