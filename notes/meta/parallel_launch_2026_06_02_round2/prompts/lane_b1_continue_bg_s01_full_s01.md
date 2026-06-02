# Lane B1 -- Continue BG S01 Full Section

You are working over SSH on `omen01.local`.

Use the existing worktree:

- worktree: `/home/ywr/odd-order-bg-s01-hall`
- branch: `codex/bg-s01-hall`
- main checkout for references: `/home/ywr/odd-order`

Do not create a new worktree for this lane. Do not discard current uncommitted
work.

## Explicit Goal

Set this as your goal at the start:

> Complete BG §1 (`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`) as a section:
> preserve the current uncommitted progress, finish every constructible BG §1
> theorem/issue in the Prop 1.2--1.6 / Hall / p-length frontier, commit larger
> logical milestones, and continue beyond the first green proof until the
> section is complete or the remaining blocker is mathematically exact and not
> hoisted.

If a goal tool is available, call it with that objective. If not, state it in
your first response and work to it.

## Rules

- Do not stop after completing Prop 1.5 or one local helper.
- Commit in larger logical chunks: a theorem group or subsection block plus its
  support lemmas and note/issue update. Do not make proof-step or single-helper
  commits unless the helper is a reusable public API by itself.
- Keep the lane worktree build-green.
- Do not run `lake update`.
- Do not push.
- Do not rewrite unrelated history or revert user/main changes.

## First Actions

1. `cd /home/ywr/odd-order-bg-s01-hall`
2. Inspect `git status --short --branch`.
3. Read the current uncommitted diff before editing:
   - `git diff -- OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
   - `git diff -- issues/0012-bg-s01-prop-1-5-hall.md notes/bg/s01_solvable.md`
4. Read current planning notes:
   - `notes/bg/s01_solvable.md`
   - `notes/bg/parallel_execution_plan_2026_05_30.md`
   - relevant open issues under `issues/` for BG §1.

## Ownership

Primary:

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `notes/bg/s01_solvable.md`
- `issues/0012-bg-s01-prop-1-5-hall.md`

Secondary only if required:

- BG §1 related issues under `issues/`
- small shared helpers already used by S01, but avoid broad refactors.

## Work Program

Treat this as a long-running lane:

1. Finish the current uncommitted Prop 1.5 / Hall work and make it build.
2. Commit that milestone only once it includes the theorem block, supporting
   lemmas, and note/issue update.
3. Continue through the remaining BG §1 frontier:
   - Prop 1.2 / Prop 1.4 cleanup if still open;
   - Prop 1.6 missing parts if they are constructible from current Ch04 APIs;
   - p-length / Hall containment lemmas if they are in S01's direct scope;
   - stale issue and note closure.
4. For each item, avoid wrapper-only declarations unless they adapt hypotheses or
   argument order in a useful way.

## Anti-Scaffold Rule

Do not prove a theorem by adding a hypothesis that is essentially the theorem.
If a book result needs an upstream theorem that is not constructible, record the
exact theorem name, file, and required statement in the note/issue instead.

## Verification

At minimum before final:

- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable`
- `lake build OddOrder` if feasible
- `git status --short --branch`

Final response should include commit hashes, build commands, and exact remaining
blockers if any.

