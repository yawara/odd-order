# Lane P1 — Peterfalvi Brauer/Inertia Layer C

You are running over SSH on `omen01.local`. Use only the remote checkout
`/home/ywr/odd-order`. Do not use `/Users/ywr/...` paths and do not use Codex app
background thread creation.

## Goal

Complete issue `0053` Layer C: prove the bridge from a free conjugation action
on nonidentity elements/classes to `ClassFunction.inertia (θ : ClassFunction H ℂ)
= H` for nontrivial irreducible characters. The concrete output should be a
sorry-free `inertia_eq_of_freeAction`-style theorem plus supporting fixed-class
count lemmas, with the relevant leaf builds green.

If the main theorem lands early, continue into the first mechanical Layer D
wiring lemma needed by Peterfalvi (6.8) T6, but do not edit S08 capstone proof
unless the Layer C API is complete and green.

## Worktree Setup

Main checkout:

```bash
MAIN=/home/ywr/odd-order
WT=/home/ywr/odd-order-pf-brauer-inertia
BR=codex/pf-brauer-inertia
```

If `$WT` exists, `cd $WT`. If it does not exist, create it from `$MAIN`:

```bash
cd "$MAIN"
git worktree add "$WT" -b "$BR"
cd "$WT"
```

If the branch already exists but the worktree does not, use:

```bash
git worktree add "$WT" "$BR"
```

Bootstrap shared dependencies without overwriting existing paths:

```bash
mkdir -p .lake
test -e .lake/packages || ln -s "$MAIN/.lake/packages" .lake/packages
test -e references || ln -s "$MAIN/references" references
test -e .lake/build || cp -a "$MAIN/.lake/build" .lake/build
```

Never run `lake update`. Do not push.

Run baseline builds:

```bash
lake build OddOrder.GroupTheory.RepresentationTheory.ConjugationBrauer
lake build OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
```

## Read First

- `AGENTS.md`
- `issues/0053-brauer-conjugation-inertia.md`
- `notes/peterfalvi/s08_6_8_assembly_plan.md`, especially §D
- `OddOrder/GroupTheory/RepresentationTheory/ConjugationBrauer.lean`
- `OddOrder/GroupTheory/RepresentationTheory/Inertia.lean`
- `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean`
- `OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusActionTI.lean`

## Task Shape

Stay focused on representation-theory/group-action infrastructure. Expected
steps:

1. Confirm existing Layer A/B API:
   `IrreducibleCharacter.conjByPerm`, `ConjClasses.conjByPerm`,
   `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`, and the
   partial fixed-Irr bridge already listed in issue 0053.
2. Prove that the trivial conjugacy class is fixed by `ConjClasses.conjByPerm g`.
3. Formalize the group-theory hypothesis needed for "only the trivial class is
   fixed". Prefer a reusable lemma with hypotheses like:
   `H.Normal`, `g ∉ H`, and `∀ h : H, h ≠ 1 → centralizer condition forcing g ∈ H`
   or the exact `C_L(h) ≤ H` form used by Frobenius/TI.
4. Convert singleton fixed-class set to
   `Nat.card (Function.fixedPoints (ConjClasses.conjByPerm g)) = 1`.
5. Bundle the result with the existing Irr-side bridge into a theorem:
   nontrivial `θ : IrreducibleCharacter H` has `g ∉ inertia θ` for every
   `g ∉ H`.
6. Finish with `ClassFunction.inertia (θ : ClassFunction H ℂ) = H`.

Avoid over-specializing to Peterfalvi's exact `SibleyDadeHypothesis` unless
needed. The best output is a general reusable lemma in
`ConjugationBrauer.lean` or `Inertia.lean`.

## Completion Criteria

- No new `sorry` or project axioms.
- `lake build OddOrder.GroupTheory.RepresentationTheory.ConjugationBrauer`
  passes.
- If AxiomsCheck has relevant assertions, add/register them and run
  `lake build OddOrder.AxiomsCheck`.
- Commit in one logical commit if green.
- Final report: files changed, commit hash, builds run, remaining blockers.

