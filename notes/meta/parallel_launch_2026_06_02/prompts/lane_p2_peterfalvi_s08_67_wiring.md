# Lane P2 — Peterfalvi S08 (6.7) Wiring

You are running over SSH on `omen01.local`. Use only the remote checkout
`/home/ywr/odd-order`. Do not use `/Users/ywr/...` paths and do not use Codex app
background thread creation.

## Goal

Turn the existing atom-level Peterfalvi (6.7.3) infrastructure into a useful
top-level (6.7) theorem for S08. The target is to close the remaining
`peterfalvi_673` unconditional/wiring gap as far as possible, especially the
`(iii)-collapse` / central-class-size constancy / rationality bridge described
in issue 0046 and `s08_6_8_assembly_plan.md` T3.

If the full (6.7) top theorem is too large, land a green, named theorem that
strictly reduces the remaining capstone to one documented mathematical atom.

## Worktree Setup

```bash
MAIN=/home/ywr/odd-order
WT=/home/ywr/odd-order-pf-s08-67
BR=codex/pf-s08-67
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
lake build OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra
lake build OddOrder.Peterfalvi.S08_CoherenceTheorems
```

## Read First

- `AGENTS.md`
- `issues/0046-peterfalvi-s08-6-8-coherence.md`
- `notes/peterfalvi/s08_6_8_assembly_plan.md`, especially T3
- `notes/peterfalvi/s08_coherence_theorems.md`, search for `peterfalvi_673`
- `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean`
- `OddOrder/Algebra/AlgInt.lean`
- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`

## Task Shape

Do not work on Brauer/inertia Layer C. Do not try to close
`sibleySetup_is_coherent` directly.

Expected path:

1. Locate existing theorems:
   `peterfalvi_673_combine`, `peterfalvi_673_cancel`,
   `peterfalvi_673_final`, `peterfalvi_673`, and any central-character
   congruence helpers.
2. Identify the exact remaining hypothesis set of `peterfalvi_673`.
3. Compare those hypotheses against the atoms documented in issue 0046:
   `a_{110}=0`, `a_{120}=|C₁|`, `ω(C_s)=α` const, and `(|C₁|, p)=1`.
4. Prove the missing structural/collapse lemma in the smallest file that fits.
   Prefer a theorem with a mathematically meaningful statement over changing
   capstone hypotheses.
5. If a top theorem `peterfalvi_67` is not currently present, add a carefully
   scoped theorem statement in S08 or ClassSumAlgebra that consumes the atom
   package and returns the final congruence `ψ(z) ≡ ψ(1) (mod |P|)`.
6. Register AxiomsCheck assertions for new reusable theorems if the surrounding
   file follows that pattern.

## Completion Criteria

- No new `sorry` or project axioms.
- `lake build OddOrder.GroupTheory.RepresentationTheory.ClassSumAlgebra` passes.
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` passes.
- Commit in one logical commit if green.
- Final report: exact remaining hypotheses for (6.7), files changed, commit
  hash, builds run.

