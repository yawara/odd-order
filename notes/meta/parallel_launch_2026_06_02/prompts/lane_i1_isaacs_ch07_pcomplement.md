# Lane I1 — Isaacs Ch07 Thompson Normal P-Complement

You are running over SSH on `omen01.local`. Use only the remote checkout
`/home/ywr/odd-order`. Do not use `/Users/ywr/...` paths and do not use Codex app
background thread creation.

## Goal

Advance issue `0031`: replace the current conditional/scaffold version of
Isaacs Thm 7.1 with authentic proof infrastructure. The target is not merely a
new wrapper around `normal_J`; it is to formalize real steps from Isaacs
§7C (mmd L3913-L3949), reducing or eliminating the forward normal-J hypothesis
inside `thompson_normal_p_complement`.

If the whole theorem is too large, land a green commit containing one coherent
block of the 7-step proof and update the issue with the exact remaining steps.

## Worktree Setup

```bash
MAIN=/home/ywr/odd-order
WT=/home/ywr/odd-order-isaacs-ch07-pcomp
BR=codex/isaacs-ch07-pcomp
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
lake build OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main
lake build OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B2_NormalJ_PComplement
```

## Read First

- `AGENTS.md`
- `issues/0031-isaacs-ch07-thm-7-1-thompson-pcomplement.md`
- `notes/isaacs/ch07_thompson.md`
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean`
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ.lean`
- `OddOrder/Isaacs/Ch07_ThompsonSubgroup/Main.lean`

## Task Shape

The current theorem surface around `thompson_normal_p_complement` is known to be
a forward-hypothesis scaffold. Work in small proof blocks:

1. Re-read issue 0031's 2026-05-30 READY section and identify the exact current
   theorem statement around `S7B2_NormalJ_PComplement.lean:1667`.
2. Extract the 7 textbook steps into named local lemmas or a small setup
   namespace. Do not add a giant monolithic proof attempt.
3. Prefer the earliest step that can be made sorry-free using existing Ch07,
   Ch05 normal complement, and `normal_J` infrastructure.
4. If a step needs a forward theorem, make the theorem statement precise and
   document it in issue 0031, but avoid adding project axioms unless it is the
   only way to preserve a green intermediate.
5. Keep the existing `normal_J` and Burnside theorem builds green.

Good measurable outcomes:

- A genuine local lemma used by `thompson_normal_p_complement`, replacing a
  placeholder assumption.
- A setup structure that faithfully encodes the 7-step proof and makes the
  scaffold theorem consume fewer forward assumptions.
- A proof of the top theorem in one nondegenerate case beyond `J(P)=⊤`.

## Completion Criteria

- No regressions in `normal_J` or Burnside.
- `lake build OddOrder.Isaacs.Ch07_ThompsonSubgroup.Main` passes.
- `lake build OddOrder.AxiomsCheck` if any flagship theorem dependency changed.
- Commit in one logical commit if green.
- Final report: proof steps completed, files changed, commit hash, builds run,
  remaining proof steps.

