# Lane B7 -- BG S10-S13 Maximal-Subgroup Foundation

You are working over SSH on `omen01.local`.

This is an optional long-horizon lane. Start it only if there is enough merge
bandwidth. It is designed to run in parallel with B6 by owning later-section
files, but it should not duplicate B6's §7-§9 setup work.

## Worktree Setup

Use:

- main checkout: `/home/ywr/odd-order`
- worktree: `/home/ywr/odd-order-bg-s10-s13-foundation`
- branch: `codex/bg-s10-s13-foundation`

Setup commands:

```bash
cd /home/ywr/odd-order
git worktree add -b codex/bg-s10-s13-foundation /home/ywr/odd-order-bg-s10-s13-foundation main
cd /home/ywr/odd-order-bg-s10-s13-foundation
mkdir -p .lake
test -e .lake/packages || ln -s /home/ywr/odd-order/.lake/packages .lake/packages
test -e references || ln -s /home/ywr/odd-order/references references
test -d .lake/build || cp -a /home/ywr/odd-order/.lake/build .lake/build
```

Do not run `lake update`. Do not push.

## Explicit Goal

Set this as your goal at the start:

> Replace BG §10-§13 scaffold surfaces with concrete, faithful maximal-subgroup
> foundation: define and document alpha/sigma/beta, M_alpha/M_sigma/M_beta,
> tau_i and E/E_i, and prime/regular action predicates; prove all definitional
> and already-constructible lemmas; leave theorem-level sorries only where they
> require unlanded §7-§9 or §12 hard results, with exact blockers.

If a goal tool is available, call it with that objective.

## Ownership

Primary:

- `OddOrder/BG/Ch3_MaximalSubgroups/S10_MalphaMsigma.lean`
- `OddOrder/BG/Ch3_MaximalSubgroups/S11_ExceptionalMaximal.lean`
- `OddOrder/BG/Ch3_MaximalSubgroups/S12_E.lean`
- `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean`
- notes:
  - `notes/bg/s10_malpha_msigma.md`
  - `notes/bg/s11_exceptional_maximal.md`
  - `notes/bg/s12_subgroup_e.md`
  - `notes/bg/s13_prime_action.md`

Do not edit B6-owned §7-§9 setup modules except for imports after B6 has landed.

## Context To Read First

- `notes/bg/scaffold_feasibility_2026_06_01.md`
- the four section notes listed above
- current S10-S13 Lean files
- `ROADMAP.md` BG §10-§13 rows

## Work Program

This lane is about making the future local-analysis spine real in Lean, not
about pretending the hard theorems are already proved.

1. Inventory all current `sorry` statements in S10-S13 and classify each as:
   - definitional/easy;
   - depends only on already landed §1-§6/§7 setup;
   - depends on unlanded BG hard proof.
2. Replace opaque `Prop` placeholders with real definitions where possible:
   - `alpha(M)`, `sigma(M)`, `beta(M)`;
   - `M_sigma`, `M_alpha`, `M_beta`;
   - tau partitions and E/E_i;
   - `ActsPrimeOn`, `ActsRegularlyOn`.
3. Prove all definitional lemmas opened by those definitions.
4. Update notes with exact result counts and missing PDF/mmd statements.
5. Keep theorem statements faithful; do not add stronger/weaker convenience
   statements without documenting the book correspondence.

Recommended broad commit boundaries. Combine adjacent items when they are one
coherent foundation increment; avoid single-helper or proof-step commits:

- S10 definitions and basic API.
- S11 hypothesis bundle and definitional cleanup.
- S12 tau/E foundation.
- S13 prime-action predicates and basic lemmas.
- notes/inventory cleanup.

## Anti-Scaffold Rule

Hard content must not be turned into fields of a setup structure unless it is a
standing hypothesis in the book at that point. If a theorem needs §9 Uniqueness,
import or depend on the actual theorem name; if it does not exist yet, document
that blocker.

## Verification

Run focused builds:

```bash
lake build OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma
lake build OddOrder.BG.Ch3_MaximalSubgroups.S11_ExceptionalMaximal
lake build OddOrder.BG.Ch3_MaximalSubgroups.S12_E
lake build OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction
```

Before final, run `lake build OddOrder` if feasible.

Final response must include commit hashes, exact definitions added, build
commands, and remaining theorem blockers.

