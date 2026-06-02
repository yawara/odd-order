# Lane R1 -- Representation Infrastructure: Mackey, Galois, Clifford

You are working over SSH on `omen01.local`.

This lane supports Peterfalvi §8-§9 and later character theory. It should build
reusable infrastructure, not own the S08/S09 capstone proof itself.

## Worktree Setup

Use:

- main checkout: `/home/ywr/odd-order`
- worktree: `/home/ywr/odd-order-repr-infra`
- branch: `codex/repr-infra-mackey-clifford`

Setup commands:

```bash
cd /home/ywr/odd-order
git worktree add -b codex/repr-infra-mackey-clifford /home/ywr/odd-order-repr-infra main
cd /home/ywr/odd-order-repr-infra
mkdir -p .lake
test -e .lake/packages || ln -s /home/ywr/odd-order/.lake/packages .lake/packages
test -e references || ln -s /home/ywr/odd-order/references references
test -d .lake/build || cp -a /home/ywr/odd-order/.lake/build .lake/build
```

Do not run `lake update`. Do not push.

## Explicit Goal

Set this as your goal at the start:

> Build the reusable representation-theory infrastructure that Peterfalvi §8-§9
> still lacks: Mackey restriction/induction formulas, Galois action on
> irreducible characters, Clifford orbit/inertia/multiplicity core, and any
> `CharacterTableIndexing.ofFinite` or class-function API needed to remove
> conditional scaffolding. Land broad coherent API commits and continue until P4
> can consume the infrastructure or a precise non-hoisted blocker remains.

If a goal tool is available, call it with that objective.

## Ownership

Primary:

- `OddOrder/GroupTheory/RepresentationTheory/*.lean`
- `OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean`
- `OddOrder/Peterfalvi/S07_Coherence.lean` only for reusable infrastructure
- relevant representation issues/notes:
  - `issues/0046-peterfalvi-s08-6-8-coherence.md`
  - `issues/0044-peterfalvi-s09-card-g0-lower-bound.md`
  - closed issues 0022/0026/0027/0040 as historical context

Avoid owning:

- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`
- `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`

Small import/API edits there are acceptable only if required by a completed
infrastructure commit.

## Context To Read First

- `issues/0046-peterfalvi-s08-6-8-coherence.md`, especially the Mackey and
  Galois prerequisite sections.
- `notes/peterfalvi/autonomous_prove_queue.md`
- `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
- `OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean`
- `OddOrder/GroupTheory/RepresentationTheory/Clifford.lean`
- `OddOrder/GroupTheory/RepresentationTheory/InflationCharacter.lean`
- `OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean`

## Work Program

Do not stop after one helper. Work down this infrastructure backlog:

1. Mackey/restriction formula sufficient for induced characters used in
   Peterfalvi (6.8) and [Is] Thm 6.34 style arguments.
2. Galois action on `Irr` and coherence invariance, enough for Peterfalvi
   (1.9)/(5.9.a) usage.
3. Clifford core: replace tautological scaffold with orbit/inertia/multiplicity
   theorems that consumers can call.
4. Character-table indexing / conjugacy class count constructors if still
   needed by unconditional column orthogonality or Brauer arguments.
5. Update AxiomsCheck for new public theorems when appropriate.

Recommended broad commit boundaries. Combine adjacent items when they form one
coherent API increment; avoid single-helper or proof-step commits:

- Mackey formula API.
- Galois action API.
- Clifford core API.
- indexing/class table API.
- AxiomsCheck + notes cleanup.

## Anti-Scaffold Rule

No theorem should merely repackage a hypothesis that states its conclusion.
Infrastructure is complete only when a downstream consumer can construct the
inputs from existing data.

## Verification

Run focused builds matching changed files, then:

```bash
lake build OddOrder.GroupTheory.RepresentationTheory
lake build OddOrder.Peterfalvi.S07_Coherence
```

Before final, run `lake build OddOrder` if feasible.

Final response must include commit hashes, APIs added, downstream consumer
examples if available, build commands, and exact remaining blockers.

