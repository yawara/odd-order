---
id: 9120
slug: suzuki-simplicity
title: "claim: SpecificGroups/Suzuki/Simplicity — simple standard Suzuki group for positive m (lane b)"
created: 2026-07-18
---

# claim: SpecificGroups/Suzuki/Simplicity — simple standard Suzuki group for positive m (lane b)

## 背景

The concrete standard Suzuki group now has a faithful doubly transitive ovoid action,
an explicitly identified Borel stabilizer, a two-cell Bruhat decomposition, and exact
order.  The next upstream layer needed by Peterfalvi Part II, Chapter I, Section 3,
Lemma 1 is simplicity for the nondegenerate parameters `0 < m` (`q >= 8`).
Repository and open 9000-claim searches found no existing Suzuki simplicity result.
The proof uses a reusable quotient criterion: a faithful quasiprimitive action of a
nontrivial perfect group with a solvable point stabilizer has simple acting group.
All group-specific perfectness and stabilizer input is proved from the concrete
root, torus, Weyl, and Borel formulas.

## やること

- [x] Add the shared `GroupAction/PerfectQuasiprimitive.lean` quotient criterion.
- [x] Add a topic-coherent `SpecificGroups/Suzuki/Simplicity.lean` leaf.
- [x] Prove the nonidentity torus action is fixed-point-free and its root
  displacement map is surjective.
- [x] Put every root, torus, and Weyl generator in the derived subgroup and prove
  `commutator (standardPermGroup m) = ⊤` for `0 < m`.
- [x] Prove the standard Borel point stabilizer is solvable.
- [x] Apply the shared quasiprimitive criterion to obtain
  `IsSimpleGroup (standardPermGroup m)`.
- [x] Wire both leaves and all public endpoints into `OddOrder.lean` and
  `OddOrder/AxiomsCheck.lean`.

## 実施結果

`PerfectQuasiprimitive.lean` proves the general quotient criterion with no
finite-group specialization.  `Simplicity.lean` proves torus displacement
surjectivity through mathlib's finite fixed-point-free commutator-map theorem,
then derives explicit root/torus/Weyl membership in the commutator subgroup,
perfectness, solvability of the Borel stabilizer, and simplicity.  The restriction
`0 < m` is essential: the `m = 0` construction has order `20`.

## 完了条件

For every positive `m`, the already constructed standard Suzuki permutation group
is proved simple without opaque hypotheses.  The leaf is warning-clean, contains no
`sorry` or new `axiom`, and passes the module, full `OddOrder`, and axiom-audit builds.

## 参照

Upstream: `SpecificGroups/Suzuki/Bruhat.lean` (issue 9119, commit `c0ef86184`).
Consumer: wiring the concrete simple `Sz(q)` target into Peterfalvi Part II, Chapter I,
Section 3, Lemma 1.  Frontier note: `notes/peterfalvi/suzuki_ch1.md`, item 9.
