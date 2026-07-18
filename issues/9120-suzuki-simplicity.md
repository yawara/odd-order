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
Mathlib provides Iwasawa's criterion, while all group-specific generation and
perfectness input must be proved from the concrete root/torus/Weyl formulas.

## やること

- [ ] Add a topic-coherent `SpecificGroups/Suzuki/Simplicity.lean` leaf.
- [ ] Construct the conjugacy-equivariant abelian subgroups needed by the simplicity argument.
- [ ] Prove their conjugates generate `standardPermGroup m`.
- [ ] Prove perfectness from explicit root, torus, and Weyl relations for `0 < m`.
- [ ] Apply Iwasawa's criterion, or an equivalent normal-subgroup argument, to obtain
  `IsSimpleGroup (standardPermGroup m)`.
- [ ] Wire the public endpoint into `OddOrder.lean` and `OddOrder/AxiomsCheck.lean`.

## 完了条件

For every positive `m`, the already constructed standard Suzuki permutation group
is proved simple without opaque hypotheses.  The leaf is warning-clean, contains no
`sorry` or new `axiom`, and passes the module, full `OddOrder`, and axiom-audit builds.

## 参照

Upstream: `SpecificGroups/Suzuki/Bruhat.lean` (issue 9119, commit `c0ef86184`).
Consumer: the concrete `Sz(q)` target for Peterfalvi Part II, Chapter I, Section 3,
Lemma 1.  Frontier note: `notes/peterfalvi/suzuki_ch1.md`, item 9.
