---
id: 9121
slug: suzuki-induction-target
title: "claim: Peterfalvi §3 Lemma 1 concrete Sz(q) target (lane b)"
created: 2026-07-18
---

# claim: Peterfalvi §3 Lemma 1 concrete Sz(q) target (lane b)

## 背景

`InductionHypothesis.lean` already proves the target-independent core of Peterfalvi
Part II, Chapter I, Section 3, Lemma 1, and `InductionHypothesisPSL.lean`
discharges the PSL branch.  Commit `db01803ac` now supplies an honestly constructed
simple standard Suzuki permutation group on an ovoid of degree
`2^(2*(2*m+1)) + 1` for every `0 < m`.  Repository and open 9000-claim searches
found no existing bridge from these concrete coordinates into the Lemma 1 core.

## やること

- [x] Add `InductionHypothesisSuzuki.lean` parallel to the PSL target leaf.
- [x] Transport the concrete ovoid degree to prove `|Omega| - 1` is a power of two.
- [x] Transport simplicity across `L ≃* standardPermGroup m`.
- [x] Feed both results into `simple_normal_oddIndex_Q_core` to identify `Q`,
  `primeComplementResidual 2 G`, and the join of conjugates.
- [x] Wire the leaf into the Suzuki hub, `OddOrder.lean`, and `AxiomsCheck.lean`.

## 完了条件

The concrete Sz(q) coordinates discharge every target-specific premise of
Peterfalvi Section 3 Lemma 1 for positive `m`, without opaque hypotheses or
new axioms.  The leaf is strict warning-clean and the module, full `OddOrder`,
and axiom-audit builds pass.

## 参照

Upstream: issue 9120, commit `db01803ac`;
`GroupTheory/SpecificGroups/Suzuki/Simplicity.lean`.
Consumers: the complete Lemma 1 target inventory and the following PSU(3,q)
branch.  Frontier note: `notes/peterfalvi/suzuki_ch1.md`, item 9.

## 結果

- Added `InductionHypothesisSuzuki.lean` with the concrete ovoid degree,
  transported simplicity, and the complete `Q`/residual/conjugate-join endpoint.
- The degree computation is the exact identity
  `|Omega| - 1 = 2^(2*(2*m+1))`; the action is transported by an equivariant
  bijection rather than inferred from an abstract group isomorphism.
- The Suzuki hub, explicit axiom audit, and full `OddOrder` build pass.  Each new
  public theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## 完了

2026-07-18.  The next document-order target is the PSU(3,q) branch of the same
lemma. Secondary order and Sylow data remain correctly deferred to Proposition 1(c).
