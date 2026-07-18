---
id: 9115
slug: suzuki-ovoid-norm
title: "claim: SpecificGroups/Suzuki/Ovoid — norm and q^2+1 point model (lane b)"
created: 2026-07-18
---

# claim: SpecificGroups/Suzuki/Ovoid — norm and q^2+1 point model (lane b)

## 背景

The defining field, Tits twist, and nonabelian root group are now concrete.
The next upstream object required for the standard Suzuki permutation target in
Peterfalvi Part II, Chapter I, section 3 is its `q^2 + 1` point ovoid.  Its
affine chart uses the anisotropic Suzuki norm
`N(x,y) = x^2 * theta(x) + x*y + theta(y)`.  Repository and open-claim searches
found no existing norm or ovoid construction.

## やること

- [x] Add `OddOrder/GroupTheory/SpecificGroups/Suzuki/Ovoid.lean`.
- [x] Define the Suzuki norm and prove its characteristic-two twist identities.
- [x] Prove `N(x,y) = 0` exactly at `(0,0)`.
- [x] Prove the reciprocal norm identity needed by the Weyl involution.
- [x] Construct the ovoid point type as infinity plus the affine root-group chart.
- [x] Prove its exact cardinality `q^2 + 1` and finite structural API.
- [x] Wire the leaf into `OddOrder.lean` and `OddOrder.AxiomsCheck`.

## 完了条件

The norm is proved anisotropic, the Weyl reciprocal identity is available, and
the concrete ovoid carrier has verified cardinality `2^(2*(2m+1)) + 1`.  The
leaf is warning-clean, contains no `sorry` or new `axiom`, and passes the full
`OddOrder` build and `OddOrder.AxiomsCheck`.

## 参照

Upstream: `OddOrder/GroupTheory/SpecificGroups/Suzuki/RootGroup.lean` (issue 9114).
Consumers: standard Suzuki root/torus/Weyl permutations and the concrete Sz(q)
target for Peterfalvi Lemma 1. Frontier note: `notes/peterfalvi/suzuki_ch1.md`,
item 9.
