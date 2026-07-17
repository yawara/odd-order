---
id: 9116
slug: suzuki-standard-generators
title: "claim: SpecificGroups/Suzuki/StandardGenerators — root, torus, and Weyl permutations (lane b)"
created: 2026-07-18
---

# claim: SpecificGroups/Suzuki/StandardGenerators — root, torus, and Weyl permutations (lane b)

## 背景

The defining field, Tits twist, root group, anisotropic norm, and `q^2 + 1`
point carrier are now concrete.  The next upstream prerequisite for the standard
Suzuki permutation target in Peterfalvi Part II, Chapter I, section 3 is the
actual root, torus, and Weyl action on that carrier.  Repository and open-claim
searches found no existing construction.

## やること

- [ ] Add `OddOrder/GroupTheory/SpecificGroups/Suzuki/StandardGenerators.lean`.
- [ ] Construct the root-group permutation homomorphism fixing infinity and acting regularly on the affine chart.
- [ ] Construct the torus permutation homomorphism with its explicit coordinate scaling.
- [ ] Prove the root/torus conjugation formula in ovoid coordinates.
- [ ] Construct the Weyl permutation, prove it swaps infinity and the affine origin, and prove involutivity from the reciprocal norm identity.
- [ ] Expose warning-clean evaluation and injectivity APIs for later group generation.
- [ ] Wire the leaf into `OddOrder.lean` and `OddOrder.AxiomsCheck`.

## 完了条件

All three generator families are concrete permutations with proved coordinate
formulas; the root and torus families are honest homomorphisms, the Weyl map is
proved involutive, and the conjugation relation is explicit.  The leaf is
warning-clean, contains no `sorry` or new `axiom`, and passes the full `OddOrder`
build and `OddOrder.AxiomsCheck`.

## 参照

Upstream: `OddOrder/GroupTheory/SpecificGroups/Suzuki/Ovoid.lean` (issue 9115).
Consumers: the generated Suzuki permutation group, double transitivity, and the
concrete Sz(q) target for Peterfalvi Lemma 1. Frontier note:
`notes/peterfalvi/suzuki_ch1.md`, item 9.
