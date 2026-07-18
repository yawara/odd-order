---
id: 9124
slug: psu-standard-generators
title: "claim: PSU(3,q) standard permutation generators (lane b)"
created: 2026-07-18
---

# claim: PSU(3,q) standard permutation generators (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 needs the concrete standard
`PSU(3,q)` action on the Hermitian unital.  Issues 9122 and 9123 constructed
the quadratic involutive field, the root group, and the exact `q^3 + 1` point
carrier.  No open 9000-series claim owns the next layer: faithful root and torus
permutations together with the unitary Weyl involution.  These generators are
the input for the Bruhat decomposition, double transitivity, exact group order,
and the eventual simplicity proof.

## やること

- [ ] Complete the quadratic-field norm-image API needed by unitary torus
  parameters, without introducing a redundant fixed-subfield carrier.
- [ ] Construct the faithful root-group permutations of the unital and prove
  regularity on the affine points.
- [ ] Construct the unitary torus weight and its root-group automorphisms, then
  realize them as permutations fixing infinity and the affine origin.
- [ ] Construct the Weyl involution swapping infinity and the origin, with the
  explicit nonzero-coordinate formula `(a,b) ↦ (a/b, 1/b)`.
- [ ] Prove the generator action and conjugation formulas required by the next
  Borel and Bruhat leaves; wire the leaf into the project and axiom audit.

## 完了条件

The three concrete generator families act by actual permutations on the exact
Hermitian unital carrier, with no posited closure, bijectivity, or action laws.
The root action is faithful and regular on affine points, the Weyl map is an
involution, and the torus action is given by the standard `SU(3)` weight.  The
leaf is strict warning-clean; its module, full `OddOrder`, and axiom-audit builds
pass.

## 参照

Upstream: issue 9123, commit `d03377936`.  Primary source: Peterfalvi Part II,
Chapter I §3, Lemma 1 (p. 105), via Huppert II, Satz 10.12.  The coordinate
formulas are the standard rank-one `SU(3)` root, diagonal, and Weyl actions.
Next consumers: the standard Borel, Bruhat decomposition, doubly transitive
permutation group, and simplicity target.
