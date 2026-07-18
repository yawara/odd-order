---
id: 9127
slug: psu-bruhat-decomposition
title: "claim: PSU(3,q) Bruhat decomposition (lane b)"
created: 2026-07-18
---

# claim: PSU(3,q) Bruhat decomposition (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 uses the standard `PSU(3,q)`
structure, while Chapter IV §3 identifies the reciprocal Weyl coordinates and
the cubic Hua parameter. Issue 9126 and commit `609fdea4f` constructed the
faithful determinant-one root--torus Borel. No open 9000-series claim owns the
next upstream layer: the nontrivial Weyl--root relation, two Bruhat cells,
point-stabilizer equality, and exact full group order.

## やること

- [ ] Construct the determinant-one Hua/Bruhat torus parameter from the nonzero
  second root coordinate and prove its underlying value is `star(b) / b^2`.
- [ ] Define the right root parameter and prove the coordinate identities needed
  for the nontrivial relation `w R(u) w = b₁ w b₂`.
- [ ] Prove the Weyl--root relation as equality of concrete unital permutations,
  including pole, origin, and generic affine cases.
- [ ] Prove inverse closure of the standard generators and use closure induction to
  obtain the honest two-cell cover `G = B ∪ B w B` for `0 < n`.
- [ ] Deduce `standardBorel = stabilizer infinity` and the exact group order
  `q^3 * (q^3 + 1) * ((q^2 - 1) / gcd(q + 1, 3))`.
- [ ] Wire the Bruhat leaves into the project and axiom audit; update the
  Peterfalvi frontier after strict, module, audit, and full builds pass.

## 完了条件

The concrete standard permutation group has an honestly proved two-cell Bruhat
decomposition. The standard Borel is identified with the infinity stabilizer and
the full PSU order is derived from the action. The Hua parameter is constructed
in `PSUTorusParameter`; no `sorry`, new `axiom`, PGU substitution, or opaque
Weyl--root relation is introduced.

## 参照

Upstream: issue 9126, commit `609fdea4f`,
`ProjectiveUnitary/Borel.lean`. Architecture reference:
`SpecificGroups/Suzuki/Bruhat.lean`. Text reference: Peterfalvi Part II,
Chapter IV §3 Proposition and Corollary 2 (pp. 129-132). Next consumer: the
exact PSU simplicity and induction-hypothesis target.
