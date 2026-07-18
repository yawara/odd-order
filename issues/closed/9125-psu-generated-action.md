---
id: 9125
slug: psu-generated-action
title: "claim: PSU(3,q) generated permutation action (lane b)"
created: 2026-07-18
---

# claim: PSU(3,q) generated permutation action (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 requires a concrete doubly transitive
action of `PSU(3,q)` on `q^3 + 1` points. Issue 9124 and commit `76db947b8`
constructed actual root, determinant-one torus, and Weyl permutations on the
Hermitian unital. No open 9000-series claim owns the next upstream layer:
taking their honest closure inside the finite symmetric group, internalizing
the generators, and proving double transitivity.

## やること

- [x] Define the standard generator set and its subgroup closure in
  `Equiv.Perm (Unital n)`, using the determinant-one torus rather than the
  larger full diagonal group.
- [x] Internalize the root, PSU-torus, and Weyl generators as elements of the
  closure; retain faithful root and torus homomorphisms and explicit actions.
- [x] Prove transitivity by moving every point to infinity using a root
  translation followed by Weyl.
- [x] Prove that the infinity stabilizer is transitive on the affine chart,
  then derive `IsMultiplyPretransitive ... 2`.
- [x] Wire the leaf into the project and axiom audit; update the Peterfalvi
  frontier after strict, module, audit, and full builds pass.

## 完了条件

The generated group is an actual finite subgroup of the unital permutation
group, not a posited carrier. Its three generator families are constructed in
the subgroup, the root and torus maps remain faithful, and the concrete action
is proved doubly transitive. No `sorry`, new `axiom`, or opaque action law is
introduced.

## 参照

Upstream: issue 9124, commit `76db947b8`,
`ProjectiveUnitary/StandardGenerators.lean`. Architecture reference:
`SpecificGroups/Suzuki/GeneratedAction.lean`. Next consumers: the standard
Borel, Bruhat decomposition, exact group order, and simplicity proof.
