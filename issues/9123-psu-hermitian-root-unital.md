---
id: 9123
slug: psu-hermitian-root-unital
title: "claim: PSU(3,q) Hermitian root group and unital (lane b)"
created: 2026-07-18
---

# claim: PSU(3,q) Hermitian root group and unital (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 needs the standard `PSU(3,q)`
permutation target of degree `q^3 + 1`.  Issue 9122 constructed the canonical
quadratic extension and proved that every Hermitian trace equation has exactly
`q` solutions.  No open 9000-series claim owns the next layer: the concrete
unitary root group and its one-point compactification.  This carrier is shared
by the standard unitary generators, the doubly transitive action, and the later
Sylow/root-group calculations in §3 Proposition 1(c).

## やること

- [ ] Define the Hermitian root group on pairs `(a,b)` satisfying
  `b + star b = a * star a`.
- [ ] Prove the standard multiplication and inverse formulas form a genuine
  finite group, without posited closure or group-law fields.
- [ ] Compute its exact cardinality `q^3` from the trace-fiber theorem and prove
  its `2`-group property.
- [ ] Define the infinity-plus-affine Hermitian unital carrier and compute its
  exact cardinality `q^3 + 1`.
- [ ] Wire the leaf into `OddOrder.lean` and `AxiomsCheck.lean`.

## 完了条件

For every positive extension exponent, the concrete root group has no opaque
carrier fields or posited algebraic/cardinality laws, and the unital carrier has
the degree required by Peterfalvi Lemma 1.  The leaf is strict warning-clean;
its module, full `OddOrder`, and axiom-audit builds pass.

## 参照

Upstream: issue 9122, commit `a148dc54a`.  Primary source: Peterfalvi Part II,
Chapter I §3, Lemma 1 (p. 105), citing Huppert II, Satz 10.12.  Next consumer:
the standard root/torus/Weyl permutation generators for `PSU(3,q)`.
