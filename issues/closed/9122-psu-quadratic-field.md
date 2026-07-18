---
id: 9122
slug: psu-quadratic-field
title: "claim: PSU(3,q) quadratic field and Hermitian trace infrastructure (lane b)"
created: 2026-07-18
---

# claim: PSU(3,q) quadratic field and Hermitian trace infrastructure (lane b)

## 背景

Peterfalvi Part II, Chapter I §3, Lemma 1 uses the standard `PSU(3,q)`
action for `q > 2` a power of two.  The next honest target construction starts
with `GF(q^2)` and its order-two `q`-Frobenius conjugation.  Repository and open
9000-claim searches found no finite unitary-group or quadratic-field involution
layer; mathlib supplies `GaloisField`, iterated Frobenius, and generic matrix
unitary groups but not this finite-field specialization.  This layer is shared by
the Hermitian unital, the root/Sylow subgroup coordinates, and the later PGU/PSU
recognition work.

## やること

- [x] Create `GroupTheory/SpecificGroups/ProjectiveUnitary/Field.lean` for the
  field of order `2^(2*n)` and the `2^n`-Frobenius conjugation.
- [x] Prove the conjugation has order two and install the corresponding
  nontrivial `StarRing` structure.
- [x] Compute the fixed-element set cardinality `2^n`.
- [x] Define Hermitian trace and norm, prove their values are fixed, and prove
  every fixed trace value has exactly `2^n` preimages.
- [x] Wire the shared leaf into `OddOrder.lean` and `AxiomsCheck.lean`.

## 完了条件

For every positive `n`, the concrete quadratic field carries an axiom-clean
q-Frobenius involution with exact fixed-field and trace-fiber counts.  No opaque
carrier fields or posited cardinality/surjectivity hypotheses remain.  The leaf is
strict warning-clean and its module, full `OddOrder`, and axiom-audit builds pass.

## 参照

Upstream: issue 9121, commit `58052dcd2`.  Primary source: Peterfalvi Part II,
Chapter I §3, Lemma 1 (p. 105), citing Huppert II, Satz 10.12.  Consumers:
Hermitian unital coordinates, the standard PSU(3,q) permutation group, and §3
Proposition 1(c).

## 結果

`FiniteField.Extension (GaloisField 2 n) 2 2` gives the canonical quadratic
extension without choosing an embedding.  The generic finite-field trace and
rank-nullity compute every trace fiber exactly; the fixed set, every Hermitian
trace equation `b + star b = a * star a`, and the trace kernel all have cardinal
`2^n`.  The q-Frobenius is also proved nontrivial for positive `n`.  The leaf is
strict warning-clean, and its module build, full `OddOrder` build (4395 jobs),
and `AxiomsCheck` build (4343 jobs) all pass.
