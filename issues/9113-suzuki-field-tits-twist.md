---
id: 9113
slug: suzuki-field-tits-twist
title: "claim: SpecificGroups/Suzuki/Field — Tits twist for Sz(q) (lane b)"
created: 2026-07-18
---

# claim: SpecificGroups/Suzuki/Field — Tits twist for Sz(q) (lane b)

## 背景

Peterfalvi Part II, Chapter I section 3, Lemma 1 requires the concrete standard
Suzuki action after the completed PSL target branch. Repository and mathlib searches found
no Suzuki field, ovoid, permutation group, or Tits-twist API. This claim reserves the
first shared leaf before construction begins.

## やること

- [ ] Add `OddOrder/GroupTheory/SpecificGroups/Suzuki/Field.lean`.
- [ ] Define the characteristic-two field of order `2^(2*m+1)`.
- [ ] Construct the `(m+1)`-fold Frobenius Tits twist.
- [ ] Prove its power formula and that its square is Frobenius `x |-> x^2`.
- [ ] Wire the shared leaf into `OddOrder.lean` and the explicit axiom audit.

## 完了条件

The leaf builds without warnings, contains no `sorry` or new `axiom`, and the
Tits-twist power and square identities pass `OddOrder.AxiomsCheck`. The issue is then
moved to `issues/closed/`.

## 参照

Consumer: `OddOrder/Peterfalvi/Appendices/Suzuki/InductionHypothesisSuzuki.lean`.
Frontier note: `notes/peterfalvi/suzuki_ch1.md`, item 9.
Existing Frobenius API: `Mathlib/FieldTheory/Perfect.lean`.
