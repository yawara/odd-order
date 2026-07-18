---
id: 2046
slug: strongly-real-elements
title: "Peterfalvi I.3 Lemma 3 strongly real elements"
created: 2026-07-19
---

# Peterfalvi I.3 Lemma 3 strongly real elements

## 背景

Peterfalvi Part II, Chapter I, §3, Lemma 3 formalizes the normal form and
centralizer parity of strongly real elements.  This is the next upstream result
after Lemma 2 in the Suzuki appendix frontier.

## やること

- [x] Define strongly real elements as products of two nontrivial involutions.
- [x] Prove that `x ^ 2 ≠ 1` forces the two chosen involutions to have distinct
  fixed points.
- [x] Formalize the transitivity on triples used to conjugate `x` to `u * t`
  with `u ∈ Q₀#`.
- [x] Prove that the centralizer of `u * t` has odd cardinality by excluding
  involutions through the odd-dihedral conjugacy argument.
- [x] Transport the centralizer result across conjugacy and audit the public
  declarations in `OddOrder/AxiomsCheck.lean`.

## 完了条件

- The exact two conclusions of Peterfalvi I.3 Lemma 3 are proved without new
  axioms, opaque carriers, or `sorry`.
- The Suzuki hub, source survey, and chapter handoff note are updated.
- The new leaf, hub, and `OddOrder/AxiomsCheck.lean` build successfully.

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
- `notes/peterfalvi/suzuki_ch1.md`
- `issues/closed/2045-conjugacy-in-v.md`
