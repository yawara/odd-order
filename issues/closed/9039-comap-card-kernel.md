---
id: 9039
slug: comap-card-kernel
title: "Public comap cardinality via kernel API"
created: 2026-07-06
---

# Public comap cardinality via kernel API

## 背景

BG §1 `S01_Solvable.lean` has a private `card_comap_eq_card_mul_card_ker`
helper for the cardinality of a subgroup preimage under a surjective finite-group
homomorphism. This is generic cardinal API and belongs in `OddOrder/Mathlib`.

## やること

- [x] Add public `Subgroup.card_comap_eq_card_mul_card_ker`.
- [x] Build `OddOrder.Mathlib.Subgroup`.

## 完了条件

The lemma is sorry-free, the target leaf build passes, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Mathlib/Subgroup.lean`


## 完了メモ

2026-07-06 lane d: added public `Subgroup.card_comap_eq_card_mul_card_ker`.
Verified by `lake build OddOrder.Mathlib.Subgroup`.
