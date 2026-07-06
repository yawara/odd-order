---
id: 9036
slug: proper-subgroup-card-api
title: "Public proper subgroup cardinality API"
created: 2026-07-06
---

# Public proper subgroup cardinality API

## 背景

BG §1 `S01_Solvable.lean` and Isaacs Ch04 both have private copies of the
finite-cardinality fact that a proper subgroup has strictly smaller cardinality
than the ambient group.

## やること

- [x] Add public `Subgroup.card_lt_card_of_ne_top`.
- [x] Build `OddOrder.Mathlib.Subgroup`.

## 完了条件

The lemma is sorry-free, the target leaf build passes, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
- `OddOrder/Mathlib/Subgroup.lean`


## 完了メモ

2026-07-06 lane d: added public `Subgroup.card_lt_card_of_ne_top`, matching the
private BG §1 / Isaacs Ch04 cardinality helper. Verified by
`lake build OddOrder.Mathlib.Subgroup`.
