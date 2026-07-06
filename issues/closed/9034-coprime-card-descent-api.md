---
id: 9034
slug: coprime-card-descent-api
title: "claim: coprime cardinality descent to subgroups and quotients API (lane d)"
created: 2026-07-06
---

# claim: coprime cardinality descent to subgroups and quotients API (lane d)

## 背景

BG §1 `S01_Solvable.lean` has private helpers:

- `coprime_card_quotient_of_coprime`
- `coprime_card_subgroup_of_coprime`

These are generic cardinal divisibility consequences: coprimality with the ambient
finite group order descends to subgroup and quotient orders.

## やること

- [x] Add public `Subgroup.coprime_card_subgroup_right`.
- [x] Add public `Subgroup.coprime_card_quotient_right`.
- [x] Build `OddOrder.Mathlib.Subgroup`.

## 完了条件

Both lemmas are sorry-free, the target leaf build passes, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Mathlib/Subgroup.lean`

## 完了メモ

2026-07-06 lane d: added public subgroup and quotient cardinal coprime descent lemmas,
both proved by `Nat.Coprime.coprime_dvd_right` and the standard subgroup/quotient card
divisibility facts. Verified by `lake build OddOrder.Mathlib.Subgroup`.
