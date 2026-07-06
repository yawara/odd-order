---
id: 9035
slug: hall-invariant-overgroup-lift
title: "Public Hall/A-invariant overgroup lift API"
created: 2026-07-06
---

# Public Hall/A-invariant overgroup lift API

## 背景

BG §1 `S01_Solvable.lean` has private proper-overgroup branch helpers:

- `lift_hall_from_invariant_overgroup`
- `proper_overgroup_branch_frame`

They are generic Hall/A-invariant overgroup packaging lemmas, using only the
Isaacs Ch03 `IsHallSubgroup`, `Subgroup.IsPiGroup`, and `IsAInvariant` APIs.

## やること

- [x] Add public `OddOrder.Isaacs.Ch03.lift_hall_from_invariant_overgroup`.
- [x] Add public `OddOrder.Isaacs.Ch03.proper_overgroup_branch_frame`.
- [x] Build `OddOrder.Isaacs.Ch03_SplitExtensions.Main`.

## 完了条件

Both lemmas are sorry-free, the target leaf build passes, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`


## 完了メモ

2026-07-06 lane d: added both public Ch03 packaging lemmas. Verified by
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main`.
