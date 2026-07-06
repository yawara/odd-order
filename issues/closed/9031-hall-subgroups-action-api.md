---
id: 9031
slug: hall-subgroups-action-api
title: "claim: Ch03 HallSubgroups action and pretransitivity API (lane d)"
created: 2026-07-06
---

# claim: Ch03 HallSubgroups action and pretransitivity API (lane d)

## 背景

BG §1 `S01_Solvable.lean` has private `HallSubgroups`/action/pretransitivity
helpers for applying Glauberman fixed-point machinery to Hall subgroups. Ch03 already owns
`IsHallSubgroup` and `hall_C`, so the Hall-subgroup action type and transitivity theorem
belong there as shared infrastructure.

## やること

- [x] Add public `HallSubgroups`.
- [x] Add public `HallSubgroups.mulAutAction` and `HallSubgroups.conjAction`.
- [x] Add public `HallSubgroups.conjAction_pretransitive`.
- [x] Build `OddOrder.Isaacs.Ch03_SplitExtensions.Main`.

## 完了条件

The Hall-subgroup action API is sorry-free, Ch03 leaf build passes, and this issue is moved
to `issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`

## 完了メモ

2026-07-06 lane d: added public Ch03 `HallSubgroups`, automorphism/conjugation actions,
and `HallSubgroups.conjAction_pretransitive` using `hall_C`. Verified by
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main`.
