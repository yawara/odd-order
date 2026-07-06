---
id: 9047
slug: complement-quotient-le-left
title: "Complement quotient descent under normal subgroup containment"
created: 2026-07-06
---

# Complement quotient descent under normal subgroup containment

## 背景

BG S03d の局所 helper `isComplement'_map_mk'` と BG S03 の quotient complement setup を、
BG S-file 依存なしで使える generic `Subgroup.IsComplement'` API として
`OddOrder.Mathlib.Subgroup` へ上げる。既存の coprime 版 `IsComplement'.map_mk'` とは
仮定が異なり、こちらは `N ≤ K` による quotient descent。

## やること

- [x] open 9000 issue と既存 complement quotient API を確認する
- [x] `Subgroup.IsComplement'.map_quotient_of_normal_le_left` を追加する
- [x] `lake build OddOrder.Mathlib.Subgroup` を通す

## 完了条件

`OddOrder.Mathlib.Subgroup` が build でき、BG/Peterfalvi S-file に触らず public shared-infra API が利用可能になる。

## 参照

- `OddOrder/Mathlib/Subgroup.lean`
- `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean`
- `OddOrder/BG/Ch1_Preliminary/S03_FrobeniusActions.lean`
