---
id: 9022
slug: pi-group-map-quotient
title: "claim: Isaacs Ch03 pi-subgroup quotient map API (lane d)"
created: 2026-07-06
---

# claim: Isaacs Ch03 pi-subgroup quotient map API (lane d)

## 背景

Lane d は 2026-07-06 hub 方針上、Peterfalvi/BG S-file へ直接入らず、
open-9000 scan 後の genuine shared-infra のみ claim できる。

`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` には `isPiGroup_map_mk'`
として、π-subgroup 性が quotient map で保たれる補題が private に置かれている。
これは Ch03 の `Subgroup.IsPiGroup` 基本 API なので Ch03 に共有化する。

## やること

- [x] `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean` に
      `Subgroup.IsPiGroup.map_quotient` を追加する。
- [x] `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` を通す。

## 完了条件

- 上記補題が sorry-free で追加され、該当 leaf build が green。
- BG/Peterfalvi S-file は本 issue では編集しない。

## 完了メモ

2026-07-06: `Subgroup.IsPiGroup.map_quotient` を追加し、
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` が成功。BG/Peterfalvi S-file は未編集。

## 参照

- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`: `Subgroup.IsPiGroup`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private 版 `isPiGroup_map_mk'`
- `notes/meta/merge_monitor.md`: lane d shared-infra hygiene / claim-before-build 方針
