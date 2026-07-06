---
id: 9021
slug: hall-map-subtype-index
title: "claim: Isaacs Ch03 Hall subgroup map-subtype index transfer API (lane d)"
created: 2026-07-06
---

# claim: Isaacs Ch03 Hall subgroup map-subtype index transfer API (lane d)

## 背景

Lane d は 2026-07-06 hub 方針上、Peterfalvi/BG S-file へ直接入らず、
open-9000 scan 後の genuine shared-infra のみ claim できる。

`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` には
`isHallSubgroup_map_subtype_of_index_no_pi` として、`H` 内の `π`-Hall subgroup
を ambient `G` へ押し戻す Hall-index transfer が private に置かれている。
これは BG Prop 1.5(b) に限らず Hall theory の基本 API なので Ch03 へ共有化する。

## やること

- [x] `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean` に
      `IsHallSubgroup.map_subtype_of_index_no_pi` を追加する。
- [x] `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` を通す。

## 完了条件

- 上記補題が sorry-free で追加され、該当 leaf build が green。
- BG/Peterfalvi S-file は本 issue では編集しない。

## 完了メモ

2026-07-06: `IsHallSubgroup.map_subtype_of_index_no_pi` を追加し、
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` が成功。BG/Peterfalvi S-file は未編集。

## 参照

- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`: `IsHallSubgroup`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private 版
  `isHallSubgroup_map_subtype_of_index_no_pi`
- `notes/meta/merge_monitor.md`: lane d shared-infra hygiene / claim-before-build 方針
