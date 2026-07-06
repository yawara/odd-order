---
id: 9019
slug: hall-mulaut-invariance
title: "claim: Isaacs Ch03 Hall subgroup automorphism invariance shared API (lane d)"
created: 2026-07-06
---

# claim: Isaacs Ch03 Hall subgroup automorphism invariance shared API (lane d)

## 背景

Lane d は 2026-07-06 hub 方針上、Peterfalvi/BG S-file へ直接入らず、
open-9000 scan 後の genuine shared-infra のみ claim できる。

`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` には
`isHallSubgroup_mulAut_smul` として「Hall subgroup は ambient automorphism で
Hall のまま」という private 補題がある。これは Isaacs Ch03 の
`IsHallSubgroup` 基本 API として共有するのが自然で、BG/Peterfalvi 側の
future consumer が BG §1 の private theorem を再実装しなくて済む。

## やること

- [x] `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean` に
      `IsHallSubgroup.mulAut_smul` を追加する。
- [x] `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` を通す。

## 完了条件

- 上記補題が sorry-free で追加され、該当 leaf build が green。
- BG/Peterfalvi S-file は本 issue では編集しない。

## 完了メモ

2026-07-06: `IsHallSubgroup.mulAut_smul` を追加し、
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` が成功。BG/Peterfalvi S-file は未編集。

## 参照

- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`: `IsHallSubgroup`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private 版
  `isHallSubgroup_mulAut_smul`
- `notes/meta/merge_monitor.md`: lane d shared-infra hygiene / claim-before-build 方針
