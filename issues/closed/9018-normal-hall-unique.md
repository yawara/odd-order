---
id: 9018
slug: normal-hall-unique
title: "claim: Isaacs Ch03 normal Hall uniqueness shared API (lane d)"
created: 2026-07-06
---

# claim: Isaacs Ch03 normal Hall uniqueness shared API (lane d)

## 背景

Lane d は 2026-07-06 hub 方針上、Peterfalvi/BG S-file へ直接入らず、
open-9000 scan 後の genuine shared-infra のみ claim できる。

`OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean` には
`eq_of_isHall_of_normal` として「有限可解群で normal `π`-Hall subgroup は任意の
`π`-Hall subgroup と一致する」局所補題がある。証明は Isaacs Ch03 の `hall_C`
から直ちに出るため、共有 API として `OddOrder.Isaacs.Ch03` 側へ置くのが自然。
これにより BG/Peterfalvi 側の downstream が BG §14 の局所名に依存せず、
Hall theory の上流 lemma を cite できる。

## やること

- [x] `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean` の `hall_C` 直後に
      `IsHallSubgroup.eq_of_normal` を追加する。
- [x] `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` を通す。

## 完了条件

- 上記補題が sorry-free で追加され、該当 leaf build が green。
- BG/Peterfalvi S-file は本 issue では編集しない。

## 完了メモ

2026-07-06: `IsHallSubgroup.eq_of_normal` を追加し、
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` が成功。BG/Peterfalvi S-file は未編集。

## 参照

- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`: `hall_C`
- `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean`: 局所版
  `eq_of_isHall_of_normal`
- `notes/meta/merge_monitor.md`: lane d shared-infra hygiene / claim-before-build 方針
