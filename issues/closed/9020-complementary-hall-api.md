---
id: 9020
slug: complementary-hall-api
title: "claim: Isaacs Ch03 complementary Hall subgroup API (lane d)"
created: 2026-07-06
---

# claim: Isaacs Ch03 complementary Hall subgroup API (lane d)

## 背景

Lane d は 2026-07-06 hub 方針上、Peterfalvi/BG S-file へ直接入らず、
open-9000 scan 後の genuine shared-infra のみ claim できる。

`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean` には complementary Hall subgroup
の card/index/product/complement 補題が private または BG-local に置かれている。
証明は Isaacs Ch03 の `IsHallSubgroup` と π/π' coprime arithmetic だけで閉じるため、
Hall theory の shared API として Ch03 に置く。

## やること

- [x] `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean` に complementary Hall API
      (`card_coprime_of_compl`, `index_coprime_of_compl`, `card_mul_of_compl`,
      `isComplement_of_compl`) を追加する。
- [x] `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` を通す。

## 完了条件

- 上記補題群が sorry-free で追加され、該当 leaf build が green。
- BG/Peterfalvi S-file は本 issue では編集しない。

## 完了メモ

2026-07-06: complementary Hall API 4 補題を追加し、
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` が成功。BG/Peterfalvi S-file は未編集。

## 参照

- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`: `IsHallSubgroup`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private 版
  `hall_compl_card_coprime`, `hall_compl_index_coprime`, `hall_compl_card_mul`
  および BG-local `hall_compl_isComplement`
- `notes/meta/merge_monitor.md`: lane d shared-infra hygiene / claim-before-build 方針
