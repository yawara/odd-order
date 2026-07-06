---
id: 9054
slug: fitting-subgroupof-map-subtype
title: "Transport Fitting subgroups through subgroupOf and subtype maps"
created: 2026-07-07
---

# Transport Fitting subgroups through subgroupOf and subtype maps

## 背景

BG §3.8 の局所補題 `fitting_subgroupOf_map_subtype_eq` と
`fitting_map_map_subtype` は、Fitting subgroup を `subgroupOf` や subtype image を
通して比較する transport API。どちらも Ch01 の `fitting_map_mulEquiv` から出る
汎用 Fitting API なので `OddOrder.Isaacs.Ch01` へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `OddOrder.Isaacs.Ch01.fitting_subgroupOf_map_subtype_eq` を追加する
- [x] `OddOrder.Isaacs.Ch01.fitting_map_map_subtype` を追加する
- [x] `lake build OddOrder.Isaacs.Ch01_Sylow.Main` を通す

## 完了条件

- `OddOrder/Isaacs/Ch01_Sylow/Main.lean` に 2 theorem が sorry-free で追加されている
- `lake build OddOrder.Isaacs.Ch01_Sylow.Main` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Isaacs/Ch01_Sylow/Main.lean`
