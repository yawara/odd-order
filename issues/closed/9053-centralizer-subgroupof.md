---
id: 9053
slug: centralizer-subgroupof
title: "Identify centralizers inside subgroupOf with ambient centralizers"
created: 2026-07-07
---

# Identify centralizers inside subgroupOf with ambient centralizers

## 背景

BG §3.8 の局所補題 `centralizer_subgroupOf` は、subgroup `S` 内の set `T` の
centralizer が、ambient group 側で `S.subtype '' T` を centralize する subgroup の
`subgroupOf S` と一致することを使っている。これは BG 固有でなく `Subgroup` の
汎用 centralizer transport API なので `OddOrder.Mathlib.Subgroup` へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `Subgroup.centralizer_subgroupOf` を追加する
- [x] `lake build OddOrder.Mathlib.Subgroup` を通す

## 完了条件

- `OddOrder/Mathlib/Subgroup.lean` に汎用 theorem が sorry-free で追加されている
- `lake build OddOrder.Mathlib.Subgroup` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Mathlib/Subgroup.lean`
