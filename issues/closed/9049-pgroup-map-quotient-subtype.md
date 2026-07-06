---
id: 9049
slug: pgroup-map-quotient-subtype
title: "P-group transport from subgroup quotient to ambient quotient image"
created: 2026-07-07
---

# P-group transport from subgroup quotient to ambient quotient image

## 背景

BG §3.8 の局所補題
`isPGroup_map_mk'_subtype_of_isPGroup_quotient` は、`K/N` が `p`-group
なら ambient quotient `G ⧸ N.map K.subtype` 内の `K` の像も `p`-group
であることを使っている。これは BG 固有でなく quotient/subtype の汎用
transport API なので `OddOrder.Mathlib.Subgroup` へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `Subgroup.isPGroup_map_quotient_subtype_of_isPGroup_quotient` を追加する
- [x] `lake build OddOrder.Mathlib.Subgroup` を通す

## 完了条件

- `OddOrder/Mathlib/Subgroup.lean` に汎用 theorem が sorry-free で追加されている
- `lake build OddOrder.Mathlib.Subgroup` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Mathlib/Subgroup.lean`
