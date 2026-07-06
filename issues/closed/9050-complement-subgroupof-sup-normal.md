---
id: 9050
slug: complement-subgroupof-sup-normal
title: "Complement transport to a normal subgroup supremum"
created: 2026-07-07
---

# Complement transport to a normal subgroup supremum

## 背景

BG §3.8 の局所補題 `isComplement'_subgroupOf_sup_of_normal` は、
`A ⊴ G` と `Disjoint A B` から、`A ⊔ B` 内の `A.subgroupOf` と
`B.subgroupOf` が complement になることを使っている。これは BG 固有でなく
`Subgroup` の汎用 complement transport API なので `OddOrder.Mathlib.Subgroup` へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `Subgroup.isComplement'_subgroupOf_sup_of_normal` を追加する
- [x] `lake build OddOrder.Mathlib.Subgroup` を通す

## 完了条件

- `OddOrder/Mathlib/Subgroup.lean` に汎用 theorem が sorry-free で追加されている
- `lake build OddOrder.Mathlib.Subgroup` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Mathlib/Subgroup.lean`
