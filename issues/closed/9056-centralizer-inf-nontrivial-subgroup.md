---
id: 9056
slug: centralizer-inf-nontrivial-subgroup
title: "Lift singleton centralizer equalities to a nontrivial subgroup"
created: 2026-07-07
---

# Lift singleton centralizer equalities to a nontrivial subgroup

## 背景

BG §3.8 の局所補題 `centralizer_inf_eq_of_le_of_cond2` は、`R₀ ≤ R` かつ
`R₀ ≠ ⊥` のとき、`R` の任意の非単位元の singleton centralizer intersection が
`C_G(R) ⊓ K` と等しいなら、`C_G(R₀) ⊓ K` も同じになることを使っている。
これは BG 固有でなく `Subgroup.centralizer` の汎用 API なので `OddOrder.Mathlib.Subgroup`
へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `Subgroup.centralizer_inf_eq_of_le_of_singleton_inf_eq` を追加する
- [x] `lake build OddOrder.Mathlib.Subgroup` を通す

## 完了条件

- `OddOrder/Mathlib/Subgroup.lean` に汎用 theorem が sorry-free で追加されている
- `lake build OddOrder.Mathlib.Subgroup` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Mathlib/Subgroup.lean`
