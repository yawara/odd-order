---
id: 9052
slug: commutator-fitting-subgroupof-sup
title: "Transport commutator-to-Fitting bounds out of subgroup suprema"
created: 2026-07-07
---

# Transport commutator-to-Fitting bounds out of subgroup suprema

## 背景

BG §3.8 の局所補題 `commutator_le_fitting_of_subgroupOf_sup` は、
`A` と `B` を `A ⊔ B` 内へ restriction した sub-configuration で
`⁅A, B⁆ ≤ F(A)` 型の結論が得られたとき、それを ambient group へ
押し戻す transport API。commutator の map と Ch01 の Fitting isomorphism transport に
よる汎用補題なので `OddOrder.Isaacs.Ch04` へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `OddOrder.Isaacs.Ch04.commutator_le_fitting_of_subgroupOf_sup` を追加する
- [x] `lake build OddOrder.Isaacs.Ch04_Commutators.Main` を通す

## 完了条件

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に theorem が sorry-free で追加されている
- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
