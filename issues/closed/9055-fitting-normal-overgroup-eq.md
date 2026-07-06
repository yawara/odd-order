---
id: 9055
slug: fitting-normal-overgroup-eq
title: "Identify Fitting of a normal overgroup containing the Fitting subgroup"
created: 2026-07-07
---

# Identify Fitting of a normal overgroup containing the Fitting subgroup

## 背景

BG §3.8 の局所補題 `fitting_map_eq_of_normal_of_fitting_le` は、
`M ⊴ G` かつ `F(G) ≤ M` のとき、`F(M)` を `G` へ押し出すと `F(G)` そのものに
なることを使っている。これは Ch01 の Fitting API として汎用なので
`OddOrder.Isaacs.Ch01` へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `OddOrder.Isaacs.Ch01.fitting_map_eq_of_normal_of_fitting_le` を追加する
- [x] `lake build OddOrder.Isaacs.Ch01_Sylow.Main` を通す

## 完了条件

- `OddOrder/Isaacs/Ch01_Sylow/Main.lean` に theorem が sorry-free で追加されている
- `lake build OddOrder.Isaacs.Ch01_Sylow.Main` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Isaacs/Ch01_Sylow/Main.lean`
