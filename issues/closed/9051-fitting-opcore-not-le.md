---
id: 9051
slug: fitting-opcore-not-le
title: "Extract a noncontained p-core from a noncontained Fitting subgroup"
created: 2026-07-07
---

# Extract a noncontained p-core from a noncontained Fitting subgroup

## 背景

BG §3.8 の局所補題 `exists_opCore_not_le_of_fitting_not_le` は、
`F(G) = ⨆ p, O_p(G)` から `F(G) ≤ S` の否定をある prime core
`O_p(G) ≤ S` の否定へ落とす。これは Fitting/opCore の基本 API なので
`OddOrder.Isaacs.Ch01` へ移す。

## やること

- [x] open 9000 issue と allowed area の既存 API を確認する
- [x] `OddOrder.Isaacs.Ch01.exists_opCore_not_le_of_fitting_not_le` を追加する
- [x] `lake build OddOrder.Isaacs.Ch01_Sylow.Main` を通す

## 完了条件

- `OddOrder/Isaacs/Ch01_Sylow/Main.lean` に theorem が sorry-free で追加されている
- `lake build OddOrder.Isaacs.Ch01_Sylow.Main` が成功する

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`
- `OddOrder/Isaacs/Ch01_Sylow/Main.lean`
