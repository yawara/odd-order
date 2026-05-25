---
id: 11
slug: bg-s01-prop-1-2-1-4-fitting
title: "BG §1 Prop 1.2-1.4 Fitting/chief-factor block を形式化する"
created: 2026-05-25
---

# BG §1 Prop 1.2-1.4 Fitting/chief-factor block を形式化する

## 背景

BG §1A の Prop 1.2-1.4 は Fitting subgroup と chief factor centralizer を結ぶ block。
`notes/bg/s01_solvable.md` では Prop 1.2 が実測 6 回引用、Prop 1.3-1.4 も後続節で使われる
中頻度依存として整理されている。

mathlib/現行 OddOrder には chief factor / composition series 周辺の shared API がまだ薄いので、
必要なら `OddOrder.GroupTheory` 配下に小さく切り出す。

## やること

- [x] BG Prop 1.2 の正確な statement を `references/bg/local-analysis.mmd` で確認する。
- [x] chief factor / centralizer / Fitting の既存 API を棚卸しする。
- [ ] Prop 1.2 を実装するか、必要な shared module の最小スコープを決める。
- [x] Prop 1.3 `C_G(F(G)) ⊆ F(G)` を実装する。
- [ ] Prop 1.4 coprime automorphism faithful-on-Fitting を実装する。

## 進捗

2026-05-25 bg-s01:

- Prop 1.2 本文確認済み (`local-analysis.mmd` L360-L378)。mathlib には抽象
  `Order.JordanHolder.CompositionSeries` はあるが、BG Prop 1.2 に必要な群の
  chief factor centralizer API は未整備。
- Prop 1.3 は `centralizer_fitting_le_fitting` として sorry-free 実装済み。
  Prop 1.2 経由ではなく、`C_G(F(G))` 内の最小正規反例 + Fitting 最大性で証明。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` と
  `lake build OddOrder.AxiomsCheck` は成功。
- Prop 1.2 は shared `ChiefSeries`/chief-factor centralizer module の設計が必要。
- Prop 1.4 は Prop 1.3 を使える状態になったが、semidirect product と Hall σ/core
  の形式化が残る。

## 完了条件

- BG Prop 1.2-1.4 の実装方針が `notes/bg/s01_solvable.md` と Lean コメントに反映される。
- 実装する theorem は sorry-free。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `notes/bg/s01_solvable.md`
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `references/bg/local-analysis.mmd` L360-L398 付近
