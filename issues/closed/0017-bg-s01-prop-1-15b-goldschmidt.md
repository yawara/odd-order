---
id: 17
slug: bg-s01-prop-1-15b-goldschmidt
title: "BG §1 Prop 1.15(b) Goldschmidt centralizer p-prime core を形式化する"
created: 2026-05-25
---

# BG §1 Prop 1.15(b) Goldschmidt centralizer p-prime core を形式化する

## 背景

BG Prop 1.15(a) は `hall_higman_solvable_specialization` として完了済み。
残る Prop 1.15(b) は Goldschmidt 部分で、可解群 `G` と p-subgroup `R` について
`O_{p'}(C_G(R)) ⊆ O_{p'}(G)` を主張する。

notes では Lemma 1.14 と Prop 1.10 を組み合わせる証明ルートが記録されているため、
issue 0014 の Prop 1.10 が依存になる。

## やること

- [ ] BG Prop 1.15(b) の正確な statement を mmd で確認する。
- [ ] `O_{p'}` / centralizer / p-subgroup の現行 API で statement を立てる。
- [ ] Lemma 1.14 の quotient Sylow lift と Prop 1.10 を使う証明ルートを試す。
- [ ] 必要なら Goldschmidt 原典ではなく Isaacs/既存補題で代替できるかを notes に記録する。

## 完了条件

- BG Prop 1.15(b) が sorry-free。
- `notes/bg/s01_solvable.md` の Goldschmidt TODO が更新される。
- `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- issue 0014
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `references/bg/local-analysis.mmd` L490-L499 付近

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

Prop 1.15(b) 両形式 sorry-free: `oPiPrimeCore_centralizer_eq_bot_of_oPiPrimeCore_eq_bot` (S01_Solvable.lean:2685) +
`oPiPrimeCore_centralizer_le_oPiPrimeCore` (:2730)。ファイル全体も実 sorry 0 (検証 2026-07-02)。
