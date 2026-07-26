---
id: 9207
slug: central-commutator-power
title: "中心的交換子の冪等式を Isaacs から使える上流 leaf に置く (BG に重複)"
created: 2026-07-26
---

# 中心的交換子の冪等式を Isaacs から使える上流 leaf に置く (BG に重複)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

`⁅x, y⁆ ∈ Z(G)` のときの `⁅x^m, y^n⁆ = ⁅x,y⁆^(mn)` (双線形性) は **repo に既に存在する**が、
場所が `OddOrder/BG/Ch1_Preliminary/S04_CommutatorCollection.lean`
(`BG.Ch1.S04.commutatorElement_pow_{left,right}_of_central`, BG Lemma 4.2(a)) で、
**BG は Isaacs の下流**ゆえ Isaacs 側から import できない。

Isaacs Problem 5A.8(b) (`⁅Γ_A, Γ_B⁆ = ⊥`) がこの恒等式を必要とするため、
**両者の上流**に共有 leaf を新設した。

## 成果 (2026-07-26)

`OddOrder/GroupTheory/CentralCommutatorPower.lean` (`OddOrder.lean` 配線済):

* `commutatorElement_pow_left_of_central` — `⁅x^n, y⁆ = ⁅x,y⁆^n`
* `commutatorElement_pow_right_of_central` — `⁅x, y^n⁆ = ⁅x,y⁆^n`
* `commutatorElement_pow_pow_of_central` — `⁅x^m, y^n⁆ = ⁅x,y⁆^(m*n)`

仮説は**当該の 1 つの交換子が中心的**であることのみ (群全体の類 2 は不要)。

## hub への申し送り (重複解消)

以下は本 leaf へ redirect できる (いずれも本 leaf の特殊化 / 同一命題):

1. `OddOrder/BG/Ch1_Preliminary/S04_CommutatorCollection.lean` の
   `commutatorElement_pow_left_of_central` / `commutatorElement_pow_right_of_central`
   — 同一命題。BG 側を削除して本 leaf を import するのが素直。
2. `OddOrder/BG/AppE_CentralizerDecomposition.lean:608`
   `commutatorElement_pow_pow_of_central` — 同一命題。
3. `OddOrder/Isaacs/Ch04_Commutators/Problems.lean:505`
   `commutatorElement_pow_left_of_commutator_le_center` — 本補題の**類 2 特殊化**。
   消費点があるので残してよいが、本補題から 1 行で導出できる。

⚠ いずれも **A レーンの territory 外のファイルを編集する**ので、実施は hub 判断。
