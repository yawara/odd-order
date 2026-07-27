---
id: 9211
slug: sl2-card-drop-charp
title: "SL(2,F) の位数公式から CharP F 2 仮説を外す (7A.2 で必要)"
created: 2026-07-27
---

# SL(2,F) の位数公式から CharP F 2 仮説を外す (7A.2 で必要)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 実施 (2026-07-27, lane a)

`OddOrder/GroupTheory/SpecificGroups/ProjectiveSpecialLinear/RootGroupSylow.lean` の
file-level `variable {F} [Field F] [Finite F] [CharP F 2]` から `[CharP F 2]` を外し、
**char 2 が本当に必要な結果だけ**を `section CharTwo` (`variable [CharP F 2]`) に閉じた:

* 一般化された (char 任意になった): `card_specialLinearGroup_mul_units` (private) /
  **`natCard_specialLinearGroup_fin_two`** (`|SL(2,F)| = q(q-1)(q+1)`)。
* char 2 のまま (本質的に必要): `center_specialLinearGroup_fin_two_eq_bot`
  (char ≠ 2 では中心 = {±I} ≠ ⊥ なので**当然**) / `natCard_projectiveSpecialLinearGroup_fin_two` /
  `rootSubgroup_index` / `rootSubgroup_index_odd`。

consumer は 2 箇所のみで両方安全: `AxiomsCheck.lean:405` (名前参照のみ) と
`NonsplitTorus.lean:230` (素の `rw`、明示 instance 引数なし)。leaf build green。

⟹ 動機: Isaacs 7A.2 が `|SL(2,3)| = 24` (char 3) を要求する。CLAUDE.md の
「特殊化債務はできる限り一般化する」に該当。
