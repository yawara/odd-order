---
id: 10
slug: bg-s01-lem-1-1-full
title: "BG §1 Lemma 1.1 minimal normal の中心化版を完成する"
created: 2026-05-25
---

# BG §1 Lemma 1.1 minimal normal の中心化版を完成する

## 背景

BG Lemma 1.1 の現行実装
`isMinimalNormal_le_fitting_and_isElementaryAbelian` は、minimal normal `M` が elementary
abelian で `M ≤ F(G)` であるところまで完成している。

原文の残りは `M ≤ Z(F(G))`、または同等に `M` が `F(G)` を中心化する部分。コメント上は
「Ch.4 待ち」になっているため、現在の Ch.4 API で閉じられるかを再確認し、足りなければ
必要な中心化補題を追加する。

## やること

- [x] Ch.4 / Ch.1 の現行 API で minimal normal が Fitting を中心化する補題を探す。
- [x] 不足していれば、`M ≤ centralizer (fitting G : Set G)` または `M ≤ Subgroup.center (fitting G)`
      へ繋ぐ補題を追加する。
- [x] BG Lemma 1.1 の full statement を `S01_Solvable.lean` に追加する。
- [x] 既存の「部分」コメントと status 表を更新する。

## 完了メモ

Ch.4 側の `OddOrder.Isaacs.Ch04.le_centralizer_of_isMinimalNormal` が現在利用可能なので、
新しい中心化補題は不要だった。既存の
`isMinimalNormal_le_fitting_and_isElementaryAbelian` を full statement に拡張し、
`M ≤ F(G)` と `M ≤ C_G(F(G))` と elementary abelian 結論を同時に返す形にした。

## 完了条件

- [x] BG Lemma 1.1 の `M ≤ Z(F(G))` までの statement が sorry-free。
- [x] `lake build OddOrder.BG.Ch1_Preliminary.S01_Solvable` が通る。
- [x] `lake build OddOrder.AxiomsCheck` が通る。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch01_Sylow/Main.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
