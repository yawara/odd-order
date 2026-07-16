---
id: 3005
slug: consolidate-normal-map-subtype-char
title: "normal_map_subtype_of_characteristic を OddOrder/GroupTheory へ統合"
created: 2026-07-17
---

# normal_map_subtype_of_characteristic を OddOrder/GroupTheory へ統合

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 内容

`normal_map_subtype_of_characteristic` (N ⊴ W の characteristic 部分群 L の
`L.map N.subtype` が W で正規) が 2 箇所に重複:

1. `OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadicalGlobal.lean:409` (public, 原本)
2. `OddOrder/Isaacs/Ch10_MoreTransfer/TransferIndexPrime.lean` の
   `normal_map_subtype_of_char` (private copy — Isaacs → BG は layering 上
   import 不可のため)

## 対処 (hub)

- `OddOrder/GroupTheory/` の適切な leaf (新設可) に public 版を置く
- BG 側は shared 版の cite に置換、Isaacs 側 private copy を削除
- 両ファイルの leaf build + full build 確認

## トリガー

hub の次回 dedup/consolidation パス、または本 lemma の第 3 の消費者出現時。
