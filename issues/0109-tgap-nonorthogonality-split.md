---
id: 109
slug: tgap-nonorthogonality-split
title: "TGapNonorthogonality.lean 1500行超 — 凍結境界で prefix-split"
created: 2026-07-12
---

# TGapNonorthogonality.lean 1500行超 — 凍結境界で prefix-split

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景

size watch (merge_monitor.md step 4、2026-07-12 tick 10) で検出: lane c の active frontier
`OddOrder/Peterfalvi/S16_NonExistenceG/TGapNonorthogonality.lean` が **1553 行** (>1500)。
PF 3.3 omega-grid exhaustion 系と (11.8) eta rigidity/residual classifier 系の 2 クラスタが同居。

## やること

- [ ] c の frontier と衝突しない**凍結境界** (先頭の PF 3.3 abstract omega grid クラスタが自然候補)
      で flat prefix-split (先頭クラスタ → 新 sibling leaf、元 file が import、module 名不変)。
- [ ] 実施 owner = hub (c が当該クラスタで idle な tick に実施)。c が自主分割してもよい
      (新主結果番号 = 新 leaf のデフォルト運用)。

## 完了条件

TGapNonorthogonality.lean ≤ ~1500 行、build green 維持、c の active work 非破壊。
