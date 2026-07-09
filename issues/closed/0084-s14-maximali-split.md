---
id: 84
slug: s14-maximali-split
title: "S14_MaximalI.lean が 1500 行超 (1538) — prefix-split 候補"
created: 2026-06-26
---

# S14_MaximalI.lean が 1500 行超 (1538) — prefix-split 候補

## 背景

merge-monitor のサイズ watch (粒度規約 1,500 行) で検出 (2026-06-26, 当時 1538 行)。
`OddOrder/Peterfalvi/S14_MaximalI.lean` は **lane b の active frontier**
(S14_MaximalI + coherence infra + carve-outs 0090/0096、正本
`notes/meta/ft_lane_reallocation_2026_06_28.md`) ゆえ、分割は凍結境界待ち。

行数 refresh (2026-07-02 hub 全体レビュー): **5882 行**。

## やること

- [ ] **trigger**: lane b の §12 tower が凍結したら (= S14_MaximalI への追記が
      一段落したら)、凍結済み先頭クラスタを上流 leaf へ prefix-split する。
- [ ] **実施 owner = hub** (lane b の frontier と衝突しない凍結境界で。前方参照は
      構文上不可ゆえ任意の宣言境界で安全)。
- [ ] 新 leaf を `OddOrder.lean` の root closure に登録。
- [ ] full build green + AxiomsCheck OK + 実 sorry 不変 (comment-strip で数える) を確認。

## 完了条件

`S14_MaximalI.lean` (と派生 leaf) が概ね 1,500 行以下、full build + AxiomsCheck green 維持。

## 参照

- 規約: CLAUDE.md「分割の owner と trigger」/ `notes/meta/merge_monitor.md` サイズ watch
- 同種 deferred split issue: 0085 (S07_Coherence), 0077 (S11), 0094 (S15_SAndT_Setup)
- lane 配分正本: `notes/meta/ft_lane_reallocation_2026_06_28.md` (2026-07-02, 3 レーン a/b/c)

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - DadeContradiction.lean (1665 行)
  - FrobeniusStructure.lean (1690 行)
  - Hypothesis.lean (753 行)
  - MinimalCounterexample.lean (2529 行)
  - RhoConstancy.lean (1916 行)
