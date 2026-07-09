---
id: 85
slug: s07-coherence-split
title: "S07_Coherence.lean 分割 (6538 行 >1500) — §7 coherence topic 別 leaf へ"
created: 2026-06-29
---

# S07_Coherence.lean 分割 (6538 行 >1500) — §7 coherence topic 別 leaf へ

## 背景

merge-monitor のサイズ watch (粒度規約 1,500 行) で検出 (2026-06-29, 当時 6538 行)。
`OddOrder/Peterfalvi/S07_Coherence.lean` は §7 coherence の中核 leaf で、**lane b の
active 領域** (coherence infra、正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)
ゆえ、分割は凍結境界待ち。

行数 refresh (2026-07-02 hub 全体レビュー): **6540 行**。

なお issue 1015 (hzeta0nu ⊥1_G) の解消により、**`IsCoherent` field 変更 (shared-structure
signature 変更) の懸念は消滅** — 分割時に IsCoherent 構造体の signature を動かす必要は
無く、純粋な prefix-split / topic-split として扱える。

## やること

- [ ] **trigger**: lane b の **(6.5.c) producer cluster が凍結**したら実施。
- [ ] **実施 owner = hub** (lane b の frontier と衝突しない凍結境界で prefix-split、
      または §7 coherence の topic 別 leaf へ分割。前方参照は構文上不可ゆえ任意の
      宣言境界で安全)。
- [ ] 新 leaf を `OddOrder.lean` の root closure に登録。
- [ ] full build green + AxiomsCheck OK + 実 sorry 不変 (comment-strip で数える) を確認。

## 完了条件

`S07_Coherence.lean` (と派生 leaf) が概ね 1,500 行以下 (または topic-coherent な複数
leaf + hub)、full build + AxiomsCheck green 維持。

## 参照

- 規約: CLAUDE.md「分割の owner と trigger」/ `notes/meta/merge_monitor.md` サイズ watch
- 関連: issue 1015 (解消済 — IsCoherent field 変更懸念の消滅), 0084 (S14_MaximalI split)
- lane 配分正本: `notes/meta/ft_lane_reallocation_2026_06_28.md` (2026-07-02, 3 レーン a/b/c)

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - CoherenceUnion.lean (1706 行)
  - DifferenceImage.lean (1195 行)
  - FamilyBundleDade.lean (1611 行)
  - NormInequalities.lean (1070 行)
  - PsiDecomposition.lean (1249 行)
