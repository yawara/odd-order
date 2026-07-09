---
id: 76
slug: s12-maximaliiiivv-split
title: "S12_MaximalIII_IV_V 分割 (3508 行, >1500)"
created: 2026-06-22
---

# S12_MaximalIII_IV_V 分割 (3508 行, >1500)

## 背景

`OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean` が 2026-06-22 tick (merge `0256fe25`, Pf (10.5)
σ-isometry bridge) で **3508 行**に到達。merge_monitor.md「サイズ watch」規約 (1,500 行超への追記は
分割 issue 起票) に従い起票。owner = **hub** (lane の frontier と衝突しない凍結境界で prefix-split)。

現所有 = lane-b (Pf §12/§13 char-grid)。active frontier = (10.5)/(10.6)/(10.7)/(10.8) char-grid。

## やること

- [x] active frontier と衝突しない**凍結済み prefix** を特定 — 境界 = 旧 :6137
      (`/-! ## (10.7)--(10.8)` セクション見出し直前; lane a の active 11.8 cluster + sorried 4 本は
      全て leaf 側、lane a worktree は clean・全 merge 済の窓で実施)
- [x] prefix を上流 leaf `S12_MaximalIII_IV_V_Core.lean` (6146 行, 凍結) に prefix-split。
      private 1 本 (`inner_left_eq_zero_of_inner_sub_eq_zero`, leaf から 7 参照) を public 化
      (CLAUDE.md「private をファイル跨ぎで使わない」)
- [x] 残り (leaf 2768 行 = (10.7)/(10.8)/(10.10) + 11.8 cluster) が Core を import、
      下流 (S13) は不変
- [x] root closure: leaf が Core を import するため `OddOrder.lean` 追記不要 (merge_monitor 3b)
- [x] full build green + AxiomsCheck OK 確認 (2026-07-02, 分割 commit 参照)

## 状態 (2026-07-02 hub, phase 1 完了 — open 維持)

8870 行 → **Core 6146 (凍結) + leaf 2768 (active)**。leaf は 1500 行超のまま (11.8 cluster が
active ゆえ現時点でこれ以上削れない)。残 phase:
- [ ] 11.8 cluster が凍結したら leaf を再 prefix-split (~1500 以下へ)
- [ ] Core (6146 行) の topic 分割 (FiniteInduce+Hypothesis / (10.5)–(10.6) chains) は
      elaboration 時間が問題化したら実施 (凍結ファイルゆえ再 build は稀)

## 完了条件

S12_MaximalIII_IV_V.lean が ~1500 行以下 (または topic-coherent な複数 leaf + hub) になり、
full build (3881 jobs) green を維持。lane-b の frontier 編集と衝突しない凍結境界で実施済み。

## 参照

- merge_monitor.md「各イテレーションの手順」step 4 (サイズ watch) + 「分割の owner と trigger」
- 既存 split 前例: issue 0069 (S14_TypePCounting) / 0071 (S15_MF) / 0075 (S15_SAndT)
- merge `0256fe25` (3508 行到達時点)
- [[feedback-record-deferred-hub-tasks-as-issues]]

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - CharacterParameters.lean (1976 行)
  - DadeCalculations.lean (3561 行)
  - Hypothesis.lean (1205 行)
