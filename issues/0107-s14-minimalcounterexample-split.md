---
id: 107
slug: s14-minimalcounterexample-split
title: "S14_MaximalI/MinimalCounterexample.lean 分割 (1563 行 > 1500 閾値)"
created: 2026-07-10
---

# S14_MaximalI/MinimalCounterexample.lean 分割 (1563 行 > 1500 閾値)

## 背景

- 2026-07-10 監視 tick の lane b 合流 (issue 2038、Pf (12.15)/(12.16 hA)) で
  `OddOrder/Peterfalvi/S14_MaximalI/MinimalCounterexample.lean` が 1421→**1563 行**となり、
  サイズ watch の 1,500 行 flag 閾値を超過 (repo hard 上限 = 2000 行、CLAUDE.md「ファイル粒度」)。
- 本 file は lane b の **active frontier** (2038 の hB/hC norm 配線が進行中、
  b commit ad627854 参照) ゆえ、分割は frontier と衝突しない**凍結境界での prefix-split** に限る。
- 分割実施 owner = **hub** (merge_monitor.md step 4)。S14_MaximalI は既に directory 化済み
  (issues/closed/0084) なので、追加 leaf を切り出して hub `S14_MaximalI.lean` (pure re-export,
  現 13 行) に import 行を足すだけで下流不変。

## やること

- [ ] hub: 2038 の hB/hC 配線が一段落したタイミング (または 2000 行に接近したら即時) で、
      冒頭の凍結クラスタ (先頭 K 宣言、b の現 frontier が参照しない部分) を新 sibling leaf
      (記述的英語名、例 `WetKernel.lean` / `RhoMBounds.lean` — 実際の内容で命名) へ prefix-split
- [ ] `S14_MaximalI.lean` hub に import 行を追加、build green + AxiomsCheck OK を確認
- [ ] b へ notes/issue で通知 (次回 main sync で取り込み)

## 完了条件

MinimalCounterexample.lean が 1,500 行未満に戻り、full build green + AxiomsCheck OK。

## 参照

- issues/closed/0084-s14-maximali-split.md (S14_MaximalI の directory 化)
- issues/2038-bfrontier-shift-bg-done.md (b の active frontier)
- notes/meta/merge_monitor.md step 4 (サイズ watch) / CLAUDE.md「ファイル粒度」
