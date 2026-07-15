---
id: 110
slug: s13-corestructure-split
title: "S13_CoreStructure 1671 行 → 分割 (a の (10.8) 完了後)"
created: 2026-07-12
---

# S13_CoreStructure 1671 行 → 分割 (a の (10.8) 完了後)

## 背景

2026-07-12 監視 tick で `OddOrder/Peterfalvi/S13_CoreStructure.lean` が **1671 行** に到達
(merge 7e6e6408 = 1025 foundational refactor で (11.4)-(11.7) parametrize)。CLAUDE.md 粒度規約の
**1500 行 watch 閾値**超過 (2000 行 hard 上限は未達ゆえ緊急でない)。

⚠ **本 file は lane a の active frontier**: a は 9087 RULING (別 issue) の (10.8) knot 閉包で
(11.4)-(11.7) chain をさらに触る予定。**active file の分割は a の作業と衝突する**ため、
分割は **a の (10.8) 作業が settle した後**に hub が凍結境界で実施する (mathlib 準拠 = dir 化
第一候補: `S13_CoreStructure/` へ topic leaf 分割、または prefix-split)。

## やること

- [ ] a の (10.8) knot 閉包 (issue 1025/9087) が landing し S13_CoreStructure が凍結したら分割着手
- [ ] 分割方式決定 (dir 化 topic-split 優先; module 名不変で下流 import 無変更)
- [ ] hub が凍結境界で実施 (a の frontier と非衝突の宣言境界)

## 完了条件

- S13_CoreStructure.lean (+ 分割後 leaf 群) が各 2000 行未満・理想 1500 未満
- `lake build OddOrder` green・下流 import 無変更

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-09 節: 1500 watch / 2000 hard / dir 化第一)
- issue 1025 (foundational (11.4)-(11.7) parametrize)、9087 (lane A direction = (10.8) 閉包)
- merge 7e6e6408 (1671 行到達)

## ✅ 完了 (2026-07-15)

- issue #1025 / #9087 の完了記録を再監査し、旧 active frontier の凍結条件成立を確認。
- (11.6) の kernel-bound cluster を `S13_CoreStructure/KernelBounds.lean` (766 行) へ切り出した。
- 親 `S13_CoreStructure.lean` は centralization / (11.7) / coherence cluster を保持して 882 行。
- 分割前後の宣言名 multiset は完全一致し、機械移動により signature と下流 module 名を保存。
- 当該 cluster の実 `sorry` は 0 → 0、`OddOrder.lean` の root closure も維持。
- focused build 4067 jobs、`lake build OddOrder OddOrder.AxiomsCheck` 4244 jobs 完走・AxiomsCheck OK。
