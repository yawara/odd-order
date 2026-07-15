---
id: 112
slug: s15-hypothesisbasics-split
title: "S15_SAndT_Setup/HypothesisBasics 1689 行 → 分割 (b の 1017 settle 後)"
created: 2026-07-13
---

# S15_SAndT_Setup/HypothesisBasics 1689 行 → 分割 (b の 1017 settle 後)

## 背景

2026-07-13 監視 tick で `OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean` が **1689 行** に到達
(merge 26bf4190 = 1017 (9.11) S-instance caseB build-out + DegreesFirstSplit からの 7 theorem relocation)。
CLAUDE.md 粒度規約の **1500 行 watch 閾値**超過 (2000 行 hard 上限は未達ゆえ緊急でない)。

⚠ **本 file は lane b の active frontier**: b は 1017 (9.11 S-instance) campaign を HypothesisBasics で
継続中 (`sSet_coherent_dade_caseB` / `sSet_caseB_memberRFamily` の残 residual、caseA lift 等)。
**active file の分割は b の作業と衝突する**ため、分割は **b の 1017 campaign が settle した後**に hub が
凍結境界で実施 (mathlib 準拠 = topic leaf 切出し or prefix-split、module 名不変で下流 import 無変更)。

## やること

- [ ] b の 1017 (9.11 S-instance) campaign が landing し HypothesisBasics が凍結したら着手
- [ ] 分割方式決定 (S-instance coherence 系 / Dade-map 系 / relocation 済 group-theory helper を
      topic leaf へ切出し; 汎用 helper (subgroup_le_of_normal_coprime_index 等) は shared infra 候補も検討)
- [ ] hub が凍結境界で実施 (b の frontier と非衝突の宣言境界)

## 完了条件

- HypothesisBasics.lean (+ 分割後 leaf 群) が各 2000 行未満・理想 1500 未満
- `lake build OddOrder` green・下流 import 無変更

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-09 節: 1500 watch / 2000 hard / dir 化第一)
- 同型 deferred split issue = 0110 (S13_CoreStructure)、0111 (S15_SAndT、closed)
- issue 1017 (b の (9.11) S-instance campaign)、merge 26bf4190 (1689 行到達)

## ✅ CLOSED (hub 裁定 2026-07-15 tick #8): HypothesisBasics 1355行 (<1500), 閾値未満。実施 owner=hub の split 完了確認済。
