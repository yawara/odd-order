---
id: 111
slug: s15-sandt-resplit
title: "S15_SAndT 1637 行 → 再分割 (b の (13.19) cascade 完了後)"
created: 2026-07-12
---

# S15_SAndT 1637 行 → 再分割 (b の (13.19) cascade 完了後)

## 背景

2026-07-12 監視 tick で `OddOrder/Peterfalvi/S15_SAndT.lean` が **1637 行** に到達
(merge afc368a0 = 2038 (13.19.c) dichotomy 組立)。CLAUDE.md 粒度規約の **1500 行 watch 閾値**超過
(2000 行 hard 上限は未達ゆえ緊急でない)。過去に 0075/0102 で分割済 (→ S15_SAndTBasic 1176 /
S15_SAndTDefs 1084 に切出し) だが本体が再成長。

⚠ **本 file は lane b の active frontier**: b は 2038 (13.19.c) の c1 bound / assembly を継続中で
S15_SAndT をさらに触る。**active file の分割は b の作業と衝突する**ため、分割は **b の (13.19)
cascade が settle した後**に hub が凍結境界で実施 (mathlib 準拠 = topic leaf への追加切出し or
prefix-split、module 名不変で下流 import 無変更)。

## やること

- [ ] b の (13.19.c) cascade (2038、c1 bound + assembly) が landing し S15_SAndT が凍結したら着手
- [ ] 分割方式決定 (既存 S15_SAndTBasic/Defs へ追加切出し or 新 topic leaf; c 所有 BetaData 領域は
      既に S15_BridgeCharacter へ移動済ゆえ非対象)
- [ ] hub が凍結境界で実施 (b の frontier と非衝突の宣言境界)

## 完了条件

- S15_SAndT.lean (+ 分割後 leaf 群) が各 2000 行未満・理想 1500 未満
- `lake build OddOrder` green・下流 import 無変更

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-09 節: 1500 watch / 2000 hard / dir 化第一)
- 過去分割 = issues/closed/0075, 0102, 0094 (S15 setup)
- issue 2038 (b の (13.19) frontier)、merge afc368a0 (1637 行到達)
