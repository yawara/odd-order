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

- [ ] active frontier (現に証明中の (10.5) 系) と衝突しない**凍結済み prefix** を特定
      (先頭の完成済み宣言群 = §10 minimal-simple 構造 / CharacterParameters carrier 定義 等)
- [ ] prefix を上流 leaf (例 `S12_CharParameters.lean` / `S12_Core.lean`) に prefix-split
      (前方参照は構文上不可能ゆえ任意の宣言境界で安全)
- [ ] 残りが上流 leaf を import、hub が束ねる。下流 (S13/S16 cite) は不変
- [ ] 新規 leaf を `OddOrder.lean` の root closure に追加 (import 行)
- [ ] full build green + AxiomsCheck OK 確認

## 完了条件

S12_MaximalIII_IV_V.lean が ~1500 行以下 (または topic-coherent な複数 leaf + hub) になり、
full build (3881 jobs) green を維持。lane-b の frontier 編集と衝突しない凍結境界で実施済み。

## 参照

- merge_monitor.md「各イテレーションの手順」step 4 (サイズ watch) + 「分割の owner と trigger」
- 既存 split 前例: issue 0069 (S14_TypePCounting) / 0071 (S15_MF) / 0075 (S15_SAndT)
- merge `0256fe25` (3508 行到達時点)
- [[feedback-record-deferred-hub-tasks-as-issues]]
