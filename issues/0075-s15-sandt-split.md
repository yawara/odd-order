---
id: 75
slug: s15-sandt-split
title: "S15_SAndT.lean split (>1500 行)"
created: 2026-06-20
---

# S15_SAndT.lean split (>1500 行)

## 背景

merge_monitor サイズ watch (手順 3/4) が `OddOrder/Peterfalvi/S15_SAndT.lean` の 1,500 行超を検出。
2026-06-20 の lane-h gate-4 作業 ((13.17.c) `complement_le_QW2`) 合流時に **1457 → 1530 行**で
threshold を跨いだ (merge `c6949aaf`)。粒度規約 (CLAUDE.md「ファイル粒度」) の enforcement。

## やること

- [ ] lane-h の gate-4 / S13.17 active frontier が S15_SAndT から離れた段階で **hub が prefix-split** を実施
      (frozen 境界で先頭 K 宣言を上流 leaf へ、残りが import する。前方参照は構文上不可ゆえ任意の宣言境界で安全)
- [ ] topic-coherent な分割点を選ぶ (S∩T 構造補題群 / type-conjugacy / (13.17.c) complement 補題群 で切る)
- [ ] 下流 import 透過を確認 (chain importer は hub leaf を import するだけで不変)

## 完了条件

S15_SAndT.lean (および分割後の各 leaf) が <1500 行。full build green + AxiomsCheck OK。

## 参照

- 同型先行例: [0071-s15-mf-split.md](0071-s15-mf-split.md) (S15_MF 7253 行、同じく active frontier ゆえ実施保留中)
- merge_monitor.md 手順 3/4 (サイズ watch)
- 実施 owner = hub。lane の frontier と衝突しない凍結境界で行う (S15_MF/0071 と同方針: frontier が active な間は起票のみ・実施保留)
