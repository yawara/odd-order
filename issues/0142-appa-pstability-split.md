---
id: 142
slug: appa-pstability-split
title: "AppA_PStability.lean 分割 (1645 行 > 1500)"
created: 2026-07-21
---

# AppA_PStability.lean 分割 (1645 行 > 1500)

## 背景

hub tick #19 (2026-07-21 23:1x) のサイズ watch で検出。
`OddOrder/BG/AppA_PStability.lean` が **1645 行** (粒度規約の 1,500 行 flag 超過)。
c が Glauberman ZJ 系 (issue 9403 完了) の p-stability bridge +13 行を追記したのが直近の増分。

- 分割 owner = hub。c の active frontier と衝突しない凍結境界で prefix-split
  (先頭 K 宣言を新 sibling leaf へ、元 file が import — module 名不変・下流 import 不変)。
- c は 9403 を close 済みなので、次の区切りで実施可能。着手前に c の未マージ commit が
  本 file に掛かっていないか確認する。

## やること

- [ ] c の未マージ commit が AppA_PStability に非接触のタイミングを確認
- [ ] 凍結済み先頭クラスタを prefix-split (mathlib 互換の記述的英語名の新 leaf)
- [ ] 新 leaf の root closure 到達性を確認 (orphan 監査 0 維持)
- [ ] `lake build OddOrder` green + AxiomsCheck OK + sorry 数不変

## 完了条件

AppA_PStability.lean が 1,500 行未満、build green・下流 import 無変更・sorry 数不変で main 合流。

## 参照

- issue 0141 (FeitSibleyTheorem 分割、同型)、issue 0103 (機械分割の道具と手順)
- CLAUDE.md「ファイル粒度」/ merge_monitor.md step 4
