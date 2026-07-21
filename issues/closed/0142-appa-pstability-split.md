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

- [x] c の未マージ commit が AppA_PStability に非接触のタイミングを確認
      (2026-07-21 tick #20: c 未マージ 0、in-flight は NearFields/SolvableTwoTransitive で非接触)
- [x] 凍結済み先頭クラスタを prefix-split — 新 leaf は作らず、**前回分割 (issue 0103 第 2 パス)
      が Basic 末尾に残した空 `section PStability` stub へ A.3 クラスタ (共役 helpers +
      `IsPStable` + `thmA3`、787 行) を移動**。結果: Basic 562→1350 行 / TAIL 1645→858 行。
      module 構成不変 = 配線・下流 import 変更ゼロ。
- [x] 新 leaf 無しゆえ orphan 監査は自明に 0 維持
- [x] `lake build OddOrder` green + AxiomsCheck OK + sorry 数不変 (6→6)

## 完了条件

AppA_PStability.lean が 1,500 行未満、build green・下流 import 無変更・sorry 数不変で main 合流。

## 参照

- issue 0141 (FeitSibleyTheorem 分割、同型)、issue 0103 (機械分割の道具と手順)
- CLAUDE.md「ファイル粒度」/ merge_monitor.md step 4
