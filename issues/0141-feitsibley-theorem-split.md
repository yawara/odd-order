---
id: 141
slug: feitsibley-theorem-split
title: "FeitSibleyTheorem.lean 分割 (1871 行 > 1500、2000 hard limit 接近)"
created: 2026-07-21
---

# FeitSibleyTheorem.lean 分割 (1871 行 > 1500、2000 hard limit 接近)

## 背景

hub tick #18 (2026-07-21 22:5x) のサイズ watch で検出。
`OddOrder/Peterfalvi/Appendices/FeitSibleyTheorem.lean` が **1871 行** に到達
(粒度規約の 1,500 行 flag 超過、リポジトリ hard limit 2000 行に接近)。

- lane a が issue 1054 (FeitSibley Theorem 8 ステップ campaign) の active frontier として
  現在も追記中 — **campaign 進行中の分割は a の編集と衝突するため実施を保留**。
- 分割 owner = hub (CLAUDE.md「分割の owner と trigger」)。lane frontier と衝突しない
  **凍結境界での prefix-split** (先頭 K 宣言を新 sibling へ、元 file が import) が第一候補。
- 兄弟 leaf は既に topic 分割されている (`FeitSibleyInduction` / `FeitSibleyReductionTwo` /
  `FeitSibleyReductionThree`) ので、campaign が閉じた区切りで topic 単位統合も検討
  (issue 9160 の Higman 系と同型)。

## やること

- [ ] a の 1054 campaign の区切り (Part A landing または issue close) を待つ
- [ ] 凍結済み先頭クラスタを特定して prefix-split (module 名不変・下流 import 不変)
      または topic leaf へ切り出し (mathlib 互換の記述的英語名)
- [ ] 新 leaf を `OddOrder.lean` に配線 (orphan 監査 0 を維持)
- [ ] `lake build OddOrder` green + AxiomsCheck OK + sorry 数不変を確認

## 完了条件

FeitSibleyTheorem.lean が 1,500 行未満になり、build green・下流 import 無変更・
sorry 数不変で main に合流される。

## 参照

- issue 1054 (lane a の campaign、分割タイミングの依存先)
- CLAUDE.md「ファイル粒度」/ `notes/meta/merge_monitor.md` step 4 (サイズ watch)
- 先例: issue 0103 (機械分割の道具と手順)、issue 9160 (Higman 系粒度)
