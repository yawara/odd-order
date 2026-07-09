---
id: 71
slug: s15-mf-split
title: "S15_MF.lean split (2352 行 >1500) — §15 凍結後に prefix-split"
created: 2026-06-16
---

# S15_MF.lean split (2352 行 >1500) — §15 凍結後に prefix-split

## 背景

`OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean` が merge-monitor のサイズ watch
(粒度規約 1,500 行) を超過 (2026-06-16 の lane-g Thm 15.2 step 2 合流時点で **2352 行**)。
merge_monitor.md 手順 4 に従い flag + 起票。

ただし S15_MF は **Lane G の active frontier** (G は §15 専念、Thm 15.2 proof body =
issue 8012 進行中)。既存の deferred split issue (S14=0069 / S10=0063 / S05=0064) と同じく、
**lane の frontier と衝突しない凍結境界が定まるまで実施は保留**。

## やること

- [ ] §15 (Thm 15.2 / Cor 15.3 / Thm 15.7 + M_F infra) が proof レベルで凍結したら、
      凍結済みクラスタ (先頭の定義 + M_F 基盤 + 完成済 conditional helper 群) を上流
      `S15_MFCore.lean` へ prefix-split し、active frontier (Thm 15.2 残 proof body 等) を
      leaf に残す。下流は hub が束ねる import で不変に保つ。
- [ ] split 後 `OddOrder.lean` の import が closure を保つことを確認 (手順 3b)。

## 完了条件

S15_MF.lean が 1,500 行以下になり、full build + AxiomsCheck green を維持。

## 参照

- 手順: `notes/meta/merge_monitor.md` 手順 4 (サイズ watch) + lane frontier 凍結待ちの前例
- 同類 deferred: issues/0069 (S14_TypePCounting), issues/0063 (S10_LocalLemmas),
  issues/0064 (S05_NarrowPGroups)
- frontier tracker: issues/8012 (Thm 15.2 proof body), issues/8008 (Lemma 15.1 gated)
- merge: 44a636eb (Thm 15.2 step 2 — 超過を発生させた合流)

## 🧾 注記 (2026-07-02 hub 全体レビュー): trigger 発火 — hygiene-only

- 旧 hold 条件「Lane G の active frontier」は**失効**: lane G は退役済 (3 レーン体制
  a/b/c)、BG 側 frontier は凍結 ⟹ **trigger 発火** (凍結境界は自由に取れる)。
- 行数 refresh: `S15_MF.lean` = **9603 行** (2026-07-02)。
- 優先度 = **hygiene-only** (BG 凍結クラスタの粒度整理であり FT 経路の実質的証明では
  ない)。hub batch の余力枠で実施。

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - Corollary155.lean (4237 行)
  - SetupLemma151.lean (1738 行)
  - Theorem152Helpers.lean (1607 行)
  - TIFailure.lean (3814 行)
