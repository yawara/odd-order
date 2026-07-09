---
id: 94
slug: s15-setup-split
title: "S15_SAndT_Setup.lean split (1715 行 >1500) — 凍結境界で prefix-split"
created: 2026-07-01
---

# S15_SAndT_Setup.lean split (1715 行 >1500) — 凍結境界で prefix-split

## 背景

`OddOrder/Peterfalvi/S15_SAndT_Setup.lean` が merge-monitor のサイズ watch (粒度規約
1,500 行) を超過。2026-07-01 の lane d 合流 (`ed8b5e2c` Pf 13.5 §8 TI-subset sorry-free)
時点で **1715 行**。merge_monitor.md 手順 4 に従い flag + 起票。

`S15_SAndT_Setup` は **lane d の active frontier** (2026-07-01 再配分で d に移管、issue
[0092](0092-hub-reallocate-lane-d-to-s15-setup.md))。残 sorry の gating map は issue
[4014](4014-s15-setup-gating-map.md) 参照 (現在 ~14 sorry 進行中)。

## やること

- [ ] §15 setup の凍結済クラスタ (先頭の Hypothesis/Sdata 定義 + carrier 基盤 + 完成済
      helper 群) が proof レベルで凍結したら、上流 `S15_SAndT_SetupCore.lean` へ prefix-split し、
      active frontier (残 sorry を含む leaf) を残す。下流 (S15_SAndT / S16) は hub が束ねる
      import で不変に保つ。
- [ ] 分割の実施 owner = hub。lane d の frontier と衝突しない凍結境界で切る。
- [ ] split 後 `OddOrder.lean` の import が root closure を保つことを確認 (手順 3b)。

## 完了条件

`S15_SAndT_Setup.lean` (および分割後の各ファイル) が 1,500 行以下になり、full build +
AxiomsCheck green を維持。

## 参照

- merge_monitor.md 手順 4 (サイズ watch)
- 同種 deferred split issue: [0071](0071-s15-mf-split.md) (BG S15_MF), [0077](0077-s11-maximaliiiiv-split.md) (S11)
- lane d 配分: [0092](0092-hub-reallocate-lane-d-to-s15-setup.md) / gating map: [4014](4014-s15-setup-gating-map.md)

## 🧾 注記 (2026-07-02 hub 全体レビュー): owner 参照更新

- 本文が参照する issue **0092 / 4014 は本日 closed** (`issues/closed/`)。lane d は退役し、
  `S15_SAndT_Setup.lean` の **active frontier は現在 lane c** (lane c = S15_SAndT_Setup /
  S15_SAndT / S16_NonExistenceG + 構成的 Clifford 9002、正本
  `notes/meta/ft_lane_reallocation_2026_06_28.md`)。
- 行数 refresh: `S15_SAndT_Setup.lean` = **1916 行** (2026-07-02)。
- **実施は lane c の setup cluster 凍結まで defer** (prefix-split owner = hub は不変)。

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - CountingLayer.lean (1975 行)
  - DegreesFirstSplit.lean (2137 行)
  - HypothesisBasics.lean (2220 行)
  - NormEstimates.lean (2336 行)
  - OrderDetermination.lean (800 行)
