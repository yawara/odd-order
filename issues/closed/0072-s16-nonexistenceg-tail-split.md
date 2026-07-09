---
id: 72
slug: s16-nonexistenceg-tail-split
title: "S16_NonExistenceG.lean tail split (2034>1500, lane-h frontier 凍結後)"
created: 2026-06-18
---

# S16_NonExistenceG.lean tail split (2034>1500, lane-h frontier 凍結後)

## 背景

merge tick (2026-06-18) のサイズ watch で検出。`S16_NonExistenceG.lean` は 2026-06-15 に
prefix-split 済 (凍結 Core `S16_NonExistenceGCore.lean` 4917 行 + editable tail)。tail は lane-h の
POLE-2 assembly landing (`fe5aa73e`) で 1979→**2034 行** (>1500)。**owner = hub** (粒度規約)。

## やること

- [ ] lane-h の POLE-2 frontier が凍結したら（= 残 producer `exists_LHypothesis`/`exists_MHypothesis` +
      hard core `field_normalizer_of_U_characteristic` の去就が定まったら）、衝突しない凍結境界で
      prefix-split する。

## 完了条件

tail が 1,500 行以下、chain importer 透過、`lake build OddOrder` 緑。

## 参照

- `OddOrder/Peterfalvi/S16_NonExistenceG.lean` (2034 行)、凍結 `S16_NonExistenceGCore.lean`
- lane-h frontier = issue 2009 (POLE-2)。**2009 が pending/closed になるまで実施保留**（active frontier 衝突回避）。
- 先行例: 0069 (S14_TypePCounting split, 同じく lane frontier 凍結待ち)

## 🧾 注記 (2026-07-02 hub 全体レビュー): trigger 書換え

- 旧 trigger「issue 2009 (lane-h POLE-2) が pending/closed になるまで保留」は stale:
  lane-h は退役済で 2009 は `issues/pending/` に移動済。**新 trigger = lane c の §15/§16
  frontier 凍結後** (`S16_NonExistenceG.lean` tail は現在 **lane c** の active 領域 —
  lane c = S15_SAndT_Setup / S15_SAndT / S16_NonExistenceG + 構成的 Clifford 9002)。
- 行数 refresh: `S16_NonExistenceG.lean` = **4548 行** (2026-07-02)。凍結 Core =
  `S16_NonExistenceGCore.lean` 4919 行。
- 分割実施は従来通り prefix-split (lane c の frontier と衝突しない凍結境界で)。

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - ComparingLM.lean (3007 行)
  - KeyInequality.lean (598 行)
  - SubgroupL.lean (2945 行)
  - SubgroupM.lean (1897 行)
