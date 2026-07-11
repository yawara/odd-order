---
id: 79
slug: feitthompson-split
title: "FeitThompson.lean 1500行超 — def-unit 境界で prefix-split 検討"
created: 2026-06-24
---

# FeitThompson.lean 1500行超 — def-unit 境界で prefix-split 検討

## 背景

size watch (merge_monitor.md step 4) で検出: `OddOrder/FeitThompson.lean` が **1958 行** (>1500)。
2026-06-24 tick で lane-b の cd tau3 (+71) 追記により閾値超過。

⚠ **このファイルは特殊**: FT endgame の def-unit 共有 wiring hub で、**4 レーンが def 単位で co-edit**
(F=mp+Prop16.1 / B=cd `section16CharacterData` / C=tp `Section16TypePStructure` 系 / H)。
通常の leaf と違い prefix-split は active frontier と衝突しやすい。

## やること

- [ ] def-unit 凝集を保つ分割境界を調査 (例: cd `section16CharacterData` cluster を別 leaf へ、
      tp `Section16TypePStructure*` を別 leaf へ — 各 lane が単一 leaf を所有する形が理想)。
- [ ] **実施は全 4 レーンが当該 cluster で idle なタイミングで hub が行う** (frontier 衝突回避)。
      凍結境界での prefix-split (前方参照は構文上不可ゆえ任意の宣言境界で安全)。

## 完了条件

FeitThompson.lean が ~1500 行以下、または def-unit 単位で複数 leaf に分割され hub が束ねる。
build-green 維持。

## 2026-06-24 lane-b note — cd cluster が frozen (split candidate)

issue 1004 完了 (commit `c57ed7ad`) で **cd `section16CharacterData` cluster が完成・frozen**。
具体的には `namespace Section16CharacterData` (building blocks, FeitThompson.lean ~1102–1664) +
producer `section16CharacterData_of_isMinimalSimpleOdd` (~1694–1710) = **~620 行が lane-b の凍結境界**。
lane-b はこの cluster で今後 active frontier を持たない (producer 完成)。

⟹ **hub への提案**: この cd cluster を別 leaf (例 `OddOrder/FeitThompson/CharacterData.lean`) へ
prefix-split すれば FeitThompson.lean が ~1380 行に収まる。ただし cluster は `Section16MaximalPair`
(mp, lane-f) / `Section16TypePStructure` (tp, lane-c) 型に依存し、下流 `section16Inputs_of_isMinimalSimpleOdd`
(~1750) が producer を消費する ⟹ core(mp/tp 構造) → cd-leaf → assembly(inputs/hypothesis) の 3-way split に
なる。**実施は hub 判断** (4 レーン co-edit ゆえ; 本 note は frozen 境界の通知のみ)。

## 参照

- `notes/meta/merge_monitor.md` step 4 (size watch) + 🔒 所有マップ (FeitThompson 共有)
- 既存 split issues: 0069 (S14_TypePCounting) / 0071 (S15_MF) / 0076 (S12) / 0077 (S11) / 0078 (S16_MainResults)

## 🧾 注記 (2026-07-02 hub 全体レビュー): 前提更新 — 4 レーン co-edit は消滅

- **`FeitThompson.lean` は現在 lane a の単独所有** (3 レーン再編 2026-07-02: lane a =
  Pf S03–S13 + FeitThompson.lean。正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)。
  「4 レーンが def 単位で co-edit」という本 issue の特殊事情は**消滅**し、通常の
  single-owner leaf として扱える (分割は lane a の frontier 凍結境界で hub prefix-split)。
- 行数 refresh: `FeitThompson.lean` = **2058 行** (2026-07-02)。
- 2026-06-24 lane-b note の cd cluster 境界 (~1102–1664 / ~1694–1710 / ~1750) は
  **line 番号 drift の可能性が高い — 実行時に要再検証** (再 grep)。

## 2026-07-12 現況 (hub tick 注記)

- `FeitThompson.lean` = **1844 行**、split-out 済の `FeitThompsonSetup.lean` も **1630 行** (>1500)。
- 本 tick で b (conj-pair producer 追記) と c ((3.9.b) field 配線) が**同 tick に co-edit** — 依然
  active な def-unit 共有 wiring hub であり、「全レーンが当該 cluster で idle なタイミングで hub が
  prefix-split」の方針を維持 (今は分割しない)。**FeitThompsonSetup.lean も本 issue の対象に追加**
  (carrier structure 宣言群 = Section16Inputs/Section16CharacterData の凝集境界で将来分割)。
