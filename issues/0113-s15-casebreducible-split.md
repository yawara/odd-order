---
id: 113
slug: s15-casebreducible-split
title: "S15_CaseBReducibleCoherence 1926 行 → 分割 (2000 hard 接近・b の caseA settle 後)"
created: 2026-07-13
---

# S15_CaseBReducibleCoherence 1926 行 → 分割 (2000 hard 接近・b の caseA settle 後)

## 背景

2026-07-13 監視 tick で `OddOrder/Peterfalvi/S15_CaseBReducibleCoherence.lean` が **1926 行** に到達
(merge 70b8ef95 = 1017 (9.11) S-instance caseA の nineElevenPairBoundS close ほか)。**2000 行 hard 上限に
極めて接近** (残 headroom 74 行) — CLAUDE.md 粒度規約の hard 上限を次の commit で超えうる。

⚠ **本 file は lane b の active frontier**: b は 1017 caseA lift をこの leaf で継続中 (残 residual =
`nineElevenEqualityRefutationS` 1 本 + strata bridge)。**active file の分割は b の作業と衝突する**が、
2000 接近ゆえ **b の caseA が settle したら即分割**、または **b が 2000 を超える前に自ら prefix-split**
(先頭の caseB reducible-coherence クラスタを sibling へ、元 file が import) が望ましい。

## やること

- [ ] hub は毎 tick の size watch で 2000 超を監視 (超えたら分割必須化)
- [ ] b の caseA (残 nineElevenEqualityRefutationS) landing で file 凍結 → hub が凍結境界で分割
      (caseB reducible / caseA lift の topic 境界で 2 leaf 化、module 名不変で下流 import 無変更)
- [ ] または b が 2000 超前に自主 prefix-split

## 完了条件

- S15_CaseBReducibleCoherence.lean (+ 分割後 leaf) が各 2000 行未満・理想 1500 未満
- `lake build OddOrder` green・下流 import 無変更

## 参照

- CLAUDE.md「ファイル粒度」(2026-07-09 節: 1500 watch / 2000 hard / dir 化第一)
- 同型 deferred split issue = 0110/0112 (active file)、0111 (closed)
- issue 1017 (b の (9.11) S-instance campaign)、merge 70b8ef95 (1926 行到達)
