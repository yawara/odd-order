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

## 2026-07-13 CLOSED (lane b, 自主 prefix-split)

b が caseA 継続前に自主 prefix-split を実施:

- **新 sibling leaf `S15_SSetMemberRFamily.lean` (739 行)**: 凍結した reducible R-family 構成クラスタ
  (`sSet_reducible_eq_muColumnSum` … `sSet_memberRFamily_orthogonal`、旧 40–737 行、16 宣言) を移設。
  body は byte-identical (diff 検証済)、sorry 0。
- **`S15_CaseBReducibleCoherence.lean` (1926 → 1222 行)**: caseB coherence
  (`sSet_coherent_dade_caseB`/`sSet_coherent_indS_caseB`) + caseA (9.11) campaign + coherence assembly
  + τ₁ engines を保持 (19 宣言、sorry 1 = `nineElevenEqualityRefutationS` residual)。新 sibling を import、
  module 名不変 → 下流 import 無変更 (importer は OddOrder.lean のみ)。
- OddOrder.lean に新 module import 追加。宣言数 35 = 16+19 保存、sorry 1 = 0+1 保存。
- `lake build OddOrder` GREEN (4181 jobs, 9.5s)。両 leaf とも 1500 行未満 (理想値内)。
