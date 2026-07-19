---
id: 9161
slug: dedup-cyclic-subgroup-uniqueness
title: "CLAIM+HUB: cyclic_subgroup_eq_of_card_eq の 3 重複を shared leaf へ集約 (cross-lane: Pf 側 call site あり)"
created: 2026-07-19
owner: lane c (提起) / hub (cross-lane 部分の裁定)
---

# cyclic_subgroup_eq_of_card_eq — 3 重複 + 汎用群論が BG 配下

## 事実 (2026-07-19 実測)

「有限巡回群で位数の等しい 2 部分群は一致する」= **汎用有限群論**が BG 配下に **3 コピー**ある:

| 場所 | 可視性 |
|---|---|
| `BG/Ch3_MaximalSubgroups/S10_LocalLemmasCore.lean:64` | public |
| `BG/Ch3_MaximalSubgroups/S10_BetaRadicalGlobal.lean:32` | private |
| `BG/Ch3_MaximalSubgroups/S12_Proposition1215.lean:44` | private |

⚠ **S10_LocalLemmasCore の docstring 自身が重複を認めて「shared helper へ hoist すべき」と
書いている**が、その後も 3 コピー目が増えている。

## なぜ今か

`OddOrder/GroupTheory/CNGroupStructure.lean` (issue 9133、Gorenstein Thm 12.1.5) の
「`A` は冪零」ステップで、巡回 Sylow `Q` の `Ω₁(Q)` の位数が `q` であることを出すのに要る。
`GroupTheory` leaf は `BG` を import できないので、現状 **4 コピー目を作るしかない**状態。

## ⚠ cross-lane — lane c 単独では実施しない

call site が **lane a territory の Peterfalvi 本文**にもある:
- `Peterfalvi/S10_MinimalSimpleBasic.lean:1030`
- `Peterfalvi/S16_NonExistenceG/SubgroupM.lean:729`

no-wrapper 方針ゆえ alias を残さず全 call site を repoint する必要があり、これは lane a の
ファイルを触る。territorial ルール上 lane c が単独でやるべきでないので hub へ上げる。

## 提案 (hub 裁定待ち)

1. 新 leaf `OddOrder/GroupTheory/CyclicSubgroupUniqueness.lean` に本体を置く。実装は
   S10_LocalLemmasCore:64 のものをそのまま (依存は mathlib のみ:
   `IsCyclic.card_powMonoidHom_ker` + `Subgroup.eq_of_le_of_card_ge`)。
2. BG の 3 コピーを削除し BG 内 call site を repoint (S10_LocalLemmasCore ×3 /
   S10_BetaRadicalGlobal / S12_Proposition1215 / S13_Theorem1310 / S12_Corollary129 /
   S12_Lemma1211 / S16_Lemma1413 / S16 TypeBridges) — **ここは lane c が実施可能**
   (全て `^OddOrder/BG/`)。
3. Peterfalvi 側 2 件の repoint は **lane a に依頼するか hub が実施**。あるいは hub 裁定で
   「c が Pf の 2 行だけ機械的置換してよい」とする (衝突リスクは極小)。

## 当面の lane c の回避策

`CNGroupStructure` 側は巡回性を使わずに済む形を先に探す。無理なら本 issue の解決を待つ。
**4 コピー目は作らない。**

## 完了条件

`OddOrder/GroupTheory/` に本体が 1 つだけあり、BG/Pf の 3 コピーが消え、全 call site が
新名を指し、full build green。

## 参照
- issue 9133 (CN 3-step dichotomy — 本 issue の需要元)
- 同種の dedup: 9130 / 9159 / 9109 / 9111
- CLAUDE.md「ラッパー方針」(alias を残さない) + 「claim-before-build」
