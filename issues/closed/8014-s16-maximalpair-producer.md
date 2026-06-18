---
id: 8014
slug: s16-maximalpair-producer
title: "Section16Inputs: section16MaximalPair producer (BG §16, lane-g)"
created: 2026-06-18
---

# Section16Inputs: section16MaximalPair producer (BG §16, lane-g)

## 背景

2026-06-18 の post-§14 監査 (11-agent code-verified, [[ft-endgame-two-poles]]) で、`typeP_duality`
は proved だが feitThompson の sorry を減らさず、真の gap = **未所有の `Section16Inputs` producer**
と判明。hub が `Section16Inputs` を 3 中間 structure に分解する skeleton を投入
(commit `80f9aa39`, `OddOrder/FeitThompson.lean`)。本 issue はその BG §16 担当ブロック。

## やること

- [ ] `section16MaximalPair_of_isMinimalSimpleOdd hG : Section16MaximalPair G`
      (`OddOrder/FeitThompson.lean:266`, 現 `sorry`) を実証明化する。
- [ ] 内容 = 極小単純奇数位数群 G から、極大対 S, T とその type 分類を構成:
      `S T : Subgroup G`, `S_maximal`/`T_maximal` (∈ `maximalSubgroups G`), `S_ne_T`,
      `S_nonI`/`T_nonI` (`IsTypeNonI`), `one_typeII` (`IsTypeII S ∨ IsTypeII T`),
      `theorem88_caseB` (Pf 8.8 trichotomy: 任意の極大 M は type-I か S/T と共役)。
- [ ] feeder = BG §16 main results (`S16_MainResults.lean` の `proposition_type_classification` /
      `theoremI_type_dichotomy` / `theoremII_tame_embedding`) + Pf 8.8
      `maximalSubgroup_type_dichotomy` (`S10_MinimalSimpleStructure.lean:112`)。現状これらは
      consumer 0 で dead-end している — 本 producer がそれらの初の実 consumer になる。

## 完了条件

`section16MaximalPair_of_isMinimalSimpleOdd` の `sorry` が消え、`lake build OddOrder` 緑。
(structure 自体は hub が定義済み・不変。)

## 参照

- skeleton commit `80f9aa39`、`OddOrder/FeitThompson.lean:180` (`structure Section16MaximalPair`),
  `:266` (producer)
- consumer chain: `section16Inputs_of_isMinimalSimpleOdd` (`:288`, sorry-free assembly) →
  `sectionSixteenHypothesis_of_isMinimalSimpleOdd` (`:457`) → feitThompson
- 関連: 7005 (typeP_structure, lane-f) / 1004 (character_data, lane-b) / 2009 (POLE-2, lane-h)
