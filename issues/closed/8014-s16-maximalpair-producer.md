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

## 解決 (2026-06-18, lane-g, commit `651a2bae`)

`section16MaximalPair_of_isMinimalSimpleOdd` を sorry-free 化 (実 sorry 141→140,
full build 3858 jobs green, AxiomsCheck OK)。組立:

- **Pf 8.8** `maximalSubgroup_type_dichotomy` (= BG Theorem I repackage) の dichotomy
  「all Type I ∨ type-P pair S,T」の case (b) が `Section16MaximalPair` 全 field に直接対応
  (covering clause は既に `∃ g, conj g • M = S` 形)。
- case (a) (all Type I) は **Pf 12.17** `theorem88_caseB_holds` で排除: その case-(b) data が
  non-Type-I 極大部分群 ⟹「all Type I」と矛盾。
- `Or`/`Exists` は `Prop` ゆえ case (b) を命題として先に確立 → `Exists.choose` で witness 抽出
  (dichotomy を `Type` goal へ直接 `rcases` 不可 = large-elimination 障壁)。
- 新補題 `not_isTypeI_of_isTypeNonI` (S16_MainResults, BG-only, §14-independent) =
  Prop 16.1 の系 (Type I ⊥ non-Type-I, `S14.isTypeF_iff_not_isTypeP` 経由)。

⟹ lane-g の §16 main results (`proposition_type_classification` / `theoremI_...`) が初めて
FT spine の実 consumer を獲得 (旧: Pf 8.8 で consumer-0 dead-end)。残 §16 gate =
`proposition_type_classification` (S16:893, type-data construction 本丸, Thm A-D gate)。
