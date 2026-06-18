---
id: 7006
slug: s16-maximalpair-enrich-gapa
title: "Section16MaximalPair の partner enrichment (gap A) — typeP producer discharge の前提"
created: 2026-06-18
---

# Section16MaximalPair の partner enrichment (gap A) — typeP producer discharge の前提

## 背景

POLE-1 §14 ブロック `section16TypePStructure_of_isMinimalSimpleOdd`
(`OddOrder/FeitThompson.lean:307`, `:= sorry`) は、2 つの独立した gap に分解される
(診断は issue 7005):

- **gap B (逆包含 = load-bearing missing §16 lemma)**: ✅ **解決済** (2026-06-18 lane-f,
  `aa177257`)。`OddOrder.BG.Ch4.S16.typeP_pair_inf_eq : M ⊓ Mstar = K ⊔ Kstar`
  (新 leaf `S16_PairIntersection`、sorry-free + axiom-clean + AxiomsCheck 登録、
  = BG Thm 14.7(4)/C(6)/I(2) の `S∩T=W`)。
- **gap A (構造の型欠陥)**: ⬜ **未解決 (本 issue)**。

**gap A の正体** (issue 7005 で確定、3 レンズ検証済): `Section16MaximalPair`
(`FeitThompson.lean:269`) は partner を **共役までしか固定しない**。covering 条件
`theorem88_caseB` は「各極大は type-I か S か T に共役」としか言わないので、真の
type-P partner を `Mstar`、`T' := Mstar^g` (非自明共役) とすると `T'` も全公理を満たすが
`mp.S ⊓ T'` は一般に位数 `qp` の cyclic でない ⟹ 強制 `W = mp.S ⊓ mp.T` が `W_cyclic`
を満たせず **`Section16TypePStructure mp` が空型** ⟹ 全域関数 `(mp) → ...` は存在不能。

⟹ **gap B (本補題) があっても producer はまだ discharge できない**。`Section16MaximalPair`
が S, T の type-P 双対対関係 (W=S∩T cyclic) を carry していないため、producer 側で
`typeP_pair_inf_eq` を呼ぶための入力 (canonical partner witness) を `mp` から復元できない。

## やること

**`Section16MaximalPair` を partner witness で enrich** (owner = **lane-f**; 2026-06-18 lane-g 退役で
BG 全域が F に集約され、struct 改変も F が単独承認可)。`typeP_pair_inf_eq` の入力にちょうど対応する field 群を追加:

- [ ] `Section16MaximalPair` に以下を追加 (canonical packaging):
      `K Kstar : Subgroup G` / `K ≤ S` / `Ch03.IsHallSubgroup (kappa S) (K.subgroupOf S)` /
      `Kstar ≤ T` / `Ch03.IsHallSubgroup (kappa T) (Kstar.subgroupOf T)` /
      `Kstar = Msigma S ⊓ C(K)` / `K = Msigma T ⊓ C(Kstar)` / `IsCyclic (K ⊔ Kstar)` /
      (`S` の type-P setup `hP/hK/hU` 相当も S, T 両側に)。
      ※ これらは `section16MaximalPair_of_isMinimalSimpleOdd` の構成内部で `typeP_duality`
      の `∃!` 出力から既に得られる情報 (S=M, T=partner Mstar) を構造体に露出するだけ。
- [ ] `section16MaximalPair_of_isMinimalSimpleOdd` (`FeitThompson.lean:275`) を S, T = type-P
      双対対として構成し直し、上記 field を埋める (`S16_MainResults.lean:1014-1050` の
      Theorem I assembly が feeder: 非-type-I 極大 S → type-P → κ-Hall K → `typeP_duality`
      で partner Mstar=T)。
- [ ] enrich 後、**producer `section16TypePStructure_of_isMinimalSimpleOdd` の wiring は
      lane-f が担当可能** (FeitThompson.lean の当該 producer のみ編集、所有境界内): 新 field +
      `typeP_pair_inf_eq` で `W = mp.S ⊓ mp.T = K ⊔ Kstar` を得て `W_eq_inter`/`W_cyclic`/
      `W_eq_join`/`W1_inf_W2_eq_bot`/`W1_commutes_W2` を discharge、残り (U/V 導来分解・counting・
      normalizer) は §14 既存補題 (`derivedInG_eq_Msigma_sup_derivedInG_complement` 等) + Lagrange。

## 完了条件

`Section16MaximalPair` が partner witness を carry し、`section16TypePStructure_of_isMinimalSimpleOdd`
の `sorry` が消え `lake build OddOrder` 緑。

## 参照

- gap A 診断: issue 7005 (型欠陥の論証 + 病的 mp の構成)
- gap B (本補題, 解決済): `OddOrder/BG/Ch4_FamilyOfMaximal/S16_PairIntersection.lean`
  (`typeP_pair_inf_eq`), commit `aa177257`
- 構造体: `FeitThompson.lean:175` (`Section16MaximalPair`), `:195` (`Section16TypePStructure`),
  `:307` (producer, sorry)
- feeder: `OddOrder.BG.Ch4.S14.typeP_duality` (`S14_TypePCounting.lean:7961`) の `∃! Mstar`,
  `S16_MainResults.lean:1014-1050` (Theorem I で S,T=双対対を構成する経路)
- 関連: 8014 (section16MaximalPair, lane-g) / 1004 (character_data, lane-b) / 2009 (POLE-2, lane-h)
- メモリ: `s16-typep-producer-unfillable`
