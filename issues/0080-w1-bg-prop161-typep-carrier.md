---
id: 80
slug: w1-bg-prop161-typep-carrier
title: "W1 (lane-f): BG §16 Prop 16.1 6 bridge + type-P carrier 構成 [純群論]"
created: 2026-06-25
---

# W1 (lane-f): BG §16 Prop 16.1 6 bridge + type-P carrier 構成 [純群論]

## 背景

FT フロンティア再設計 (2026-06-25 relane #9、正本 `notes/meta/ft_frontier_remap_2026_06_25.md`)
で同定した **4 独立フロントの W1** = lane-f 担当。Arm A (S16.Hypothesis 構成) の mp 側。
**純群論/局所解析で char gate が無く、最大 fan-out (`proposition_type_classification` は 8+ consumer)
ゆえ最優先・最 de-risk フロント**。

## やること

- [ ] `proposition_type_classification` (`OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults.lean:2404`)
      の 6 inline bridge (@2437-2448) を埋める。engine `proposition_type_classification_of_inputs`
      + 4 input (`isTypeI_of_isTypeF` 等) は sorry-free 済。
  - forward 2 (`hP1neIIIIV`/`hP1eqV`): 型-P₁ `TypePData` 構成 (Pf (8.3)/(8.8))
  - reverse 4 (`hIF`/`hIIP2`/`hIIIIVP1`/`hVP1`): carrier-level `π(W₁) ⊆ κ(M)` / W₁=κ-Hall
    characterization (**issue 8015**)
- [ ] **検証残し**: `theoremA_maximal_structure` (S16_MainResults.lean:144) が真に on-path か確定
      (ft-assembly「Yes, S12:632 経由」 vs verifier「docstring 参照のみで off-path」)。off-path なら凍結。

## 完了条件

`proposition_type_classification` の 6 bridge が sorry-free + axiom-clean。mp producer
(`exists_section16MaximalPair_data`) の type-classification 依存が解消。

## 参照

- 正本: `notes/meta/ft_frontier_remap_2026_06_25.md` §2 (W1)
- 主所有: `OddOrder/BG/**` + `FeitThompson.lean` mp/carrier 宣言
- 関連: issue 8015 (π(W₁)⊆κ reverse carrier)、7007 (Prop 16.1 deep theorems)、2016 ((12.9) Hall-compl)
