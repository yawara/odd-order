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

- [ ] `proposition_type_classification` の 6 inline bridge を埋める。engine
      `proposition_type_classification_of_inputs` + 4 input は sorry-free 済。
  - **forward `hP1eqV` (型 P₁∧MF=Mσ → V)**: ✅ **2026-06-26⁵ 配線済** (型 V TypePData 完全構成
    `typePData_of_isTypeP1_mf_eq_msigma` + FittingIsTI ケース discharge)。残差 = ¬FittingIsTI の
    Peterfalvi (8.8) Suzuki trichotomy (`nonTI_Fitting_structure`, deep)。詳細 issue 8015。
  - **forward `hP1neIIIIV` (型 P₁∧MF≠Mσ → III/IV)**: 残。TypePData(P₁,U≠⊥) を要し M'/M_F nilpotent
    (Coq `Fcore_structure`) が核 gate。詳細 issue 8015。
  - reverse 4 (`hIF`✅/`hIIP2`/`hIIIIVP1`/`hVP1`): FeitThompson 未使用 (off-path、`.mpr` のみ使用)。
- [x] **検証残し 解決 (2026-06-26⁵)**: `theoremA_maximal_structure` (S16:144, sorry) は
      **`Peterfalvi/S12_MaximalIII_IV_V.lean:632` で cite = on-path** (verifier の「docstring のみ」は誤り)。
      ただし用途は **`.2.1` = A(2) `IsCyclic ↥K` のみ**で、これは sorry-free な
      `typeP_auxiliary_structure hG hM hKM hUM hK rfl hU |>.2.1` (conj 2) で置換可能
      (hKM=`Subgroup.map_subtype_le`, hUM 同様)。⟹ **凍結不要・dependency は除去可能**。
      `theoremA_maximal_structure` の唯一の cross-lane caller ゆえ、swap 後は dead で削除可。
      **lane-b (W3) タスク**: S12:632 の citation を `typeP_auxiliary_structure` に swap。

## 完了条件

`proposition_type_classification` の 6 bridge が sorry-free + axiom-clean。mp producer
(`exists_section16MaximalPair_data`) の type-classification 依存が解消。

## 参照

- 正本: `notes/meta/ft_frontier_remap_2026_06_25.md` §2 (W1)
- 主所有: `OddOrder/BG/**` + `FeitThompson.lean` mp/carrier 宣言
- 関連: issue 8015 (π(W₁)⊆κ reverse carrier)、7007 (Prop 16.1 deep theorems)、2016 ((12.9) Hall-compl)

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

W1 目標達成: Prop 16.1 axiom-clean — `AxiomsCheck.lean:6205` に
`#assert_only_allowed_axioms OddOrder.BG.Ch4.S16.proposition_type_classification` (検証 2026-07-02)。
残 1 点 (S12_Core:1055 の theoremA_maximal_structure cite → sorry-free な typeP_auxiliary_structure への差替) は
issue 1012 (L2087) に転記済。
