---
id: 9103
slug: s-typep2-field-removal
title: "b-2: Hypothesis.S_typeP2 field 削除 — T_isTypeP2_gate の honest resolution (Pf (13.1) 対称化)"
created: 2026-07-15
---

# b-2: Hypothesis.S_typeP2 field 削除 — T_isTypeP2_gate の honest resolution (Pf (13.1) 対称化)

## 背景 (0118 b-2 の分析結果、lane b 2026-07-15)

root #7 前半 `T_isTypeP2_gate` (CDS:34、sorried) の resolution 調査で確定した事実:

1. **0118 の推奨「hTTypeII explicit param 化」は論理循環で不成立**。
   `T_isTypeP2` (TTypeII:901、(14.9)) の証明は `hvfull := (T_side_caseB_facts hG hyp).2` を
   入力に取る (Coq `FTtypeP_min_typeII` の `v1p_gt_u1q` 対応)。`T_side_caseB_facts` →
   `T_caseB_facts_unconditional` → (no-λ branch) `T_caseB_facts_of_q_lt_p` →
   `d_eq_one`/`T_caseB_v_eq_full` (gate の残 citer 2 箇所、#86)。この chain に
   `hT2 : IsTypeP2 T` param を thread すると TTypeII:199 の call site で供給不能
   (T_isTypeP2 の証明内 = IsTypeP2 T が結論の contradiction argument 内)。
   TTypeII:184-190 の docstring が既に同じ循環を警告している。

2. **原文/Coq の honest 構造**: Pf (14.4) は (13.13)/(13.15) を M = T に適用する。これは
   (13.1) の対称性 (「In this section, S and T play the same role」) による。Coq PFsection13
   の section context は `StypeP : of_typeP S ...` = **FTtype ∈ {2,3,4} (typeP-weak)** で、
   PFsection14 は `FTtypeP_nonGalois_facts maxT` / `card_FTtypeP_Galois_compl maxT` と
   **T-instance を無料で取る** (PFsection14.v:519-530 の `galT`/`oV`)。

3. **Lean の根本原因**: `Hypothesis.S_typeP2 : IsTypeP2 S` field (SubcoherenceInputs:115)
   が Pf (13.1) より強い (Pf (13.2.a) は「S is of Type II **or Type III**」まで;
   「if q<p then II」は §14 の (14.1) 下でのみ)。swap (HypothesisSwap:185
   `S_typeP2 := hT2`) がこの field のせいで `IsTypeP2 T` を要求し、(14.4)-対応の
   swap-instance が gate に化けた。

4. **部品は揃っている**: `not_isTypeIV_of_mem_maximalSubgroups` (S13_NonGaloisExclusion:1007、
   proven) + `proposition_type_classification` (TaxonomyOutput:381、proven) +
   `no_typeV_maximal_unconditional` (proven) から
   **`isTypeII_or_isTypeIII_of_isTypeNonI`** / **`fittingIsTI_of_isTypeNonI`** が組める
   (→ 本 issue Phase 0 で landed)。`S_nonI`/`T_nonI` は (13.1) の対称 field なので
   swap-instance でも供給可能。

## 裁定 (lane b、規約「gate 依存を除去する」の実現)

**`Hypothesis.S_typeP2` field を削除し、consumer を (13.2.a)-faithful (II∨III) に置換する。**
swap が完全対称になり、gate `T_isTypeP2_gate` と hT2 param は消滅する。

### consumer 全数精査 (2 subagent、2026-07-15)

`isTypeII_of_isTypeP2 … hyp.S_typeP2` 9 sites + `fittingIsTI_of_isTypeP2` 3 sites +
`.1`/isTypeP 系 ~6 sites:

| 分類 | sites | 対処 |
|---|---|---|
| **M_F=M_σ 依存 (II 固有、III で偽)** | NineElevenSteps:459 (9.11.4 gap-patch) / BridgeCharacter:1028 (`sharpP_union_V_subset_A0`) / CaseASylowCenter:134 / CoherentEtaOrthogonality:157 (c-owned) | **#84 の T-side fix の逆輸入** (hHMs を ≤ 版に弱化 + σ'-枝再構成; T-mirror `mem_honestTypeP2ASet_of_mem_H_sup_cuSubOf_T` は 0975e47f で一般 P 化済) |
| **II 分岐の位数式** | HypothesisBasics:571 (`card_P_eq`、`typeII_III_IV_order_relations.1` = `\|H\|=\|W₂\|^q` の II 分岐) | III 分岐 (`.2`) の位数式を確認し (13.2.b)-faithful 化 (Pf (13.2.b) は II∨III unconditional) |
| **q_lt_p_forces_typeII field** | HypothesisBasics:1264 (`basic_structure`) | κ-ordering 部品 `isTypeP2_of_typeP_kappaHall_lt` (S13_TypeDetermination、proven) で導出 |
| **共通 core のみ (typeP/common/U_commutative)** | OrderDetermination:377 (a-owned) / CountingLayer:167,508 (**a-flip まで touch 禁止**) / SAndTBasic:35 / HypothesisBasics:1264 の hSdataUne | `isTypeII_or_isTypeIII_of_isTypeNonI` + 共通 core 射影へ機械置換 (TypeIIIData に同名 field) |
| **FittingIsTI 結論** | SAndTDefs:172 / Machinery135:1102 / G0Coprime:162 (c-owned) | `fittingIsTI_of_isTypeNonI` へ機械置換 |
| **IsTypeP のみ (.1 等)** | HonestTypeP2A0 ×5 | `isTypeP_of_isTypeNonI hG S_maximal S_nonI` へ機械置換 |
| **供給側 (field へ入れる側)** | FeitThompson:1352,1482 / FeitThompsonSetup / S13_TypeDetermination:269 / S12_TypeIIGridTranspose:663 (a-owned 含む) | field 削除に伴い供給行を削除 (機械的) |

### Phase 分割 (file 所有と 0118 hold の制約)

- **Phase 0 (landed)**: `isTypeII_or_isTypeIII_of_isTypeNonI` + `fittingIsTI_of_isTypeNonI`
  (S13_NonGaloisExclusion 追記、build green)。
- **Phase 1 (b-owned、即継続)**: M_F=M_σ 3 sites の一般 P 化 (NineElevenSteps /
  BridgeCharacter / CaseASylowCenter) + card_P_eq の II∨III 化 + q_lt_p_forces_typeII の
  κ-ordering 化 (HypothesisBasics) + SAndTBasic:35 / SAndTDefs:172 / Machinery135:1102 の置換。
  **この段階では S_typeP2 field は残す** (置換した consumer が S_typeP2 を読まなくなるだけ;
  build は常に green)。
- **Phase 2 (a-flip landing 後 + c 調整後)**: CountingLayer:167,508 (hold 解除後) /
  OrderDetermination:377 (a-owned、機械的追従 + self-flag or a 依頼) /
  CoherentEtaOrthogonality:157 + G0Coprime:162 (c-owned、同上) の置換 → **field 削除** +
  swap hT2 param 削除 + `T_isTypeP2_gate` 削除 + CDS `d_eq_one`/`T_caseB_v_eq_full` の
  summon 除去 + FT 層供給行削除 (a-owned、9081/#83 precedent の機械的追従)。

### hub 宛 flag

- 0118 b-2 の「param 化が正」は上記 1. の通り循環で不成立 — 「gate 依存を除去する」側の
  option を採る。0116 Finding 2 の「T_isTypeP2 cite は証明循環」制約の完全解と同型。
- Phase 2 は a-2 (0116 flip) / c の workstream と file 交差する。hub の landing flag 運用
  (0118) に Phase 2 の kickoff を組み込むこと (b-5 と同様の gated 項目扱い) を提案。
- root #4 (`nuGridSupply`) は本 campaign と独立に残る (swap の pins 入力; a-1/9096)。

## 完了条件

- [x] Phase 0: 新部品 2 本 landed (S13_NonGaloisExclusion、build green)
- [ ] Phase 1: b-owned consumer の S_typeP2-free 化 (各 build green、AxiomsCheck 不変)
- [ ] Phase 2: field 削除 + gate/param 削除、`d_eq_one`/`T_caseB_v_eq_full` が
  sorry-free 化 (残 sorryAx = nuGridSupply のみ)、AxiomsCheck assert 追加
- [ ] issue 2035 の root #7 前半を closed 記録

## 参照

- issues/0118 (b-2 の割当) / 0116 (Finding 2) / 2035 #82-86 (hT2 弱化 campaign)・#94 (本裁定記録)
- coq/theories/PFsection14.v:519-530 (`galT`/`oV`) / PFsection13.v:1431 (`FTtypeP_nonGalois_facts`)
- references/peterfalvi/04.15 (13.1)/(13.2)/(13.13)/(13.15)、04.16 (14.4)/(14.9)
- 精査レポート: 2 subagent (isTypeII consumer 8 sites、2026-07-15 session b)
