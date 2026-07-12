---
id: 9087
slug: lane-a-cluster-complete-direction
title: "lane A クラスタ完遂 — spine bare sorry = (10.8) knot 閉包 vs §15/§16 pivot の方向裁定"
created: 2026-07-12
---

# lane A クラスタ完遂 — spine bare sorry = (10.8) knot 閉包 vs §15/§16 pivot の方向裁定

> **HUB 裁定依頼 (lane A → hub)**: lane A (§9-13 char core + typeP_Galois) の genuine new-math
> frontier が枯渇したことを code-level に確定。次方向を hub が裁定されたい (CLAUDE.md「frontier 枯渇・
> 方向・reallocation は user でなく hub」)。lane A は best-available work を継続しつつ本 issue で報告。
>
> **✅ 裁定 = (A) (ユーザー 2026-07-12「Aで」)**: (10.8) knot 閉包を完遂し spine bare-sorry-free を
> 達成する。実装は issue 1025。threading 対象 (dirty via C_eq_cSub、`#print axioms` 確定) =
> S11_NineElevenCaseA (nineElevenPairBound / caseA_two_summand_inertia_inputs /
> caseA_nineElevenThree_count_inputs / caseA_nineElevenTwo_tiWitness) + S11_NineElevenPairAdjoin
> (nineElevenSevenEightRefutation) + S11_NineElevenAlphaBound (nineElevenNormBound_of_sevenEightRefutation /
> nineElevenEqualityRefutation_of_sTwoExtraction_normBound / nineElevenEqualityRefutation_of_sevenEightRefutation)
> + S13_Orthogonality (coherent_sOf_H0C / coherent_SOf_H0C_of_column_identities / exists_zeta_residual rewire)。
> wiring theorem (caseA_refuter_of_equality_refutation 等) は param 化済 clean で threading 不要。

## 確定した状態 (2026-07-12 全数トレース)

lane A の headline は全完遂: **W1** (feitThompson capstone、bare sorry 0) / **W2** (issue 1024
typeP_Galois + (11.9) Type III、pending) / **9083 Phase E** ((9.11) 𝒮(H₀C′) coherence machinery) /
**(11.5)/(11.6)/(11.7)** structural results。

lane A 領域 (`Peterfalvi/S0[3-9]|1[0-3]*` + FeitThompson) の残 13 sorry は**全て**次のいずれか:
- **OFF-PATH**: S09 (7.10) `card_G0_lower_bound`
- **gated**: S10 (§12-gated 9080) / S12_MaximalIII_IV_V (§14-gated coherent_Sset_diff_SHCSet) /
  S12 typeV 群 (issue 2022 six_two-gated)
- **vestigial**: S13_CoreStructure の OrthogonalityData carrier 3 本 (consumer 0、証明しない)
- **legacy import-DAG artifact (honest heir 既存)**: S11 sibleyTarget_H0C / S12_MaximalBasic
  S_not_coherent (10.8、honest = `S12.S_not_coherent_unconditional`) / S12_TypeIIFrobenius
  exists_typeIICrossIsometryData ((10.7)、honest = `typeII_HU_frobenius_of_coherent'`、issue 9079/1020)

⟹ **lane A の owned territory に genuine な未形式化 new math は残っていない** (全て done / gated /
vestigial / honest-heir-既存の legacy bookkeeping)。§14 Sibley S(HC) coherence (`coherent_SOf_HC`) も
axiom-clean 確認済。

## FT spine の唯一 bare sorry の所在

`feitThompson` の唯一の bare spine sorry = `card_kappaHall_lt_of_isTypeIIIorIV` (AxiomsCheck:7150)、
residual = `exists_zeta_residual_not_orthogonal_H0C_of_refuter` (S13_Orthogonality:1010)。
`#print axioms` 全トレースで dirty root は **(10.8) import-DAG knot のみ** に局所化:
`exists_zeta_residual` → `secondDerived_eq_HC` (11.5) / `coherent_sOf_H0C` (caseA) →
`C_eq_cSub` → `chief_H0_eq_bot` (11.7) → `H0_eq_Hprime` (11.6) → `secondDerived_eq_HC` (11.5) →
`HC_le_secondDerived` → `coherent_quotient_bound` (11.4) → `S_H0C_not_coherent` (11.3) →
**`S12.S_not_coherent` (10.8、legacy sorried)**。honest `S12.S_not_coherent_unconditional` は存在するが
S12_Noncoherence が下流ゆえ import-DAG で cite 不可。

## 方向の選択肢 (hub 裁定事項)

- **(A) (10.8) knot 閉包で spine bare-sorry-free 達成** (issue 1025)。spine の `hrefute`
  (= clean `S_H0C_not_coherent_unconditional`) を (11.4)-(11.7) chain + S11 (9.11) caseA machinery に
  thread。**foundational 半分 (S13 (11.4)-(11.7) parametrize) は commit aec0d595 で完了・green**。
  残 = S11_NineElevenCaseA/PairAdjoin の 5 therem (nineElevenPairBound / caseA_two_summand_inertia_inputs
  / caseA_nineElevenThree_count_inputs / caseA_nineElevenTwo_tiWitness / nineElevenSevenEightRefutation)
  + consumer cascade への threading (~15-25 theorem、大規模)。
  - ⚠ 評価: honest 10.8/9.11 は**既に存在**し、これは spine を honest route へ re-wire する作業。
    CLAUDE.md doneness 基準 (carrier 構成 / free-field→実証明 / 新定理証明) では「既存 sorried route を
    実証明で置換」に該当 (genuine) だが、新規数学の積み上げではない。landmark (spine bare-sorry-free) だが
    feitThompson 全体は §14/§15/§16 の推移 sorry で依然 dirty ゆえ「FT 完成」ではない。
- **(B) §15/§16 の actual FT frontier へ pivot**。lane A cluster 完遂ゆえ、残る genuine char math
  (§14 Sibley (6.7)/(5.8) の image-side / §15 norm/order determination / §16 T-side) の**未所有 shared
  prerequisite** を lane A が build (policy B: 未所有 leaf 新設は consumer 他レーンでも in-scope)。
  要調査 (具体 target 未特定)。

## lane A の暫定行動 (hub 裁定まで)

best-available = (A) の (10.8) 閉包を継続 (concrete・foundational 半分完了済・cross-lane 調整不要)。
hub が (B) を選ぶなら pivot。**S13 foundational commit (aec0d595) は (A)(B) どちらでも保全** (whenever
(10.8) が閉じられる際に必要な正しい parametrization)。

## 参照

- issue 1025 (foundational refactor)、1024 (W2)、1020/9079 (honest-heir 移行)、9083 ((9.11) Phase E)
- commit aec0d595 (S13 (11.4)-(11.7) parametrize)
- CLAUDE.md「進捗の測り方」/「hub は cross-lane を自律裁定」
