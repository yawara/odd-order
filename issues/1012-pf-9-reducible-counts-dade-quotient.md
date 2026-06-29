---
id: 1012
slug: pf-9-reducible-counts-dade-quotient
title: "Pf §9 reducible counts (9.9.b)/(9.8.b)/(9.10) — quotient Dade framework (4.5)/(4.7) + (8.4.d)"
created: 2026-06-29
---

# Pf §9 reducible counts — quotient Dade framework gate

> lane-a (α, Pf §10-13)。`caseB_degree_qu` (9.9.a) 完成 (sorry-free) 後の §9 frontier。
> 正本分析 = `notes/peterfalvi/s10_13_maximal_structure.md` §12 追補⁶⁷⁸。

## やること (S11_MaximalII_III_IV.lean)

- [ ] `caseB_character_counts` (9.9) conjunct 2,3,4: `{φ∈𝒮(H₀)|¬irr}.ncard = p-1` (reducible count) +
      reducible は degree qu かつ ∈𝒮(H₀C) + (9.9.c) `(𝒮(H₀C') に irr 無) → C=⊥ ∧ u=(p^q-1)/(p-1)`。
      (conjunct 1 = (9.9.a) は proven caseB_degree_qu で wire 済)。
- [ ] `caseA_character_counts` (9.8) conjunct b,c,d (parallel)。
- [ ] `exceptional_case_frobenius_realization` (9.10): conjunct 1 = opaque field
      `quotientSemidirectFrobenius` de-opacify + exceptional u + HU Frobenius。

## ゲート分析 (原文 04.11 精読、確定) — 2026-06-29 更新: §6 count は完了

(9.9.b) 証明 = 「By (4.7) and Theorem (4.5), 𝒮(H₀)/𝒮(H₀C) contain exactly p-1 reducible μ_j」。
- **Theorem (4.5)/(4.7)** = 書籍 §6 (mmd 04.6 "Dade Isometry for Certain Type of Subgroup")。
  (4.5): Hypothesis (4.2) 下 μ_j=∑_{0≤i<w₁}μ_{ij} (0≤j<w₂); reducible count = w₂-1 = p-1 (w₂=p)。
  ✅ **2026-06-29 完了**: (4.5)(a),(b) 分類は 2026-06-11 既完成 (`exists_eq_certainType_or_induce`)。
  上の reducible-COUNT corollary を本 lane-a セッションで追加 (全 axiom-clean):
  `S06_CertainTypeClifford.lean` の `induce_chiRestrict_not_isIrreducible` /
  `induce_not_isIrreducible_iff` / **`card_reducible_induce_eq_W2`** (`|{χ∈Irr(K)|Ind^L_K χ reducible}|
  = w₂`)。⟹ **§6 count は citeable**。旧「未完」評価は stale だった ([[verify-port-state-by-number-not-coq-name]])。
- **(8.4.d)** = Hypothesis (4.6)/(4.2) for L = **M/H₀** (商群)。S10 `DadeSupportHypothesisData` は §4 部分のみ、
  「Hypothesis (4.6)/(5.2) char-family は TODO」明記 (S10:451)。**← 残る唯一のゲート**。

## 真の難所 = quotient Dade framework

`Hypothesis46 (A) (L)` は `L:Subgroup G` だが (8.4.d) は **L=M/H₀ (商)**。Peterfalvi は「H₀⊆Ker の文字を
X/H₀ の文字と同一視」((1.6)) で商で作業。⟹ §9 reducible-count は **§4-§6 Dade-certain-subgroup framework
を商 M/H₀ で構築**する必要。`Hypothesis46` の field `tic:TICyclicHypothesis G` (σ-isometry,ω/μ grid) +
`dade0:S04.Hypothesis` + `tau:FullDadeIsometryData` は core Dade 構築で商版が要る。

## 必要作業 (signature-contract で進める; gated 宣言で止めない)

> ⚠ **方針** (2026-06-29、再配分ポリシー準拠): 「§4/§6-gated だから relane / dedicated focus」とは
> **しない**。signature-contract で進める — §6 reducible-count を pin した statement (sorried 可) として書き、
> (9.9.b)/(9.8.b) を cite で実証明して前に進む。`typePData_toS06Hypothesis` 既存 = §6 `S06.Hypothesis` は
> type-P data から構成可能 (S12:1011) ⟹ §6 machinery は available。M/H₀ 商版の bridge が要点。

1. §6 reducible-count obligation (Theorem (4.5)/(4.7): μ_j count = w₂-1) を pin (consumer side、sorried 可)。
2. (8.4.d) Hypothesis(4.6)-for-M/H₀: `typePData_toS06Hypothesis` の商版 bridge。
3. (9.9.b)/(9.8.b) instantiate → caseB/caseA_character_counts conjunct 2,3,4 を cite で証明。
4. (9.10) de-opacify + exceptional 構造。

## 完了条件

S11 の caseB_character_counts / caseA_character_counts / exceptional_case_frobenius_realization が
sorry-free (上流 §6 obligation cite は可)。

## 下流 (unblock するもの)

(10.7) typeII_derived_frobenius (needs (9.8.b)/(9.9.b)/(9.10)) → (10.8) S_not_coherent →
(11.8) exists_zeta_residual_not_orthogonal → card_kappaHall_lt_of_isTypeIIIorIV (FT spine)。
∴ lane-a endgame 全体がこの quotient Dade framework に bottom-out。「最難・最高コストの指標終盤」。

## 参照

- `caseB_degree_qu` (9.9.a, 完成): S11_MaximalII_III_IV.lean、commit ab2b1557 系。
- 原典: Pf (9.8)/(9.9)/(9.10) = `references/peterfalvi/04.11_*`; (4.5)/(4.7) = `04.6_*`。
- 関連: issue 2030 (count-statement audit)、notes/peterfalvi/s10_13_maximal_structure.md §12。
