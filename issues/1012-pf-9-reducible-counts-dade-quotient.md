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

1. ✅✅ **DONE (2026-06-29)**: §6 side 完全クローズ (全 axiom-clean、pin 不要で実証明)。
   - `card_reducible_induce_eq_W2` (`S06_CertainTypeClifford`、`|reducible Ind|=w₂`)。
   - **`card_reducible_Hnontrivial_induce_eq_W2_sub_one`** (`S06_CertainTypeSupport`、任意 W₂≤H≤K で
     `|reducible Ind ∧ H⊄Ker| = w₂-1`) + helper `chiRestrict_one_eq_trivial`。これが (9.9.b) "p-1
     reducible" の §6 完全形 (H=H̄, w₂=p)。`induce_not_isIrreducible_iff` / (4.7) structural
     `not_subset_characterKernel_chiRestrict_of_ne_one` (既存) を統合。
   - **重要簡約**: count は STRUCTURAL `Hypothesis L` のみ要 (Dade τ 不要) ⟹ (8.4.d) bridge も
     「`Hypothesis (M/H₀)` 構造のみ + 文字対応」で足り、商上 Dade 等長写像構成は不要。
   「(4.5)/(4.7) 未完」は stale だった。
2. **← 次手 (残る唯一のゲート) = B1: `S06.Hypothesis (↥M ⧸ H₀')` の構成** (構造のみ、Dade τ 不要)。
   **2026-06-29 de-risk 完了 — 以下が field-by-field の construction recipe (要 ~150-200 行 def)**:
   - **L = `↥M ⧸ (chief.H0.subgroupOf M)`**。H₀⊴M = `normal_subgroupOf_iff_le_normalizer` +
     `chief.H0_normalized_by_M` (9.4)。`q := QuotientGroup.mk' (H0.subgroupOf M)`。
   - **K̄ = `((derivedInG M).subgroupOf M).map q`** (= M'/H₀ = HU/H₀)。`K_normal` ← image of normal。
   - **W̄₁ = `(data.W1.subgroupOf M).map q`**, **W̄₂ = `(data.W2.subgroupOf M).map q`**。
   - **foundations landed** (2026-06-29, S11, axiom-clean): `chiefFactor_H0_subgroupOf_normal`
     (H₀◁M) + `chiefFactor_W1_inf_H0_subgroupOf_eq_bot` (W₁⊓H₀=⊥) + `chiefFactor_coprime_H0_W1`
     (Coprime|H₀||W₁|)。
   - フィールド証明:
     - **`isComplement K̄ W̄₁` = 1-liner**: `data.M_complement.map_mk' hcop (H₀.subgroupOf M)`
       (`IsComplement'.map_mk'` @ `OddOrder/Mathlib/SchurZassenhausConj.lean:49`、N=M'.subgroupOf M,
       K=W₁.subgroupOf M, L=H₀.subgroupOf M; hcop=Coprime|M'||W₁|=hHall)。K̄/W̄₁ も自動で image 形。
     - `W1_cyclic/W2_cyclic`: image of cyclic。`W1_nontrivial`: `chiefFactor_W1_inf_H0_..._eq_bot` で
       W̄₁≅W₁≠⊥。`card_coprime`: |K̄| ∣ |K|, |W̄₁|=|W₁|, `hHall`。`W2_le_K`: image monotone。
     - **`W2_nontrivial` + |W̄₂|=p**: `typeP_chiefFactor_card` (S11:888) が `|C_{H̄}(W₁)|=p` 供給。
       **⚠ type-II 注意 (S11:2032 faithfulness note)**: type II では `|W₂| > p` (W₂∩H₀≠⊥)、
       使うのは **image-order |W̄₂|=p** (typeP_chiefFactor_card)、**`|W₂|` ではない** (後者は
       type III/IV のみ p)。W̄₂ = image of W₂ = C_{H̄}(W₁), order p。
     - **`centralizer_W2` (= (8.4.d) crux)**: `C_{↥M⧸H₀'}(x̄) ⊓ K̄ = W̄₂` for x̄∈W̄₁^#。**3-step 分解**:
       1. ✅ **DONE (2026-06-29)**: `C_{↥M⧸H₀'}(x̄) = (C_{↥M}(x)).map mk'` = **一般補題
          `centralizer_map_mk'_eq_of_coprime_zpowers`** (S11、axiom-clean、reusable):
          `C_{Γ/N}(x̄) = (C_Γ(x)).map mk'` for Coprime|⟨x⟩||N|。⊆ = `coprime_fixedPoints_quotient_of_coprime_normal`
          (φ=MulAut.conj∘zpowers subtype, IsAInvariant ∵N normal, hg_fix ∵x̄,ḡ commute⟹power commute)。
          **これが (8.4.d) の本質的 content** (BG Lem 1.14 は p-group 限定で ⟨x⟩ 不適用、直接組立した)。
       2. **`(C_{↥M}(x)).map mk' ⊓ K̄ = (C_{↥M}(x) ⊓ K).map mk'`** (`ker mk'=H₀'≤K=M'.subgroupOf M` ゆえ
          image∩image=image∩; mathlib `Subgroup.map_inf_eq_map_inf_comap`/`map_inf` ker条件 系)。残。
       3. **`C_{↥M}(x) ⊓ (M'.subgroupOf M) = W₂.subgroupOf M`** (= `data.centralizer_W1`
          `derivedInG M ⊓ centralizer{x} = W₂` の ↥M subgroupOf transport)。残。
       ⟹ 残 = step 2+3 (algebraic plumbing) + x̄→x lift 接続。crux 本質 (step 1) 完了。
     - `W_odd`: image of W₁⊔W₂ odd ← |G| odd。
   - **B1 def の home**: S12 (typePData_toS06Hypothesis 近傍) or 新 bridge leaf。`typePData_toS06Hypothesis`
     (S12:1062, L=M版) が subgroupOf-transport の template; B1 は mk'-image-transport 版。
3. **B2**: §9 `chars.SOf chief.H0` (HU→M induced family) ↔ §6 induction-family {Ind^L_K̄ χ̄} on M/H₀。
   χ̄∈Irr(K̄)↔χ∈Irr(HU) with H₀⊆Ker (inflation (1.6)); `Ind^{M/H₀}_{K̄} χ̄` ↔ inflation of `Ind^M_{HU} χ`
   (induction-inflation commute)。H̄⊄Ker χ̄ ↔ H⊄Ker χ。reducibility 対応。
4. **B3**: `card_reducible_Hnontrivial_induce_eq_W2_sub_one` を B1 の Hypothesis(M/H₀), H=H̄, w₂=p で
   instantiate → (9.9.b)/(9.8.b) count を discharge。
5. (9.10) de-opacify + exceptional 構造。

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
