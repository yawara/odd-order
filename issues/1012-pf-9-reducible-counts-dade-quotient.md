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
     - ✅ **`W2_nontrivial` (= W̄₂≠⊥ ⟺ W₂⊄H₀) DONE (2026-06-29)**: `chiefFactor_W2_not_le_H0`
       (axiom-clean): `coprimeFrobeniusChiefFactor_card.2` で `|fixedByE|=p≠1` ⟹ fixedByE≠⊥;
       `map_fixedSubgroup_eq_fixedSubgroup_quotient` で fixedByE=(C_H(W₁)).map mk' ⟹ C_H(W₁)⊄N;
       `typeP_fixedSubgroup_map`+`typeP_H_inf_centralizer_W1` で C_H(W₁).map H.subtype=W₂、
       N.map H.subtype=H₀ ⟹ W₂⊄H₀。**⚠ type-II 注意 (S11:2032)**: |W₂|>p 可だが image-order
       |W̄₂|=|fixedByE|=p を使った (|W₂| でなく)。
     - ✅✅✅ **B1 完成 (2026-06-29)**: **`chiefFactorQuotientHypothesis`** (S11、axiom-clean、全 13
       field): `S06.Hypothesis (↥M ⧸ H₀)` = Peterfalvi (8.4.d) の certain-type structural hypothesis。
       isComplement=`M_complement.map_mk'`, centralizer_W2=`chiefFactor_centralizer_W2bar`,
       W2_nontrivial=`chiefFactor_W2_not_le_H0`, W_odd=|W̄₁⊔W̄₂|∣|↥M⧸H₀|∣|↥M|∣|G| odd、他=image of
       cyclic/normal。引数 `[(chief.H0.subgroupOf M).Normal]` + hodd + hHall。
     - **`centralizer_W2` (= (8.4.d) crux)**: `C_{↥M⧸H₀'}(x̄) ⊓ K̄ = W̄₂` for x̄∈W̄₁^#。**3-step 分解**:
       1. ✅ **DONE (2026-06-29)**: `C_{↥M⧸H₀'}(x̄) = (C_{↥M}(x)).map mk'` = **一般補題
          `centralizer_map_mk'_eq_of_coprime_zpowers`** (S11、axiom-clean、reusable):
          `C_{Γ/N}(x̄) = (C_Γ(x)).map mk'` for Coprime|⟨x⟩||N|。⊆ = `coprime_fixedPoints_quotient_of_coprime_normal`
          (φ=MulAut.conj∘zpowers subtype, IsAInvariant ∵N normal, hg_fix ∵x̄,ḡ commute⟹power commute)。
          **これが (8.4.d) の本質的 content** (BG Lem 1.14 は p-group 限定で ⟨x⟩ 不適用、直接組立した)。
       2. ✅ **DONE**: `map_inf_map_of_ker_le` (一般、`ker f≤B ⟹ A.map f ⊓ B.map f=(A⊓B).map f`)。
       3. ✅ **DONE**: `chiefFactor_centralizer_inf_derived` (`C_{↥M}(x)⊓M'=W₂`、`centralizer_W1` +
          `S03h.centralizer_subgroupOf` transport)。
       ✅✅ **crux 全完了 (2026-06-29、3 lemma axiom-clean)**: **`chiefFactor_centralizer_W2bar`**
       (step1+2+3+lift 統合): `C_{↥M⧸H₀'}(x̄)⊓K̄=W̄₂` for x̄∈W̄₁^#。これで **B1 の最難 field
       (centralizer_W̄₂) 完成**。lift coprimality は `chiefFactor_coprime_H0_W1`+card chain。
     - `W_odd`: image of W₁⊔W₂ odd ← |G| odd。
   - **B1 def の home**: S12 (typePData_toS06Hypothesis 近傍) or 新 bridge leaf。`typePData_toS06Hypothesis`
     (S12:1062, L=M版) が subgroupOf-transport の template; B1 は mk'-image-transport 版。
3. **B2 (deep character bridge、次の phase、~3-5 反復見込み)**: §9 `chars.SOf chief.H0` (HU→M induced
   family) ↔ §6 induction-family {Ind^L_K̄ χ̄} on M/H₀。**精密 recipe (2026-06-29 scoped)**:
   - **K̄ ↔ HU 同定**: §6 K̄ = `((derivedInG M).subgroupOf M).map mk'` (B1 で構成)、`derivedInG M =
     data.H ⊔ data.U = HU` (`derivedInG_eq_fitting_sup_U`+`H_eq`)、§9 `huSub data` = HU realized in
     ↥M。⟹ K̄ = (huSub data).map mk' = HU/H₀。
   - **inflation bijection**: 𝒳(H₀) = `xiOf data chief.H0` = {χ∈Irr(huSub)|H⊄Ker, H₀⊆Ker} ↔
     {χ̄∈Irr(K̄)|H̄⊄Ker χ̄} via `inflate` (`compHom mk'`、InflationCharacter.lean)。infra 既存:
     `IsIrreducibleCharacter.compHom_of_surjective` (inflation 既約保存)、`inflate_apply_one` (degree)、
     `exists_inflate_eq_of_subset_characterKernel` (H₀⊆Ker char の surjectivity)、`inflate` injective。
   - **induction-inflation commute** (B2 crux、新規 general lemma、~100行): `Ind_H^G (compHom (f.subgroupMap H) χ̄)
     = compHom f (Ind_{H.map f} χ̄)` for `f:G→*Q surj`, `ker f≤H`, χ̄∈ClassFunction ↥(H.map f)。
     **proof 完全 mapped (2026-06-29、build は fresh-context 反復で)**:
     1. ✅ **DONE (2026-06-29)**: term equality = **`induceTerm_compHom_subgroupMap`** (S11、axiom-clean、
        general): `induceTerm H (compHom (f.subgroupMap H) χ̄) x g = induceTerm (H.map f) χ̄ (f x) (f g)`
        for `ker f≤H`。条件同値 = `Subgroup.comap_map_eq_self hker` + mem_comap; 値一致 = subgroupMap
        coe defeq `f(x⁻¹gx)` + map_mul/map_inv。
     2. ✅ **DONE (2026-06-29)**: fiberwise sum = **`sum_comp_mk'_eq`** (S11、axiom-clean、general):
        `Σ_{x:Γ} g(mk' N x) = |N| • Σ_q g q` (`sum_fiberwise_of_maps_to` + 各 fiber const + fiber card
        = **`card_fiber_mk'_eq`** : fiber ≃ N via x↦x₀⁻¹x)。⚠ `(g:=)` named arg は Fintype M 誤 synth →
        minimal invocation で解決。
     3. ✅ **DONE (2026-06-29)**: normalize = **`card_eq_card_subgroup_mul_card_map_mk'`**
        (|H|=|N|·|H.map(mk' N)|、first-iso `quotientKerEquivRange`)。
     ✅✅ **commute 全体 DONE = `induce_compHom_subgroupMap_mk'`** (S11、axiom-clean): `f=mk' N` 版
     `induce H (compHom ((mk' N).subgroupMap H) χ̄) = compHom (mk' N) (induce (H.map (mk' N)) χ̄)`。
     term eq + sum_comp + normalize で |N| 相殺 (ℂ: `invOf_eq_inv`+`mul_inv`+`inv_mul_cancel₀`)。
     **⟹ B2 最難所 (induction-inflation commute) 完成**。残 B2 = inflation bijection 𝒳(H₀)↔{χ̄|H̄⊄Ker} +
     reducibility 対応 (commute で φ=inflate(Ind χ̄) ⟹ inflation 既約保存で両向き)。次反復。
     ⟹ `induce H (inflate χ̄) g = compHom f (induce (H.map f) χ̄) g`。inflation 既約保存
     (`compHom_of_surjective` + 逆) で reducibility 両向き。
   - **reducibility 対応**: φ=Ind χ reducible (M-char) ⟺ Ind^L_K̄ χ̄ reducible (M/H₀-char) (inflation
     既約保存の両向き)。`{φ∈𝒮(H₀)|¬irr}` ↔ `{χ̄∈Irr(K̄)|¬irr(Ind χ̄)∧H̄⊄Ker}` の ncard bijection。
4. **B3**: (a) **|W̄₂|=p** (`Nat.card ((W₂.subgroupOf M).map mk') = chief.p`、`|fixedByE|=p` の
   W̄₂↔fixedByE iso、M/H₀↔H̄ identification 経由、~30-50行); (b) H=H̄ = (data.H.subgroupOf M).map mk'
   (≤K̄) で `card_reducible_Hnontrivial_induce_eq_W2_sub_one (chiefFactorQuotientHypothesis chief)`
   instantiate; (c) B2 bijection で `{φ∈𝒮(H₀)|¬irr}.ncard = §6 count = |W̄₂|-1 = p-1` → (9.9.b) discharge。
5. (9.10) de-opacify + exceptional 構造。

> **状況 (2026-06-29)**: §6 side + (8.4.d) bridge B1 (structural Hypothesis(M/H₀)) 完成 (全 axiom-clean)。
> 残 = B2 (inflation character bridge、最難所 = induction-inflation commute lemma) + B3 (|W̄₂|=p +
> instantiate)。本プロジェクトで「最難・最高コスト」と記された指標終盤の最後の山。

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
