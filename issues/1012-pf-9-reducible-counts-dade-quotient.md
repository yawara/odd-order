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
     **⟹ B2 最難所 (induction-inflation commute) 完成**。
   - **残 B2 = inflation bijection (realization plumbing、intricate but conceptually clear given commute)**:
     `{φ∈chars.SOf chief.H0 | ¬irr φ} ≅ {χ̄∈Irr(K̄) | ¬irr(induce K̄ χ̄) ∧ H̄⊄Ker χ̄}` (ncard 両 = p-1)。
     **key identifications**:
     - `huSub data = (derivedInG M).subgroupOf M` (∵ `derivedInG M = data.H⊔data.U` = hM'eq S11:383)
       ⟹ K̄ = `(chiefFactorQuotientHypothesis chief).K` = `(huSub data).map (mk' H₀')`、
       induceHU = `induce (huSub data)`。
     - **commute 適用**: `induce_compHom_subgroupMap_mk' (chief.H0.subgroupOf M) (hNH: H₀'≤huSub) χ̄`
       ⟹ `induceHU (inflate χ̄) = inflate (induce K̄ χ̄)`。Invertible 2 つ + DecidablePred は classical/Finite。
     - **inflation iso** (InflationCharacter.lean infra): `inflate_injective` + `exists_inflate_eq_of_subset_characterKernel`
       ⟹ Irr(K̄) ≅ {χ∈Irr(huSub)|H₀⊆Ker} (= xiSet の H₀⊆Ker 部); restriction で
       {χ̄|H̄⊄Ker}↔xiOf data chief.H0。
     - **reducibility 対応**: φ=induceHU(inflate χ̄)=inflate(induce K̄ χ̄)、inflation 既約保存
       (`compHom_of_surjective` + 逆) ⟹ ¬irr φ ⟺ ¬irr(induce K̄ χ̄)。
     - **ncard bijection**: 上記 chain で `{φ∈sOf|¬irr} ≅ {χ̄|¬irr(induce χ̄)∧H̄⊄Ker}`。
4. **B3**: (a) **|W̄₂|=p** (`chiefFactor_W2_not_le_H0` 系の card 版、`|fixedByE|=p` の W̄₂↔fixedByE iso); (b)
   H=H̄ = (data.H.subgroupOf M).map mk' で `card_reducible_Hnontrivial_induce_eq_W2_sub_one
   (chiefFactorQuotientHypothesis chief)` instantiate (= w̄₂-1 = p-1); (c) B2 bijection で
   `{φ∈𝒮(H₀)|¬irr}.ncard = p-1` → caseB_character_counts conjunct 2,3,4 discharge。
   > **状況**: §6 + B1 + B2 crux (commute) + bijection 基盤 = 完成 (全 axiom-clean)。残 = B2 bijection
   > assembly + B3。conceptually clear, mechanically intricate (§9 carrier 同定 + instance 管理)。

   **⚠ 2026-06-29 知見 (cont.¹⁶)**:
   - **§9-commute は standalone lemma で書けない** — `ClassFunction.induce` の RHS は ambient
     `↥M⧸H₀` の `Fintype` を `induceSum` の `∑ x` で要し、これは statement-level で `[Finite G]`
     からは synth されない (general commute は `[Fintype Γ]` 引数から `Fintype (Γ⧸N)` を得る)。
     かつ induceHU の内部 `letI Fintype ↥M` と statement の `[Fintype ↥M]` 引数で **Fintype diamond**
     リスク。⟹ **bijection assembly 内で `letI : Fintype ↥M` 1 つの下で `induce_compHom_subgroupMap_mk'`
     を inline 適用** (両辺同一 Fintype で diamond 回避)。inclusion `chiefFactor_H0_le_huSub`
     (H₀≤HU、commit `<this>`) は landed。
   - **|W̄₂|=p は cross-quotient** — W̄₂=(W₂.subgroupOf M).map (mk' H₀') は `↥M⧸H₀` 設定、
     `coprimeFrobeniusChiefFactor_card.2`=|fixedByE|=p は `↥data.H⧸chief.N` 設定。`chiefFactor_W2_not_le_H0`
     proof が両者の infra を持つ (hcard.2, hmap: fixedSubgroup.map mk'=fixedByE, hCHW1: .map H.subtype=W2)
     が、2 quotient (↥M⧸H₀ vs ↥H⧸N、H₀ vs N) の橋渡しが要 ⟹ assembly と同様 intricate。
     ⟹ `induce H (inflate χ̄) g = compHom f (induce (H.map f) χ̄) g`。inflation 既約保存
     (`compHom_of_surjective` + 逆) で reducibility 両向き。

   **⚠⚠ 2026-06-29 知見 (cont.¹⁷): bijection assembly は当初 recipe より大きい sub-phase**:
   - **target = `caseA_character_counts` (S11:3935) conjunct 1** = `{φ∈chars.SOf chief.H0|¬irr}.ncard = chief.p-1`
     (caseB 版も同様)。**ただし caseA_character_counts は 4-conjunct の大定理** (他: degree formula
     `φ 1 = q·u`、𝒮(H₀⊔C) irreducible 存在、𝒮(H₀⊔U') irreducible count) ⟹ (9.9.b) reducible count は
     1 conjunct のみ。残 conjunct は別途 (degree=induceHU_apply_one+commute、irreducible count=certain-type)。
   - **🛑 crux = induceHU の orbit 構造 (Pf (9.5)/(9.9) 行間、要careful read)**: induceHU は 𝒳 全体では
     **単射でない** — HU=M'◁M ゆえ Mackey/Clifford で M/HU≅W₁ が Irr(HU) に作用、induction は W₁-orbit を潰す
     (⟨Ind χ,Ind χ'⟩=Σ_{g∈M/HU}⟨χ,χ'^g⟩)。**但し reducible-inducing χ̄ は W̄₁-stable** (induce_K̄^L χ̄
     reducible ⟺ χ̄ が W̄₁ で安定 ⟹ orbit size 1) ⟹ **reducible subset 上では induceHU 単射**、counts 一致
     (|𝒮(H₀) reducible|=|{reducible χ̄}|=p-1)。⟹ 形式化要 = 「reducible⟹W̄₁-stable⟹induceHU InjOn」の
     Clifford/Mackey argument (§6 stability 構造依存) + Pf (9.5)/(9.9) の正確な statement 確認
     (Coq PFsection9.v 併読 or ChatGPT 相談が有効、[[feedback-ask-chatgpt-for-elided-gaps]])。
     **upstream-first ゆえ次の着手 = この orbit/injectivity の正確な定式化**。現状 `induceHU_mem_ZIrr` のみ。
   - **assembly 全 chain** (injectivity 後): `{φ∈sOf chief.H0|¬irr}` --(induceHU InjOn)--> `{χ∈xiOf|¬irr(induceHU χ)}`
     --(inflate iso + huSub⧸N_huSub≅K̄ transport)--> `{χ̄∈Irr(K̄)|¬irr(induce K̄ χ̄)∧H̄⊄Ker χ̄}` --(§6 count)--> |W̄₂|-1
     --(|W̄₂|=p)--> p-1。各 step に transport/instance friction。**実質 multi-iteration sub-phase**
     (§6+B1+B2 crux の hard math は完了、残は intricate Lean glue + injectivity prereq)。

   **✅✅ 2026-06-29 知見 (cont.¹⁸): assembly 大幅 de-risk — 鍵 tool 既存 (Pf (6.2) 流用)**:
   Coq `PFsection9.v` 併読 (ResIndXmu @ L1064: `Res_{HU}('Ind χ_s)=q·χ_s` via `cfclass_inertia big_seq1`
   = inertia singleton、injectivity @ L1068 = `congr1 'Res` + scalerK) で proof strategy 確定。**さらに
   repo に鍵 tool が既存**:
   - **`induce_eq_induce_iff_conj`** (`InducedIrreducible.lean:200`): `induce H θ = induce H ψ ↔ ∃g, conjBy g θ = ψ`
     (H◁G、Pf (6.2) step-4a の fibre 記述)。⟹ **inertia-stable θ (conjBy g θ=θ ∀g) では fibre singleton
     ⟹ induceHU 単射** = near-cite (orbit/injectivity prereq は新規大物でなく既存 machinery の適用)。
   - `card_smul_restrict_induce` (Mackey `|H|•Res(Ind θ)=∑_x conjBy x⁻¹ θ`)、`card_conjByOrbit_eq_index_inertia`
     (orbit size=inertia index)、`card_mul_inner_self_induce_eq_card_inertia` も既存。
   - **`huSub_normal` instance landed** (commit `<this>`): HU=M'◁M ⟹ induce_eq_induce_iff_conj 適用可。
   - §6 stability machinery (`conjByPerm`/`conjByMulEquiv` @ S06_CertainTypeClifford) 既存。
   ⟹ **assembly は cont.¹⁷ の悲観評価より tractable**。残 content = reducible⟹inertia-stable (§6 certain-type
   から、reducible μ_j は W̄₁-stable=I_L(χ̄)=L) + induce_eq_induce_iff_conj 適用 + inflate iso + |W̄₂|=p。

   **✅ cont.¹⁹ (commit `<this>`): 単射 lemma landed + stability source 特定**:
   - **`induce_injective_of_inertia_stable`** (`InducedIrreducible.lean`、general、axiom-clean):
     `(∀g, conjBy g θ=θ) → induce θ=induce ψ → ψ=θ`。`induce_eq_induce_iff_conj` の near-cite
     (予言通り)。⟹ 単射 piece 完成 (general/reusable)。
   - **stability source 特定** (Coq `PFsection9.v`): reducible⟹inertia-stable は **`def_IXmu` @ L1048**
     (`{in Xmu, forall s, 'I_M['chi_s]=M}` = 完全 inertia)、その source = **`sW1_Imu` @ L996**
     (`W1 ⊆ 'I[theta(mu_f i) %% H0]`)。即ち **reducible family の χ は inflate された HC-linear char
     ゆえ W₁ がその inertia に入る** (HU⊆I 常、HU·W₁=M ⟹ I_M=M)。⟹ §9 で要 = 「reducible-inducing χ∈xiOf
     は W₁⊆I_M(χ)」(certain-type linear-char 構造から)。次着手 = この W₁-stability (or inflate iso)。
   - **reducibility 対応**: φ=Ind χ reducible (M-char) ⟺ Ind^L_K̄ χ̄ reducible (M/H₀-char) (inflation
     既約保存の両向き)。`{φ∈𝒮(H₀)|¬irr}` ↔ `{χ̄∈Irr(K̄)|¬irr(Ind χ̄)∧H̄⊄Ker}` の ncard bijection。

   **✅ cont.²⁰ (commit `<this>`): reducibility correspondence core landed**:
   **`isIrreducibleCharacter_compHom_mk'_iff`** (`InflationCharacter.lean`、general、axiom-clean):
   `IsIrreducibleCharacter (compHom (mk' N) ψ) ↔ IsIrreducibleCharacter ψ` (任意 ψ:ClassFunction(G⧸N))。
   forward=`compHom_of_surjective`、backward=N⊆characterKernel (compHom n=ψ 1=degree) ⟹ `exists_inflate_eq`
   で =inflate χ̄ ⟹ `compHom_injective` で ψ=χ̄。⟹ commute (induceHU(inflate χ̄)=compHom(mk')(induce K̄ χ̄))
   と合わせ **φ=induceHU(inflate χ̄) reducible ⟺ induce K̄ χ̄ reducible** (reducibility 対応完成)。
   残 assembly = §9 W₁-stability (単射適用) + inflate iso (xiOf↔Irr(K̄)) + inline commute + |W̄₂|=p + ncard。
4. **B3**: (a) ✅✅ **|W̄₂|=p DONE (2026-06-30, commit 218e9226)**: **`chiefFactor_card_W2bar`** (S11、
   axiom-clean): `Nat.card ((W₂.subgroupOf M).map(mk' H₀')) = chief.p`。**明示 cross-quotient iso 不要** —
   W̄₂ と商 fixedByE=F.map(mk' N) を共に `|F|/|F⊓ker|` 形に分解 (`nat_card_quotient_subgroupOf_eq_card_map`
   + `card_eq_card_quotient_mul_card_subgroup`)、injective H.subtype で kernel 位数一致
   (|J₁|=|N⊓F|=|W₂⊓H₀|) + |F|=|W₂| ⟹ |W̄₂|=|fixedByE|=p。**type II 注意は解決** (|W₂|>p でも image は p)。
   (b) H=H̄ = (data.H.subgroupOf M).map mk' (≤K̄) で `card_reducible_Hnontrivial_induce_eq_W2_sub_one
   (chiefFactorQuotientHypothesis chief)` instantiate (= |W̄₂|-1 = p-1); (c) B2 bijection で
   `{φ∈𝒮(H₀)|¬irr}.ncard = §6 count = p-1` → (9.9.b) discharge。
5. (9.10) de-opacify + exceptional 構造。

> **状況 (2026-06-30 更新)**: §6 count + B1 (商 Hypothesis) + B2 crux (commute) + injectivity
> (`induce_injective_of_inertia_stable`) + reducibility correspondence (`isIrreducibleCharacter_compHom_mk'_iff`)
> + **B3a (|W̄₂|=p, `chiefFactor_card_W2bar`)** = 完成 (全 axiom-clean)。残 = **B2 inflation-bijection
> assembly** (W₁-stability で induceHU InjOn + inflate iso xiOf↔Irr(K̄) + commute inline + |W̄₂|=p で
> ncard chain → p-1) + B3b/c instantiate。bijection assembly は依然 intricate multi-iteration (§9 carrier
> 同定 + instance 管理) だが、構成要素は全て landed — 残は glue。次着手 = **W₁-stability**
> (reducible-inducing χ∈xiOf ⟹ W₁⊆I_M(χ)、`induce_injective_of_inertia_stable` を適用するため)。

**2026-06-30 知見 (B3b は inline)**: `chiefFactorQuotient_card_W2_eq_p` (S11、bridge: 商 hypothesis の
`card W̄₂ = p` = `chiefFactor_card_W2bar`) landed。但し §6 count `card_reducible_Hnontrivial_induce_eq_W2_sub_one`
の **standalone 再述は instance elaboration と衝突** — conclusion 型が `ClassFunction.induce h.K` を含み、
statement-level で `Fintype (↥M⧸H₀')` + `Invertible (card h.K)` を要求 (proof-body の haveI では遅い、§6 の
`variable` context が失われる)。⟹ **B3b count は §9 assembly 内で inline 適用** (local instances 下で
`h.card_reducible_Hnontrivial_induce_eq_W2_sub_one hW2H` → rw `chiefFactor_card_W2bar` → p-1)。standalone
count lemma は作らない。

**W₁-stability の Clifford 機構 (2026-06-30 scoped)**: reducible Ind_{HU}^M χ ⟺ I_M(χ)=M
(∵ M/HU≅Z/q prime ゆえ inertia は HU か M のみ; ⟨Ind χ,Ind χ⟩=[I:HU]、reducible⟺[I:HU]>1⟺I=M)
⟹ χ M-invariant (∀g, conjBy g χ=χ) ⟹ `induce_injective_of_inertia_stable` 適用可。infra =
`card_mul_inner_self_induce_eq_card_inertia` + prime-quotient dichotomy。次 = この「reducible ⟹ I=M」。

**✅ 2026-06-30 (commit a19cc41b): W₁-stability の核心 landed — prime-quotient 不要だった**:
`chiRestrict_conjBy_eq` (`S06_CertainTypeClifford`、axiom-clean): reducible-inducing column
`chiRestrict χ₂` は **`L`-invariant** (∀g∈L, conjBy g (chiRestrict χ₂)=chiRestrict χ₂)。reducible⟺column
(`induce_not_isIrreducible_iff`)、column=`Res_K μ` (`coe_chiRestrict`) ゆえ `L`-class function μ の制限で
共役不変 (`conj_eq`)。⟹ q が prime でなくても column は **全 L で固定** (inflate された W̄₁-stable 列ゆえ;
当初の「prime cyclic quotient」評価は不要、column の Res-構造が直接 full inertia を与える)。
⟹ `induce_injective_of_inertia_stable` を column に適用可。

**残 assembly (次着手)**: (1) **transport**: §6 column の `L=M/H₀`-invariance → §9 `inflate(chiRestrict χ₂)`
の `M`-invariance (conjBy を inflate/compHom 通す)。(2) reducible φ∈𝒮(H₀) ↔ column χ̄ の inflate iso +
reducibility correspondence (`isIrreducibleCharacter_compHom_mk'_iff` + commute、landed)。(3) ncard
bijection → p-1 (B3b count inline)。core piece は出揃った — 残は §9↔§6 transport glue。

**✅✅ 2026-06-30 (commit e1926427): source↔image injectivity landed (§6 level)**:
`induce_chiRestrict_injective` (`S06_CertainTypeClifford`、axiom-clean): `induce K̄` は reducible column 上で
injective (distinct χ₂ → distinct `Ind_K̄ (chiRestrict χ₂)`)。`chiRestrict_conjBy_eq` (L-inertia-stable) +
`induce_injective_of_inertia_stable` + `chiRestrict_injective`。⟹ reducible induced **image** 数 = column 数。

**✅✅✅ 2026-06-30 COMPLETE (commit 652fec2f): §9↔§6 bijection 完成 — (9.9.b)/(9.8.b) reducible
count 実証明・axiom-clean**: `reducible_count_sOf_H0` (S11、`[propext,Classical.choice,Quot.sound]`)
が `{φ∈𝒮(H₀)|¬irr}.ncard = p-1` を §9↔§6 全単射で証明、**caseA conjunct 1 + caseB conjunct 2 両方に
wire 済**。下記「完全実行レシピ」を全て landed:
- **Φ-identity** = commute `induce_compHom_subgroupMap_mk'` + transport `induce_compHom_subgroupCongr`
  (`g = subgroupCongr(K_eq.symm)∘subgroupMap`)。**全 instance を 1 つの `letI`-transparent scope に
  hoist** して Fintype/Invertible diamond 解消 (`induceHU` unfold は `letI` 透過性が鍵; `haveI` は
  opaque で rfl 不能)。
- **image 等式** = `exists_compHom_eq_of_subset_characterKernel` (inflation 全射) +
  `subset_characterKernel_compHom_iff` (kernel 対応) + `isIrreducibleCharacter_compHom_mk'_iff` (reducibility)。
- **InjOn** = `induce_injective_on_reducible` + `compHom_injective_of_surjective`。
- **W̄₂⊆H̄** (`H̄=hInHu.map g`) = `data.W2≤data.H` の element chase。
- **ncard chain** = `Set.InjOn.ncard_image` + `Nat.card_coe_set_eq` + §6 count + `chiefFactorQuotient_card_W2_eq_p`。
- **refactor**: `induce_compHom_subgroupCongr` を FeitThompson→InducedCharacter に上流移動 (S11 から
  cite 可に)、explicit `Invertible` binder + `subst;congr 1;Subsingleton.elim`。

**残 §9 (別 conjunct、reducible count とは独立)**: (9.9.b) degree=qu + membership 𝒮(H₀C) (caseB
conjunct 3) / (9.9.c) exceptional (caseB conjunct 4) / (9.8.b,c,d) (caseA conjunct 2,3,4) /
(9.10) `exceptional_case_frobenius_realization`。

**2026-06-30 精密分析 (caseB conjunct 3 = (9.9.b) degree+membership)**:
- **degree は free**: `caseB_degree_qu` が 𝒮(H₀C') 全体で degree=qu を既証明、`𝒮(H₀C)⊆𝒮(H₀C')`
  (C'≤C, `sOf_antitone`) ゆえ。**✅ landed `forall_mem_sOf_H0C_apply_one_eq_qu`** (commit a4676bc6)。
  ⟹ conjunct 3 は **membership に帰着**: reducible φ∈𝒮(H₀) → φ∈𝒮(H₀C) が分かれば degree は cite で済む。
- **✅✅✅ 2026-06-30 BREAKTHROUGH (commit 45e634a5): membership は cardinality で proven — full theta
  construction 不要だった**。`reducible_mem_sOf_H0C` (PROVEN): `𝒮(H₀C)⊆𝒮(H₀)` (`sOf_antitone`,
  H₀≤H₀C) ゆえ reducibles も subset; 両 count=p-1; **subset + 等 finite card ⟹ 全体一致**
  (`Set.eq_of_subset_of_ncard_le`, finite は p-1≠0 ∵ p prime)。⟹ 全 reducible 𝒮(H₀)-member は
  𝒮(H₀C) に既在。**caseB conjunct 3 (degree+membership) 完全 wire 済** (degree=`forall_mem_sOf_H0C_apply_one_eq_qu`,
  membership=`reducible_mem_sOf_H0C`)。当初の「deep Clifford crux (HC/H₀ 直積, theta family, Coq Part_a)」
  評価は **over-pessimistic だった** — cardinality が full construction を回避。
  - **残 = `reducible_count_sOf_H0C` (sorried)**: 𝒮(H₀C) の reducible count=p-1。`reducible_count_sOf_H0`
    の **PARALLEL** — `M/(H₀C)` certain-type hypothesis ((8.4.d) は M/H₀C でも成立、W̄₂'=W₂-image は
    依然 order p ∵ W₂∩H₀C=W₂∩H₀, W₂≤H・C≤U が H で trivial 交差)。
    **2026-06-30 build plan (foundation 着手済)**:
    - ✅ **`centralizer_W2bar_quotient` landed (commit dfc66c89)**: (8.4.d) centralizer crux を quotient
      kernel N' で generic 化 (N'≤M' + Coprime|W₁||N'| が input、core は N'-independent
      `chiefFactor_centralizer_inf_derived`)。`chiefFactor_centralizer_W2bar`=N'=H₀ instance。**最難 helper
      を H₀C 用に reusable 化**。
    - **残 foundation (各 generic 化 or H₀C instance)**: (a) Coprime|W₁||H₀C| (=Coprime|W₁||H₀|·|C|、
      `chiefFactor_coprime_H0_W1`+`typeP_coprime_U_W1` で C⊆U)、(b) H₀C≤M'.subgroupOf (H₀⊆H⊆M'・C⊆U⊆M')、
      (c) W₁⊓H₀C=⊥ (W₁⊓M'=⊥)、(d) W₂⊄H₀C (`chiefFactor_W2_not_le_H0`+W₂∩H₀C=W₂∩H₀)、
      (e) |W̄₂'|=p (`chiefFactor_card_W2bar` generic、|W₂|/|W₂∩H₀C|=|W₂|/|W₂∩H₀|=p)。
    - **次 step**: 上記 foundation で `chiefFactorQuotientHypothesis` を N'=H₀C へ instantiate
      (generic 化 or 並行 def) → bijection (`reducible_count_sOf_H0` を generic 化 or 並行) → count=p-1。
      bounded だが ~200 行 multi-iteration。§6 shortcut 不要は確定 (C̄ は §6 W-structure 外)。
- **⚠ caseA は独自 degree lemma 要**: caseA_character_counts は caseB を scope に持たない ⟹
  `caseB_degree_qu` cite 不可。(9.8.b) degree も caseA 版 chief-factor-constituent で別途。
- **⚠ caseA は独自 degree lemma 要**: caseA_character_counts は caseB を scope に持たない ⟹
  `caseB_degree_qu` cite 不可。(9.8.b) degree も caseA 版 chief-factor-constituent で別途。
- **(9.9.c)/(9.10)** = exceptional (C=⊥ ∧ u=(p^q-1)/(p-1) + Frobenius)。`quotientSemidirectFrobenius`
  free field 絡みで Singer field model 依存の見込み (別 deep)。

これらは reducible count とは別経路の deep §9 Clifford。frontier は「quick fill 枯渇、各片が bijection
並み」フェーズに入った。

---
（以下、完成前の分析メモ — 履歴として保存）

**🛑 残 = 単一 non-decomposable inline block (focused session 推奨)**: (9.9.b) conjunct 2 =
`{φ∈chars.SOf chief.H0|¬irr}.ncard = p-1` (S11:4549) は **§9↔§6 ncard 全単射の 1 つの inline 証明**:
合成写像 `χ̄ ↦ induceHU(inflate χ̄) = inflate_M(induce K̄ χ̄)` (commute) が §9 sOf-reducibles と §6 columns を
全単射。**commute は standalone 不可** (cont.¹⁶ の Fintype-diamond: induceHU 内部 letI vs general commute の
[Fintype ↥M]) ⟹ assembly 全体を `letI Fintype ↥M` 1 つの下で inline 構築。**全 core piece は landed**
(|W̄₂|=p / column L-不変 / induce-injective / inflate iso infra / commute / reducibility correspondence /
§6 source count) — 残は chars(Section11CharacterData)↔chiefFactorQuotientHypothesis の構造 bridge を張り、
inflate iso (xiOf↔Irr(K̄)) + commute + Set.ncard 全単射 を chain する **~100-150 行の inline glue**。
loop-fragment 不適 (分割不能・Fintype 管理重) ⟹ **focused session 推奨**。

**✅ 2026-06-30 (commit 9b3b916d): bijection の最後の 2 つの reusable piece landed (全 axiom-clean)**:
- **`subset_characterKernel_compHom_iff`** (`InflationCharacter.lean`、general): `f:H→*G`, χ̄:ClassFunction G,
  A≤H で `A⊆ker(compHom f χ̄) ⟺ A.map f⊆ker χ̄`。= **`H⊄ker χ ⟺ H̄⊄ker χ̄` transport** (§9 `hInHu⊄ker`↔§6 `H̄⊄ker`)。
  proof = `simp[Set.subset_def,SetLike.mem_coe,Subgroup.mem_map,mem_characterKernel,characterDegree_def,compHom_apply,map_one]` + 両向き。
- **`Hypothesis.induce_injective_on_reducible`** (`S06_CertainTypeClifford.lean`): `induce_chiRestrict_injective` の
  一般形 — reducible-inducing **全** χ∈Irr(K) で `induce χ=induce χ' → χ=χ'` (各 χ は column `chiRestrict χ₂`、
  `induce_not_isIrreducible_iff`+`induce_chiRestrict_injective`)。= bijection **InjOn** が要する形。

**📋 残 bijection の完全実行レシピ (2026-06-30 確定、focused session 用)**: target `caseB_character_counts`
S11:4549 sorry。全 transport 補題が repo 実在ゆえ機械的に組める:
- **set-up**: `N:=chief.H0.subgroupOf M`、`[N.Normal]` = `chiefFactor_H0_subgroupOf_normal chief` (haveI)。
  `hodd:Odd(card G)` (hG から)。`hHall:Coprime(card↥(derivedInG M))(card↥W1)` = `data.nontrivial.1`
  (=`hU:U≠⊥`) + S11:404-410 の derivation (`derived_complement.card_mul`+`typeP_coprime_{H,U}_W1`)。
  `h:=chiefFactorQuotientHypothesis chief hodd hHall`。`q:=mk' N`。`KbarM:=(huSub data).map q`。
  `hKeq:h.K=KbarM` = `chiefFactorQuotientHypothesis_K_eq`。`letI Fintype ↥M` + Invertible 群を 1 つの scope に。
- **Φ** (§6→§9): `χ̄:Irr(KbarM) ↦ induceHU data (compHom (q.subgroupMap (huSub data)) χ̄)`。
- **commute**: `induce_compHom_subgroupMap_mk' N (chiefFactor_H0_le_huSub data chief) χ̄`
  ⟹ `induceHU(compHom(q.subgroupMap huSub)χ̄)=compHom q (induce KbarM χ̄)` (inline、両辺同一 Fintype↥M)。
- **B' set** (§6 columns): `{χ̄:Irr(KbarM)|¬irr(induce KbarM χ̄)∧¬(H̄⊆ker χ̄)}`、H̄=`hInHu.map(q.subgroupMap huSub)`。
- **image 等式** `{φ∈sOf chief.H0|¬irr}=Φ''B'`: 
  - 順 (φ∈§9→Φ''B'): φ=induceHU χ, χ∈xiOf chief.H0 (H₀⊆ker χ ∵ ker(q.subgroupMap huSub)=`(N).subgroupOf huSub`)。
    `exists_compHom_eq_of_subset_characterKernel` (S11:4382 が同型 pattern) で χ=compHom(q.subgroupMap huSub)χ̄。
    χ̄∈B': ¬irr ← commute+`isIrreducibleCharacter_compHom_mk'_iff`; H̄⊄ker ← `subset_characterKernel_compHom_iff`。
  - 逆 (Φ''B'⊆§9): compHom χ̄∈xiOf chief.H0 (H⊄ker←kernel iff、H₀⊆ker←ker(map)⊆ker(compHom))+¬irr φ←commute。
- **InjOn Φ on B'**: Φχ̄=Φχ̄' →(commute)→ compHom q(induce KbarM χ̄)=compHom q(induce KbarM χ̄')
  →(`compHom_injective_of_surjective`)→ induce KbarM χ̄=induce KbarM χ̄' →(transport hKeq + `induce_compHom_subgroupCongr`)→
  induce h.K (...)=induce h.K (...) →(`induce_injective_on_reducible`)→ χ̄=χ̄' (h.K↔KbarM 同定後)。
- **ncard**: `Set.ncard_image_of_injOn` で `(Φ''B').ncard=B'.ncard`; `B'.ncard=Nat.card B'`
  (`Set.Nat.card_coe_set_eq`); `rw[hKeq]` で B' を Irr(h.K) 形に → §6 count
  `h.card_reducible_Hnontrivial_induce_eq_W2_sub_one hW2H` (hW2H:`h.W2.subgroupOf h.K≤H̄'`、`data.W2≤data.H`
  =`(data.W2_le ·).1` + map/subgroupOf_mono) + `chiefFactorQuotient_card_W2_eq_p` ⟹ p-1。
  ⚠ `rw[hKeq]` が H̄ (=hInHu.map…) と §6 の H̄' を同定する必要 — H̄=KbarM 設定 vs H̄'=h.K 設定。
  ここが唯一の非自明 glue (両 H̄ が同一 underlying 部分群 = (data.H.subgroupOf M).map q を Set 同定)。
- **下流 conjunct** (S11:4550 degree+membership / 4551 (9.9.c)): degree=qu は `induceHU_apply_one_eq_q_mul`+
  χ̄(1)=1 (column linear); membership 𝒮(H₀C)・(9.9.c) は別途 (B' の column が C-trivial の構造)。

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
