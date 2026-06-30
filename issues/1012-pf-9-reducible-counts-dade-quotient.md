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

   **✅✅ 2026-06-30 (commit f8d302fa): Coq `nb_redM` 併読で設計確定 + 構造入力 2/3 landed**:
   Coq `PFsection9.v` の `nb_redM K` (L787) を精読 — 還元 count `count redM (S_ K) = p-1` は
   **generic K で証明**され、H₀ と H₀C は共に instance。統一条件は **`K ◁ M` ∧ `K ⊆ HU` ∧
   `K ∩ H = H₀`** の 3 つだけ ((a)-(e) の個別 foundation はこの 3 つから従う:
   K≤HU ⟹ Coprime|W₁||K| (hHall) ・W₁⊓K=⊥ ・K≤M'; K∩H=H₀ ∧ W₂≤H ⟹ W₂∩K=W₂∩H₀ ⟹ W₂⊄K ∧
   |W̄₂'|=p)。⟹ 「parallel quotient を一から作る」でなく **`chiefFactorQuotientHypothesis` /
   `reducible_count_sOf_H0` を generic N' (3 条件) で一般化し、H₀/H₀C を instance 化**するのが正。
   Coq L834-835 は K=H₀C の `K∩H=H₀` を `group_modl` (Dedekind) + `tiHU` (H⊓U=1) で証明 — Lean でも同型。
   - **landed (S11, axiom-clean)**: `chiefFactor_H0supC_inf_H_eq_H0` ((H₀⊔C)⊓H=H₀, Dedekind crux =
     統一条件) + `chiefFactor_H0supC_le_derived` (H₀C≤M'=HU)。= 構造入力 2/3。
   - **残 1/3 = H₀C ◁ M** (Coq `Ptype_Fcore_extensions_normal` L240)。`M ≤ N(H₀⊔C)` を
     `M=⟨H,U,W₁⟩` の生成元別に (各 g で `conj g • (H₀⊔C) = (conj g•H₀)⊔(conj g•C)`、H₀ は M-normal
     ⟹ gH₀g⁻¹=H₀、残 = gCg⁻¹⊆H₀⊔C):
     - **H ≤ N(H₀C)**: H≤M≤N(H₀) + hCh⁻¹⊆H₀C (∵ `commutator_cSub_H_le_H0` [C,H]≤H₀ ⟹ hch⁻¹=[h,c]·c∈H₀·C)。
     - **U ≤ N(H₀C)**: U≤M≤N(H₀) + C◁U (`cSub_subgroupOf_U_normal`)。
     - **✅✅ crux = W₁ ≤ N(C) DONE (commit 4f2bf341): `cSub_normalized_by_uW1`** (S11、axiom-clean):
       `data.U⊔data.W1 ≤ N_G(cSub)`。C=`ker(uActionHom)` を L=↥(U⊔W₁) 内で `U'⊓ker(quotientMulAutHom)`
       と realize (`map_comap_eq`+`comap_ker`)、両者 L-normal (U'=Frobenius `typeP_uW1_frobenius.isNormal`、
       kernel=`MonoidHom.normal_ker`)⟹inf も L-normal。L の normal は L.subtype 押し出しで ↑(U⊔W₁) 全体に
       正規化 (`le_normalizer_map`+`normalizer_eq_top`+`range_subtype`、`← MonoidHom.range_eq_map`)。
     - **✅✅✅ 組立 DONE (commit 57f9239e): `chiefFactor_H0supC_subgroupOf_normal`** (S11、axiom-clean)。
       ⟹ **3 構造入力 (∩H=H₀ / ≤HU / ◁M) 全完成**。下記レシピ通り landed:
       `(normal_subgroupOf_iff_le_normalizer hH0CleM).mpr (M ≤ N(H₀⊔C))`。M≤N(H₀⊔C) を:
       - **helper `key`** (`∀g∈Hs, toConjAct g•K≤K → Hs≤N(K)`): `conjAct_pointwise_smul_iff` +
         le_antisymm、逆向きは `pointwise_smul_le_pointwise_smul_iff.mpr (hle g⁻¹)` + `←mul_smul,←map_mul,
         mul_inv_cancel,map_one,one_smul`。
       - **U⊔W₁ ≤ N(H₀C)**: `le_inf (U⊔W₁≤M≤N(H₀)) (cSub_normalized_by_uW1)` ▸
         `Subgroup.normalizer_inf_normalizer_le_normalizer_sup chief.H0 (cSub data chief)`。
       - **H ≤ N(H₀C)**: `key` で、`toConjAct h•(H₀⊔C)≤H₀⊔C` を `smul_sup`+sup_le。H₀-part=
         `conjAct_pointwise_smul_eq_self (chief.H0_normalized_by_M (H_le_M data hh))`。cSub-part: x∈toConjAct h•cSub
         ⟹ `mem_pointwise_smul_iff_inv_smul_mem` で c₀:=(toConjAct h)⁻¹•x=h⁻¹xh∈cSub (`ConjAct.smul_def`+
         `ofConjAct_inv`+`ofConjAct_toConjAct`)、x=⁅h,c₀⁆·c₀ (`group`)、⁅h,c₀⁆∈H₀ (`commutator_mem_commutator hh hc₀`
         +`commutator_comm`+`commutator_cSub_H_le_H0`) ⟹ x∈H₀⊔cSub (`mul_mem le_sup_left le_sup_right`)。
       - **M≤H⊔U⊔W₁**: `M=derivedInG M⊔W₁` (`M_complement.sup_eq_top` を `map_sup`+`subgroupOf_map_subtype`+
         `inf_of_le_left`+`⊤.map subtype=M` で G 化) + `derivedInG M=H⊔U` (`derivedInG_eq_fitting_sup_U`+`H_eq`)
         + `sup_assoc` ⟹ `M ≤ H⊔(U⊔W₁)` で `sup_le hH hUW1` に流す。
     その後 generic count refactor (chiefFactorQuotientHypothesis を N' (3条件: ◁M / ≤HU / ∩H=H₀) 一般化 +
     H₀/H₀C instance)。

   **✅✅ 2026-06-30 (commit 248e268e): generic count refactor step 1 — hypothesis 層 一般化**:
   - `chiefFactorQuotientHypothesisGen` (S06.Hypothesis(↥M⧸N') を generic N' (◁M, ≤M', W₁⊓N'=⊥, ¬W₂≤N')
     で構成)。`chiefFactorQuotientHypothesis` (H₀) は delegate (bridge lemmas + reducible_count_sOf_H0 不変)。
   - H₀C instance 入力: `chiefFactor_W1_inf_H0supC_subgroupOf_eq_bot` + `chiefFactor_W2_not_le_H0supC`。
   - 残 (次 iteration、reducible_count_sOf_H0C へ): **A. generic |W̄₂'|=p** (H₀C 版): `Nat.card((W₂.subgroupOf M).map(mk' N'))`
     = |W₂.subgroupOf M|/|W₂.subgroupOf M ⊓ N'`、kernel 一致 `W₂⊓H₀C=W₂⊓H₀` (W₂≤H, chiefFactor_H0supC_inf_H_eq_H0)
     ⟹ H₀ 版 (`chiefFactor_card_W2bar`) と同値 = p。**B. `reducible_count_sOf_H0` を carrier K で一般化**
     (~150 行、chief.H0→K、H₀-specific lemma → Gen + 一般 K_eq `chiefFactorQuotientHypothesisGen_K_eq` +
     K≤huSub=hN'le + |W̄₂|=p 入力)。**C. H₀/H₀C instantiate** → `reducible_count_sOf_H0C` 実証明。
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

## ⚑ lane-a endgame 状況 (2026-06-30, 要判断)

**還元 count 中核 = 完了** (H₀C reducible count、本 issue の "最難" piece、sorry-free)。**残 lane-a は
全て一様に deep FT endgame** — tractable な pivot 先は無い:
- §9: caseA conjunct b degree (`chiefFactor_caseA_char_inertia` = non-Galois Hpart Clifford 解析、
  caseB inertia infra 全体 ~150 行規模の analog)、caseB (9.9.c)、(9.10) Singer。
- §10-13 (S12): `typeII_derived_frobenius` (10.7)、`typeII_coherence_contradiction_estimate` (10.8)、
  `exists_zeta_residual_not_orthogonal` (11.8 = 唯一の bare FT spine sorry)、`typeV_forces_coherence` (10.10)。

**進め方**: deep だが incremental に grind 可 — caseA inertia は 1 iteration = 1 supporting lemma の
ペースで caseB inertia infra を analog 構築。難所の数学が真に impasse なら **ChatGPT 相談**
([[feedback-ask-chatgpt-for-elided-gaps]]、strongest model) を併用。

**✅✅ 2026-06-30: inertia plumbing 4 層 全 generalize 完了 (build-green、commits dd3576fe→1203f462)**:
`inertia_eq_hcInHu_of_inf_le` / `inertia_inf_uInHu_le_cInHu_of_realized` /
`caseB_inertia_realized_of_charInertia` / `caseB_char_inertia_inflation_of_core` — 各層を θbar-generic
な hypothesis で parametrize、caseB は delegate。⟹ caseA inertia chain は parametrized 連鎖の trivial
適用 + 単一 core `chiefFactor_caseA_char_inertia` に還元。

**残 (deep)**: (1) **core `chiefFactor_caseA_char_inertia`** — caseB core は θ nontrivial で g 固定⟹
g trivial だが caseA では一般 θ で偽; reducible-relevant θbar (W₁-transitive Hpart 対称) 限定で成立。
(2) caseA_exists_for_reducible + (3) caseA_degree_qu + wiring。

**🛑 2026-06-30 重大発見: caseA core は (9.7) case-a 構造の de-opacify に gated**:
`CliffordCaseAData` の `W1_transitive_on_parts` / `quotient_factors_cyclic_order_a` /
`Ubar_embeds_product` は **opaque な bare `Prop` field** (trivial `_holds`)。⟹ core が要する W₁-transitivity
は **usably 形式化されていない scaffold**。caseB は対応する genuine content を standalone lemma
(`chiefFactor_caseB_action_fpf` 等) + `hcaseB` (既約性 hypothesis) で供給 — caseA も同様に **(9.7)
case-a 構造 (H̄=⊕Hpart_i 直積, W₁ transitive permute, Ū embeds in product) の concrete lemma/hypothesis**
が必要。これは genuine な §9 Clifford 形式化 = substantial upstream piece。
⟹ **caseA degree = inertia plumbing (✅完了) + (9.7) case-a 形式化 (deep) + core + assembly**。

**✅ 2026-06-30 精緻化: (9.7) case-a は concrete 構築済・opaque 露出 (de-opacify は「露出」、scratch でない)**:
producer (chiefFactor_clifford_U_dichotomy の case-a 枝、S11:4288-4316) は **Hpart を concrete に構築**:
`Hpart j = act.φ ↑(e.symm j) • S₀` = 単一 U-invariant order-p factor S₀ の **W₁-orbit translate**
(`exists_supIndep_aInvariant_family_of_iSup` で S₀ から q 個の supIndep aInvariant family を生成)。
⟹ W₁-transitivity は **construction に implicit** だが usable field 化されてない (`:= True`)。
**de-opacify = CliffordCaseAData に orbit 構造 (S₀ generator, act, orbit indexing) を usable field
として carry + W₁-transitivity を lemma 化** (structure + producer refactor、plumbing より重いが grindable)。
その後 core (W₁-symmetric θbar stabilizer) → caseA_exists → degree_qu。inertia plumbing は reusable 基盤。

**✅✅ impasse 解消 (2026-06-30、Coq-first で発見)**: 「W₁-symmetric stabilizer」framing は誤り
だった。Coq `PFsection9.v` `def_Itheta` (L938-949) が **inertia θ̄ = HC を直接証明**:
- 還元 χ の chief-factor 構成 θ̄ = `cfBigdprod defHbar f` = **q 個の order-p Hpart factor H̄_i 上の
  *nontrivial* linear char の積** (f ∈ `Ftheta` = pffun_on で全成分 nonzero)。
- **per-factor (`inertia_irr_prime`, L948)**: order-**p** (prime) 群の nontrivial char の U-stabilizer
  = centralizer。理由 = **Aut(ℤ/p)=(ℤ/p)* は nontrivial char に *自由*作用** ⟹ char 固定の U-elt は
  その factor を中心化。
- **`inertia_bigdprod_irr` (L947)**: 積 char の inertia = 各 factor inertia の ∩。
- ⟹ ∩(per-factor centralizers) = C_U(H̄) = **C** ⟹ inertia θ̄ = HC。
私は「新しい W₁-対称論」を探して詰まったが、実際は **per-factor order-p free-action という routine な
論証**を見落としていた (= reconstruction gap, not research gap、[[feedback-ask-chatgpt-for-elided-gaps]]
の典型)。**Coq-first check で発見** (ユーザー 2026-06-30 指針)。

**Lean 形式化 path (clear)**: (1) de-opacify (9.7): Hpart 構造を露出 (producer の supIndep family)。
(2) **per-factor stabilizer**: order-p 群の nontrivial char → stabilizer=centralizer (Aut(ℤ/p) free)。
(3) bigdprod inertia (∩) → (4) inertia θ̄=HC → (5) inertia plumbing (✅) → caseA inertia=HC → degree u。

**✅ 2026-06-30 cleaner path 発見 (bigdprod permutation 機構を回避)**: type-P では **U が各 Hpart factor を
正規化** (producer の S₀ は U-invariant `hS₀inv`、かつ W₁≤N(U) ∵ U◁U⋊W₁ Frobenius ⟹ 各 W₁-translate
S₀^w も U-invariant: u S₀^w u⁻¹ = w (w⁻¹uw) S₀ (…)⁻¹ w⁻¹ = w S₀ w⁻¹、w⁻¹uw∈U)。⟹ U は **diagonal 作用**
(factor を permute しない)。⟹ 議論:
- g∈U が regular θ̄ (各 factor で nontrivial) を固定 ⟹ 各 factor で θ̄|_{Hpart_i} を固定 (factor U-invariant)。
- Hpart_i order p ⟹ nontrivial char の stabilizer = centralizer (Aut(ℤ/p)=(ℤ/p)* free、既存
  `inertia_eq_of_freeAction` 系 @ ConjugationBrauer.lean:277 が近い infra)。
- g が全 factor を中心化 ⟹ H̄=⟨Hpart_i⟩ を中心化 ⟹ g∈C。
⟹ **bigdprod inertia の permutation 機構不要**。必要 piece: (A) Hpart U-invariance、(B) θ̄ regular ⟹
θ̄|_{Hpart_i} nontrivial、(C) per-factor free-Aut stabilizer、(D) 全 factor 中心化⟹H̄ 中心化。
既存 infra: `inertia_eq_of_freeAction`, inertia transfer (`mem_inertia_compHom_iff`)。

**2026-06-30 API survey (piece C の framework-fitting)**: 数学は自明 (faithful char fixed by auto ⟹ id)
だが Lean は API-building 要: `characterKernel` は **Set** (`{g|χ g=χ 1}`、S03:378)、Subgroup 版なし。
piece C 鎖 = (i) irreducible char of abelian K は linear (degree 1) [mathlib/repo 要確認]、(ii) nontrivial
linear of prime-order K は faithful (characterKernel={1}、kernel-subgroup の order∣p 論)、(iii) faithful θ
+ θ(αx)=θx ⟹ α=1 (injective)。**caseA degree = clear math + substantial Lean API-building** (mechanical
plumbing と違い careful work)。grind 順: piece C (faithful-char API) → de-opacify (9.7) (CliffordCaseAData に
Hpart の SupIndep/iSup/U-invariance を field 追加、producer の `exists_supIndep_aInvariant_family_of_iSup`
出力 `hexist.choose_spec` から、Fin q reindex 経由) → 還元χ⟹θbar regular → 組立 → core → plumbing → degree u。

## 進捗サマリ (2026-06-30 更新)

**✅✅✅ 還元 count (9.8.b)/(9.9.b) 全完成 (sorry-free, axiom-clean)** — issue 1012 の中核:
- `reducible_count_sOf_K` (generic carrier、Coq `nb_redM`) + `chiefFactorQuotientHypothesisGen`
  (commit 6c19150d, 248e268e)。
- H₀C 構造入力 4 本 (∩H=H₀ / ≤M' / W₁⊓=⊥ / ¬W₂≤ / ◁M) + |W̄₂'|=p
  (`chiefFactor_card_W2bar_H0supC`、helper `nat_card_map_mk'_eq_of_inf_eq`、commit 0cee8e67)。
- ⟹ `reducible_count_sOf_H0` / `reducible_count_sOf_H0C` 両方 実証明、`reducible_mem_sOf_H0C` honest、
  caseB conjunct 3 (degree+membership) 完全 honest。

**残 §9 (還元 count とは別経路、各 substantial な新 machinery 要)**:
- **caseA conjunct b (degree+membership)**: membership ✅ citeable (`reducible_mem_sOf_H0C hG chars`、
  commit f92cf378 で case-agnostic 化済)。degree = **要 `caseA_degree_qu` (9.8.a-analog)** =
  caseA chief-factor-constituent machinery (`caseB_exists_chiefFactorConstituent` (S11:4880) の
  caseA 版)。χ∈𝒳 の χ(1)=u は定義から自明でない (xiSet=`{χ|H⊄ker χ}` のみ、degree 条件なし) — 真の定理。
  **次 iteration の最有力** (caseB 機構の直接 analog、doc 順最上流)。
- **caseA conjunct c (9.8.c)**: ∃ irreducible degree qu in 𝒮(H₀C)。
- **caseA conjunct d (9.8.d)**: irreducible count 下界 in 𝒮(H₀U')。
- **caseB conjunct 4 (9.9.c)**: 𝒮(H₀C') に irr 無 ⟹ C=⊥ ∧ u=(p^q-1)/(p-1) (exceptional)。
- **(9.10) `exceptional_case_frobenius_realization`**: `quotientSemidirectFrobenius` free field +
  Singer field model 依存 (別 deep)。
- **`sibleyTarget_H0C`**: coherence wiring。

**注**: 還元 count (中核) 完了後、残は各々 caseB constituent 並みの新 machinery を要する phase。
fresh context で 1 つずつ。次着手 = caseA degree machinery。

**caseA degree machinery — Coq (9.8) 精読 (2026-06-30、`PFsection9.v` L840-940 `typeP_nonGalois_characters`)**:
- (9.8.a) `Part_a` = `{in X_ H0, forall s, a ∣ χ(1)}` (**divisibility**, 等式でない)。inertia
  `T='I_HU['chi_t]` + H̄ の `bigdprod` 分解 (`cfBigdprod_Res_lin`) 経由 — 長い (L883-940)。
- (9.8.b) reducibles `mu_` = `{in mu_, isIndHC mu_j}`、`isIndHC zeta := zeta 1=qu ∧ zeta∈S_H0C ∧
  ∃ linear xi:'CF(HC), zeta='Ind xi`。⟹ **caseA conjunct b の degree qu = mu_j が HC の linear char
  から induced (degree [M:HC]=qu)**。mu_j は `primeTIred` (Dade W₁/W₂ prime-TI 構造)。
- **Lean 写像**: 還元 φ∈𝒮(H₀) = induceHU(inflate χ̄)、χ̄=column (chiRestrict)、degree=q·χ̄(1)。
  degree qu ⟺ **χ̄(1)=u** (§6 column の degree=u)。これが (9.8.a)/(9.9.a) の本体 = caseA/caseB
  共通の column-degree=u。**要調査**: 既存 §6 `Hypothesis` から column degree=u が出るか (W̄₁-inflation
  の degree、`card_reducible_…` 近傍)。出れば caseA/caseB 両 degree が §6 経由で case-agnostic に取れる
  可能性 (caseB_degree_qu の constituent 経路と別ルート)。
- **状況**: 残 §9 は全て deep (caseA constituent/exceptional/Singer/§14-gated sibleyTarget)。
  還元 count 中核は完了。各 deep piece は fresh context で。

**❌ §6 column-degree shortcut は無効 (2026-06-30 確認)**: column χ̄=`chiRestrict χ₂`=`Res_K(μ_{0j})`、
χ̄(1)=μ_{0j}(1) (§6 columnFamily grid char)。§6 は generic certain-type framework ゆえ μ_{0j}(1) を
u に pin する lemma **無し** (u=[U:C] は §9-specific)。⟹ degree qu (φ(1)=q·χ̄(1)=qu ⟺ χ̄(1)=u) は
**(9.8.a)/(9.9.a) 本体** = §9-specific constituent 解析が必須、shortcut 不可。

**⟹ caseA degree build plan (次 iteration、deep)**: `caseA_exists_chiefFactorConstituent` (caseB の
analog、但し inertia は非 HC=non-Galois split) → `caseA_degree_qu` (χ(1)=u on 𝒳(H₀C'))。crux =
caseA inertia 解析 (CliffordCaseAData の Hpart 直積構造経由)。Coq `Part_a` (L883-940) +
`isIndHC` (reducible mu_j=Ind linear HC char ⟹ degree qu) 参照。**caseB-constituent 並みの multi-iteration。**
membership half は ✅ (`reducible_mem_sOf_H0C hG chars`、case-agnostic 済)。

**❌ inertia=HC shortcut も無効 (2026-06-30 確認)**: `inertia_eq_hcInHu` (S11:4115) は
`caseB.actsIrreducibly` (U が H̄ 上既約) を要求 — caseB-specific。caseA (non-Galois) では θ₀ の inertia≠HC
ゆえ caseB_degree_qu の「χ=Ind_HC(linear)⟹degree u」機構は **reducibles にも直接転用不可**。
⟹ caseA reducible degree は **CliffordCaseAData.Hpart 直積構造経由の inertia 解析が必須**
(Coq Part_a の non-Galois 版)。= 真の deep piece、case-agnostic 経路は全て排除済。

**✅ crux 精密 localize 完了 (2026-06-30)**: caseA conjunct b degree の唯一の欠落 piece =
**`inertia θ₀ = HC for reducible-inducing χ`**。`caseB_degree_qu` の構成要素を分解すると、
**case-agnostic で既存**: constituent 存在+linearity (`caseB_exists_chiefFactorConstituent` の
step 1/2/4)、degree extraction `apply_one_eq_index_of_liesOver_linear_inertia` (χ over θ₀ (inertia I,
linear) + ψ (linear) ⟹ χ(1)=[HU:I])、index `[HU:HC]=u` (`index_hcInHu_eq_relindex_cInHu` +
`index_cInHu_subgroupOf_uInHu_eq_u`)。**caseB-specific は `inertia_eq_hcInHu` のみ** (S11:4115、
`≤` 方向の `inertia_inf_uInHu_le_cInHu` が U-既約 `hcaseB` を使用 = U-elt が θ₀ 固定⟹H̄ 中心化)。
caseA (non-Galois) では一般 χ で inertia≠HC だが、**reducible χ (M-invariant) は W₁ が Hpart factors を
transitive permute ゆえ全 factor 対称 ⟹ inertia=HC** が成り立つはず (要 Hpart-inertia 証明、Coq
PFsection9 `Part_a` L883-940 の reducible 部分)。⟹ build = `caseA_inertia_eq_hc_for_reducible`
(Hpart 解析) → 残は case-agnostic machinery を caseB と同形に組むだけ。**well-delimited な deep piece**。
**注 (FT spine)**: (10.7) typeII_derived_frobenius が要するのは (9.8.b)+(9.9.b)+(9.10)。(9.9.b) は
caseB conjunct 3 込み完了、(9.8.b) は count 完了 + **degree (caseA conjunct b) が残**。⟹ FT-spine-critical
残 §9 = **caseA conjunct b degree** + **(9.10)** のみ (caseA c/d・caseB 9.9.c は (10.7) 非依存の可能性大)。

## 完了条件

S11 の caseB_character_counts / caseA_character_counts / exceptional_case_frobenius_realization が
sorry-free (上流 §6 obligation cite は可)。**還元 count 部分は完了**、残は上記 (9.9.c)/(9.10)/caseA c/d。

## 下流 (unblock するもの)

(10.7) typeII_derived_frobenius (needs (9.8.b)/(9.9.b)/(9.10)) → (10.8) S_not_coherent →
(11.8) exists_zeta_residual_not_orthogonal → card_kappaHall_lt_of_isTypeIIIorIV (FT spine)。
∴ lane-a endgame 全体がこの quotient Dade framework に bottom-out。「最難・最高コストの指標終盤」。

## 参照

- `caseB_degree_qu` (9.9.a, 完成): S11_MaximalII_III_IV.lean、commit ab2b1557 系。
- 原典: Pf (9.8)/(9.9)/(9.10) = `references/peterfalvi/04.11_*`; (4.5)/(4.7) = `04.6_*`。
- 関連: issue 2030 (count-statement audit)、notes/peterfalvi/s10_13_maximal_structure.md §12。


## 進捗 2026-06-30 (caseA inertia core 実証明完了)

**caseA degree の inertia 核を完全形式化** (当初「research impasse」と誤判定 → Coq-first `def_Itheta`
で routine reconstruction と判明 → 完遂)。7 commits:
1. `injective_of_prime_card_of_ne_one` — prime-order group の nontrivial char は injective。
2. `mulAut_eq_one_of_fixes_ne_one_hom` — それを固定する auto は id。
3. `mulAut_eq_one_of_fixes_irr_ne_trivial_of_prime_card` — per-factor stabilizer (IrreducibleCharacter
   framework、LinearCharacter.lean の `exists_linearIrreducibleCharacter_eq_of_isMulCommutative` bridge)。
4. `mulAut_eq_one_of_eq_id_on_iSup` — piece D: spanning family 上 trivial な auto は id。
5. `mulAut_eq_one_of_fixes_regular_on_prime_span` — **assembly**: regular char を固定する auto on
   prime-span は id (pieces C+D+bridge を element-wise per-factor で合成)。
6. **de-opacify CliffordCaseAData**: `Hpart_iSup` (spanning) + `Hpart_aInvariant` (U-invariance) 露出、
   producer `clifford_caseA_data` で証明 (spanning は exists_supIndep choose_spec を Fin q reindex)。
7. **`chiefFactor_caseA_char_inertia`** = caseB core の analog。regular θ (各 order-p Hpart 上 nontrivial)
   を固定する φ_U(g) は =1。assembly を de-opacified 構造で instantiate。axiom-clean、full build green
   (3889 jobs)。

**残 (caseA conjunct b degree への接続)**:
- **(9.8.b) regular**: reducible χ ⟹ 構成 θ̄ が各 Hpart summand 上 nontrivial (= regular)。これが
  `chiefFactor_caseA_char_inertia` の `hreg` を供給。Clifford 還元 (reducible ⟺ regular) の content。
- **plumbing 配線**: caseA core を既存の parametrized inertia plumbing (`inertia_eq_hcInHu_of_inf_le` /
  `caseB_inertia_realized_of_charInertia` / `caseB_char_inertia_inflation_of_core` — core を引数に取る)
  に通して caseA inertia=HC → degree u → `caseA_character_counts` conjunct b。


## caseA degree (conjunct b) wiring plan — Coq PFsection9 併読 (2026-06-30)

Coq `typeP_nonGalois_characters` (L845, = Pf (9.8)) の核心構造 `isIndHC` (L840):
```
isIndHC zeta := [/\ zeta 1 = (q*u), zeta ∈ S_ H0C & ∃ xi : CF(HC), xi linear & zeta = Ind xi]
```
- **(b)** reducibles `mu_j` は全て `isIndHC` を満たす (`{in mu_, isIndHC}`)。
- **(c)** ∃ irreducible `chi_t`, `isIndHC chi_t`。

⟹ **degree qu の出所** = `mu_j = Ind_{HC}^M(xi)` (xi LINEAR ∈ CF(HC))。linear ⟹ xi(1)=1 ⟹
`(Ind xi)(1) = [M:HC]·1 = [M:HU]·[HU:HC] = q·u` (q=|W1|=[M:HU], u=[U:C]=[HU:HC])。

**chiefFactor_caseA_char_inertia (proven) の役割**: reducible mu_j に対応する chief-factor char θ̄ が
**regular** (各 Hpart summand 上 nontrivial) ⟹ inertia I_{HU}(θ̄)=HC (= my core) ⟹ HC-constituent が
HC 上 linear で induce ⟹ mu_j = Ind_{HC}(linear)。∴ my core は on-path (degree の Ind 構造を license)。

**残ステップ (caseA degree 配線)**:
1. **reducible ⟹ regular θ̄**: mu_j reducible (prTIred) ⟹ 対応 θ̄ が各 Hpart 上 nontrivial。Coq
   `Part_a` (L883) / `typeP_reducible_core_Ind` (L1423) / `typeP_reducible_core_cases` (L1439) 参照。
2. **mu_j = Ind_{HC}(linear)**: 1 + my core (inertia=HC) + Clifford induction。
3. **degree [M:HC]=qu**: index 算術 ([M:HU]=q=|W1|, [HU:HC]=u)。caseB_degree_qu の
   `induceHU_apply_one_eq_q_mul` 系が部分再利用可。
caseB_degree_qu (irreducible, S_ H0C') の構造 (caseB_exists_chiefFactorConstituent → inertia → degree)
が template。caseA は reducible 版で parallel。


## 進捗 2026-06-30 追記 (caseA inertia 機構 完備)

`inertia_eq_hcInHu_caseA` 実証明 (commit 85ada93a)。regular θ̄ の inflation θ₀ の HU-inertia = HC。
proven な `chiefFactor_caseA_char_inertia` を **parametrized plumbing** (`caseB_char_inertia_inflation_of_core`
→ `caseB_inertia_realized_of_charInertia` → `inertia_inf_uInHu_le_cInHu_of_realized` →
`inertia_eq_hcInHu_of_inf_le` — 全て core/realized/inf を引数に取る case-agnostic 設計) に通すだけ。

⟹ **caseA inertia side = 完全に DONE** (core + lift、caseB と parallel)。degree の inertia 入力完備。

**残 (caseA degree、inertia 以外)**:
1. **reducible χ ⟹ θ̄ regular** (= 各 Hpart summand 上 nontrivial): これが `inertia_eq_hcInHu_caseA` の
   `hreg` を供給。**prTIred 機構** (reducibles = prime-TI reducible chars) の content。Coq `Part_a`
   (L883-905, `[exists w in W1bar, Res theta != 1]` の各 w 版) + reducible↔θ̄ 対応。
2. **`caseA_exists_chiefFactorConstituent`** (caseB の analog, L5005): inertia step を
   `inertia_eq_hcInHu_caseA` に差し替え + regular 仮説。θ₀ + inertia=HC + linear を供給。
3. **`caseA_degree_qu`** (caseB_degree_qu の analog, L5090): 2 + Clifford degree → φ(1)=qu。
4. **配線**: `caseA_character_counts` conjunct b の degree sorry を埋める。
caseB は (1) 不要 (irreducibility で全 θ inertia HC); caseA は regular に限るので (1) が固有の追加。


## caseA degree side — Coq 精読 + infra 査定 (2026-06-30)

**Coq `typeP_reducible_core_Ind` (L1423)**: reducibles `mu_j` は **prime-TI reducible chars
`primeTIred ptiWM j`** (j≠0) と同定。degree (isIndHC) は本体 `typeP_nonGalois_characters` (9.8) に委譲。
**`typeP_reducible_core_cases` (L1439)**: conjunct c の irreducible も isIndHC (= `Ind_M,HC(linear)`,
deg [M:HC]=qu) で構成。

**degree path (my inertia 機構経由)**: reducible φ ⟹ 構成 θ̄ regular ⟹ `I_HU(θ̄)=HC`
(`inertia_eq_hcInHu_caseA` ✅) ⟹ HC 上 linear に extend ⟹ φ=Ind_HC(linear) ⟹ deg [M:HC]=qu。

**infra 査定**: prime-TI/Dade 機構は Lean §5–8 (S05_TICyclic / S05_SigmaIsometry / S06–S08) に存在。
但し **§11 reducibles ↔ primeTIred ↔ regular θ̄ の接続は未 port** で §13 cyclic-TI に entangle。

**最短 path 判定 (次セッション)**:
- **conjunct c (∃ irreducible deg qu)** が conjunct b より tractable な可能性: reducible↔regular の
  prime-TI 同定を回避し、**regular θ̄ を直接構成** (H̄ elementary abelian = ⊕ Hpart の各 factor 上
  nontrivial な linear char = 各 Hpart* の nontrivial char の direct product) → my lift → induce で
  irreducible deg qu。要 **SupIndep 露出** (de-opacify 追加; producer は exists_supIndep で既に保持) +
  Clifford induction (caseB_degree_qu に部分実在)。
- **conjunct b** は reducible φ の構成 θ̄ が regular であることの証明が必要 (= reducibles=primeTIred の
  spread 性) で prime-TI 同定に依存 = より重い。
∴ 次は **conjunct c 経由 + SupIndep de-opacify + regular θ̄ 構成** を優先検討。my inertia 機構
(core+lift) は両 conjunct の共通 enabling ingredient で完備。


## regular θ̄ 構成の mathlib 機構 (2026-06-30)

conjunct c の regular θ̄ (各 Hpart 上 nontrivial な linear char) 構成に使える mathlib:
- `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity {a≠1} : ∃ χ:G→*Mˣ, χ a ≠ 1`
  (FiniteAbelian/Duality.lean:64) — char が点を分離 (ℂ は hasEnoughRootsOfUnity)。
- `MonoidHom.restrict_surjective (H:Subgroup G) : Surjective (G→*Mˣ の H 制限)` (同:108) —
  部分群の char は G へ拡張可。
- 構成: H̄ = ⊕ Hpart (Hpart_iSupIndep + Hpart_iSup) ⟹ H̄ ≅ ∏ Hpart (internal direct product iso;
  `Subgroup.noncommPiCoprod` / `DirectSum.IsInternal` 系) ⟹ θ̄ = (∏ ψ_i) ∘ iso⁻¹ (各 ψ_i nontrivial)。
  regular char 数 = (p-1)^q > 0 ゆえ存在は確実。union-bound は弱すぎ (q<p 不要)、tuple 対応 (iso) が正道。

**次の構成ステップ**: (1) H̄ ≅ ∏ Hpart の iso (iSupIndep+iSup=⊤ から; elementary abelian ゆえ
additive `DirectSum.IsInternal` も可)、(2) 各 Hpart i の nontrivial char (exists_apply_ne_one)、
(3) 合成で regular θ̄、(4) `inertia_eq_hcInHu_caseA` → induce → conjunct c。multi-piece、fresh context 推奨。


## regular θ̄ 構成の正確な mathlib 配線 (2026-06-30、次イテレーション用)

`exists_regular_char` (一般補題、`[CommGroup Hbar]` で述べれば subgroup の CommGroup instance は自動):
```
theorem exists_regular_char {Hbar} [CommGroup Hbar] [Finite Hbar] {ι} [Fintype ι]
  (Hpart : ι → Subgroup Hbar) (hindep : iSupIndep Hpart) (hspan : ⨆ i, Hpart i = ⊤)
  (hp : ∀ i, (Nat.card ↥(Hpart i)).Prime) : ∃ θ : Hbar →* ℂˣ, ∀ i, ∃ x ∈ Hpart i, θ x ≠ 1
```
配線 (GroupTheory/NoncommPiCoprod.lean):
1. `choose ψ hψ using fun i => exists_ne_one_hom_of_prime_card (hp i)` — ψ i : ↥(Hpart i)→*ℂˣ, ≠1。
2. commuting: Hbar abelian ⟹ `fun _ _ _ _ _ _ => mul_comm _ _` 系で Pairwise Commute。
3. `e := Subgroup.noncommPiCoprod Hpart hcomm : (∀ i, ↥(Hpart i)) →* Hbar`。
4. inj: `injective_noncommPiCoprod_of_iSupIndep` (hindep + 各 subtype inj)。
   surj: range = `noncommPiCoprod_range`/`noncommPiCoprod_mrange` = ⨆ Hpart = ⊤ (hspan)。
5. `eEquiv := MulEquiv.ofBijective e ⟨inj, surj⟩`。
6. `θ := (MonoidHom.noncommPiCoprod ψ (commuting in ℂˣ auto)).comp eEquiv.symm.toMonoidHom`。
7. nontriv: ψ i ≠1 ⟹ ∃ x:↥(Hpart i), ψ i x ≠1。`eEquiv.symm ↑x = Pi.mulSingle i x` (x∈Hpart i ゆえ
   coprod の single slot) ⟹ θ ↑x = ψ i x ≠1。`noncommPiCoprod_mulSingle` が single-slot 計算。
注: 一般補題ゆえ instance friction 無し。use site (Hbar=↥H⧸N) で IsMulCommutative→CommGroup の
letI が要る (別途)。~50 行、fresh context 推奨。


## conjunct c の状態 (2026-06-30、regular θ̄ 機構完成後)

**揃った入力** (全て本セッションで実証明):
- `exists_regular_irr_caseA`: regular θ̄ (各 Hpart 上 nontrivial) ∃。✅
- `inertia_eq_hcInHu_caseA`: regular θ̄ ⟹ I_HU(θ₀)=HC。✅
- `induceHU` (Ind_HU^M) + `induceHU_apply_one_eq_q_mul` (deg = q·χ(1)) + `xiSet`/`sOf`/`mem_sOf`。✅

**欠けている核心 = Clifford correspondence**: 「I_HU(θ₀)=HC ⟹ Ind_{HC}^{HU}(θ₀ 上の linear) は
irreducible、degree [HU:HC]=u」。これは S11:4402 で**docstring コメントとして言及されるのみ、
未だ lemma 化されていない**。conjunct c (∃ irreducible deg qu ∈ 𝒮(H₀C)) はこの correspondence を
要する最大の残ピース。

**次イテレーション手順**:
1. mathlib の Clifford correspondence (induced-from-inertia-group is irreducible) を探す
   (`leansearch` / `Mathlib.RepresentationTheory` の Clifford/inertia)。無ければ repo 内
   `IrreducibleCharacter.LiesOver`/inertia infra で構築。
2. θ₀ 上の linear HC-char を構成 (inertia=HC ⟹ θ₀ が HC へ linear 拡張)、Ind_{HC}^{HU} で
   irreducible (deg u) → χ ∈ xiSet ∩ 𝒳(H₀C)。
3. `induceHU` で 𝒮(H₀C)、deg = q·u (`induceHU_apply_one_eq_q_mul`)。
conjunct b は更に reducible↔regular (prTIred) を要し別ピース。conjunct d は count。


## conjunct c の Clifford correspondence — repo infra 確認 (2026-06-30)

mathlib に Clifford correspondence は**無い**が、**repo 内に Clifford 完備 infra あり**:
- `OddOrder/GroupTheory/RepresentationTheory/Clifford.lean` — Isaacs Thm 6.5/6.11、**inertia
  bijection** (induction from inertia T)、`restrictionMultiplicity`、`IrreducibleCharacter.LiesOver`/
  `inertia`/`inertiaQuotient`、conjBySimpleSemilinear (Clifford module setup)。
- `InducedIrreducible.lean` — Frobenius irreducibility (Isaacs Thm 6.34、inertia=H 特殊化)、
  Mackey norm (`card_mul_inner_self_induce` で ‖Ind θ‖²=1 ⟹ irreducible)。
- `CliffordSingleOrbit.lean` — single-orbit Clifford。

**conjunct c 構築 path**: regular θ̄ (inertia=HC) ⟹ Clifford **Thm 6.11 inertia bijection**
(Clifford.lean) で「I_HU(θ₀)=HC 上の Irr(HC) char ↔ Irr(HU) over θ₀」⟹ Ind_{HC}^{HU}(θ₀ 拡張 linear)
irreducible deg [HU:HC]=u ⟹ χ∈xiSet∩𝒳(H₀C) ⟹ induceHU deg q·u。次イテレーションは Clifford.lean の
Thm 6.11 lemma を特定 (induce-from-inertia-bijective/irreducible の usable form) して適用。


## 重要な再framing: conjunct b/c は M-level (W1-orbit) で bottom out (2026-06-30)

深い解析で判明: 私の caseA inertia 機構 (`inertia_eq_hcInHu_caseA`, I_HU(θ₀)=HC) は **HU-level** で
necessary だが **sufficient でない**。degree conjunct (b/c) は **M-level** inertia I_M(ξ)=HC を要する:
- HU-level Clifford (`isIrreducibleCharacter_induce_of_inertia_eq` + `hcInHu_normal`、既存) ⟹
  Ind_{HC}^{HU}(ξ) irreducible deg u。✅ 支持あり。
- だが 𝒮(H₀C) は `induceHU` = Ind_{HU}^**M**。conjunct c の最終 χ の irreducibility は M-level、
  = I_M(ξ)=HC、= I_HU=HC (済) **+ W1 が regular θ̄ 上 free に作用** (regular = trivial W1-stabilizer)。
- この **W1-orbit 構造 (regular ⟺ free W1-orbit)** が prime-TI content で、**conjunct b の
  reducible↔regular とも共有**。両 degree conjunct はここに bottom out。

**∴ 次の真の上流 = W1-orbit 解析** (regular θ̄ の W1-stabilizer 自明 / M-level inertia=HC)。これは
prime-TI (primeTIred) / §13 cyclic-TI と entangle。私の HU-inertia 機構 + regular θ̄ 構成は
この上流の prerequisite として完備、残りは M-level W1-orbit ピース。caseB は U-irreducible ゆえ
W1-orbit 自明 (全 θ̄ regular) で此処を回避; caseA 固有の追加。


## conjunct c の最終的に sharp な構築 target — aperiodic tuple (2026-06-30)

crux を最も具体的な形に: **W1 (order q, prime) は q 個の Hpart factors を q-cycle で transitive 置換**
(W1_transitive_on_parts の実体)。dual で W1 は per-factor chars (ψ_i) を巡回 shift。
- free W1-orbit char θ̄ = **aperiodic tuple** (ψ_1,…,ψ_q): 非自明 σ^k で固定 ⟺ 全 ψ_i 相等
  (q-cycle ゆえ)。∴ **「全相等でない」⟹ trivial W1-stabilizer ⟹ I_M(χ)=HU**。
- 存在: q≥3 (odd prime) かつ各 factor に p-1≥2 個の nontrivial char ⟹ not-all-equal tuple 存在。
- downstream 完備: `huSub_normal` (HU◁M) ✅ + `isIrreducibleCharacter_induce_of_inertia_eq` ✅
  ⟹ induceHU(χ) irreducible deg q·u。

**唯一の残 prerequisite = W1-action de-opacify**: W1 が factors に q-cycle で作用する構造を (9.7)
`typeP_Galois_Pn` (non-Galois 分解) から producer に threading + `W1_transitive_on_parts` 実体化。
**次イテレーションの構築**: (1) producer に W1-permutation σ:Fin q≃Fin q (q-cycle) を露出、
(2) 一般補題 `exists_aperiodic_regular_char` (exists_regular_char + not-all-equal で σ-stabilizer 自明)、
(3) caseA instantiate → I_M=HU → induceHU irreducible deg qu → conjunct c。
conjunct b も同じ W1-orbit (reducibles = 特定 W1-orbit 類) ゆえ此処共有。


## 真の gating prerequisite 確定: (9.7) non-Galois decomposition の port (2026-06-30)

調査確定: **(9.7) non-Galois 分解 (Coq `typeP_Galois_Pn`) は Lean 未 port**。S11 には opaque
`W1_transitive_on_parts := True` のみ。producer (`clifford_caseA_data`) の S₀ は**任意の
U-invariant order-p factor** で、non-Galois 分解の H1 (W1-conjugates が q factors を transitive
置換) とは未接続。⟹ **W1-transitivity / W1-action は producer の現データから導けない**。

**∴ 残 caseA degree (conjunct b/c/d) の gating = (9.7) typeP_Galois_Pn の port** (実質的新規形式化):
Coq `typeP_Galois_Pn : ~~typeP_Galois → {H1 | oH1 ∧ nH1U ∧ defHbar : Hbar = \prod_{w∈W1bar} H1^w ∧ ...}`。
H̄ = ⊕_{w∈W1bar} H1^w (W1-conjugate 分解)、H1 order-p、W1 が conjugates を巡回置換。これを Lean 化し
producer の Hpart を H1^w に同定すれば W1-action (q-cycle) + transitivity が出る。

**完成済 (gate まで)**: HU-inertia 機構 (core+lift), regular θ̄ 構成, combinatorial core
(`constant_of_perm_invariant_of_transitive`)。**gate 後** (port 後): W1-action de-opacify →
aperiodic regular θ̄ → I_M=HU (prime-index, relindex 不在ゆえ Nat.card 版要) → induceHU irreducible
→ conjunct c。conjunct b は reducible=特定 W1-orbit。
**次の真の作業 = (9.7) typeP_Galois_Pn の Lean port** (Coq PFsection9 の typeP_Galois_Pn 周辺精読 +
W1-conjugate 分解構築)。これは数十行〜の coherent な新規形式化、fresh context 推奨。


## (9.7) port の precise design — Coq typeP_Galois_Pn 精読 (2026-06-30、Coq-first)

Coq `PFsection9.v` L323-365 精読完了:
- `typeP_Galois := acts_irreducibly U Hbar` (= caseB、CliffordCaseBData.actsIrreducibly に対応)。
- `typeP_Galois_Pn (~~Galois)` (= caseA) → `{H1 | #|H1|=p, U/H0 ⊂ N(H1), [acts U on H1],`
  `⊕_(w∈W1bar) H1:^w = Hbar, a-property}`。
- **構築**: H1 = U-minimal-normal subgroup of H̄ (mingroup_exists; ~~irreducible ゆえ proper、order p)。
  = **my producer の S₀ に相当** (U-invariant order-p factor)。
- **核心 = Clifford dprod 分解** `⊕_(w∈W1bar) H1:^w = Hbar`: UW1-表現 rUW1 (abelem_repr) に Clifford
  理論 (`Clifford_basis irrUW1 simV1`) を適用、H1 = U-simple submodule の W1-conjugates が H̄ を
  direct-sum 分解。W1 が conjugates を置換 = W1-transitivity (by construction)。

**port 設計 (Lean)**:
1. `typeP_Galois` predicate = U-action irreducible (既 CliffordCaseBData.actsIrreducibly)。
2. caseA: U-minimal H1 ≤ H̄ (order p, U-inv) を取る (= 現 producer の S₀ 役)。
3. **H̄ = ⊕_(w∈W1bar) H1^w** を Clifford 理論 (repo `Clifford.lean`) で構築 — **rep-theory-heavy 核心**。
4. producer rework: Hpart j := H1^{w_j} (W1-conjugates、現 maximal-SupIndep 族を置換) ⟹ W1-action
   (W1 permutes conjugates) + transitivity が by-construction で出る。

**∴ (9.7) port の hard core = Clifford dprod 分解 (H̄=⊕H1^w)** = rep-theory 重量級、`Clifford.lean`
(clifford_decomposition 等) 活用、fresh focused context 推奨。これが caseA degree (conjunct b/c/d) の
唯一の真の gate。完成済は全て gate まで (HU-inertia + regular θ̄ + combinatorial core)。


## 真の bottom 確定: caseA degree は Clifford rep-theory core (issue 0026) に gated (2026-06-30)

決定的調査結果: `Clifford.lean` の `clifford_decomposition` は **conditional 再包装のみ** (Clifford data
t,e,θ を**仮説として取る**)。docstring 明記: 実構築は「InducedCharacter + SecondOrthogonality proof
core (issues/0026-peterfalvi-clifford-core.md に分離)」を要し、**未構築**。Coq (9.7) dprod は
**module Clifford 理論** (`abelem_repr` + `Clifford_basis`) を使用。

**∴ caseA degree の完全 dependency chain**:
```
conjunct b/c/d → (9.7) port → Clifford dprod (H̄=⊕H1^w) → Clifford rep-theory core (issue 0026、
  InducedCharacter + SecondOrthogonality、partially-unbuilt、substantial)
```
caseA degree は **deep rep-theory gate (issue 0026) に transitively gated**。完成済 HU-level milestone
(inertia core+lift, regular θ̄, combinatorial core = 12 commits) は **この gate まで到達可能な境界そのもの**。

**lane-a 戦略含意**: caseA degree (conjunct b/c/d) は issue 0026 (Clifford core) が真の上流。これは
major rep-theory 形式化 (InducedCharacter + 2nd orthogonality)。**upstream-first ⟹ 次の真の作業は
issue 0026 の Clifford core** (or それを回避する別 lane-a FT-path 作業の再評価)。caseA degree の HU-level
milestone は honest かつ完備で、deep gate ゆえ此処が自然な区切り。


## 重要訂正: (9.7) dprod は elementary、issue 0026 に gated していない (2026-07-01)

前項「caseA degree は issue 0026 (character Clifford core) に gated」は**誤り**。難所を掘ったところ
(9.7) dprod `H̄=⊕H1^w` は **elementary な count 論**で構築可、character Clifford 不要:
- **H は abelian H̄ に trivial 作用** ([H,H]≤H0 ゆえ): M acts on H̄ factors through M/H≈UW1。
  ⟹ **M-irreducible = UW1-irreducible** (chief factor ゆえ M-irr 既知)。
- S₀ (U-minimal order-p, dichotomy) は **W1-fixed でない** (else S₀ UW1-inv ⟹ ⊥/⊤、|S₀|=p 矛盾)。
- W1-conjugates {φ(w)•S₀} は **U-invariant** (U◁UW1: φ(u)φ(w)•S₀=φ(w)φ(w⁻¹uw)•S₀=φ(w)•S₀)、
  UW1-orbit=W1-orbit (U が各 conjugate に trivial) ⟹ **span ⊤**。
- W1 prime order q + S₀ not W1-fixed ⟹ **W1 free 作用 ⟹ q distinct conjugates**。
- q distinct order-p subgroups span order-p^q ⟹ **count で internal direct product**
  (`noncommPiCoprod_bijective_of_card` ✅ landed: ∏|S_i|=|K| + span ⟹ bijective)。

**∴ caseA degree は issue 0026 に gated していない。(9.7) dprod は elementary group theory で完結。**
landed: `noncommPiCoprod_bijective_of_card` (count⟹bijective core)。残: W1-conjugate setup
(U-inv/not-W1-fixed/span/card の §11 plumbing) → iso H̄≅∏ → aperiodic regular θ̄ (iso 直接、iSupIndep 回避可)
→ I_M=HC → induceHU irreducible → conjunct c。grinding 継続。


## conjunct c — char-side 完成 + 構造的発見 (2026-07-01)

**char-side 完成** (21+ commits): elementary (9.7) dprod toolkit + §11 instantiation
(`clifford_caseA_exists_regular_char_on_conjugates`) + non-W1-fixed char
(`exists_regular_char_not_fixed`、equivariance 不要、restriction-fact + char-existence で構成)。
最難の aperiodic char が clean general lemma 化。

**構造的発見 (path に影響)**: non-fixed θ̄ は **W1-conjugates** (act.φ↑w•S₀) 上 regular だが、
`inertia_eq_hcInHu_caseA` は **caseA.Hpart** (producer の maximal-SupIndep 族) に tied。**別の族**ゆえ
直接適用不可。**解決**: assembly `mulAut_eq_one_of_fixes_regular_on_prime_span` は Hpart 族に generic
ゆえ W1-conjugates (order-p ✅ card_pointwise_smul、span ✅ span-reduction、U-inv ✅
isAInvariant_comp_subtype_pointwise_smul、iSupIndep は bijection 経由不要) を直接 drive 可。

**残 conjunct c 配線 (substantial multi-step)**:
1. §11 instantiate `exists_regular_char_not_fixed` (τ=act.φ(w₀)、w₀≠1、p≥3 odd) → non-fixed θ̄。
2. W1-conjugates で inertia 再導出 (assembly + generic plumbing caseB_*_of_core) → I_HU(θ₀)=HC。
3. M-level: I_M(χ)=HU (non-W1-fixed → I_M≠M → prime-index `eq_of_le_of_prime_index` ✅)。
4. χ=Ind_{HC}^{HU}(linear) irreducible deg u (`isIrreducibleCharacter_induce_of_inertia_eq` + hcInHu_normal ✅)。
5. induceHU(χ) irreducible deg qu (M-level、`isIrreducibleCharacter_induce_of_inertia_eq` + huSub_normal ✅)。
6. χ∈𝒳(H₀C) (kernel 条件) → conjunct c。
inertia/§6 framework 横断の multi-step。char-side は完備、残は inertia-side 配線。
