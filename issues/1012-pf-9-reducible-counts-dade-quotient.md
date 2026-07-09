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


## conjunct c — 構造的 worry は FALSE ALARM、step 2 は健全 (2026-07-01, Coq 確認)

**前回の「W1-conjugates は U-invariant でない」は誤り。** producer 確認: `caseA.Hpart j =
act.φ↑(e.symm j)•S₀`、`Hpart_aInvariant = isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv`。
**任意の a で `act.φ(a)•S₀` は U-invariant**: S₀ U-inv + U◁UW1 ⟹ u∈U で
`act.φ(u)•act.φ(a)•S₀ = act.φ(ua)•S₀ = act.φ(a)•act.φ(a⁻¹ua)•S₀ = act.φ(a)•S₀`
(`a⁻¹ua∈U` が S₀ を固定)。**U は各 W1-conjugate を (部分群として) 固定**し、permute するのは W1 のみ。
⟹ W1-conjugates は `haInv` を満たし、`inertia_eq_hcInHu_gen` が**直接適用可** (step 2 健全)。

**Coq PFsection9.v (9.8) 構成 (正本、L916-963)**:
- `cfJ w i := 'chi_(isom_Iirr (conj_isom H1 w) i)` — H1^w の char (i:Iirr H1)。
- `thetaH f := cfBigdprod defHbar (fun w => cfJ w (f w))` — Hbar=⊕_w H1^w の char (f:W1bar→Iirr H1)。
- `theta f := cfDprodl defHCbar (thetaH f)` — HC への拡張。
- `Ftheta := pffun_on 0 W1bar (predC1 0)` — **各 W1-conjugate で f w ≠ 0 (nontrivial)** = regular 族。
  (= 私の clifford_caseA_exists_regular_char_not_fixed の hreg 条件と一致 ✅)。
- `def_Itheta: f∈Ftheta → 'I_HU[theta f %% H0] = HC` (L938) — **私の inertia_eq_hcInHu_gen に相当**。
  Coq は inertia_bigdprod_irr + inertia_irr_prime 経由 (別 route だが同結論; 私は U-inv family assembly)。
- `irrXtheta: f∈Ftheta → 'Ind[HU](theta f %% H0) ∈ irr HU` (L950) — inertia_Ind_irr で degree-u irreducible。
- `Xtheta := {cfIirr('Ind[HU] 'chi_t) | t∈Mtheta}` (L954) — **double induction Ind_{HU}^M(Ind_{HC}^{HU}(θ_f))**。
- `oXtheta: u·|Xtheta| = (p-1)^q` (L955) — count。
- conjunct c は ∃ なので Xtheta の 1 元を構成すれば足る (free orbit = not W1-fixed の f)。

**残 step (path 明確化)**: step1 θ̄ (hom) → IrreducibleCharacter (linearIrreducibleCharacter) +
hreg ClassFunction 化 → inertia_eq_hcInHu_gen 適用 (Hpart=W1-conj、hp_order/hspan/haInv) → I_HU=HC →
Ind_{HC}^{HU} deg-u irr (inertia_Ind) → not-W1-fixed (step1 の hnf) ⟹ I_M=HU → Ind_{HU}^M deg-qu irr → 𝒳。


## conjunct c — steps 1/2/2-apply landed; bridge pieces identified (2026-07-01)

**Landed** (axiom-clean, build-green): step1 `clifford_caseA_exists_regular_char_not_fixed` (hom θ̄ +
regular + not-W1-fixed) / step2 `chiefFactor_caseA_char_inertia_gen`+`inertia_eq_hcInHu_gen` (generic
inertia) / step2-apply `clifford_caseA_regular_inertia_hc` (I_HU(θ₀)=HC for W1-conjugate regular θbar)。

**残 path (全 piece 同定済、欠落機構なし)**:
- **bridge** (hom θ̄ → IrreducibleCharacter): `linearIrreducibleCharacter` (K→*ℂˣ → IrreducibleCharacter)
  + `ClassFunction.compHom_linearIrreducibleCharacter` (値) + `linearIrreducibleCharacter_injective`。
  ⟹ θbar=linearIrr θ̄、hom regularity (θ̄ x≠1) → ClassFunction regularity ((θbar)x≠(θbar)1) →
  clifford_caseA_regular_inertia_hc で I_HU=HC。
- **degree-u** (step4): `isIrreducibleCharacter_induce_of_inertia_eq` (InducedIrreducible.lean:436) +
  hcInHu_normal ⟹ Ind_{HC}^{HU}(θ₀) irreducible deg u。
- **M-level** (step3): ζ=Ind_{HC}^{HU}(θ₀) not-W1-fixed (⟸ θ̄ not-fixed、step1 hnf) ⟹ I_M(ζ)≠M ⟹
  prime-index `eq_of_le_of_prime_index` ([M:HU]=q) ⟹ I_M(ζ)=HU。
- **degree-qu** (step5): `isIrreducibleCharacter_induce_of_inertia_eq` + huSub_normal ⟹
  Ind_{HU}^M(ζ) irreducible deg qu。
- **𝒳** (step6): kernel 条件 → χ∈𝒳(H₀C) → caseA_character_counts conjunct c。


## conjunct c — bridge/seed DONE; 残=degree-u/qu induction (2026-07-01)

**Landed**: `clifford_caseA_exists_char_inertia_hc_not_fixed` (= (9.8.c) seed: ∃ θ hom, I_HU(θ₀)=HC
∧ ∃w₀ not-W1-fixed)。inertia heart 完成 (steps 1/2/2-apply/bridge、25 feature commits)。
conjunct c の sorry = caseA_character_counts:5166 (refine の 2 番目 ?_、∃χ∈𝒮(H₀C) irr deg qu)。

**残 path + 利用機構**:
- **degree-u** (Clifford 拡張 + 誘導): I_HU(θ on H)=HC → ψ on HC → Ind_{HC}^{HU}(ψ) irr deg u。
  Coq の θ_f は HC 上直接 (cfDprodl→HCbar)。**OPEN: Clifford 拡張 (θ on H→ψ on HC) の所在**。
  機構: `isIrreducibleCharacter_induce_of_inertia_eq` (θ:IrreducibleCharacter H, inertia=H → Ind irr)
  + `hcInHu_normal` (HC◁HU)。**次の調査: 既存 (9.9.a) caseB_degree_qu (S11:5579) が I_HU=HC→deg-u を
  どう作るか** (拡張パターン流用; 既存に有れば conjunct c はそれを呼ぶだけ)。
- **degree-qu** (M-level): ζ not-W1-fixed (⟸ θ not-fixed) → I_M(ζ)=HU (prime-index, eq_of_le_of_prime_index,
  [M:HU]=q) → χ=induceHU(ζ) irr (huSub_normal + isIrreducibleCharacter_induce_of_inertia_eq) deg q·u=qu
  (induceHU_apply_one_eq_q_mul)。
- **𝒳**: ζ∈𝒳(H₀C) (kernel 条件 + xiOf membership) → χ=induceHU(ζ)∈𝒮(H₀C) (sOf_iff)。


## conjunct c — 𝒳 framework解明 + 完全構成マップ (2026-07-01)

**𝒳 def** (S11): `xiSet` = HU の irreducible char で **H ⊄ ker** (H 上 nontrivial)。
`xiOf(Y)` = xiSet ∩ {Y ⊆ ker}。⟹ **𝒳(H₀C) = HU irr char、H 上 nontrivial かつ H₀C ⊆ ker**。
conjunct c (5166): ∃ζ∈xiOf(H₀C), ζ(1)=u ∧ induceHU(ζ) irr (deg q·u=qu、induceHU_apply_one_eq_q_mul)。

**重要簡略化**: H∩C=1 ∧ [H,C]≤H₀ ⟹ **HC/H₀C ≅ H̄** ⟹ ψ on HC = **θ̄ の inflation** (H₀C 自動的に
ker、Clifford 拡張不要)。⟹ 私の I_HU=HC seed (clifford_caseA_exists_char_inertia_hc_not_fixed) が
正しい入力。Coq cfDprodl も同じ (Cbar 上 trivial = inflation)。

**残 layers (多層 plumbing、機構は全て同定済)**:
1. ψ on HC = inflate θ̄ (HC↠HC/H₀C≅H̄)。← iso HC/H₀C≅H̄ の構成 (H∩C=1 + [H,C]≤H₀、both repo に有:
   commutator_cSub_H_le_H0)。
2. inertia_{HU}(ψ)=HC: clifford_caseA_regular_inertia_hc (H-part の inertia=HC) +
   restriction-inertia relation (inertia(ψ)⊆inertia(ψ|_H) + ψ HC-invariant)。Coq sub_inertia_Res。
3. ζ=Ind_{HC}^{HU}(ψ) irr deg u: `isIrreducibleCharacter_induce_of_inertia_eq` + `hcInHu_normal`。
4. M-level I_M(ζ)=HU: ζ not-W1-fixed (⟸ θ̄ not-fixed の伝播) → I_M≠M → prime-index
   `eq_of_le_of_prime_index` ([M:HU]=q)。
5. χ=induceHU(ζ) irr deg qu: `huSub_normal` + `isIrreducibleCharacter_induce_of_inertia_eq`。
6. 𝒳: ζ∈xiOf(H₀C) (H⊄ker: θ̄ nontrivial on H̄; H₀C⊆ker: inflation で自動) → χ∈𝒮(H₀C) (sOf_iff)。

inertia heart (seed) は完成、残は char-construction plumbing (多層だが機構既知)。layer 1-2 が次。


## conjunct c — extraction lemma 同定、forward construction が残 (2026-07-01)

`caseB_exists_chiefFactorConstituent` (S11:5529) = **extraction** (χ∈𝒳 → θ₀ over、inertia=HC、linear)。
(9.9.a) degree 決定用。conjunct c は **forward** (θ₀ regular → χ∈𝒳(H₀C) over θ₀ 構成) が必要。
利用機構: `IrreducibleCharacter.LiesOver` / `exists_constituent_not_subset_characterKernel` /
`exists_compHom_eq_of_subset_characterKernel` / `isIrreducibleCharacter_induce_of_inertia_eq` /
`hcInHu_normal` / `huSub_normal`。

**layer 1 (次)**: ψ on HC = inflate θ̄ — realized HC↠H̄ hom (HC=hInHu⊔cInHu⊆huSub、quotient
HC/H₀C≅H̄)。これが realized-subgroup setting で intricate (subgroupOf chain + quotient iso)。
seed (I_HU=HC + not-fixed、inertia heart) は完成、残は forward Clifford correspondence + M-level + 𝒳。


## conjunct c — caseB machinery は degree-determination、construction は新規 (2026-07-01)

caseB_degree_qu / apply_one_eq_index_of_liesOver_linear_inertia / caseB_exists_chiefFactorConstituent
は **与えられた χ の degree 決定** (extraction 方向)。conjunct c は χ の **construction** (新規)。
私の seed (clifford_caseA_exists_char_inertia_hc_not_fixed) は θ₀ on hInHu (linear, inertia=HC) を
直接供給 = caseB_exists_chiefFactorConstituent の出力と同形 ⟹ 正しい入力。

**construction layer 1 (crux)**: θ₀ on hInHu を ψ on HC=hInHu⊔cInHu に拡張 (cInHu 上 trivial) =
realized HC↠H̄ hom (hInHu→H̄ の f=(mk'N)∘hInHuEquivH を HC へ延長)。intricate subgroupOf-chain。
**layer 2+**: χ=Ind_{HC}^{HU}(ψ) irr (isIrreducibleCharacter_induce_of_inertia_eq + inertia(ψ)=HC,
ψ HC-inv + restriction-inertia) → χ∈𝒳(H₀C) over θ₀ deg u → not-fixed → I_M=HU → induceHU deg qu。
利用可能: exists_liesOver / coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce (CliffordSingleOrbit)。


## conjunct c — build 方針確定: explicit realized inflation hom (2026-07-01)

**確認**: (1) `typeP_H_inf_U` (S11:134) = H∩U=⊥ ⟹ HC=hInHu⋊cInHu (internal semidirect、hInHu∩cInHu=⊥)。
(2) repo に abstract char-extension lemma 無し (linearIrreducibleCharacter 系のみ) ⟹ ψ は
**explicit realized inflation hom HC↠H̄ を構成**するしかない (semidirect 経由、~50-100 行)。

**layer 1 build approach (post-summarization で実行)**:
- hom ↥(hInHu⊔cInHu)→↥H⧸N: hInHu◁HC + HC=hInHu·cInHu (semidirect) を使い、g=h·c↦f(h)
  (f=(mk'N)∘hInHuEquivH on hInHu、cInHu 上 trivial)。well-defined: f は cInHu-invariant
  (θ̄ on H̄、C 中心化) + hInHu∩cInHu=⊥。
- ψ=linearIrreducibleCharacter(θ̄∘(この hom))、ψ on HC、cInHu⊆ker、ψ|_hInHu=θ₀。
- χ=Ind_{HC}^{HU}(ψ) irr (isIrreducibleCharacter_induce_of_inertia_eq + inertia(ψ)=HC via
  clifford_caseA_regular_inertia_hc + restriction-inertia)。→ χ∈𝒳(H₀C) over θ₀ deg u。
- M-level: not-fixed → I_M=HU → induceHU(χ) irr deg qu → conjunct c (5166)。

seed (inertia heart) 完成。残 = explicit inflation hom + induction chain (機構・facts 全確定、fresh context で build)。


## conjunct c — 🔑 戦略転換: counting で explicit construction を回避できる可能性 (2026-07-01)

**重大発見**: repo は explicit char construction を**系統的に counting/antitone で回避**している:
- `reducible_mem_sOf_H0C` (5766): `Set.eq_of_subset_of_ncard_le` (両者 p-1 ⟹ subset=whole)。
- `forall_mem_sOf_H0C_apply_one_eq_qu` (5728): `sOf_antitone` + caseB_degree_qu。
- `HC/H₀=H̄×(C/H₀)` dprod は docstring のみ (実証明は使わない)。

⟹ **conjunct c (∃ irreducible deg-qu ∈ 𝒮(H₀C)) も counting で出せる可能性大** —
explicit inflation hom 不要。方針: |𝒮(H₀C)| - |reducibles(=p-1)| = |irreducibles| > 0 ⟹ ∃ irreducible。
`reducible_count_sOf_H0C` (p-1、§9↔§6 bijection、no explicit construction) は既存。
Coq oXtheta: u·|Xtheta|=(p-1)^q ⟹ |Xtheta|=(p-1)^q/u ≥ 1 (irreducible 存在)。

**次の探索 (counting 路線、explicit hom より優先)**:
- 全 𝒮(H₀C) member は deg qu か (case-A 版 forall_degree_qu)? caseA_character_counts conjunct 2
  (reducibles deg qu) + irreducible も同 → ∃ irreducible で conjunct c。
- |𝒮(H₀C)| total count or |irreducibles|>0 を §9↔§6 bijection / 既存 count から出せるか。
- 出せれば explicit inflation hom (intricate) を完全回避。出せなければ explicit construction に戻る。

seed (inertia heart) は両路線で不要になる可能性 (counting なら) だが、explicit fallback では中核入力。


## conjunct c — counting 路線却下、explicit construction 確定 (2026-07-01)

**counting 却下**: repo に 𝒮(H₀C)/𝒳(H₀C) の **total count 無し** (reducible count p-1 のみ)。
total が無いと irreducible = total - reducible が出せない。Coq oXtheta (u·|Xtheta|=(p-1)^q) も
Xtheta 構成依存。⟹ **explicit construction が必要** (確定、fallback でなく唯一路線)。

**構成路線確定 (second isomorphism theorem)**: HC/H₀C ≅ H̄ を 2nd iso で構成:
HC = hInHu·(realized H₀C) (H₀⊆hInHu, C⊆H₀C) ∧ hInHu∩(realized H₀C)=realized H₀ ⟹
HC/H₀C ≅ hInHu/H₀ ≅ H̄ (hInHuEquivH 経由)。manual semidirect bookkeeping 不要。

**multi-layer build (各 iteration で 1 layer)**:
- L1: iso HC/H₀C≅H̄ (mathlib 2nd iso: QuotientGroup.quotient*Equiv系) + hom HC→H̄。
- L2: ψ=linearIrr(θ̄∘hom) on HC、cInHu⊆ker、ψ|hInHu=θ₀。
- L3: inertia(ψ)=HC (clifford_caseA_regular_inertia_hc + restriction-inertia)。
- L4: χ=Ind_{HC}^{HU}(ψ) irr deg u (isIrreducibleCharacter_induce_of_inertia_eq + hcInHu_normal)。
- L5: M-level I_M=HU (not-fixed) → induceHU(χ) irr deg qu (huSub_normal)。
- L6: χ∈𝒳(H₀C) + induceHU∈𝒮(H₀C) → conjunct c (5166)。
seed (inertia heart) は L3 の中核入力。


## conjunct c — iso/hom DONE (10 lemmas); inertia(ψ)=HC が次の深部 (2026-07-01)

**Landed (10 construction lemmas、axiom-clean)**: subgroup foundation (H∩C=⊥, H∩H₀C=H₀,
H₀C=H₀⊔C, H⊔H₀C=HC) + H₀C◁HU + transports (realizedH₀C.subgroupOf hInHu=realizedH₀, =N.comap,
.map=N) + **2nd iso hcQuotientEquivHbar (HC/H₀C≅H̄、crux)** + **hcHom (HC→H̄ inflation hom)**。

**次: ψ = linearIrreducibleCharacter(θ.comp hcHom) + inertia(ψ)=HC**:
- 重要: inertia framework は H◁G 要。**HC◁HU は hcInHu_normal で成立** ⟹ inertia(ψ) 定義可、
  isIrreducibleCharacter_induce_of_inertia_eq 適用可。
- inertia(ψ)=HC: ≥ は subgroup_le_inertia。≤ は inertia(ψ)⊆inertia(Res_hInHu ψ)=inertia(θ₀)=HC
  (seed)。restriction-inertia (conjBy が restrict と可換、hInHu◁HC◁HU) が key sub-lemma (build/find)。
  conjBy_restrict (Inertia.lean:154) が近い。**OR Clifford 対応 lemma (ψ over θ₀ ⟹ inertia(ψ)=inertia(θ₀))**。
- **degree ζ(1)=u は既存 apply_one_eq_index_of_liesOver_linear_inertia** で ANY ζ over θ₀ + over linear ψ。
- ζ=Ind_{HC}^{HU}(ψ) irr (isIrreducibleCharacter_induce_of_inertia_eq + inertia(ψ)=HC)。
- 残: ζ∈xiOf(H₀C) (H⊄ker: θ̄ nontrivial、H₀C⊆ker: ψ inflation) + not-W1-fixed → χ=induceHU(ζ) irr qu。
- HC=hInHu⊔realizedH₀C=hInHu⊔cInHu (hInHu_sup_realizedH0supC) で seed inertia と同定。


## conjunct c — hcHom_inclusion: hfwd 解決、main assembly が letI-unfold で詰まり (2026-07-01)

**13 construction lemmas landed** (iso hcQuotientEquivHbar + hom hcHom + ψ hcPsi + hcHom-kills-H₀C +
HC◁HU realized + 全 subgroup transports)。

**hcHom_inclusion (hcHom|hInHu=f) 進捗**: hfwd `quotientInf(mk' h)=mk'(incl h)` は **解決**:
```
simp only [QuotientGroup.quotientInfEquivProdNormalQuotient,
  QuotientGroup.quotientInfEquivProdNormalizerQuotient, MulEquiv.trans_apply,
  QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.quotientKerEquivOfSurjective,
  QuotientGroup.quotientKerEquivOfRightInverse, MulEquiv.coe_mk, MulEquiv.symm_mk,
  MonoidHom.toMulEquiv_apply, QuotientGroup.kerLift_mk]; rfl
```
**残 obstacle (main assembly)**: `hcHom(incl h) = congr(quotientInf.symm(mk'(incl h))) = congr(mk' h)
= mk'(hInHuEquivH h)`。simp [hcQuotientEquivHbar, trans_apply, ←hfwd, symm_apply_apply, congr_mk] で
trans_apply/symm_apply_apply/congr_mk が **unused** = hcQuotientEquivHbar (letI-wrapped def) の trans
構造を simp が露出できず。**fix 候補**: (a) hcQuotientEquivHbar を letI 無し term に再定義 (instances
を separate instance 化) で unfold 可能に、(b) explicit rw + MulEquiv.trans_apply、(c)
hcQuotientEquivHbar_apply lemma を別途証明。次 iteration で main assembly を fresh に解決。
build slow (~2min post-merge) → background build 使用。


## conjunct c — home stretch: ζ irr + degree DONE; H₀C⊆ker が giant-term whnf で詰まり (2026-07-01)

**Landed (20 construction lemmas、axiom-clean)**: subgroup foundation + 2nd iso hcQuotientEquivHbar +
hom hcHom + ψ hcPsi + **hcHom_inclusion (deep crux)** + ψ|hInHu=θ₀ (hcPsi_apply_inclusion) +
restriction-inertia (hcPsi_inertia_le) + **inertia(ψ)=HC (hcPsi_inertia_eq_hc)** +
**ζ=Ind irr (hcZeta_irreducible)** + [HU:HC]=u (hc_index_eq_u) + **ζ(1)=u (hcZeta_apply_one)**。

**残 (home stretch)**:
- **H₀C⊆ker ζ**: `subsetCharacterKernel_induce_of_subgroupOf` (S03、induce-kernel for normal A⊆ker θ)
  + ψ trivial on H₀C (hcHom_eq_one_of_mem_realizedH0supC) で証明可。**但し giant HC/hcHom (iso-composite)
  term で whnf 爆発** (refine + proof body 共に、2000000 heartbeats でも timeout)。giant-declaration
  技法要 ([[lean-giant-declaration-debugging]]: HC abbreviation/type-synonym、term-pinning、
  hcHom を opaque に扱う rw)。fresh context で。
- **H⊄ker ζ**: ζ over θ₀ (nontrivial on H)。
- **bundle ζ as IrreducibleCharacter** ⟨induce HC ψ, hcZeta_irreducible⟩。
- **M-level**: ζ not-W1-fixed → I_M(ζ)=HU (prime-index eq_of_le_of_prime_index) → χ=induceHU(ζ) irr
  (isIrreducibleCharacter_induce_of_inertia_eq + huSub_normal) deg q·u=qu (induceHU_apply_one_eq_q_mul)。
- χ∈𝒮(H₀C) → conjunct c (caseA_character_counts:5166)。

inertia heart + degree-u irreducible 完成 (最難部分)。残は giant-term 注意の final assembly。


## H₀C⊆Ker ζ LANDED + H⊄Ker ζ の route 確定 (2026-07-01, commit 1bf9e469)

**giant-term whnf/isDefEq 突破 (前 iteration の blocker 解消)**: H₀C⊆Ker ζ を 2 段技法で landing:
- **instance-free 本体抽出**: `hcPsi_mem_characterKernel_of_mem_realizedH0supC` +
  `hcPsi_realizedH0supC_subgroupOf_subset_characterKernel` を induce/Invertible instance scope
  の外で証明 (巨大 HC/ψ 項が whnf-exploding manipulation に入らない)。
- **A/H pin (named args)**: `subsetCharacterKernel_induce_of_subgroupOf (A:=)(H:=)` で {A H} の
  繰り返し巨大 unification (isDefEq 爆発源) 回避。`hcZeta_H0supC_subset_ker` axiom-clean green。
  → **giant-declaration の汎用パターン**: 巨大項の lemma 適用は (1) 本体を instance-free helper に
  逃がす + (2) implicit subgroup を named-arg で pin。[[lean-giant-declaration-debugging]]

**残 home stretch の route 確定 (全 machinery 在庫確認済)**:
1. **H⊄Ker ζ (ζ∈xiSet)** = `¬(hInHu ⊆ characterKernel ζ)`。route:
   - `IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver HC ζ ψ` (Clifford.lean:583): ⟨Ind ψ,ζ⟩≠0
     ⟺ ζ LiesOver ψ。ζ=Ind ψ ゆえ ⟨Ind ψ,ζ⟩=⟨ζ,ζ⟩=1≠0 (ζ irreducible self-inner)。→ ζ LiesOver ψ。
   - `liesOver_mem_characterKernel` (S11:5579): ζ LiesOver ψ + (g:HU)∈ker ζ → g∈ker ψ (g:HC)。
     仮に hInHu⊆ker ζ → ∀h∈hInHu, ψ(incl h)=ψ(1)。
   - 矛盾: `hcPsi_apply_inclusion` で ψ(incl h)=θ₀-value、θ nontrivial (hθnt 仮説、assembly では
     CliffordCaseAData の regular θ̄) → ∃h ψ(incl h)≠ψ(1)。∴ H⊄Ker ζ。
   - **実装**: bundled `def hcZeta := ⟨induce HC ψ, hcZeta_irreducible⟩` を先に作り `hcZeta_mem_xiSet` 証明。
2. **ζ∈xiOf(H₀C)**: `mem_xiOf.mpr ⟨hcZeta_mem_xiSet, hcZeta_H0supC_subset_ker⟩` (cSub=chars.C 一致確認)。
3. **M-level**: ζ not-W1-fixed → I_M(ζ)=HU (prime-index [M:HU]=q, eq_of_le_of_prime_index) →
   χ=induceHU(ζ) irr (isIrreducibleCharacter_induce_of_inertia_eq + huSub_normal) deg
   q·u=qu (`induceHU_apply_one_eq_q_mul` + `hcZeta_apply_one` ζ(1)=u)。
4. χ∈SOf(H₀C) = `mem_sOf.mpr ⟨ζ, ζ∈xiOf, rfl⟩` → conjunct c (caseA_character_counts:5270)。

inertia heart + ζ-irreducible + degree + H₀C⊆Ker 完成。残=xiSet membership (LiesOver descent) + M-level。


## ζ∈𝒳(H₀C) 完成 + M-level route 確定 (2026-07-01, commits 2c428020/a6225c3a)

**LANDED**: `hcZeta_mem_xiSet` (H⊄Ker ζ, Frobenius/LiesOver descent — construction 方向の xiSet
産出、新領域) + `hcZeta_mem_xiOf` (両半分合成)。**ζ = Ind_{HC}^{HU}(ψ) ∈ 𝒳(H₀C) 完全確立**。

**残 = M-level のみ (conjunct c の最終ゲート)**:
- **degree (easy)**: `induceHU (ζ:CF)(1) = q·ζ(1) = q·u = qu`。`induceHU_apply_one_eq_q_mul` +
  `hcZeta_apply_one` (ζ(1)=u、既 landed)。coe_mk で bundled→induce HC ψ。
- **χ∈SOf (easy)**: `mem_sOf ⟨ζ, hcZeta_mem_xiOf, rfl⟩` (SOf=sOf, chars.C=cSub data chief 確認済)。
- **IsIrreducibleCharacter (induceHU ζ) (hard, propagation 要)**:
  - `isIrreducibleCharacter_induce_of_inertia_eq` at M-level: I_M(ζ)=HU → induceHU ζ irreducible。
  - **I_M(ζ)=HU** via `eq_of_le_of_prime_index` (S11:2230, HU≤I≤M ∧ [M:HU]=q prime ∧ I≠M → I=HU):
    - HU≤I_M(ζ): subgroup_le_inertia (HU◁M)。
    - [M:HU]=q: huSub_index_eq_q (既 landed)。
    - **I_M(ζ)≠M (= ζ not-W1-fixed) = 残る実質ゲート**: θ̄ は `clifford_caseA_exists_regular_char_not_fixed`
      (S11:4914) で regular ∧ θ̄.comp(act.φ w₀)≠θ̄ (non-W1-fixed) を産出済。propagation
      **θ̄^{w₀}≠θ̄ → ζ^{w₀}≠ζ → I_M(ζ)≠M** を新規に組む (conjugation が induction+inflation と可換;
      ζ^{w₀}=ζ → 各 LiesOver constituent θ₀ も θ₀^{w₀} と一致 → θ̄^{w₀}=θ̄ の対偶)。これが (9.8.c) の
      最後の本質的数学。

**assembly**: 上 3 つ + hcZeta 構築 (CliffordCaseAData の θ̄ + inertia fact hθ₀ + instances) →
caseA_character_counts:5270 conjunct c。caseA_character_counts は H₀C machinery 後 (file 末) に relocate。

inertia heart + ζ-irreducible(HU) + degree + H₀C⊆Ker + xiSet + xiOf 完成。残=M-level propagation のみ。


## M-level 3 pieces LANDED; conjunct c は hIM-gated で組立可 (2026-07-01, commits bb5868ec/4bbbef61/40eaba00)

**LANDED (axiom-clean)**:
- `hcZeta_induceHU_apply_one`: (Ind_{HU}^M ζ)(1) = q·u = qu。
- `hcZeta_induceHU_mem_sOf`: Ind_{HU}^M ζ ∈ 𝒮(H₀C)。
- `hcZeta_induceHU_irreducible` (**hIM-gated honest conditional**): hIM (I_M(ζ)≠⊤) を仮定して
  Ind_{HU}^M ζ irreducible (HU≤I_M via subgroup_le_inertia, [M:HU]=q prime via huSub_index_eq_q +
  data.nontrivial.2.1, eq_of_le_of_prime_index → I_M=HU, isIrreducibleCharacter_induce_of_inertia_eq)。

**conjunct c (caseA_character_counts:~5270) は hIM さえあれば組立可**: χ=induceHU(induce HC ψ),
∈SOf ✓ deg qu ✓ irreducible ✓(hIM)。残 = **hIM discharge (唯一の本質ゲート)**:
- **propagation θ̄^{w₀}≠θ̄ → conjBy w₀ ζ≠ζ → I_M(ζ)≠⊤** (deep Clifford)。
  w₀ datum = `clifford_caseA_exists_char_inertia_hc_not_fixed` (S11:5014) が θ + hθ₀ + w₀ 産出。
  - conjBy(w₀-as-M-elt) (induce_{HC}^{HU} inflation θ) = induce(inflation θ^{w₀}) (conjugation が
    induce+inflation と可換) ≠ ζ (injective: θ̄↦ζ)。Coq PFsection9.v Part_a (880-915):
    cfInd_sum_Inertia / inertia_irr_prime / sub_inertia_Res で M-level inertia 計算。**Coq 証明本体を
    熟読してから組む** (標準 Coq-first)。
- **assembly**: caseA から S₀/hS₀ne/hS₀inv/hS₀card/hp3 → θ 構築; instances (Fintype/Invertible/Normal
  for HC) 確立; hIM discharge → conjunct c の sorry 埋め (relocate 後)。

ζ∈𝒳(H₀C) + degree + SOf + M-level irreducible(gated) 完成。残=propagation 1 ゲート + assembly。


## conjunct-c FULLY ASSEMBLED — 残ゲートは propagation 1 本のみ (2026-07-01, commit 96e9c0a8)

**hcZeta_exists_irreducible_sOf** (hIM-gated): ∃ χ∈𝒮(H₀C), IsIrreducibleCharacter χ ∧ χ(1)=qu を
3 ピース (mem_sOf + irreducible + deg) で組立完了。conjunct c は **hIM さえ discharge すれば閉じる**。

**build-red 修正 (重要)**: 40eaba00 の hcZeta_induceHU_irreducible は **leaf stale-green** で commit された
build-red だった。原因 = (1) Invertible (card M) 未供給、(2) induceHU vs ClassFunction.induce の
**letI/haveI desync** (induceHU は letI で instance を焼込むので、ambient も **letI (透明) で供給せねば
defeq せず** exact/show/convert 全滅; haveI=opaque で破綻)。修正 = 全 instance を letI 供給 → exact 一発。
正本 memory = [[lean-induce-transport-instance-desync]]。**clean rebuild (rm olean) で検証必須**
([[leaf-build-stale-green]])。

**残 = hIM discharge のみ (唯一の本質ゲート)**: θ̄^{w₀}≠θ̄ → conjBy w₀ ζ≠ζ → I_M(ζ)≠⊤ (deep Clifford)。
machinery 在庫: `liesOver_conjBy`/`liesOver_conjBy_iff` (Clifford:836/846, conjBy equivariance),
`RestrictionConstituentsSingleOrbit` (Clifford:870, 単一軌道), `induce_conjBy_eq` (Clifford:531),
`clifford_caseA_exists_char_inertia_hc_not_fixed` (S11:5014, θ+hθ₀+w₀ 産出)。
route: ζ LiesOver θ₀ → conjBy w₀ ζ=ζ なら ζ LiesOver conjBy w₀ θ₀ → 単一軌道で θ₀,conjBy w₀ θ₀ が
HU-共役 → θ̄^{w₀}∈U-orbit(θ̄) → free-orbit 矛盾。Coq PFsection9 Part_a (880-915) +
factor-permutation (980-994: conjg_Iirr) を熟読してから組む。

ζ∈𝒳(H₀C) + degree + SOf + M-level irreducible(gated) + assembly 完成。残=propagation 1 本。


## propagation (hIM) 完全 mapping — 残ゲートの precise gap 特定 (2026-07-01)

**explicit route (全 producer 在庫確認)**:
1. ζ LiesOver θ₀ (hInHu-level): `exists_constituent_not_subset_characterKernel` (ζ∈xiSet=H⊄ker ζ →
   ∃θ₀ constituent nontrivial on hInHu)。θ₀ = inflation of 何らかの nontrivial θ̄'。
2. SingleOrbit ζ: `restrictionConstituentsSingleOrbit_of_isIrreducible ζ` (CliffordSingleOrbit:120,
   Clifford Thm 6.5、[hInHu.Normal][Fintype][Invertible] で直接適用)。
3. 仮定 conjBy w₀_M ζ=ζ → `liesOver_conjBy` で ζ LiesOver conjBy w₀_M θ₀。
4. `RestrictionConstituentsSingleOrbit.exists_conj` (Clifford:828): θ₀, conjBy w₀_M θ₀ HU-共役
   → ∃h∈HU, conjBy h θ₀ = conjBy w₀_M θ₀ → **θ̄^{w₀} ∈ U-orbit(θ̄)** (h の U-成分)。

**precise gap (残る本質)**: 矛盾には **θ̄^{w₀} ∉ U-orbit(θ̄)** が要る。現 seed
`clifford_caseA_exists_char_inertia_hc_not_fixed` は **θ̄^{w₀}≠θ̄ しか与えない** (U-orbit が
θ̄^{w₀} を含めば ≠ でも矛盾せず; U-stab(θ̄)=C≠U ゆえ U-orbit は u 元で非自明)。
**strengthen 要**: regular θ̄ の factor 構造 (W1 が q factor を q-cycle で置換、U は
factor-arrangement 保存) から θ̄^{w₀} ∉ U-orbit(θ̄) を導く (= free-W1-orbit の真の content)。
+ **w₀ の M-realization** (act.E elt → M elt) + conjBy。deep、複数 iteration。

**alternative route (counting、要検討)**: Coq `oXtheta` (PFsection9:952) `u·|Xtheta|=(p-1)^q>0` →
∃ irreducible 𝒮(H₀C)-member (個別構成+I_M=HU 不要、cardinality から存在)。conjunct c は
∃ で足りるので、total |𝒮(H₀C)| count - reducible(p-1) > 0 で済む可能性。次 iteration で
Coq oXtheta 構造を精査し、explicit(free-orbit) vs counting のどちらが tractable か判断。

construction 完成 (assembly まで)。残 = hIM 1 本 (free-orbit content、deep)。


## propagation — 完全構造設計 (build-ready lemma chain) (2026-07-01)

**次 iteration は BUILD (再分析でなく)**。hIM = `ClassFunction.inertia (induce HC ψ) ≠ ⊤` を以下の
lemma chain で。machinery 在庫確認済 (inner_conjBy_conjBy, SingleOrbit, exists_conj, liesOver_conjBy)。

**L1 (新, restriction-conjBy commute across levels)**: `Res_{hInHu}(conjBy_{M,HU} m ζ)
= conjBy_{M,hInHu} m (Res_{hInHu} ζ)` (m∈M)。proof = ext x; 両辺 ζ(m⁻¹ x m)。`conjBy_restrict`
(Inertia:154) は G-char 専用で不適 (ζ は HU-char、M-char でない) → 新規。多段 coercion
(hInHu→HU→M) に注意。

**L2 (M-equivariance of restrictionMultiplicity)**: `restrictionMultiplicity (conjBy m χ) (conjBy m θ)
= restrictionMultiplicity χ θ` = inner(Res(conjBy m χ))(conjBy m θ) =[L1] inner(conjBy m (Res χ))(conjBy m θ)
=[inner_conjBy_conjBy, Inertia:173] inner(Res χ)(θ)。

**L3 (構造 reduction、hIM core)**: `(∃m∈M, conjBy m θ₀ ∉ HU-orbit(θ₀)) ∧ ζ LiesOver θ₀ → hIM`。
conjBy m ζ=ζ 仮定 → [L2] ζ LiesOver conjBy m θ₀ → [restrictionConstituentsSingleOrbit_of_isIrreducible
ζ + exists_conj] conjBy m θ₀ ∈ HU-orbit(θ₀) 矛盾 → m∉inertia(ζ) → inertia≠⊤。
(ζ LiesOver θ₀ は exists_constituent_not_subset_characterKernel から、ζ∈xiSet ゆえ)。

**L4 (∉ U-orbit、最深 gap)**: conjBy m θ₀ ∉ HU-orbit(θ₀) を θ̄^{w₀}∉U-orbit(θ̄) から。
**θ̄ non-constant factor-data + U が factor 内で作用 (S₀ U-inv → 各 act.φ w•S₀ U-保存) +
W1 が q factor を q-cycle 置換** → θ̄^{w₀}(置換) ≠ θ̄^u(factor 内 twist) ∀u。
`exists_regular_char_not_fixed` (S11:2314, θ̄^{τ}≠θ̄ のみ) を ∉ U-orbit に**強化要** (per-factor
support 比較、全 u∈U)。free-W1-orbit の真の content。

**L5 (W1 realization)**: w₀∈act.E → 実 W1≤M elt m。conjBy m と act.φ w₀ の対応。

construction (assembly まで) 完成・full build green。残 = L1-L5 (deep §9 free-orbit、複数 iteration)。


## propagation build — 新 infrastructure 要 (definitive assessment) (2026-07-01)

L1-L3 の build 着手で判明: **M-conjugation の既存 API が無い**。`conjBy (g:G)(θ:CF ↥H)` は H◁G・g∈G
を要するが、θ₀ : CF ↥(hInHu data) で hInHu data は **Subgroup ↥(huSub data)** (HU 内)、m∈↥M ゆえ
**hInHu を ↥M の subgroup として持ち直す transport が必要** (hInHu.map huSub.subtype 等)。
さらに既存 Clifford framework (`restrictionConstituentsSingleOrbit_of_isIrreducible`,
`exists_conj`, `restrictionMultiplicity_conjBy_right`) は全て **HU-conjugation (g∈huSub) 前提**で、
hIM が要する **M-conjugation (m∈M) と framework-bridge が要る**。

**次 iteration が先に build すべき infrastructure (fresh context 推奨)**:
- (I1) hInHu char の M-conjugation: m∈M に対し h↦mhm⁻¹ を hInHu-aut として実現 (H◁M ゆえ
  well-def) し `conjBy`-互換な CF ↥(hInHu) を定義、または hInHu.map huSub.subtype で ↥M-subgroup 化。
- (I2) restrictionMultiplicity の M-equivariance (I1 + inner_conjBy_conjBy)。
- → その後 L3 (reduction) は既存 SingleOrbit/exists_conj で閉じる。
- L4 (θ̄^{w₀}∉U-orbit, type-clean だが factor-arrangement deep) + L5 (W1 realization) は別途。

これは **substantial sub-project** (新 conjBy-transport infra + deep factor content)。construction
(assembly まで) は完成・full build green。残 hIM = この sub-project。stale-green 注意 (rm olean 検証)。


## propagation — CLEANER build path (compHom-by-aut, transport 回避) (2026-07-01)

前記 infra assessment の subgroup-transport は**不要**。M-conjugation を **m-conjugation aut で compHom**
として表せば全て hInHu レベルで閉じる:
- **φ_m : ↥(hInHu data) →* ↥(hInHu data)**, h ↦ ⟨m·h·m⁻¹, _⟩ (well-def: H◁M ゆえ m が hInHu 正規化)。
  coercion 鎖 ↥(hInHu)→↥(huSub)→↥M に注意 (huSub data : Subgroup ↥M)。
- **核心 identity**: `Res_{hInHu}(conjBy (G:=↥M)(H:=huSub) m ζ) = ClassFunction.compHom φ_m (Res_{hInHu} ζ)`
  (ext + 値計算 ζ(m h m⁻¹))。← これで M-conjugation を compHom-by-aut に変換。
- conjBy m ζ=ζ → Res ζ = compHom φ_m (Res ζ) → θ₀ constituent なら compHom φ_m θ₀ も constituent
  (要 **inner-compHom-by-aut invariance**: inner(compHom φ a)(compHom φ b)=inner a b, φ aut; 既存
  inner_conjBy_conjBy 類似、無ければ build)。
- `restrictionConstituentsSingleOrbit_of_isIrreducible ζ` + `exists_conj`: ∃g∈huSub,
  conjBy_{huSub} g θ₀ = compHom φ_m θ₀ → (g-conj = m-conj on θ₀) → θ̄^{w₀}∈U-orbit → free-orbit 矛盾。

**hIM 自体は clean** (inertia_M(ζ)=conjBy (G:=↥M)(H:=huSub) m ζ、huSub data : Subgroup ↥M ゆえ多段不要)。
fiddly なのは argument 内の Res↔compHom 橋 (φ_m + identity + inner-compHom)。次 iteration build。
construction 完成・green。


## propagation Clifford reduction 完全完成 (L1+L2+L3+assembly) — 残 L4/L5 (2026-07-01)

**LANDED (commits 94a76573/7412a9e1/afc5c7a1/8d4162ac/239bbd27/1d8e5293、全 clean-rebuild green)**:
- L1: `hInHuConj` (φ_m, m-conjugation aut) + `hInHuConj_restrict_conjBy` (Res(conjBy m ζ)=compHom φ_m(Res ζ))。
- L2: `innerSum/inner_compHom_of_bijective` + `hInHuConj_bijective` + `hcZeta_liesOver_compHom_of_fixed`
  (conjBy m ζ=ζ ∧ ζ LiesOver θ₀ → ζ LiesOver φ_m·θ₀)。
- L3: `hcZeta_exists_conj_of_fixed` (→ ∃g∈HU, conjBy g θ₀=compHom φ_m θ₀)。
- assembly: `hcZeta_inertia_ne_top_of_free` (**hIM ⟸ free-orbit hfree + ζ LiesOver θ₀**)。

**残 L4 (free-orbit hfree、deep) — 大量 reuse 判明**:
- `conjBy_compHom_hInHuEquivH` (S11:4500) = **inflation-conjugation commute 既存**:
  conjBy g (compHom hInHuEquivH θ) = compHom hInHuEquivH (compHom (typeP_conjAction a) θ) (↑g=↑a)。
- θ₀ = compHom hInHuEquivH (compHom (mk' N) (linearIrr θ̄))。conjBy g θ₀ / compHom φ_m θ₀ を
  これ + compHom_comp で quotient action on θ̄ に落とす (caseB_char_inertia 系が手本)。φ_m (m∈M) 側は
  conjBy_compHom_hInHuEquivH の m∈M 類似が要 (または hInHuConj を huSub-conjBy 経由で接続)。
- inflation injective (exists_compHom_eq 系) → hfree ⟺ θ̄^{w₀}∉U-orbit。
- **free-orbit θ̄^{w₀}∉U-orbit**: `exists_regular_char_not_fixed` (S11:2314、θ̄^{τ}≠θ̄) を ∉U-orbit に強化
  (regular θ̄ non-constant factor、W1 q-cycle 置換、U factor 内): per-factor support 比較。
**残 L5**: w₀∈act.E の m∈M realization + 構築 ζ の ζ LiesOver θ₀ → assemble hIM →
`hcZeta_inertia_ne_top_of_free` → `hcZeta_induceHU_irreducible` → `hcZeta_exists_irreducible_sOf` → conjunct c。

Clifford reduction (genuinely new infra) 完成。残=L4 (free-orbit 深) + L5 (realization wiring)。


## L4 connection chain — caseB inertia machinery で大量 pre-built (2026-07-01)

L4 の connection chain (hfree ⟺ θ̄^{w₀}∈U-orbit) は **caseB inertia machinery でほぼ既存**:
- `conjBy_compHom_hInHuEquivH` (conjBy g) + `compHom_hInHuConj_hInHuEquivH` (compHom φ_m、新規 build 済):
  両 conjugation を typeP_conjAction a/b (↑g=↑a, ↑m=↑b) へ。
- `compHom_typeP_conjAction_inflation` (S11:4400、**rfl**): typeP_conjAction a (compHom (mk' N) θ̄)
  = compHom (mk' N) (quotientMulAutHom a θ̄)。← descent to quotient action。
- `compHom_injective_of_surjective` (hInHuEquivH surj + mk' N surj): 二重 inflation strip。
- → conjBy g θ₀=compHom φ_m θ₀ ⟺ quotientMulAutHom (g-image) θ̄ = quotientMulAutHom (w₀) θ̄
  ⟺ θ̄^{act.φ(U-image of g)} = θ̄^{w₀}。g∈huSub の quotient image は huSub/hInHu≅U で U-element
  (H-part は inner=trivial) → ∃g ⟺ **θ̄^{w₀}∈act.φ-U-orbit**。
- `caseB_inertia_realized` (S11:4570) が realization+descent の手本 (a∈U, g∈huSub, ↑g=↑a)。

**残 L4 = (1) connection reduction lemma** (上を組む、realization g→U-image 込) **+ (2) 深部
free-orbit θ̄^{w₀}∉act.φ-U-orbit** (`clifford_caseA_exists_char_inertia_hc_not_fixed` は θ̄^{w₀}≠θ̄
のみ → ∉U-orbit に強化: regular θ̄ non-constant factor、W1 q-cycle 置換、U factor 内)。
**残 L5 = w₀ realization (m∈M) + 構築 ζ の ζ LiesOver θ₀** (ζ LiesOver ψ→θ₀、restriction 推移)。
→ assemble hIM → hcZeta_induceHU_irreducible → conjunct c。

Clifford reduction + connection commutes 完成。残=connection reduction wiring + free-orbit (深) + L5。


## free-orbit = factor-structure inertia (Coq def_Itheta) — 深部 crux 確定 (2026-07-01)

connection core (eebacf96) で hfree ⟺ θ̄^{w₀}∉U-orbit (≡ I_M(θ₀)≤HU、≡ Stab_{UW1}(θ̄)≤U) に帰着。
これは **θ̄^{w₀}≠θ̄ より真に強い** (U が factor char に transitive だと ≠ でも ∈U-orbit になりうる)。

**Coq PFsection9 def_Itheta (938-948)**: `f∈Ftheta → I_HU[theta f]=HC` を **`inertia_bigdprod_irr`
+ `inertia_irr_prime`** で証明 = **factor-structure (bigdprod) inertia 機構**。free-orbit は
この factor inertia 論 (W1-conjugate factors {act.φ w•S₀} の bigdprod、U は各 factor 保存、
W1 は q-cycle 置換、regular θ̄ の per-factor char が factor 跨ぎで非自明) を要する。Lean に
inertia_bigdprod_irr 相当が無ければ新規 (substantial §9 機構)。Coq oXtheta (u·|Xtheta|=(p-1)^q) は
counting だが conjunct c の M-level IsIrreducibleCharacter は I_M=HU を要し、現 explicit approach
(L1-L3+connection core 完成) が直接提供 — 残 free-orbit 1 本。

**propagation 完成度**: L1+L2+L3+assembly+connection commutes+connection core = 9 commits、
hIM ⟸ θ̄^{w₀}∉U-orbit。残 = (1) **free-orbit factor inertia** (深、Coq inertia_bigdprod_irr guide) +
(2) g→a∈U realization (wiring) + (3) L5 (w₀→m, ζ LiesOver θ₀) + assembly。free-orbit が
research-level に深ければ Coq 熟読 → ChatGPT escalation も選択肢 ([[feedback-ask-chatgpt-for-elided-gaps]])。


## ChatGPT consult SENT — free-orbit strategy (2026-07-01)

free-orbit θ̄^{w₀}∉U-orbit (深部 crux、cleanest Lean strategy 不明) を ChatGPT Pro (model 最高)
に送信。**tabId 1470253202** (chatgpt.com、新 chat、ログイン済 石田和 Pro)。プロンプト =
`notes/peterfalvi/s11_freeorbit_chatgpt_prompt.md` (commit済)。質問: (a) factor-permutation/
direct-product inertia vs (b) Frobenius-subgroup argument vs (c) cleaner; θ̄^{w₀}≠θ̄ で十分か
"no U-conjugate is W1-fixed" が要るか; 構築時に ∉U-orbit を即時にする θ̄ の選び方; precise lemmas。

**次 iteration**: `mcp__Claude_in_Chrome__get_page_text{tabId:1470253202}` で回答を回収 (Pro は
思考 ~10min)。回答を厳密検証してから free-orbit を formalize。未了なら再 poll + 並行で wiring
(ζ LiesOver θ₀, realization) を build。tools: ToolSearch{query:"chrome browser tab navigate page"}。


## ChatGPT consult ANSWER (verified) — 構築 strengthen 要・lemma chain 確定 (2026-07-01)

回答回収・**厳密検証済** (counterexample 具体的に正しい、Lemma A/F の証明正しい)。正本=
`notes/peterfalvi/s11_freeorbit_chatgpt_answer.md`。**重大**: 現構築 (fact 2 = θ̄^{w₀}≠θ̄) は
**θ̄^{w₀}∉U-orbit に不十分** (反例 C₇⋊C₃/p=29、uw₀ が θ̄ を固定しうる)。

**lemma chain (formalize 対象)**:
- **Lemma A** (semidirect stabilizer、q prime): I_G(x)≤U ⟺ x^{w₀}∉x^U。pure group theory。
- **Lemma C** (direct-product char extensionality), **D/E** (component formula + factor-orbit
  separation): θ̄^w∈θ̄^U ⟺ ∃u,∀i transport_w(θ_{w⁻¹i})=θ_i^u; ∃i で ∉U-orbit(θ_i) なら θ̄^w∉θ̄^U。
- **Lemma F** (marked-factor): U-orbit-label i↦[θ_i]_U 非定数 → q-cycle (q prime) で固定不可 →
  θ̄^{w₀}∉U-orbit。**要 ≥2 U-orbit on Irr(factor)^# = im(U→F_pˣ) proper (u<p-1)**。
- im(U) transitive なら **exponent criterion (Lemma G)**: Δ_{w₀}(a)∉ρ(U)。u=1 なら fact 2 で十分。

**redirected plan**: 現 reduction (hcZeta_inertia_ne_top_of_free, hfree 取る) は正しく構築済。
残 = hfree (θ̄^{w₀}∉U-orbit) を **marked-factor 構築 (strengthen clifford_caseA_exists_char_not_fixed)
+ Lemma C/D/E/F chain** で discharge。**要 caseA で u<p-1 (im(U) proper) を確認** (否なら Lemma G)。
+ realization wiring (g→a) で connection core を全 g に lift。


## free-orbit 構築: a∣p-1、marked-factor は a<p-1 要、exponent criterion が robust (2026-07-01)

`CliffordCaseAData.a` (a∣p-1) = U の factor 上 action order (|im(U→F_pˣ)|=a)。U-orbit-class 数 =
(p-1)/a。**marked-factor (Lemma F) は ≥2 class 要 = (p-1)/a≥2 = a<p-1** (a∣p-1 では保証されない;
a=p-1 なら U transitive で marked-factor 不可)。

**→ exponent-vector criterion (Lemma G) が robust path** (a 不問): θ̄ を exponents e=(e_i)∈(F_pˣ)^q
で encode、U-action ρ(u)∈(F_pˣ)^q (factor 毎 scalar)、Δ_{w₀}(e)_i:=e_i⁻¹ e_{w₀⁻¹i}。
θ̄^{w₀}∈U-orbit ⟺ Δ_{w₀}(e)∈ρ(U)。|ρ(U)|=a ≤ p-1 << (p-1)^q (q≥2) ゆえ大半の e で Δ_{w₀}(e)∉ρ(U)
→ 構築時に e を選べば θ̄^{w₀}∉U-orbit。**exists_regular_char を Δ_{w₀}(e)∉ρ(U) 込で強化**。

**残 build (次 iteration、深 construction)**: (1) Lemma C (direct-product char ext: χ=ψ⟺∀i factor 上等)
+ D/E (factor-orbit separation)、(2) θ̄ 構築 (Δ_{w₀}(e)∉ρ(U) or marked-factor if a<p-1 確認) →
θ̄^{w₀}∉U-orbit = hfree、(3) g→a realization で connection core を全 g lift →
hcZeta_inertia_ne_top_of_free → conjunct c。reduction+connection 完成済; 残=construction-side discharge。
session 巨大 (compaction 近); 次 fire は fresh context で深 construction を engage。

## ★ 重大 redirect: (9.8.c) は counting+parity であって free-orbit/exponent でない (2026-07-01)

**Coq PFsection9.v `typeP_nonGalois_characters` (= Peterfalvi (9.8)) part (c) を精読** (CLAUDE.md の
Coq-first で行間補完)。part (c) = `exists t, isIndHC 'chi_t` で `isIndHC zeta := [/\ zeta 1 = (q*u),
zeta ∈ S_ H0C & ∃ xi linear, zeta = 'Ind xi]` — **これが我々の conjunct c そのもの** (degree qu の
M-irreducible 𝒮(H₀C)-member)。

**Coq の証明は free-orbit/exponent 構築でなく counting + parity** (PFsection9.v:1083-1107):
- `Xtheta` = HU-level の degree-u irr chars (𝒳(H₀C) に相当)、`oXtheta: u·|Xtheta| = (p-1)^q`。
- `Xmu` ⊆ `Xtheta` = **constant factor-data** から来る reducible-producing ζ、`|Xmu| = p-1`
  (`mu_f i := [ffun w => if w∈W1bar then i else 0]`、`sW1_Imu`: constant data は W1-invariant)。
- **parity dichotomy**: `Xmu ⊆ Xtheta` を `eqVproper` で2分:
  - **proper (Xmu ⊊ Xtheta)**: ∃ s ∈ Xtheta\Xmu → `'Ind[M] 'chi_s ∈ irr M` (reducible なら mu_ に
    入り s∈Xmu に矛盾、`cfclass_Ind_irrP`/`ResIndXmu` 経由) → degree qu witness。
  - **equality (Xmu = Xtheta)**: `|Xtheta|=|Xmu|=p-1` → oXtheta から `u = (p-1)^{q-1}`。p odd で
    (p-1) even ⟹ u even。だが **u は ODD** (odd-order: u=|Ū| ∣ |G| odd) ⟹ 矛盾。∴ この場合は不可能。
- ∴ parity が強制的に proper case を選び、witness t を生む。**number-theory (ρ(U)=K) gap を完全回避**。

**→ 新 plan (free-orbit/exponent route を放棄)**: conjunct c を以下で閉じる:
1. **(A) total count `u·|𝒳(H₀C)| = (p-1)^q`** (oXtheta) — **未形式化、最大の残ピース**。bijection
   𝒳(H₀C) ↔ regular factor-data Ftheta (|Ftheta|=(p-1)^q)、u-fold induction fiber。
2. **(B) reducibles ⊆ 𝒳(H₀C)、count p-1**: `reducible_count_sOf_K` 既存 ✓ (Xmu 相当)。
3. **(C) u odd**: odd-order から導出 (要 wiring)。
4. **(D) parity**: |𝒳(H₀C)| ≥ p-1 (B) かつ等号なら u=(p-1)^{q-1} even が u-odd と矛盾 ⟹ **|𝒳(H₀C)| > p-1 厳密** ⟹ ∃ ζ ∉ reducible-set。
5. **(E) ζ ∈ 𝒳\reducible ⟹ Ind_M(ζ) irreducible** (degree qu): cfclass 論 (reducible⟹mu_⟹矛盾)。

**既存 free-orbit machinery** (hcZeta_inertia_ne_top_of_free, conjBy_eq_compHom_iff_quotient,
Clifford conjugation reduction、~13 commits) は **green・保存** だが conjunct-c の主経路からは外れる
(別 route として valid、機械は再利用可)。**Lemma C (char_eq_of_eq_on_factors) は commit 382b02df で
landed** (counting route でも factor-data bijection で有用)。

**次 iteration**: (A) total count の形式化に着手 (𝒳(H₀C) ↔ Ftheta bijection、|Ftheta|=(p-1)^q)。
これが counting route の心臓。Coq PFsection9.v:956 `oXtheta` + 920-960 の `theta f`/`inj_theta`/
`card_imset_Ind_irr` を port。session 巨大 (compaction 近)。

## ★ counting route 3 片 landed — 次 crux = def_Itheta (U-inertia) (2026-07-01 cont.)

前 redirect (counting+parity) に沿って **3 lemma landed (全 axiom-clean [propext/Classical.choice/
Quot.sound]、commits 5bd37de3/62aeb4f0)**:
1. `charRestrictEquiv`+`card_regular_chars` (抽象、S11:2337/2359): internal direct product
   H̄=⊕Sᵢ (各 order p、q factor) の全 factor 上非自明 char 数 = (p-1)^q。charRestrictEquiv
   (char ≃ factor-restriction tuple、inj=Lemma C `char_eq_of_eq_on_factors`/surj=
   `char_eq_on_factors_of_bijective`) + subtypeEquiv + `card_monoidHom_of_hasEnoughRootsOfUnity`。
2. `card_regular_chars_Hbar` (concrete、S11:~2471): 上を `CliffordCaseAData.Hpart` に instantiate。
   H̄=↥H⧸N の各 Hpart i 上非自明 char 数 = (p-1)^q。Hpart_iSupIndep+iSup で noncommPiCoprod
   bij、`IsMulCommutative→CommGroup`=scoped instance (`open scoped IsMulCommutative`)。= **oXtheta 分子**。
3. `exists_regular_not_reducible_of_odd` (parity 核、S11:~5350): finite X⊇Xmu (|Xmu|=p-1)、
   u·|X|=(p-1)^q、u odd、p-1 even>0、q≥2 ⟹ ∃s∈X, s∉Xmu。equality |X|=p-1 ⟹ u=(p-1)^{q-1}
   が (q-1≥1・p-1 even で) even となり u-odd 矛盾。= **(9.8.c) dichotomy 抽象核**。

**既存 (9.8.c) construction 機構 (free-orbit route 由来だが counting でも再利用可)**:
- `hcPsi θ` (6118): θ:H̄→*ℂˣ から HC-linear char ψ=θ∘hcHom (trivial on H₀C)。
- `hcQuotientEquivHbar` (6084): HC/H₀C ≅ H̄ (第二同型)。
- `hcZeta_irreducible` (6312): **hθ₀ を仮定すれば** Ind_{HC}^{HU}(hcPsi θ) irreducible (degree u)。
  hθ₀ = `inertia(compHom hInHuEquivH (compHom mk'_N (linearIrr θ))) = hInHu ⊔ cInHu` (=HC at HU-level)。

**次 crux = def_Itheta (hθ₀ の証明、= U-inertia)**: regular θ (全 Hpart i 上非自明) に対し
inertia(inflated θ in HU) = HC を証明 = 「Ū=U/C が regular θ 上 free に作用」。
- 易半 HC ≤ inertia: `subgroup_le_inertia` (C=C_U(H̄) は H̄ に trivial 作用 → θ 固定)。
- 難半 inertia ≤ HC: U∖C の元は regular θ を動かす。**Hpart_aInvariant (U が各 factor 保存 ⟹
  Coq の factor-permutation case を回避、単純化)** ゆえ inertia(⊗θ_i)=∩ᵢ Stab_U(θ_i)、
  nontrivial θ_i on order-p factor で Stab_U(θ_i)=C-related (CliffordCaseAData.a 絡み)。
  要 新 machinery: (i) 「内部直積上の product char の inertia = ∩ factor inertia」(一般 reusable) +
  (ii) 「order-p factor 上 nontrivial char の U-stabilizer = C」。Coq inertia_bigdprod_irr+
  inertia_irr_prime。**deep、multi-iteration、fresh context 推奨**。

**assembly (def_Itheta 後)**:
- **oXtheta**: u·|Xtheta| = (p-1)^q。Xtheta={Ind_{HC}^{HU}(hcPsi θ) | regular θ}⊆𝒳(H₀C)。
  u-fold fiber = Ū-conjugate θ が同一 ζ を産む (def_Itheta の帰結)。numerator=`card_regular_chars_Hbar`。
- **(E) reducible⟹Xmu**: s∈Xtheta∖Xmu ⟹ Ind_M(chi_s) irreducible。対偶=reducible なら
  constant-factor-data (Xmu) に入る (Coq `cfclass_Ind_irrP`/`ResIndXmu`)。**W1-inertia 数論を回避**。
- **(C) u odd**: odd-order (|Ū|∣|G| odd)。
- **assembly**: `exists_regular_not_reducible_of_odd` + (E) → conjunct c。reducible count (B)=
  `reducible_count_sOf_H0` (既存、5347 で conjunct b1 に wire 済)。

**level 注意**: 𝒳(H₀C)=`xiOf data H0C` (HU-char)、𝒮(H₀C)=`sOf`=Ind_M 𝒳 (M-char)。conjunct c は
𝒮(H₀C) member = Ind_M(s), s∈Xtheta⊆𝒳(H₀C)。Xtheta=regular ones (Coq: Xtheta⊆X_H0C、**等号不要**)。

## ⭐ 訂正: def_Itheta は既に PROVEN (`inertia_eq_hcInHu_caseA`) (2026-07-01 cont.²)

**上の「次 crux = def_Itheta (deep 未証明)」は誤り** ([[verify-port-state-by-number-not-coq-name]]
の教訓そのもの — descriptive 名で grep せず deep 判定しかけた)。`inertia_eq_hcInHu_caseA`
(S11:4858) が **まさに def_Itheta**: regular θ̄ (∀i, θ̄ nontrivial on Hpart i) に対し
`I_{HU}(inflated θ₀) = hInHu ⊔ cInHu (=HC)` を**証明済み** (`inertia_eq_hcInHu_gen` →
`chiefFactor_caseA_char_inertia` 経由、case-agnostic plumbing)。これは `hcZeta_irreducible`
(6312) の `hθ₀` 仮定そのもの。

**⟹ 各 regular θ に対し degree-u irreducible ζ_θ = Ind_{HC}^{HU}(hcPsi θ) ∈ 𝒳(H₀C) は
既に構成可能** (`hcZeta_irreducible` に `inertia_eq_hcInHu_caseA` を hθ₀ として渡すだけ)。

**残 oXtheta = u-to-1 counting のみ (deep でない)**: 写像 θ ↦ ζ_θ ({regular H̄-char} → 𝒳(H₀C))。
- fiber = Ū-orbit (ζ_θ=ζ_θ' ⟺ hcPsi θ, hcPsi θ' が HU-共役 ⟺ θ, θ' が Ū-共役)。
- inertia=HC ⟹ Ū が regular θ 上 free (Stab_Ū=1) ⟹ 各 fiber size = |Ū| = u。
- ⟹ u·|Xtheta| = |{regular θ}| = (p-1)^q (`card_regular_chars_Hbar`)。
- 要: Ū-action on regular chars 設定 + free-action orbit count (mathlib MulAction) or
  induction-imset count (Coq `card_imset_Ind_irr` 相当)。**moderate**。

**残全体 (全て moderate、deep なし)**: (a) oXtheta u-to-1 count、(b) (E) reducible⟹Xmu
(cfclass 対偶)、(c) u odd (odd-order)、(d) assembly (`exists_regular_not_reducible_of_odd`)。
reducible count (B) = `reducible_count_sOf_H0` 既存。

## discharge recipe 確認済 + ⚠ whnf 壁 (bundled ζ_θ 構成) (2026-07-01 cont.³)

**hθ₀ discharge recipe は正しく型検査を通る** (試作で確認): regular θ:(↥H⧸N)→*ℂˣ から
```
have hreg' : ∀ i, ∃ x ∈ caseA.Hpart i,
    (linearIrreducibleCharacter θ : ClassFunction _ ℂ) x ≠ (linearIrreducibleCharacter θ : ...) 1 :=
  fun i => by obtain ⟨x,hx,hne⟩ := hreg i; exact ⟨x,hx, by
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one];
    simpa using hne⟩
have hθ₀ := inertia_eq_hcInHu_caseA data chief caseA hreg'  -- : hcZeta の hθ₀ そのもの
```
`hθ₀` は `hcZeta_irreducible`/`hcZeta_mem_xiOf`/`hcZeta_induceHU_*` の hθ₀ 引数に直接渡せる
(型一致確認済)。regular θ は `exists_regular_char caseA.Hpart Hpart_iSupIndep Hpart_iSup
(order→p_prime)` で取得 (要 `letI : CommGroup (↥H⧸N) := {inferInstance with mul_comm :=
chief.quotient_elementaryAbelian.comm}`、sub-block に scope)。θ≠1 は
`hreg ⟨0, data.nontrivial.2.1.pos⟩` (data.nontrivial.2.1 : (data.q).Prime) から。
instances (Fintype/Invertible huSub+sup、Normal sup=`hcInHu_realized_normal`) は proof 内 letI/haveI
で供給可 (存在文なら signature threading 不要)。

**⚠ 但し bundled ζ_θ 項の構成が whnf 壁**: `⟨ClassFunction.induce _ (hcPsi chief θ),
hcZeta_irreducible chief θ hθ₀⟩ : IrreducibleCharacter ↥(huSub data)` を作って coerce
(degree via `hcZeta_apply_one`、membership via `hcZeta_mem_xiOf`) すると **whnf timeout >2M
heartbeats** (induce-coercion defeq 爆発、[[lean-induce-transport-instance-desync]] /
[[lean-giant-declaration-debugging]])。`hcZeta_mem_xiOf` 自体は maxHeartbeats 1000000 で通るが、
呼び出し側で bundled 項を組むと爆発。試作 `exists_irr_deg_u_xiOf_caseA` は revert 済。

**次 iteration の対処** (count 構築時):
- coercion whnf を回避: `show`/`change` で ClassFunction 形に pin、degree/membership goal を分割、
  Invertible instance を named-arg `(Z:=)(S:=)` で pin、`rw` でなく `exact`。
- または **ClassFunction レベルで作業し bundled IrreducibleCharacter を最後に一度だけ materialize**
  (count は Set/Finset の ncard なので、写像 θ↦ζ_θ を ClassFunction 値で定義し injectivity/fiber を
  ClassFunction 等式で示す方が whnf 安全な可能性)。
- `hcZeta_induceHU_irreducible`/`hcZeta_exists_irreducible_sOf` (free-orbit endpoint) は既に
  同型の bundled 項を hIM 付きで扱っており、そこでの whnf 対処 (letI transparent 保持、6585 の
  hunfold idiom) が手本。

**残タスク (再掲、全 moderate、def_Itheta は proven)**: (a) oXtheta u-to-1 count (whnf 注意)、
(b) (E) reducible⟹Xmu、(c) u odd、(d) assembly (`exists_regular_not_reducible_of_odd`)。

## ★ oXtheta 設計確定 + crux 非依存入力 3 点 landed (2026-07-01 cont.⁴)

**セッション成果 (commits 8b1f996e/dd2dd97f、S11 leaf green、全 axiom-clean)**: oXtheta
`u·|Xtheta|=(p-1)^q` (θ↦ζ_θ=induce(hcPsi θ) の u-to-1 fibre count) の **crux 非依存入力 3 点**:
- `u_odd`: `Odd chars.u` (u=|Ū|=|range uActionHom| ∣ |U⊔W₁| ∣ |G| odd)。parity 入力。
- `hcHom_surjective` + `hcPsi_injective`: θ↦hcPsi θ 単射 ⟹ |{hcPsi θ|regular}|=(p-1)^q
  (`card_regular_chars_Hbar` の分子)。
- `hcPsi_inertia_index_eq_u`: regular θ で `[HU:I_{HU}(hcPsi θ)]=u` (inertia_eq_hcInHu_caseA→
  hcPsi_inertia_eq_hc→HC, hc_index_eq_u)。= 一様 fibre size。

**oXtheta engine 確定 = `card_filter_induce_eq_index_inertia`** (`InducedIrreducible.lean:259`):
conjugation-invariant Finset `T` の各 fibre `{θ∈T|induce θ=induce θ₀}.card=[G:I(θ₀)]`。
⟹ `T=RegSet.image (hcPsi chief)` (|T|=(p-1)^q), `image=T.image (induce HC ·)`,
`T.card=Σ_{ζ∈image} u = u·|image|` (Finset.card_eq_sum_card_fiberwise + 各 fibre=u)。

**残 crux = T conjugation-invariance** (`∀χ∈T,∀g, conjBy g χ∈T`)。分析確定:
1. **commute**: `(hcPsi θ:ClassFunction)=compHom hcHom (linearIrr θ)`
   (`ClassFunction.compHom_linearIrreducibleCharacter`)。`conjBy g χ=compHom (conjByMulEquiv g) χ`
   (定義: conjBy g θ h=θ(g h g⁻¹)=θ(conjByMulEquiv g h))。⟹ conjBy g (hcPsi θ)=
   compHom (hcHom.comp (conjByMulEquiv g)) (linearIrr θ)。
2. **factoring A_g**: `hcHom.comp (conjByMulEquiv g)=A_g.comp hcHom` (ker hcHom=H₀C=
   ker(hcHom∘conjByMulEquiv g) ∵ H₀C◁HU normal ゆえ g H₀C g⁻¹=H₀C)。A_g:H̄→*H̄ を
   MonoidHom.liftOfRightInverse (hcHom surj) or QuotientGroup.map + iso 経由で構成。
   ⟹ conjBy g (hcPsi θ)=compHom hcHom (linearIrr (θ.comp A_g))=hcPsi (θ.comp A_g)。
3. **regularity** (深部): θ.comp A_g regular ⟺ θ regular。要 A_g が各 Hpart factor 保存。
   g∈HU (W₁ 成分なし) ⟹ U-action は各 factor 保存 (`Hpart_aInvariant`)、H-part は H̄ 上 trivial
   ⟹ A_g(Hpart i)=Hpart i。**A_g↔U-action 接続が crux** (free-orbit の compHom_hInHuConj_hInHuEquivH
   の HC-level analog、L1-L3 並み)。`conjBy_compHom_eq_compHom_conjBy` (ConjugationBrauer:306) が
   inflation-conj equivariance だが H'≤G/M 形で hcHom の iso 層 (hcQuotientEquivHbar) が挟まり
   直接非適用 — iso 分解 (hcHom=iso∘mk') して mk' 部分に適用する要あり。

**次着手**: (1) commute existence `hcPsi_conjBy_eq: conjBy g (hcPsi θ)=hcPsi (θ.comp A_g)` (A_g 構成)、
(2) regularity (A_g factor 保存、U-action 接続)、(3) T-invariance 組立 + oXtheta 集約
(card_filter fiberwise)。その後 Xmu⊆Xtheta+|Xmu|=p-1 (reducible bijection) + 最終 assembly
(exists_regular_not_reducible_of_odd で witness、whnf 注意)。crux は multi-session (deep char endgame)。

## ✅ regularity half (T-invariance step (2)) COMPLETE — A_g↔U-action crux 解決 (2026-07-01 cont.⁵)

step (2) の crux (「A_g↔U-action 接続」= cont.⁴ で identified された唯一の深部) を **6 補題で完全形式化**
(S11、全 axiom-clean `[propext,Classical.choice,Quot.sound]`、S11 leaf green):
- **P3 `hcConjDescend_eq_uActionHom`**: `u∈uInHu` に対し `∃a, ∀z, hcConjDescend u z = uActionHom a z`
  (A_u = U-action の realization a)。証明 = `z=hcHom(incl h)` (hcHom∘incl 全射) で両辺を
  `mk'_N(G値 u_G·h_G·u_G⁻¹)` に落とす: 左 = `hcConjDescend_hcHom`+`hcHom_inclusion`+conjugate∈hInHu
  (normal.conj_mem)、右 = `quotientMulAutHom_apply_mk'`+`typeP_conjAction_apply`。**A_g↔U-action 接続の核心**。
- **factor-preservation `hcConjDescend_maps_Hpart`**: `∀g∈HU, z∈Hpart i → A_g z∈Hpart i`。
  分解 `g=h·u` (`Subgroup.normal_mul`+`hInHu_sup_uInHu_eq_top`) → `A_g=A_h∘A_u=A_u` (`hcConjDescend_mul`+
  `_eq_id_of_mem_hc`、h∈hInHu⊆HC) → P3 → `Hpart_aInvariant.smul_mem`。= cont.⁴ (1616) の `A_g(Hpart i)=Hpart i`。
- **`hcConjDescend_one`** (A_1=id、1∈HC) + **`hcConjDescend_apply_inv_apply`** (A_g∘A_{g⁻¹}=id、mul+A_1)
  ⟹ A_g は各 Hpart 上 bijection。
- **`hcConjDescend_comp_subtype_eq_one_iff`** (per-factor) + **`hcConjDescend_comp_regular_iff`**:
  `(∀i, θ∘A_g nontrivial on Hpart i) ⟺ (∀i, θ nontrivial on Hpart i)` = **regularity preservation**。
  bijection ゆえ value multiset 一致。

**⟹ step (2) 完了**。commute (step 1 `hcPsi_conjBy_eq`、既 landed) + regularity preservation で
**T={hcPsi θ|θ regular} は HU-conjugation で閉じる**: `conjBy g (hcPsi θ)=hcPsi(θ∘A_g)` (commute)、
`θ∘A_g regular ⟺ θ regular` (regularity)。

**⟹ step (3) T-invariance 組立 + oXtheta 集約 も COMPLETE (2026-07-01 cont.⁶)**。3 補題で
oXtheta numerator を完全形式化 (S11、axiom-clean、leaf green):
- **T-invariance closure** (前 commit): `hcPsi_irreducibleConjBy_eq` (IrreducibleChar 版 commute) +
  `hcPsi_regular_conjBy` (∃θ' regular, (hcPsi θ)^g=hcPsi θ' = T 閉性)。
- **`comp_subtype_ne_one_iff_exists`**: regularity hom-form ↔ pointwise-form bridge
  (card_regular_chars_Hbar↔hcPsi_inertia_index_eq_u 接続)。
- **`oXtheta_count`**: **u·|Xθ|=(p-1)^q** (Xθ=T.image induce の distinct 集合)。組立 =
  T=RegF.image(hcPsi) 閉性 (hcPsi_regular_conjBy) → `card_filter_induce_eq_index_inertia` で各 fibre=
  [HU:HC]=u (hcPsi_inertia_index_eq_u) → `Finset.card_eq_sum_card_fiberwise` で |T|=u·|Xθ| →
  |T|=(p-1)^q (hcPsi_injective + card_regular_chars_Hbar) ⟹ 結論。
  **instance-diamond 対処 (note の warn)**: `induce`/`Finset.univ` が statement-level で
  Fintype/Invertible を要する ⟹ explicit instance binder (`[Fintype ↥huSub][Fintype ((↥H⧸N)→*ℂˣ)]
  [Invertible (card huSub:ℂ)][Invertible (card HC:ℂ)]`) で解決。`set HC` は induce の
  instance-guarded occurrence を fold しない ⟹ carrier は `_` 推論に任せ goal と同一 FULL 式に統一。

**残 = caseA conjunct c 最終 assembly (parity 適用)**: `exists_regular_not_reducible_of_odd` (S11:~5350,
既 landed: X⊇Xmu (|Xmu|=p-1) ∧ u·|X|=(p-1)^q ∧ u odd ∧ p-1 even>0 ∧ q≥2 → ∃s∈X∖Xmu) に oXtheta_count
+ u_odd + Xmu (reducibles, |Xmu|=p-1) を供給 → witness s∈Xθ∖Xmu → s∉Xmu ⟹ Ind_M(s) irreducible
(reducible↔Xmu 対偶) → caseA_character_counts:~5270 conjunct c。
**要 wiring**: (i) Xθ (oXtheta の image) を X に同定、(ii) Xmu = reducible-inducing の image を
|Xmu|=p-1 で (reducible_count 系)、(iii) s∈Xθ∖Xmu → Ind_M(s) irr deg qu (M-level、既 hcZeta_induceHU_*
の hIM を parity witness が供給)。deep math 無し・char-level plumbing (whnf/instance 注意)。

## ★ conjunct c は hIM discharge に完全還元 — endpoint 特定 (2026-07-01 cont.⁷)

**重要発見**: `hcZeta_exists_irreducible_sOf` (S11:7028、既 landed) が **hIM-gated conjunct c そのもの** —
regular θ + hθnt(θ≠1) + hθ₀(inertia=HC、inertia_eq_hcInHu_caseA で供給) + **hIM
(`inertia(Ind_{HC}^{HU}(hcPsi θ)) ≠ ⊤` = ζ_θ が M-level で W₁-fixed でない)** を受けて
`∃χ∈𝒮(H₀C), IsIrr χ ∧ χ1=qu` (= conjunct c) を返す。⟹ **conjunct c ⟺ ある regular θ≠1 で hIM**。

私の **oXtheta_count** + `exists_regular_not_reducible_of_odd` (parity) がこの hIM を供給する経路:
witness s∈Xθ∖Xmu → Ind_M(s) irr ⟺ hIM。∴ 残 = parity の 2 入力のみ:
- **|Xmu|=p-1**: Xmu={ζ_θ : θ constant factor-data} の count (constant nonzero 値 p-1 個の直接 count、
  または reducible_count_sOf_H0C との bijection)。
- **(E)**: `Ind_M(ζ_θ) reducible → θ constant factor-data` (対偶、Coq cfclass_Ind_irrP/ResIndXmu、
  **W₁-inertia 数論を回避する Clifford 論**)。free-orbit route の θ̄^{w₀}∉U-orbit より弱く済む。

⟹ **conjunct c assembly = (Xθ/Xmu を Set 化 + |Xmu|=p-1 + (E)) → exists_regular_not_reducible_of_odd
→ hIM 抽出 → hcZeta_exists_irreducible_sOf**。oXtheta numerator + endpoint は landed、残は
(E)+Xmu-count の fresh Clifford 単位 (deep でないが substantial、reducible-count infra と接続)。
次 iteration の着手 = Xmu (constant factor-data) の定義 + count + (E)。

## ★ conjunct c の残 gate 精密確定 (Coq PFsection9:992-1108 精読, 2026-07-01 cont.⁸)

**私の oXtheta_count + exists_regular_not_reducible_of_odd は Coq の Xtheta/oXtheta/eqVproper と
EXACT 一致確認** (Coq-first 精読):
- Coq `Xtheta := [set cfIirr('Ind[HU] chi_t)]` (L954) = **HU-level** ⟹ 私の Xθ (HU-level) 正しい ✓。
- `oXtheta: u·#|Xtheta|=p.-1^q` (L955) = 私の `oXtheta_count` ✓。
- `Xmu ⊆ Xtheta` の `eqVproper` (L1083-1108): equality→u=(p-1)^{q-1} even vs u odd 矛盾 /
  proper→∃s∉Xmu→`contraR ... red_Ind_s` で Ind_M(s) irr = 私の `exists_regular_not_reducible_of_odd` ✓。

**残 gate = |Xmu|=p-1 で、Coq は Xmu を constant factor-data で構成** (`mu_f i:=[ffun w=>if w∈W1bar
then i else 0]`, `Xmu:=[set cfIirr(mk_mu i)|i in predC1 0]`, `|Xmu|=cardC1·card_Iirr_abelian=p-1`,
L1047/1071/1108)。これは **W₁-orbit 構造 (bigdprod over W1bar)** に依存:
- `sW1_Imu` (L996): constant data は W₁-stable (`I_M ⊇ W₁`)。
- `def_IXmu` (L1048): I_M(chi_s)=M for s∈Xmu (M-fixed→Ind_M reducible)。
- surjectivity (`Dmu: Smu=mu_`, L1073): |Smu|=p-1=|mu_|(reducible_count) + Smu⊆mu_ ⟹ 全 reducible が
  constant-data の Ind。∴ |Xmu|=p-1 は constant 構成が本質 (単なる injective では |Xmu|≤p-1 止まり)。

**⟹ conjunct c は `CliffordCaseAData.W1_transitive_on_parts` の DE-OPACIFY に gated** (現状 opaque
`Prop:=True`)。W₁ が q factor を q-cycle で置換する構造を **usable field 化** (orbit generator S₀ +
act.φ(w)•S₀ の W₁-indexing + W₁-transitivity lemma) しないと constant factor-data (= 各 factor に同一
H1-char) が canonical に定義できない (factor 間の canonical iso が W₁-transitivity 由来)。producer =
`chiefFactor_clifford_U_dichotomy` case-a 枝 (S₀ の W₁-orbit で Hpart 構成、transitivity は construction
に implicit だが field 化されてない)。

**利用可能 Clifford infra (landed)**: `card_smul_restrict_induce` (|H|•Res(Ind)=∑conjBy)、
`induce_injective_of_inertia_stable` (M-fixed→Ind injective)、`induce_eq_induce_iff_conj`、
`card_mul_inner_self_induce_eq_card_inertia`。⟹ def_IXmu/ResIndXmu/Smu=mu_/(E) の wiring は
これらで組める。**本体 = W₁-transitivity de-opacify (structure+producer refactor、substantial upstream)**。

### ✅ de-opacify 第一歩 DONE (commit 38f474f5, 2026-07-01 cont.⁹)
CliffordCaseAData の opaque `W1_transitive_on_parts:Prop:=True` を usable orbit 構造に置換
(**S0**:order-p 生成子 / **orbitRep**:Fin q→↥(U⊔W₁) / **Hpart_orbit**:`Hpart j = quotientMulAutHom
chief.N_aInvariant (orbitRep j) • S0`)。Finite-free `quotientMulAutHom` で phrase
(typeP_quotientCoprimeAction.φ:=quotientMulAutHom hN の defeq、producer で rfl 充足)。consumer 無し・
full build 緑。

### ⚠ 深部発見: |Xmu|=p-1 の injectivity は Ū-action 構造にも依存 (cont.⁹)
constant-data 構成 recipe を精査: constant θ (値 θ_0 on S0、各 Hpart j に translate φ(orbitRep j) で
transport) の集合 ≅ {θ_0:S0→*ℂˣ}、regular (θ_0≠1) で **p-1 個**。だが Xmu=|{ζ_θ:θ constant}| の count は
**θ_0 ↦ ζ_θ の injectivity** を要し、これは「distinct constant θ が distinct Ū-orbit」= **Ū∩Δ={1}**
(Ū に非自明な対角 scaling (s,…,s) 無し) に帰着。Ū-conjugate constant θ_0,θ_0' ⟺ ∃ū diagonal
s_j(ū)=s ∀j かつ θ_0'=θ_0^s ⟺ (Ū∩Δ={1} なら) θ_0=θ_0'。Coq の `Ū↪(cyclic_a)^{q-1}=∏^q/Δ`
(L15 note) が正に Ū∩Δ={1} (∏→∏/Δ injective)。⟹ **これも opaque field `Ubar_embeds_product` の
de-opacify に依存** (orbit 構造だけでは不足)。

### ✅ de-opacify foundations DONE (commits f800adfa/99f6cad7, cont.¹⁰)
- `caseA_S0_card`: |S₀|=p (Hpart_orbit + card_pointwise_smul)。
- `caseA_orbitEquiv j : ↥S₀ ≃* ↥(Hpart j)` (transport iso、equivMapOfInjective + subgroupCongr)。

### ★★ SURJECTIVITY route 発見 (cont.¹⁰) — constant-char 構成を回避、|Xmu|=p-1 が cleaner
**Xmu := {ζ∈Xθ : Ind_M(ζ) reducible}** と直接定義すると (E) が trivial + |Xmu|=p-1 が既 landed
reducible_count に bijection で還元:
- **injective** (landable now): reducible → I_M(ζ)=M (⟨Ind,Ind⟩=|I|/|HU|>1 ⟺ I≠HU、prime index
  [M:HU]=q で I=M) → M-fixed → `induce_injective_of_inertia_stable` (landed) ⟹ |Xmu|≤p-1。
- **surjective** (crux、W₁-transitivity 依存): reducible φ=Ind_M(ξ)∈𝒮(H₀C)、ξ M-fixed。ξ の HC-構成子
  θ̄_0 が **regular**: θ̄_0 が Hpart i で trivial ⟹ Ū-conjugates も trivial (**U が各 Hpart 保存**、
  既 Hpart_aInvariant) ⟹ {θ̄_0 nontrivial な Hpart} は Ū-不変かつ (ξ W₁-fixed で) **W₁-不変** ⟹
  W₁-transitive で ∅ or 全体、H⊄ker で非空 ⟹ 全体 = θ̄_0 regular ⟹ ξ=ζ_θ∈Xθ。⟹ Ind_M:Xmu→reducibles
  全単射 ⟹ **|Xmu|=|reducibles of 𝒮(H₀C)|=p-1** (`reducible_count_sOf_H0C` LANDED)。
- **⟹ constant-char 構成 + Ū∩Δ={1} injectivity は不要** (surjectivity route が全部を reducible_count に還元)。

**⟹ conjunct c 残 = (1) orbit de-opacify ✅ + (2) W₁-transitivity lemma (factors=W₁-orbit、W₁ 推移;
orbitRep∈W₁ に refine or 「W₁-不変 Hpart-set は ∅/全体」) + (3) injective (reducible→M-fixed、既 infra)
+ (4) surjective (reducible→θ̄_0 regular、W₁-transitivity + 構成子解析) + (5) parity 組立**。
crux = W₁-transitivity + surjectivity の 構成子解析 (Coq PFsection9 の Res-constituent 論)。次着手 =
W₁-transitivity lemma (producer で factors=W₁-orbit、orbitRep を W₁ に取れる) or injective lemma
(self-contained、landable)。**deep だが constant-char 構成より短い経路**。

### ✅ injective 全 foundation DONE (commits 4947abe2/604b61fe, cont.¹¹)
- `inertia_eq_top_of_induceHU_not_irreducible`: reducible → I_M=⊤ (induce_of_inertia_eq 対偶 +
  eq_of_le_of_prime_index、inner-product 不要)。
- `caseA_induceHU_inj_of_reducible`: reducible-inducing χ で Ind_M inj (mem_inertia +
  induce_injective_of_inertia_stable)。⟹ |Xmu|≤p-1 の injective 半分完成。

### ★★ 再フレーミング (cont.¹¹): W₁-transitivity は producer refactor 不要 — W₁-conjugate indexing で FREE
W₁-transitivity を producer で証明する必要は無い。**W₁-conjugate 族 `{act.φ ↑w • S₀ : w∈act.E}`
(index=act.E=W₁bar、`wConjugate_coprod_bijective` 既存、W₁ が translation `w'·w` で自明に transitive)**
を使えば W₁-transitivity は index 集合 W₁ の translation 推移性で FREE。機構は family-generic
(clifford_caseA_exists_regular_char_on_conjugates が既にこの族で regular char 構成)。producer の
caseA.Hpart (maximal SupIndep) と別族だが assembly は generic。

**⟹ conjunct c の真の crux は「構成子解析」のみ** (W₁-transitivity は free): reducible ξ (M-fixed,
∈xiOf(H₀C)) → HU-構成子 θ̄_0 が regular:
- θ̄_0 抽出: `exists_constituent_not_subset_characterKernel` / `IrreducibleCharacter.LiesOver` (既存)。
- ξ M-fixed → θ̄_0 の Ū-orbit が W₁-invariant (ξ=ξ^w → θ̄_0,θ̄_0^w が HU-conjugate)。
- {w∈act.E : θ̄_0 nontrivial on φ(w)•S₀} は Ū-inv (U が factor 保存) ∧ W₁-translation-inv ∧ 非空
  (H⊄ker) → W₁-translation 推移で全体 → θ̄_0 regular → ξ=ζ_θ∈Xθ。⟹ Ind_M:Xmu→reducibles 全射
  → |Xmu|=p-1。
次着手 = 構成子解析の逐次 build (θ̄_0 抽出 → Ū-orbit W₁-inv → nontrivial-set 全体 → regular)。
Clifford char 論だが producer refactor 不要ゆえ tractable。Coq PFsection9 の Res-constituent 論を port。

## ✅✅ 構成子解析 step 1 + step 2 core LANDED — L1-L5 再利用で difficulty 急落 (2026-07-01 cont.¹²)

**★ 重大発見**: cont.⁷ の **forward hIM propagation 用 L1-L5 machinery** (hInHuConj /
hcZeta_liesOver_compHom_of_fixed / **hcZeta_exists_conj_of_fixed** [L3=single-orbit] /
compHom_hInHuConj_hInHuEquivH [L5] / **conjBy_eq_compHom_iff_quotient** [L4 bridge]) が
**surjectivity 逆向きにそのまま再利用可能**。cont.¹¹ の「構成子解析は substantial」評価は
over-pessimistic だった — 核心 (single-orbit + M-conj↔chief-action bridge) は landed 済。

### landed (build-green, axiom-clean)
- **step 1 (commit 64ab0dfa)**: `exists_hom_constituent_of_mem_xiSet_H0` — χ∈𝒳, H₀⊆Ker χ →
  ∃ nontrivial θbar:H̄→*ℂˣ, LiesOver χ (linearIrreducibleCharacter (θbar∘mk'N∘hInHuEquivH))。
  caseB_exists_chiefFactorConstituent を template に **hom-form seed** を返す (regularity 論が
  θbar.comp (Hpart i).subtype で per-factor 測るため)。
- **step 2 core (commit 1c741e26、2 補題)**:
  - `exists_uInHu_conjBy_eq_of_fixed` (B): χ M-fixed (conjBy m χ=χ) + LiesOver θ₀ → ∃u∈uInHu,
    conjBy u θ₀ = compHom φ_m θ₀。L3 の g∈HU を hInHu⊔uInHu 分解 (`Subgroup.normal_mul`)、
    H-part h∈inertia θ₀ (`subgroup_le_inertia`) で fix → `conjBy_mul` で U-元 u に還元。
  - `exists_uPart_theta_comp_quotient_eq_of_fixed` (C): θ₀=inflation θbar で
    `conjBy_eq_compHom_iff_quotient` + `linearIrreducibleCharacter_injective` →
    **θbar∘q(a) = θbar∘q(b)** (a∈U, q=quotientMulAutHom)。form alignment (step-1 form ↔ inflation
    form) は ext+simp の hinfl で処理。⟹ **W₁-twist θbar∘q(w) が θbar の U-orbit 内**。

### 残 = D/E (orbit equality → θbar regular)
- **D (nontrivial-Hpart-set の W₁-permutation-invariance)**: θbar∘q(w) trivial on Hpart_i ⟺
  θbar trivial on q(w)•Hpart_i (q(w) iso); a∈U preserves Hpart (`Hpart_aInvariant` /
  `caseA_uActionHom_comp_subtype_eq_one_iff`) + C の θbar∘q(a)=θbar∘q(w) ⟹ nontrivial-set が
  q(w)-permutation で不変。**form alignment 注意**: q(a) (a∈U⊔W₁) ↔ uActionHom a' の変換
  (`hcConjDescend_eq_uActionHom` の template、uActionHom def S11:1644)。
- **E (regularity assembly)**: nontrivial-set が W₁-permutation-inv + 非空 (H⊄ker) + W₁-transitive
  → full → regular。**crux = Hpart↔W₁ 整合**: Hpart i = q(orbitRep i)•caseA.S0
  (`Hpart_orbit`)、W₁-conjugate 族 {q(v)•S0 : v∈act.E} で `eq_univ_of_nonempty_of_mul_mem_left`。
  **subtlety**: (1) caseA.S0 の U-invariance (clifford_caseA_data 構築で使うが structure field で
  ないので要確認/再構成)、(2) orbitRep i∈U⊔W₁ が act.E(W₁) に入るか (cont.¹¹「orbitRep∈W₁ に
  refine or W₁-不変 Hpart-set は ∅/全体」)。
- **次着手 = D** (self-contained: C + Hpart_aInvariant + caseA_uActionHom)。E は Hpart↔W₁ で最難、
  最後。D+E 後: regular θbar → `inertia_eq_hcInHu_caseA` → Clifford correspondence
  (`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`) → ξ=Ind_{HC}(hcPsi θbar)∈Xθ →
  Xmu surjective → |Xmu|=p-1 → `exists_regular_not_reducible_of_odd` → conjunct c (sorry S11:5552)。

### ⚠ E-blocker 発見 + D₁ landed (2026-07-01 cont.¹² cont.)

**D₁ landed (commit d2d7fd87)**: `caseA_theta_comp_quotient_uPart_comp_subtype_eq_one_iff` —
a∈U⊔W₁ (↑a∈U) → θbar∘q(a) trivial on Hpart_i ⟺ θbar trivial on Hpart_i。caseA_uActionHom への
form-alignment (uActionHom = quotientMulAutHom.comp (U.subgroupOf).subtype、defeq)。

**⚠ E-blocker**: clifford_caseA_data (S11:4909) を精読して判明:
- `Hpart j = act.φ ↑(e.symm j) • S₀`、e.symm j ∈ t = `exists_supIndep_aInvariant_family_of_iSup` の
  **任意 choice** ⊆ U⊔W₁。orbitRep j∈U⊔W₁ は **W₁ 保証なし**。
- `CliffordCaseAData` structure に **S0 U-invariance フィールドなし** (construction input hS₀inv のみ、
  Hpart_aInvariant は各 Hpart の U-inv のみ)。
- ⟹ W₁ が caseA.Hpart を **transitively permute する保証がない**。E (nontrivial-set の W₁-transitive →
  full) が block。

**E resolution path** (次 iteration で判断):
- **(a)** clifford_caseA_data を W₁-conjugate family `{q(w)•S0 : w∈act.E}` で refine (orbitRep を W₁
  enumerate に)。downstream (oXtheta/hcPsi_regular/card_regular_chars_Hbar) 影響、要検証。
- **(b) [有力]** 「U-invariant order-p summand は S0 の W₁-conjugate」を証明 (type-P non-Galois 構造:
  U が H̄=⊕S0^w に diagonal 作用、U-inv line は S0^w のみ) → S0 U-inv で caseA.Hpart_i = q(orbitRep i)•S0
  = q(W₁-part)•S0 (U-part 消去) → Hpart family = W₁-conjugate family → W₁-transitive。cont.¹¹ の
  「別族だが assembly generic」= この transport。
- **(c)** regularity を W₁-conjugate 族で定式化し hcPsi/oXtheta 側を対応 (大改修、非推奨)。

**残 build 順**: D₂ (θbar∘q(w) trivial on Hpart_i ⟺ θbar trivial on q(w)•Hpart_i、precompose-iso の
一般 lemma、E と独立に landing 可) → E (resolution (a)/(b) 選択 + assembly) → regular θbar →
inertia_eq_hcInHu_caseA → Clifford correspondence → ξ∈Xθ → Xmu surjective → conjunct c (S11:5552)。

**この session の landed 総括**: step 1 (constituent extraction) + B/C (M-fixed→H̄-orbit equality core
bridge) + D₁ (Ū preserves Hpart nontriviality)。L1-L5 再利用で surjectivity の crux 大半が landed、
difficulty 急落。残 = D₂ (trivial) + E (Hpart↔W₁ transport、構造的 subtlety)。

## ✅✅✅ step 2 (M-fixed → regular) 完成 — surjectivity crux LANDED (2026-07-01 cont.¹³)

**caseA_reducible_theta_regular** (commit cd07bb07、full build green): M-fixed ζ (I_M=⊤) +
LiesOver θ₀=inflation θbar + θbar≠1 → θbar regular。**surjectivity route の deep crux 完成**。

### E-blocker (Hpart は W₁-closed でない) を S0 集約で回避
cont.¹² の E-blocker (caseA.Hpart family が W₁-permute する保証なし、orbitRep∈U⊔W₁) を、
**Hpart↔W₁ の直接 transitivity を使わず S0 に集約**して回避:
- **E foundation** (3737b907): CliffordCaseAData.S0_aInvariant (S0 U-inv を field 化) +
  comp_uActionHom_..._of_aInvariant (一般 K の Ū-inv)。
- **D₂ + E2-quotient** (09501be9): comp_subtype_pointwise_smul_eq_one_iff (θ on a•S ⟺ θ∘a on S) +
  comp_quotient_uPart_..._of_aInvariant (E2 の quotient form)。
- **step1-W1 / step1** (cd07bb07): C + E2-quotient で W₁ 版 → Frobenius v=u·w (Subgroup.normal_mul) +
  D₂×2 + E2-quotient で ∀v∈U⊔W₁, θbar∘q(v) on S0 ⟺ θbar on S0。
- **E-main** (cd07bb07): θbar nontrivial on S0 (Hpart span ⊤ 背理法) + ∀i via D₂ + step1
  (Hpart_i=q(orbitRep i)•S0、orbitRep∈U⊔W₁ を Frobenius で吸収 — W₁-closure 不要)。

### 残 = step 5 (ζ = Ind_{HC}(hcPsi θbar) ∈ Xθ) — infra gap あり、substantial
regular θbar → ζ∈Xθ の chain:
- (a) **lies-over 推移性**: ζ over θ₀ (H⊆HC) → ∃ψ'∈Irr(HC), ζ over ψ' ∧ ψ' over θ₀。**要確認/新規**。
- (b) **inertia(ψ')=HC**: ψ' over θ₀ ⟹ inertia(ψ')⊆inertia(θ₀)=HC (E-main+inertia_eq_hcInHu_caseA)、
  ⊇HC 常。**要 general Clifford (conjugation preserves lies-over)**。
- (c) **Ind_{HC}(ψ') irreducible**: isIrreducibleCharacter_induce_of_inertia_eq (既存)。
- (d) **ζ=Ind_{HC}(ψ')**: coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce (既存、235)。
- (e) **ψ' linear**: ζ(1)=u ⟹ ψ'(1)=1 (Ind degree)。
- (f) **ψ' trivial on H₀C**: ζ trivial on H₀C ⟹ constituent も。
- (g) **ψ'=hcPsi θbar**: linear+trivial HC-char over θ₀ は hcPsi 形 (HC/H₀C≅H̄、hcHom)、over θ₀ で
  θ''=θbar (inflation injective)。
- **⚠ infra gap**: Clifford correspondence 存在形 (ζ→ψ') が repo に無い。(a)(b) は general Clifford
  (lies-over 推移 + conjugation-preserves-lies-over) の新規 build 要。inertia_eq_hcInHu_caseA は
  IrreducibleCharacter-regular form ゆえ E-main (hom-regular) の変換 (comp_subtype_ne_one_iff_exists) 要。

**次着手**: (a)(b) の general Clifford infra (lies-over 推移性 + inertia 包含) を build → step 5 assembly。
または Xmu を「reducible ξ そのもの」で定義し Xθ 経由を避ける再設計を検討 (ξ=Ind_{HC}(hcPsi θbar) を
明示せず、reducible ξ の集合と Xθ∩reducible の bijection を count で)。

## step 5 deep 精密 build plan — general-Clifford correspondence 存在形 (2026-07-01 cont.¹⁴)

**infra 確認**: coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce (CliffordSingleOrbit:235、
ψ を与えて ζ=Ind ψ) と inner_induce_ne_zero_iff_liesOver (Clifford:583) はあるが、**Clifford
correspondence 存在形 (ζ→ψ') + restriction/lies-over 推移性は無い**。step 5 foundation
(caseA_reducible_inflation_inertia_eq: I_HU(θ₀)=HC) は landed (3ab7a5ea)。

**目標**: reducible ξ∈xiOf(H₀C) (M-fixed, seed θbar regular) → **ξ = Ind_{HC}(hcPsi θbar) ∈ Xθ**。
coe_eq_induce with ψ=hcPsi θbar が使える (Ind_{HC}(hcPsi θbar) irreducible = hcZeta_irreducible +
foundation の I_HU(θ₀)=HC) — 要 **ξ lies over hcPsi θbar**。

**ξ lies over hcPsi θbar の証明 (要 general-Clifford infra, 次 iteration build 順)**:
1. **restriction 推移性** (新規, general): H≤K≤G で `restrict (H.subgroupOf K) (restrict K φ) =
   compHom (subgroupOfEquivOfLe hHK).symm (restrict H φ)` (subgroupOf transport, ext+pointwise)。
2. **lies-over 推移性** (新規, general, 1 依存): ξ over θ₀ (H=hInHu⊆HC) → ∃ψ'∈Irr(HC), ξ over ψ' ∧
   ψ' over θ₀ (Res_H(ξ)=Res_H(Res_{HC}ξ)=Σ e_ψ Res_H(ψ)、⟨·,θ₀⟩≠0 で ∃ψ')。
3. **inertia(ψ')=HC** (新規, general): ψ' over θ₀ ⟹ I(ψ')⊆I(θ₀)=HC (conjBy preserves lies-over:
   g∈I(ψ')→ψ'=ψ'^g over θ₀^g、single-orbit で θ₀^g H-conj θ₀→g∈I(θ₀))、⊇HC 常。
4. **ψ' linear**: ξ(1)=u, ξ=Ind_{HC}(ψ') (coe_eq_induce with 2,3,c) ⟹ u=[HU:HC]ψ'(1)=uψ'(1) ⟹ ψ'(1)=1。
5. **ψ' trivial on H₀C**: ξ trivial on H₀C (∈xiOf(H₀C)) + liesOver_mem_characterKernel ⟹ H₀C⊆ker ψ'。
6. **ψ'=hcPsi θbar** (crux, tractable): linear ψ' (=linearIrreducibleCharacter ψ_hom via
   exists_units_monoidHom) trivial on H₀C ⟹ ψ_hom factors через hcHom (ker=H₀C surjective) ⟹
   ψ'=hcPsi θ''; ψ' over θ₀=inflation θbar ⟹ θ''=θbar (inflation injective)。
7. ⟹ ξ over hcPsi θbar (=ψ') → coe_eq_induce → **ξ=Ind_{HC}(hcPsi θbar)∈Xθ**。

**その後**: Xmu surjective (全 reducible∈Xθ) → |Xmu|=p-1 (bijection + reducible_count) →
exists_regular_not_reducible_of_odd (oXtheta+u odd) → hIM → hcZeta_exists_irreducible_sOf → conjunct c
(S11:5552)。

**⚠ 判断分岐**: (1)-(3) の general-Clifford (restriction/lies-over 推移性 + inertia 包含) は Clifford.lean
上流に置くべき shared infra だが、まず S11 local で build → 動作後に上流移動を検討 (claim-before-build)。
step 2 (regularity crux) 完成後の最後の assembly ゆえ、深いが grindable。

## step 5 assembly 完成 (2026-07-02 cont.¹⁸) — reducible ζ = Ind_{HC}(hcPsi θbar) landed

**landed (全 axiom-clean [propext, Classical.choice, Quot.sound]、commit `<this>`)**:
- **`caseA_reducible_eq_hcZeta`** (S11): reducible (M-fixed) ζ∈𝒳(H₀C) が seed inflation θ₀ に over
  (θbar regular ≠1) ⟹ **ζ = Ind_{HC}^{HU}(hcPsi θbar)**。step-5 (a)-(g) chain を collapse。
  - **重要な簡約**: plan の step 3 (inertia(ψ')=HC 独立計算) と step 4 (ψ' linear) は **bypass**。
    Ind_{HC}(hcPsi θbar) の既約性は `hcZeta_irreducible` + foundation
    `caseA_reducible_inflation_inertia_eq` (I_{HU}(θ₀)=HC) から出る (ψ' の inertia を独立計算しない)。
    ψ' linear は `exists_hcPsi_eq_of_hcHom_ker_subset` が H̄ abelian から自動導出 (step (e)/(f) subsumed)。
  - chain: `exists_liesOver_intermediate` (lies-over 推移) → HC-constituent ψ' (ζ over ψ' ∧ ψ' over θ₀')
    → ζ trivial on H₀C=Ker hcHom を `liesOver_mem_characterKernel` で descend (Ker hcHom⊆Ker ψ')
    → ψ'=hcPsi θbar'' (`exists_hcPsi_eq_of_hcHom_ker_subset`) → ψ' linear ⟹ Res single irr で seed
    identification θbar''=θbar → `coe_eq_induce_of_liesOver_...` で ζ=Ind_{HC}(hcPsi θbar)。
- **supporting general lemmas** (reusable): `hcPsi_restrict_hInHu_subgroupOf` (hcPsi θ の hInHu.subgroupOf HC
  制限 = transported seed inflation、subgroupOf 版 hcPsi_apply_inclusion); `eq_of_liesOver_of_restrict_eq_irr`
  (χ over θ + Res χ=irr η ⟹ η=θ、Clifford 直交); `hcPsi_seed_eq_of_restrict_eq` (hInHu-制限が seed を決定)。
- step 5 (g) `exists_hcPsi_eq_of_hcHom_ker_subset` の壊れた uncommitted work も修正 landed (coercion 明示化)。

### 次の frontier = 抽出 (extraction) — conjunct 2 (9.8.b) と conjunct 3 (9.8.c) 共通の上流
`caseA_character_counts` (S11:5560) 現状: conjunct 1 (reducible count=p-1) = **proven**
(`reducible_count_sOf_H0`)。conjunct 2/3/4 = sorry (5573-5575)。上流優先+文書順 ⟹ 次は **extraction**:

- **共通上流 (要 build)**: **reducible φ∈𝒮(H₀) → M-fixed HU-constituent ζ∈𝒳(H₀C) over θ₀ regular ∧
  φ=Ind_{HU}^M ζ**。これが得られれば:
  - **conjunct 2 (9.8.b 後半)**: φ=Ind_{HU}^M(Ind_{HC}(hcPsi θbar)) (caseA_reducible_eq_hcZeta) ⟹
    degree qu (`hcZeta_induceHU_apply_one`) ∧ ∈𝒮(H₀C) (`hcZeta_induceHU_mem_sOf`)。
  - **conjunct 3 (9.8.c)**: |Xmu|=p-1 (extraction で reducible↔Xmu bijection + `caseA_induceHU_inj_of_reducible`
    injective + reducible_count) → `exists_regular_not_reducible_of_odd` (oXtheta_count u·|Xθ|=(p-1)^q + u_odd)
    → 非 M-fixed regular θ (hIM) → `hcZeta_exists_irreducible_sOf` (7258) → conjunct 3。
- **要確認 infra**: reducible φ → HU-source ζ (φ=Ind_{HU}^M ζ、Clifford at HU/M level); ζ∈𝒳(H₀C) ∧
  ζ over θ₀ regular の抽出 (caseA 版 `caseB_exists_chiefFactorConstituent` 相当が要るか grep)。
  `inertia_eq_top_of_induceHU_not_irreducible` (5009: reducible⟹M-fixed)、`caseA_induceHU_inj_of_reducible`
  (5033) は landed。

## conjunct (b) 完成 + (c) plan (2026-07-02 cont.¹⁹)

**landed (commits, 全 axiom-clean)**:
- **`caseA_reducible_induceHU_apply_one_eq_qu`**: reducible φ∈𝒮(H₀) は degree qu (9.8.b degree)。
  step-5 assembly の初 consumer。extraction (`exists_hom_constituent_of_mem_xiSet_H0`) + C-kernel
  (`reducible_mem_sOf_H0C` cardinality + `caseA_induceHU_inj_of_reducible`) + `caseA_reducible_eq_hcZeta`
  + `hcZeta_induceHU_apply_one`。
- **`caseA_character_counts` conjunct (b) 完成** + 末尾へ relocate (step-5 machinery を cite するため;
  コード comment 6337 が既に予告)。(b) = count (`reducible_count_sOf_H0`) + degree (上記) + membership
  (`reducible_mem_sOf_H0C`)。conjunct (c)/(d) は sorry (S11:8143/8144)。

**次 = conjunct (c) = 9.8.c: |Xmu|=p-1 Finset bijection assembly**:
- **Xθ** (`oXtheta_count` 内) = `RegF.image (fun θ => Ind_{HC}(hcPsi θ))` (RegF={θ regular})。
  `u·|Xθ|=(p-1)^q` (`oXtheta_count`)。
- **Xmu** := `Xθ.filter (fun ζ => ¬irr (induceHU ζ))`。
- **|Xmu|=p-1 の証明** (cleanest, Set/Finset bridge):
  1. `↑(Xmu.image (induceHU data)) = {φ∈𝒮(H₀)|¬irr}` (Set 等式)。⊆: ζ∈Xmu ⟹ induceHU ζ ∈𝒮(H₀)
     (ζ∈Xθ ⟹ ⟨ζ,hcZeta_irreducible⟩∈xiOf(H0)=hcZeta_mem_xiOf) ∧ reducible。⊇: reducible φ ⟹
     source χ = Ind_{HC}(hcPsi θbar) (extraction+`caseA_reducible_eq_hcZeta`), θbar regular
     (`caseA_reducible_theta_regular`) ⟹ χ∈Xθ ∧ reducible ⟹ χ∈Xmu、φ=induceHU χ。
  2. `Xmu.card = (Xmu.image induceHU).card` (`Finset.card_image_of_injOn`、`caseA_induceHU_inj_of_reducible`)。
  3. `= ncard {reducibles} = p-1` (`Set.ncard_coe_Finset` + `reducible_count_sOf_H0`)。
- **conjunct (c) 組立**: `exists_regular_not_reducible_of_odd` (X=Xθ, |Xmu|=p-1, u·|Xθ|=(p-1)^q,
  `u_odd`, p-1 even, q≥2) → ζ∈Xθ\Xmu (Ind_{HU}^M ζ **irreducible** 直接)。ζ=Ind_{HC}(hcPsi θ)
  (θ∈RegF regular⟹θ≠1) ⟹ witness = induceHU ζ ∈𝒮(H₀C) (`hcZeta_induceHU_mem_sOf`)、irreducible
  (ζ∉Xmu 直接、hIM 経由不要)、degree qu (`hcZeta_induceHU_apply_one`)。
- **共有 helper 案** `caseA_reducible_source_eq_hcZeta`: reducible φ∈𝒮(H₀) ⟹ ∃θbar regular,
  φ=induceHU(Ind_{HC}(hcPsi θbar))。degree lemma と Xmu 全射の両方が使う extraction+C-kernel+eq_hcZeta。

## conjunct (c) = 9.8.c 完成 (2026-07-02 cont.²⁰) — 𝒮(H₀C) irreducible degree-qu

**✅✅✅ 9.8.c 完全クローズ (全 axiom-clean [propext, Classical.choice, Quot.sound])**。step-5 の headline
payoff。`caseA_character_counts` (末尾へ relocate 済) の conjunct (b)+(c) proven、残 (d) のみ sorry
(S11:8343)。以下 landed (commits):
- **`caseA_reducible_source_eq_hcZeta`** (shared extraction core): reducible φ∈𝒮(H₀) ⟹ ∃regular θbar,
  φ=Ind_{HU}^M(Ind_{HC}(hcPsi θbar))。degree lemma と Xmu 全射が共有。
- **`caseA_regular_inflation_inertia_eq`** / **`caseA_hcZeta_irreducible_of_regular`**: regular seed θ ⟹
  I(θ₀)=HC ⟹ Ind_{HC}(hcPsi θ) irreducible (Xθ-member を IrreducibleCharacter に bundle)。
- **`caseA_Xmu_card_eq`**: |Xmu|=p-1。ζ↦Ind_{HU}^M ζ が Xmu ≃ {reducible 𝒮(H₀)} の bijection
  (inj=`caseA_induceHU_inj_of_reducible`、surj=`caseA_reducible_source_eq_hcZeta`)、
  `induceHU '' Xmu = reducibles` + `Set.ncard_image_of_injOn` + `reducible_count_sOf_H0`。
  ⚠ `open scoped Classical in` 要 (statement の filter DecidablePred; `set` が classical tactic だけでは
  拾えない)。
- **`caseA_exists_irreducible_sOf_H0C`** (= 9.8.c): `exists_regular_not_reducible_of_odd`
  (X=Xθ, u·|Xθ|=(p-1)^q via `oXtheta_count`, p-1 even ∵ p∣|G| odd, u odd via `u_odd`, |Xmu|=p-1) →
  ζ∈Xθ\Xmu (Ind_{HU}^M ζ **irreducible** 直接、hIM 不要) → witness=induceHU ζ (∈𝒮(H₀C)
  `hcZeta_induceHU_mem_sOf`、irreducible、degree qu `hcZeta_induceHU_apply_one`)。

**残 = conjunct (d) = 9.8.d のみ** (S11:8343): `𝒮(H₀U')` に degree qa の irreducible が
`((p-1)/a)·(|U|/(a|U'|))` 個以上。別構造 (a divisor、Uprime、type-P Galois の a=|U:C_U(...)|)。step-5
machinery とは独立の新 phase。full build green (3893 jobs)。

## 残 §9 frontier 精査 (2026-07-02 cont.²¹) — 全て deep/opaque-gated、caseA step-5 の続きでない
9.8.b/c 完了後の残 S11 sorry を精査。**clean な小 win は無い**。honest な次手は下記いずれかの新 sub-phase:

- **9.8.d** (S11:8343, caseA conjunct d): 🛑 **opaque-gated**。degree-qa の Galois a-family count
  (`((p-1)/a)·(|U|/(a|U'|))` 個以上)。`CliffordCaseAData.quotient_factors_cyclic_order_a := True` /
  `Ubar_embeds_product := True` (S11:4970-4973) が **opaque `True` stub**。honest に建てるには
  type-P non-Galois の Galois 構造 (H1、a=|U:C_U(H1)|、cyclic Ū、theta family = Coq `theta f`) を
  de-opacify 要 (CliffordCaseAData への field 追加=構造変更)。**`True` stub の上に建てるのは doneness 違反**
  ([[scaffold-sorry-free-not-done]])。Coq: PFsection9 `typeP_nonGalois_characters` (d) part。
- **9.9.c** (S11:6256, caseB conjunct c): deep exceptional。`(¬∃irr∈𝒮(H₀C')) → C=⊥ ∧ u=(p^q-1)/(p-1)`。
  **caseB (Galois case) 固有** — u=(p^q-1)/(p-1) は Galois-specific で caseA parity
  (`exists_regular_not_reducible_of_odd`、u=(p-1)^(q-1) を出す) から**出ない**。Coq: PFsection9
  `typeP_Galois_characters` 系。9.8.c の Hpart/S₀ machinery は caseA 専用ゆえ流用不可。
- **9.10** (S11:6277, `exceptional_case_frobenius_realization`): opaque field
  `quotientSemidirectFrobenius` de-opacify + 全 body sorry。Coq: PFsection10 (coherence/Frobenius)。
- **9.11 `sibleyTarget_H0C`** (S11:6293): §14-gated + lane-B (6.8) 依存。**lane-A 即時対象外**。

**次 iteration の honest 着手候補** (document-order): 9.8.d の Galois 構造 de-opacify (H1/a/theta) が
文書順最上流だが構造変更大。または 9.9.c (caseB exceptional, 構造変更不要だが deep §9-10 coherence 依存)。
どちらも fresh-context で Coq `typeP_{non,}Galois_characters` 精読からの multi-iteration build。

## 🛑 §9 残 = hub-gated (frozen Galois territory) → lane-a pivot (2026-07-02 cont.²²)
cont.²¹ の opaque-gating を追跡 → **remaining §9 (9.8.d/9.9.c/9.10) は全て type-P Galois 土台 gated、
かつその土台は issue 9000 で HUB 裁定中 (policy 8, 凍結)**:
- CliffordCaseAData `quotient_factors_cyclic_order_a`/`Ubar_embeds_product` + CliffordCaseBData
  `field_model`/`Ubar_cyclic` = 全 opaque `True` stub。de-opacify = typeP_Galois (9.7) 構造構築。
- **issue 9000**: lane a の S11 Galois pieces (`isCyclic_card_dvd_..._irreducible_faithful_comm`
  e2a673bd 等) が lane d の σ-theory leaf と**重複**、hub 裁定待ちで**「これ以上広げない」凍結**。
  ∴ 9.8.d/9.9.c の Galois de-opacify は凍結領域拡張ゆえ **lane-a は今着手不可**。
- **判定**: policy 8 (lane d は「hub 裁定待ちの間、別 on-spine 上流へ」) を lane a も適用。
  §9 の残は Galois 土台 land 後に再開 (skeleton 前倒しも凍結ゆえ保留)。

**lane-a pivot 先 (ungated、次 iteration 着手)**: S10 (13 sorry)、S13 (11 sorry)、
issues ~~1013 (S09 §7 certificate)~~、~~1015 (hzeta0nu coherence orth)~~、1016 (T-side typePdata threading)、
~~0065 (Cor 12.16)~~ (取り消し線 = 2026-07-02 時点で完了済)。文書順+上流優先で選択。caseA/B_character_counts は現状 §12-13 に consumer 無
(endpoint) ゆえ §9 残の緊急度は低い。

## S10 §8 pivot 着手 (2026-07-02 cont.²³) — (8.2.a) + (8.6.b II) closed, 残の gating map

cont.²² の pivot 判断 (§9 残 = hub-gated Galois → ungated S10/S13 へ) を実行。S10
(`S10_MinimalSimpleStructure.lean`, 文書順最上流) から着手。**S10 sorry 11→9**、いずれも axiom-clean
[propext, Classical.choice, Quot.sound]:

- **(8.2.a) `typeF_card_U0_eq_exponent`** (commit `997e7c5e`): 型 F で |U₀|=exp(U)。
  `frobenius_HU0` の複体 U₀ = 奇位数 Frobenius 複体 ⟹ Z-group (全 Sylow cyclic; [BG] Prop 3.9 /
  Huppert V.8.18) ⟹ `IsZGroup.exponent_eq_card`。新 helper `isZGroup_of_isFrobeniusGroup_of_odd`
  (既存 action 形式 `isZGroup_of_isFrobeniusAction_of_odd` の pair-form bridge)。奇位数仮説
  `Odd (Nat.card G)` を追加 (数学的に必須、無いと U₀=Q8 反例; consumer 0 ゆえ安全)。
- **(8.6.b II) `typeII_normalizer_not_le_of_typePData`** (commit `a5ce54dd`): 型 II で任意型 P データ
  data に ¬N_G(data.U)≤M。data.U と型 II witness td.typeP.U は M'=derivedInG M 内で M_F の補群 ⟹
  Schur–Zassenhaus 共役 (`exists_conj_of_coprime`) ⟹ normalizer 移送 + M 自己共役で td.normalizer_not_le
  に帰着。`card_Msigma_inf_centralizer_eq_card_W2` の共役パターンを鏡写し。

### S10 残 9 sorry の gating map (次 iteration 用)
S10_BGInterface.lean (0 sorry) の docstring が明示する通り、残の多くは **BG §14–16 (sorried) gated**:
- **(8.11) `hall_maxNilpotentNormalHall_and_mainSubgroup`**: 型 I/II は済
  (`S10_BGInterface.maxNilpotentNormalHall_isHall_of_typeI_or_II`)、**型 III/IV は M_s=M', M_F は M_σ の
  proper Hall ⟹ 未証明 BG §14–15 構造 gated**。full 版は型 III/IV 必須ゆえ現状不可。
- **(8.12.b) `typeI_or_typeII_centralizer_unique`** / **(8.13) `escapingCentralizers_control`**: BG §16
  Thm B + Prop 16.1 (要 sorried 状態確認)。`isUniquelyMaximal_of_maximalSubgroupsContaining_eq_singleton`
  (S10_BGInterface, bridge) は済。
- **(8.15) `dadeSupportHypotheses_{typeI,typeP}`** / **(8.16) `typeII_A_sets_{TI,normalizer}`**: 復元済
  (8.14)-(8.17) support 記法 + BG §16/Pf (2.3) 依存。
- **(8.17) bgTheoremE type-I cover branch** (`bgTheoremE_cover_data` の `𝓜_P=∅` 枝): §8 route-B endpoint gated。
- **(8.18) `support_mutual_exclusion`**: BG Theorem E cover 依存。

**次 iteration 着手判断**: (8.12.b)/(8.13) の BG §16 Thm B / Prop 16.1 の sorried 状態を確認し、
signature 正なら sorried-cite で wiring、genuine local 論証が要るなら実証明。BG-gated が深いなら S13
(§11、10 sorry) か issues ~~1013~~/~~1015~~/1016/~~0065~~ へ (文書順+上流優先; 取り消し線 =
2026-07-02 完了済)。

## 🧾 注記 (2026-07-02 hub 全体レビュー)

- **issue 9000 は裁定済**: 「hub 裁定待ちで凍結」(cont.²²) は解消 — σ-theory claim は
  lane a に承継され、**S11 dup 3 定理の retire→generic leaf cite (dedup) が lane a の
  σ-tail 次手** (9000 の 2026-07-02 承継節参照)。凍結を理由にした §9 Galois 保留は今後
  9000 の残タスク進行に読み替える。
- done 項目を strike 済: **1013 / 1015 / 0065 は完了** (1013 = §7 certificate discharge
  実質完了、1015 = hzeta0nu 解消、0065 = Cor 12.16 faithful statement は
  `S12_Corollary1216.lean` に存在)。
- **S10 残 = 8 sorry** (comment-strip 計数, 2026-07-02。cont.²³ の「残 9」は stale)。
- 0080 (closed 系レビュー) から転記の追加タスク: **`S12_MaximalIII_IV_V_Core.lean:1055` の
  `theoremA_maximal_structure` cite を sorry-free な `typeP_auxiliary_structure`
  (`S15_MF.lean:1706`) に差替** — BG sorried 依存を 1 本削減できる (swap 後、
  `theoremA_maximal_structure` は唯一の cross-lane caller を失い dead で削除可)。

## 2026-07-04 update (lane-a) — mkSection11CharacterData BREAKTHROUGH connects degree side

**新 infra (S12, committed)**: `Hypothesis.mkSection11CharacterData` — S12.Hypothesis + data + chief →
`Section11CharacterData`。char families derived、genuine field = u=|Ū| (rfl pinned)、
tau/H0CprimeSupport/quotientSemidirectFrobenius は degree-irrelevant (placeholder、count/degree で不使用;
(9.11) coherence だけが使う)。⟹ **§9 degree/count 機構が S12.Hypothesis 上で reachable**。
`forall_sOf_H0Cprime_degree_qu_caseB` (committed) が `clifford_dichotomy` + `caseB_degree_qu` compose を validate。

**⟹ (9.9.a) degree qu は Hypothesis 上で得られる**。残 count crux は本 issue の B2 assembly:
- **次手 = induceHU injectivity-on-reducibles** (上記 cont.¹⁷ の crux): 「reducible-inducing χ̄ は W̄₁-stable
  ⟹ induceHU InjOn reducible subset」。§6/Clifford stability + Pf (9.5)/(9.9) orbit 構造。B1
  (`chiefFactorQuotientHypothesis`) + B2 commute (`induce_compHom_subgroupMap_mk'`) は landed ゆえ、
  この injectivity + bijection assembly が |S(HC)|=n (card_SHCSet_filter_eq_charParam_n) への残路。
- **δ=1 側 (charParam_d_modEq_one)**: d=|Ū| (μ_j degree qu / w1 = u、上記 correspondence) + |Ū|≡1 mod q
  (Frobenius quotient `IsFrobeniusAction.quotient`; action-instance を internal letI で setup 要、
  card_kernel_modEq_one 流)。charParam_delta_eq_one arithmetic は proven。

**capstone (11.8) 全体**: exists_zeta_residual_not_orthogonal は sorry-free wired、残 = charParam_d_modEq_one
+ card_SHCSet_filter_eq_charParam_n (両 = 本 issue の correspondence/injectivity) + coherent_Sset_of_column_identities
(τ₂ union、別 gate: S₂ coherence 9.11 = coherent_H0C_commutator on genuine chars)。

## 2026-07-05 update¹⁴ (lane-a, opus) — (11.8.1) count 大幅前進 + S12→S13 producer linchpin landed

**(11.8.1) `|S(HC)| = n` count を軌道数え上げで実質証明化** (全 sorry-free、7 commits):
- **軌道数え上げ核** (`card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one`, S12_Section9Counts):
  `|M'^{ab}| = w₁·|S(HC)| + 1`。非自明 linear char θ of M' は induce 既約 (`inertia_eq_derived_of_linear`
  を S13_SixTwoBridge→S12_Section9Counts へ上流移動 + [Is]6.34)、degree-w₁ 既約 member は全て linear source を
  持ち、各 member は自由共役軌道 (size w₁=[M:M']) で hit される (`card_filter_induce_eq_index_inertia`)。
  linear char 数 = `|M'^{ab}|` は Pontryagin (`card_filter_degree_one_eq_card_abelianization`)。
- **算術リダクション** (`card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq`, sorry-free):
  `|M'^{ab}| = d` ∧ δ=1 ⟹ `|S(HC)| = n` (軌道数 + n_formula `n·w₁=d−1` で w₁ 相殺)。
- **`charParam_d_eq_u`** (d=u=|Ū|) を公開補題として抽出。`card_SHCSet_filter_eq_charParam_n` の残 sorry は
  **単一の `|M'/M''| = params.d`** に精密化 (S12_Section9Counts、δ=±1 を hδpm で threading)。

**根本発見 = (11.5)/(11.8) の repo 順序逆転**: 教科書では (11.5)`M''=HC` は (11.8) の上流だが、repo では
`secondDerived_eq_HC` (11.5) が S13 (S12 の下流) にあり、(11.8) capstone `exists_zeta_residual_not_orthogonal`
(S12) から cite 不可。さらに **S13.Hypothesis の producer が皆無** = §13 (11.1-11.7) 理論全体が spine 未接続だった。

**✅ linchpin landed: `S13.exists_hypothesis_of_isTypeIIIorIV`** (S13_MaximalIII_IV、sorry-free、commit 58b3631f):
S12.Hypothesis(type III/IV) → S13.Hypothesis。全フィールド構成 (params=exists_charParameters_full を
proof-irrel で ∀hG hodd 化、chief=exists_chiefFactorData.choose、**C_normalized_by_M=`typePData_C_normalized_by_M`**
= 本セッションで証明した最難フィールド、C=U⊓C_G(H) rfl、formula は placeholder)。⟹ §13 全体 (11.5/11.7 含む) が
spine から reachable に。

## 次手 (count gate 閉包の完全レシピ、producer 後の残り)

**(11.8) capstone を S13 下流へ re-home して count を閉じる**:
1. **新 leaf `S13_Orthogonality.lean`** (import S13_MaximalIII_IV): `exists_zeta_residual_not_orthogonal` +
   `w2_lt_w1_of_hypothesis` を S12_MaximalIII_IV_V から移設 (S12 の補題は cite; τ₂ `coherent_Sset_of_column_identities`
   は依然 sorry で別 gate)。FeitThompson は新 leaf を import。
2. **供給補題 `|M'^{ab}| = params.d`** (S13_Orthogonality 内 or S13、producer 経由):
   - `secondDerived_eq_HC` (11.5): M'' = HC = H ⊔ (U⊓C_G(H))。
   - **構造 iso `|M'/HC| = |U/C|`** (S12 structural、要新規): M'=H⋊U (`derived_complement`)、H⊴M'、H⊓U=⊥、
     C≤U ⟹ HC/H≅C ⟹ M'/HC ≅ U/C。
   - **(11.7) H₀=1** (`core_structure`) で C_U(H̄)=C_U(H)=C ⟹ `|Ū| = |U/C|`、+ `charParam_d_eq_u` (d=u=|Ū|)
     ⟹ `|M'^{ab}| = |M'/M''| = |M'/HC| = |U/C| = |Ū| = u = d`。
   - `card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq` に流して count 閉包。
3. これで **spine gate 2 本中 count が閉じる** (残 = τ₂ `coherent_Sset_of_column_identities` = (9.11)/(6.8) coherence)。

**注意**: params は existential ゆえ S12版 params.d と producer版 s13.params.d の同一性は degree_independent+params_mu_eq
で follow (両 = muGrid 列 degree)。供給補題は re-home 後の `exists_zeta_residual` 内 params に対して直接証明するのが
安全 (params 選択の二重化を避ける)。

## 2026-07-05 update¹⁵ (lane-a, opus) — ⚠ 重要: count は (10.8)/(11.7) に gated (単独閉包不可)

構造 iso `typePData_card_derived_mul_card_C_eq` (|M'|·|C| = |HC|·|U|, sorry-free, commit 3f44d4ed) を landing
後、供給補題 `|M'^ab| = d` の依存を精査して **count は独立に閉じられない**ことが判明:

**依存チェーン (確認済)**:
- 供給 `|M'^ab| = |M'/M''| = |M'/HC| = |U/C|` は **(11.5) `secondDerived_eq_HC`** (M''=HC) を要する。
- `|U/C| = u = d` の u-match は **(11.7) `H_elementaryAbelian`** (chief.H0 = ⊥、H₀=1) を要する
  (`.u = |U/C_U(H̄)|`、H̄=H/H₀ ゆえ C_U(H̄)=C_U(H)=C は H₀=1 が要る)。
- **(11.7) `H_elementaryAbelian` は sorry** (S13_CoreStructure)。
- **(11.5) → (11.3) `S_H0C_not_coherent` → (10.8) `S12.S_not_coherent` → `typeII_coherence_contradiction_estimate`
  (§7 norm estimate、sorry)**。`HC_le_secondDerived` → `coherent_quotient_bound` → `S_H0C_not_coherent` の鎖。

⟹ **count `|M'^ab|=d`・τ₂ 両 gate とも究極的に (10.8) に依存**。しかも `exists_zeta_residual_not_orthogonal`
自身が末尾で `S_not_coherent` (10.8) を矛盾に使う。⟹ **「re-home で count を閉じる」計画 (update¹⁴) は
(10.8) が sorry ゆえブロック** — re-home は sorry 依存を移すだけで honest close にならない。

**真の terminal (ungated leaves、これが本当の上流)**:
- **(10.7) `typeII_derived_frobenius`** (S12:47) — [S,S] Frobenius、type-II partner 構造。`kernel_is_SF:Prop`
  は opaque scaffold field。
- **(10.8) `typeII_coherence_contradiction_estimate`** (S12:445) — §7 norm-counting 解析 (family_inequality
  (7.5) + (10.6.b) proven + (7.8.b) + TI-counting)。(10.8) `S_not_coherent` が全 (11.x) の根。
- **(10.10) `typeV_forces_coherence`** / **τ₂ `coherent_Sset_of_column_identities`** ((9.11)/(6.8) cross-lane)。

**redirect**: count の orbit-count/構造 iso/producer は genuine 上流 math として landing 済 (無駄でない;
(10.8)/(11.7) が閉じた瞬間に count が sorry-free で follow する形に整備済)。次の genuine work は
**(10.8) §7 norm estimate または (10.7) partner Frobenius を正面から** (upstream-first)。

## 2026-07-05 update¹⁶ (lane-a, opus) — ⚠⚠ lane-a frontier 全数診断: 全て issue-2030 research-grade + 一部 spine 未接続/cross-lane/gated

update¹⁵ の「count は (10.8) gated」を受け、lane-a の全 open sorry を spine 接続性込みで精査:

**spine 接続の open sorry (FT に効く) — 全て (10.8) coherence cluster に収束**:
- `typeV_forces_coherence` (10.10, S12:3905): `no_typeV_maximal`→`isTypeIIIorIV` 経由で spine 接続。
  ただし conjunct 1/2 = `typeV_parameter_formula`/`typeV_coherence_formula` は **opaque Prop field**
  (CharacterParameters、generic params で証明不能 = scaffold)。conjunct 3 (S coherent) のみ genuine。
- `typeII_coherence_contradiction_estimate` (10.8, S12:445): `S_not_coherent` 経由 spine 接続 = **cluster の根**。
  残 gate = (7.8.b) norm bound [**§7 coherence = lane b**] + TI-counting + (10.7)。mechanical spine は proven。
- `typeII_derived_frobenius` (10.7, S12:47): `S_not_coherent` が partner に消費。book proof = §9 (9.8.b/9.9.b/9.10)
  + (5.7)/(5.8) coherence + (8.8) partner。`kernel_is_SF:Prop` opaque。

**spine 未接続の open sorry (現状 FT に効かない、消費者 grep=0)**:
- `caseA_character_counts` (9.8, S11): 残 conjunct = (9.8.d) count 下界。opaque `quotient_factors_cyclic_order_a`
  /`Ubar_embeds_product` (CliffordCaseAData) に依存 = (9.7)(a) 形式化要。
- `exceptional_case_frobenius_realization` (9.10, S11): 2 sorry = (1) opaque `quotientSemidirectFrobenius`
  (Section11CharacterData field、generic chars で証明不能; producer は `True`) + (2) type-II HU-Frobenius
  (= 10.7、H₀=1 (11.7←10.8) gated)。u-formula は proven。
- `sibleyTarget_H0C` (9.11, S11): §14 structural witness (cross-lane)。

**結論 (戦略 redirect)**: lane-a の remaining は全て **(A) 深い §9 Clifford/character proof** + **(B) carrier
de-scaffold (opaque Prop field: quotientSemidirectFrobenius / typeV_*_formula / quotient_factors_cyclic_order_a
/ Ubar_embeds_product / kernel_is_SF)** + **(C) cross-lane ((7.8.b)=b coherence, sibleyTarget=§14)** +
**(D) gated (count←11.5←10.8, 9.10.2←11.7←10.8)** の組合せ。**quick-fill は皆無**、issue 2030 の research-grade
multi-session が正体。sorry-free 上流 (orbit count/構造 iso/producer/d=u) は landing 済で、(10.8)/(11.7) が
閉じた瞬間 count が follow する形。

**hub への flag**: F1 の「(11.8) 3 gates」framing は count を独立 gate とみなすが、実際は count・τ₂ とも
(10.8) coherence cluster に gated。lane-a が spine を前進させる唯一の道 = **(10.8) cluster の根**
((10.7) partner Frobenius via §9 + (7.8.b)[b] + TI-counting) を正面から、または carrier de-scaffold を
9000 claim で。次 iteration はこのどちらかに sustained commit すべき (再調査でなく)。

## ✅✅✅ (9.10) 完全クローズ (2026-07-09 lane a, commit f66c3921) — 本 issue の §9 scope 完遂

`exceptional_case_frobenius_realization` の最終 conjunct (type-II HU-Frobenius) を実証明
(Coq `typeP_reducible_core_cases` 右枝 mirror): exceptional ⟹ C=⊥ ⟹ U≅Ū cyclic ⟹
Schur–Zassenhaus 共役で type-F complement へ cyclic 移送 ⟹
`typeF_frobenius_of_card_eq_exponent` collapse ⟹ 新 helper
`IsFrobeniusGroup.conj_complement` で type-P の U へ transport。

**⟹ 本 issue の (9.9.b)/(9.8.b)/(9.10) は全て実証明済**。S11 の残 sorry は
`sibleyTarget_H0C` (§14 cross-lane、do-not-fill 設計) のみ。同日 (9.7.a) 側も完遂
(issue 9000: caseA_u_le_cyclotomicQuotient + 無条件 u_le_cyclotomicQuotient +
opaque pair 2 組削除)。残る §9-隣接 work = S12 (10.7) 一般 case (T2 coherence、
issue 1017 管轄; exceptional 枝は本定理 cite で閉じられる)。→ **CLOSE 推奨**
(hub merge tick で issues/closed/ へ)。
