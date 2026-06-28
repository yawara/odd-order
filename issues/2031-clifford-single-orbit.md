---
id: 2031
slug: clifford-single-orbit
title: "Clifford single-orbit RestrictionConstituentsSingleOrbit — (9.9.a) degree gate"
created: 2026-06-28
---

# Clifford single-orbit `RestrictionConstituentsSingleOrbit` — the (9.9.a) degree gate

> lane-b (W3). 発信 = (9.9.a) Clifford 次数 (issue 2030)。ユーザー裁可で「Clifford 対応を構築」。

## 背景: (9.9.a) degree は single-orbit 1 定理に de-risk された (2026-06-28)

issue 2030 で **(9.9.a) の character-side inertia `I_U(θ)⊆C` は完全に proven** (FPF → 抽象 char
inertia → inflation 還元 → realization → capstone `caseB_inertia_realized`、全 axiom-clean)。残
(9.9.a) = Clifford 誘導次数 `χ(1)=u`。本セッションの infrastructure 調査 (Explore) で、これが
**一般 Clifford 対応のうち単一定理 `RestrictionConstituentsSingleOrbit` に帰着**すると判明。

### 次数の分解 (基底展開)

任意の χ∈Irr(G) と H◁G で `χ(1) = (Res χ)(1) = Σ_{θ∈Irr H} ⟨Res χ,θ⟩·θ(1)` (基底展開)。
(9.9.a) では Res χ の constituent が θ₀ の **single G-orbit** をなし、各々:
- 共通 multiplicity `e` (`hasCommonRestrictionMultiplicity_of_singleOrbit`、**既存**)、
- 個数 = `|orbit| = [HU:I_HU(θ₀)] = [HU:HC] = u` (`card_conjByOrbit_eq_index_inertia`、**既存** +
  I_HU(θ)=HC は capstone `caseB_inertia_realized`、+ [HU:HC]=u は `typeP_H_inf_U` 由来 index 計算)、
- 共通次数 `θ(1)=θ₀(1)=1` (conjBy は次数保存 + θ₀ linear ∵ H̄ abelian)。
⟹ `χ(1) = e·u·1`。**残 e=1** (各 isotypic 成分が multiplicity 1) + **single-orbit**。

### ∴ 真の gate = `RestrictionConstituentsSingleOrbit` (single-orbit) + e=1

`RestrictionConstituentsSingleOrbit χ` (Clifford.lean:811): Res χ の全 constituent が単一 G-orbit。
現状 `clifford_decomposition` (Clifford.lean:914) は **forward-dep scaffold** (data を hypothesis に
取り再パッケージ) で、single-orbit は**未定理化**。これを定理化するのが本 issue。

## 既存 infrastructure (Explore 調査、全て cite 可)

- **module-level transitivity = 解決済** (`CliffordAlgClosed.lean`):
  `conjSemilinearEnd ρ g` / `isSimpleModule_map_conjSemilinearEnd` /
  **`iSup_map_conjSemilinearEnd_eq_top`** (ρ irreducible ⟹ W の G-共役が ⊤ を張る) /
  `isIsotypicOfType_of_conjugates` (`Submodule.linearEquiv_of_sSup_eq_top` で「simple 部分加群は
  共役の1つに ≅」を実装)。
- **multiplicity↔intertwining dim**: `restrictionMultiplicity_eq_finrank_intertwiningMap` (Clifford.lean:373)。
- **multiplicity 整数性/非負**: `restrictionMultiplicity_natCast`/`_nonneg`/`_int`。
- **orbit machinery**: `conjByOrbit`/`card_conjByOrbit_eq_index_inertia` (InducedIrreducible.lean:227)。
- **conjBy 指標保存**: `restrictionMultiplicity_conjBy_right`; conjBy g θ の次数 = θ(1)。
- **multiplicity-one 特殊形** (inertia=G, G/H cyclic, IsAlgClosed): `restriction_isIrreducible`
  (CliffordMultiplicityOne.lean:318) — (9.9.a) は inertia=HC⊊HU ゆえ**別ケース**だが Skolem-Noether/
  cliffordConj/End 代数解析の機構は e=1 で流用可能性。

## 2026-06-28 重要更新: dictionary は `CliffordConjugateChar.lean` に既存 + module-level single-orbit landed

調査で、想定した dictionary 補題 1-3 は **`CliffordConjugateChar.lean` に既に実装済**と判明:
- **補題1 (iso-invariance)** = mathlib `Representation.char_iso` (Character.lean:171)。
- **補題2 (submoduleChar)** = `Subrepresentation.ofSubmodule'.toRepresentation.character` +
  `subRep_isIrreducible` (N simple ⟹ subrep 既約) + `subRepAsModuleEquiv`/`equivOfAsModuleEquiv`
  (asModule↔Representation 変換)。
- **補題3 (conjugate-character)** = `character_subRep_conj` (CliffordConjugateChar:218,
  `χ_{(ρg)W}(h)=χ_W(g⁻¹hg)`, `char_iso` 経由) + `submodule_iso_of_character_eq` (Schur 逆向き)。

**✅ module-level single-orbit landed** (commit `0d7d573f`, `CliffordSingleOrbit.lean`):
`character_conj_of_simpleSubmodule` (sorry-free + axiom-clean) — G-既約 ρ で Res^G_H ρ の任意 2 つの
simple k[H]-部分加群 N,N' は共役指標 ∃g, χ_{N'}(h)=χ_N(g⁻¹hg)。`iSup_map_conjSemilinearEnd_eq_top` +
`linearEquiv_of_sSup_eq_top` + `equivOfAsModuleEquiv`+`char_iso` + `character_subRep_conj` で組立。
**= single-orbit の module-level 核**。⚠ `set_option backward.isDefEq.respectTransparency false` が
asModule instance 合成に必須 (CliffordConjugateChar と同様)。

## 残 gap = 補題4 (constituent ⟺ simple submodule) — character-level single-orbit の唯一の橋

`RestrictionConstituentsSingleOrbit` (character-level) に残るのは **補題4 のみ**:
- **θ constituent of Res χ ⟺ ∃ simple k[H]-部分加群 N ⊆ (Res ρ).asModule, char(ofSubmodule' N)=θ**。
- 経路: `restrictionMultiplicity_eq_finrank_intertwiningMap` で multiplicity = finrank(IntertwiningMap σ_θ (Res ρ))
  ≠ 0 ⟹ ∃ nonzero intertwiner f:σ_θ→Res ρ ⟹ (Schur, σ_θ 既約) f injective ⟹ range f を
  `Submodule k[↥H] (resRep ρ H).asModule` 化 (Representation↔asModule-submodule 変換) ⟹ range f ≅ σ_θ
  ⟹ simple + char=θ。
- **deep gate**: IntertwiningMap → 単純部分加群の抽出 (mathlib IntertwiningMap plumbing + Schur +
  range-as-asModule-submodule)。次セッションの焦点。

組立 (character-level single-orbit、補題4 入れば即): θ,η constituents ⟹ N_θ,N_η simple (補題4) ⟹
`character_conj_of_simpleSubmodule` で χ_{N_θ}=conjBy g χ_{N_η} ⟹ θ=conjBy g η。

## e=1 (single-orbit と別の残)

各 constituent の multiplicity e=1。BG Prop 2.2 / Gallagher 型。(9.9.a) では θ₀ が inertia HC へ
linear extend する構造 (HC/H = C, coprime) から。`CliffordMultiplicityOne` の Skolem-Noether 機構
(End 代数 = k via Schur) が inertia 内で効く可能性。要設計。

## やること (research-grade, multi-session)

- [x] **補題1 (iso-invariance)** = mathlib `Representation.char_iso` (既存)。
- [x] **補題2 (submoduleChar + N simple ⟹ 既約)** = `ofSubmodule'.toRepresentation.character` +
      `subRep_isIrreducible` (CliffordConjugateChar 既存)。
- [x] **補題3 (conjugate-character)** = `character_subRep_conj` (CliffordConjugateChar 既存)。
- [x] **module-level single-orbit** = `character_conj_of_simpleSubmodule` (commit `0d7d573f`、本 leaf)。
- [x] **補題4 core** = `exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner` (commit `d076fce1`):
      nonzero intertwiner σ→Res ρ (σ 既約) ⟹ simple 部分加群 N で char(ofSubmodule' N)=χ_σ
      (Schur `injective_of_ne_zero` + `equivLinearMapAsModule` + `LinearEquiv.ofInjective` + `char_iso`)。
      **= IntertwiningMap→単純部分加群抽出 (deep content) 完了**。
- [x] **補題4 wrapper + character-level single-orbit 組立** = `restrictionConstituentsSingleOrbit_of_isIrreducible`
      (commit `65dd09e4`、★): **`RestrictionConstituentsSingleOrbit` を irreducibility から完全に定理化**
      (長年の scaffold 仮説を除去)。wrapper (χ.isIrreducible → ρ、`restrictionMultiplicity_eq_finrank` →
      nonzero intertwiner → 補題4 core) を inline、`character_conj_of_simpleSubmodule` + IrreducibleCharacter.conjBy
      接続で組立。sorry-free + axiom-clean。
- [x] **degree formula** = `apply_one_eq_restrictionMultiplicity_mul_index_inertia` (commit `9b3363d2`):
      `χ(1) = ⟨Res χ,θ₀⟩·[G:I_G(θ₀)]·θ₀(1)`。degree-side + single-orbit + common-mult + orbit-size を
      Finset.sum_filter + sum_const + cardinality bridge で集約。**= 一般 Clifford 次数機構 完成**。
- [ ] **e=1** (multiplicity-one、別 track、(9.9.a) 固有): θ₀ が inertia HC へ linear extend ⟹ Res χ
      multiplicity-free。Gallagher/extension or Skolem-Noether in inertia。**残る deep 数学**。
- [ ] (9.9.a) consumer wiring: G=HU, H=H, θ₀ = chief factor の nontrivial constituent。
      `caseB_inertia_realized` (issue 2030) で I_HU(θ)=HC ⟹ [HU:I]=[HU:HC]=u (typeP_H_inf_U)、
      θ₀(1)=1 (H̄ abelian ⟹ linear)、e=1 → degree formula で χ(1)=u → S11 caseB_character_counts 第1連言。

## 2026-06-28: ★ 一般 Clifford 次数機構 完成 (single-orbit 定理化 + degree formula)

ユーザー裁可「Clifford 対応を構築」を完遂: `RestrictionConstituentsSingleOrbit` を irreducibility から
定理化 (commit `65dd09e4`、長年 scaffold 仮説を除去) + 次数公式
`χ(1)=⟨Res χ,θ₀⟩·[G:I]·θ₀(1)` (commit `9b3363d2`)。dictionary は CliffordConjugateChar 既存活用、
新規 build = degree-side / module single-orbit / 補題4 核 / single-orbit 組立 / degree formula。
全 sorry-free + axiom-clean。**(9.9.a) χ(1)=u は degree formula へ e=1 + 固有値代入で導出可** =
残 deep 数学は e=1 (multiplicity-one) のみ。
- [ ] (9.9.a) consumer wiring (S11 `caseB_character_counts` 第1連言)。

## 2026-06-28 cont.: ★★ 一般 Clifford 対応 2 keystone landed — e=1 を「ψ linear」に再フレーム (lane-b 再開)

原文 (9.9.a) 精読 (`04.11` L99) で **degree-formula の e=1 経由でなく直接ルートが Peterfalvi 忠実**と判明:
χ∈𝒳(H₀C') ⟹ ψ=θλ を Res_{HC} χ の既約成分に取り、I(ψ)∩U=C ⟹ **Ind_{HC}^{HU}(ψ) 既約 = χ**、
**C'⊆Ker χ ⟹ (θλ)(1)=1** ⟹ χ(1)=[HU:HC]·1=u。e=1 ⟺ ψ linear ⟺ ψ(1)=1 で同値だが、後者は
**commutator 論法で直接**: [HC,HC]⊆Ker ψ ([H,H]⊆H₀=chief.N (H̄ abelian)、[H,C]⊆H₀ (C=C_U(H̄)=cSub)、
[C,C]=C'⊆Ker χ) ⟹ HC/[HC,HC] abelian。中心積指標論 (θ⊗λ) を回避。

**2 reusable keystone landed (axiom-clean、両 AxiomsCheck 登録)**:
- **`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`** (commit `8c32413d`, CliffordSingleOrbit):
  [Is] Thm 6.11 = ψ∈Irr(I), Ind_I^G ψ 既約, χ が ψ の上 ⟹ (χ:ClassFunction)=Ind_I^G ψ。
  証明 = Frobenius reciprocity (`inner_induce_ne_zero_iff_liesOver`) で ⟨Ind ψ,χ⟩≠0 + 既約直交性
  (`irreducibleCharacter_inner_eq_ite`) ⟹ 一致。**I の正規性不要** (Ind ψ 既約は仮説)。
  degree 系 `apply_one_eq_index_mul_of_liesOver_of_isIrreducibleCharacter_induce`: χ(1)=[G:I]·ψ(1)。
- **`apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`** (commit `73b1e0d0`,
  InflationCharacter, +import LinearCharacter acyclic): ψ∈Irr(G), N⊴G, N⊆characterKernel ψ,
  IsMulCommutative (G⧸N) ⟹ ψ(1)=1。証明 = `exists_inflate_eq_of_subset_characterKernel` で K⧸N へ
  descend → `apply_one_eq_one_of_isMulCommutative` → `inflate_apply_one` degree 保存。

⟹ **(9.9.a) χ(1)=u の概念的内容は完了** (e=1=ψ linear を含め)。残 = **全て carrier realization plumbing**。

### cont.²: 抽象正規性 keystone landed (commit `e186e0a4`)

step 2 (HC⊴HU) の抽象核を landed: **`OddOrder.GroupTheory.sup_normal_of_normal_left_of_normal_subgroupOf`**
(SubgroupInAmbient.lean、axiom-clean): H◁G, C≤U, `(C.subgroupOf U).Normal`, H⊔U=⊤ ⟹ (H⊔C)◁G。
証明 = `normalizer_eq_top_iff` + `mem_normalizer_iff` + `mem_sup_of_normal_left`、H が [h,c]·c で
正規化・U が uHu⁻¹=H/uCu⁻¹=C で正規化。**carrier の HC⊴HU はこれを instantiate するだけ** (下記 step 2)。

### 残 (9.9.a) = carrier realization (S11、multi-session、概念的に easy だが plumbing-heavy)

carrier goal: **χ∈xiOf data (chief.H0⊔chars.Cprime) ⟹ (χ:IrreducibleCharacter ↥(huSub data)) 1 = chars.u**
(これで φ=induceHU χ の φ(1)=q·χ(1)=qu、第1連言成立)。Γ=↥(huSub data)=HU、I=HC realized で 2 keystone 適用:
1. **HC を HU 内に realize** = `(HC.subgroupOf M).subgroupOf (huSub data)`、HC=data.H⊔cSub (Subgroup G)。
2. **HC ⊴ HU**: [HU,HC]⊆HC via H⊴HU (`hInHu_normal`) + [U,C]⊆C (**C=cSub=ker(uActionHom)⊴U 自動**=hom の核) + [H,C]⊆H₀。
3. **ψ∈Irr(HC) を Res_{HC} χ の成分に** (`exists_liesOver`) + **χ lies over ψ**。
4. **ψ(1)=1**: [HC,HC]⊆characterKernel ψ (上記 commutator 3 facts、H₀=chief.N realized⊆Ker χ も要) → keystone 2。
5. **Ind_{HC}^{HU} ψ 既約**: `isIrreducibleCharacter_induce_of_inertia_eq` (HU,HC,ψ) 要 inertia_HU(ψ)=HC。
   ⟵ **caseB_inertia_realized** (I_U(θ̄)⊆C、abstract φ 形) を ψ (HC-char) の inertia に lift + Dedekind
   I=H·(I∩U)=HC。**= realization の真の crux** (abstract φ-inertia ↔ IrreducibleCharacter.inertia of ψ)。
6. **[HU:HC]=u** = chars.u (cSub の `u_eq_card_quotient` range + [HU:HC]=[U:C]=u first-iso)。
7. 2 keystone 合成: χ=Ind ψ ⟹ χ(1)=[HU:HC]·ψ(1)=u·1=u。

**次セッション = 上記 realization** (HC realize+normality が最初の brick、inertia lift (step 5) が crux)。

## 完了条件

`RestrictionConstituentsSingleOrbit` が irreducible χ に対し定理化 (hypothesis 除去) され、(9.9.a)
の `χ(1)=u` が sorry-free + axiom-clean で導ける。S11 `caseB_character_counts` 第1連言が閉じる。

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/{Clifford,CliffordAlgClosed,CliffordMultiplicityOne,
  InducedIrreducible,Inertia,ZIrr}.lean`、`issues/0026-peterfalvi-clifford-core.md` (旧 core routing)。
- issue 2030 (上流: (9.9.a) inertia 完了)。
- 原典: Isaacs Thm 6.5 (Clifford) / 6.11 (induction from inertia)、Peterfalvi §3 (1.5)/(1.7)。
