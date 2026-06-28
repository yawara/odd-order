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
- [ ] **補題4 (constituent ⟺ simple submodule)** — IntertwiningMap → simple submodule 抽出 (Schur +
      range-as-asModule-submodule)。**残る唯一の deep gate**、次の焦点。
- [ ] **character-level single-orbit 組立** → `restrictionConstituentsSingleOrbit_of_isIrreducible`
      (補題4 + `character_conj_of_simpleSubmodule`、補題4 入れば即)。
- [ ] **degree assembly**: 基底展開 + common-mult + orbit-size + 次数保存 → `χ(1)=e·u·θ₀(1)`。
- [ ] **e=1** (別 track、Gallagher/extension or Skolem-Noether in inertia)。
- [ ] (9.9.a) consumer wiring (S11 `caseB_character_counts` 第1連言)。

## 完了条件

`RestrictionConstituentsSingleOrbit` が irreducible χ に対し定理化 (hypothesis 除去) され、(9.9.a)
の `χ(1)=u` が sorry-free + axiom-clean で導ける。S11 `caseB_character_counts` 第1連言が閉じる。

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/{Clifford,CliffordAlgClosed,CliffordMultiplicityOne,
  InducedIrreducible,Inertia,ZIrr}.lean`、`issues/0026-peterfalvi-clifford-core.md` (旧 core routing)。
- issue 2030 (上流: (9.9.a) inertia 完了)。
- 原典: Isaacs Thm 6.5 (Clifford) / 6.11 (induction from inertia)、Peterfalvi §3 (1.5)/(1.7)。
