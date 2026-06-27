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

## 残 gap = module→character dictionary (補題群) → single-orbit

1. **iso-invariance of character**: ℂ[H]-LinearEquiv な部分加群は等 character (trace の iso 不変)。
   mathlib 近傍を要確認。最も foundational、まず着手。
2. **`submoduleChar`**: simple ℂ[H]-部分加群 N ⊆ (Res ρ).asModule の character。N simple ⟹ 既約 H-指標。
   **MISSING** (Subrepresentation→character、新規)。
3. **conjugate-character**: `char(N.map(conjSemilinearEnd ρ g)) = conjBy g (char N)` (semilinear twist
   `h↦ghg⁻¹` 由来)。**MISSING**。
4. **constituent ⟺ simple submodule**: θ constituent of Res χ ⟺ ∃ simple 部分加群 N, char N=θ
   (`restrictionMultiplicity_eq_finrank_intertwiningMap` + nonzero intertwiner の image は simple ≅ σ_θ)。

組立 (single-orbit): θ,η constituents ⟹ N_θ,N_η simple (4) ⟹ transitivity
(`iSup_map_conjSemilinearEnd_eq_top` + `linearEquiv_of_sSup_eq_top`) で N_θ ≅ (N_η)^g ⟹ (2,3,1)
θ = conjBy g η。

## e=1 (single-orbit と別の残)

各 constituent の multiplicity e=1。BG Prop 2.2 / Gallagher 型。(9.9.a) では θ₀ が inertia HC へ
linear extend する構造 (HC/H = C, coprime) から。`CliffordMultiplicityOne` の Skolem-Noether 機構
(End 代数 = k via Schur) が inertia 内で効く可能性。要設計。

## やること (research-grade, multi-session)

- [ ] **補題1 (iso-invariance of character)** — foundational・mathlib 近傍確認、まず着手。
- [ ] **補題2 (submoduleChar + N simple ⟹ 既約)** — Subrepresentation→character 基盤。
- [ ] **補題3 (conjugate-character = conjBy)** — semilinear twist。
- [ ] **補題4 (constituent ⟺ simple submodule)** — intertwining map 経由。
- [ ] **single-orbit 組立** → `restrictionConstituentsSingleOrbit_of_isIrreducible`。
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
