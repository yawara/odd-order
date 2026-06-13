---
id: 8003
slug: s13-lemma136-contradiction
title: "BG Lemma 13.6 contradiction 分岐 (q∉β ∧ X⊄M_σ') の構成"
created: 2026-06-14
---

# BG Lemma 13.6 contradiction 分岐 (q∉β ∧ X⊄M_σ') の構成

## 背景

`S13_PrimeAction.maximalContaining_eq_singleton_of_E1` (Lemma 13.6) の残 sorry は
contradiction 分岐 `¬(q∈β(M) ∨ X⊆M_σ')` = `q∉β(M) ∧ X⊄M_σ'`。BG L3610-3624 はこの配置が
不可能 (False) であることを示す。reduction 分岐 (Cor 12.14 faithful) は commit 99d7d053 で完成。

**全 dependency は pin 済み** (再調査不要):
- Thm 13.5 = `E1_actsPrime hG h hE1ne : ActsPrimeOn (M_σ) E₁` (S13_PrimeAction:410)
- Lemma 12.19 (mmd の "Theorem 12.13" は **誤引用**) = `S12_E.derivedE_centralizes_betaComplement`:
  `∃ W ≤ M_σ, IsHallSubgroup (β M)ᶜ (W.subgroupOf M_σ) ∧ derivedInG E ≤ C(W)`
- Lemma 12.17 = `S12_E` (C_{M_σ}(E) ⊆ M_σ', [M_σ,E]=M_σ) (S12_E:72)
- Cor 12.6(a) = `S12_Corollary126.elemAb_normal_in_E_of_tau2` (1st conjunct: `E ≤ N(A)` = A◁E)
- Thm 12.5(d) = `Msigma_nilpotent_of_tau2` の第4 conjunct `M_σ ⊓ C(A) = ⊥`
- Thm 13.4 = `S13_Theorem134.centralizer_le_centralizer_of_tau1`:
  `C_{M_σ}(P) ≤ C_{M_σ}(R)` (P∈ℰ_p¹(E) τ₁, R∈ℰ_r¹(C_E(P)))
- Prop 1.5 = Isaacs Ch04 `exists_aInvariant_sylow` / `aInvariant_sylow_conj` /
  `aInvariant_pSubgroup_le_aInvariant_sylow` (ForwardFromCh03:440/492/554)

## 証明ステップ (BG L3608-3624)

1. **X ⊆ C_{M_σ}(E₁)**: hXC (X≤M_σ⊓C(P)) + E1_actsPrime + P≤E₁,P≠⊥ で
   `M_σ⊓C(P)=M_σ⊓C(E₁)`。[clean・独立] 核: g∈P# 取り `fixedByElement M_σ g = fixedBy M_σ E₁`、
   `M_σ⊓C(P) ≤ M_σ⊓C(g) = M_σ⊓C(E₁) ≤ M_σ⊓C(P)`。
2. **🔴 X ⊆ C_{M_σ}(E') [crux / reconstruction gap]**: 原文「by Prop 1.5, we can assume E
   normalizes S and X⊆S⊆C_{M_σ}(E')」。Lemma 12.19 で E' は Hall β' W を中心化 (W⊇ Sylow q,
   q∈β')。coprime 作用の正規化で X を含む E'-中心化 Sylow q を取る必要。**X が E'-invariant か
   非自明**。contradiction 分岐ゆえ与えられた S は無視可・自前の便利な Sylow を構成してよい点が鍵。
   → 真剣に再構成 (Prop 1.5(a)+(c): C_{M_σ}(E') 内の E-不変 Sylow) を試み、詰まれば ChatGPT 再構成依頼
   ([[feedback-ask-chatgpt-for-elided-gaps]])。
3. **E₁E' ≠ E**: Lemma 12.17 (C_{M_σ}(E)⊆M_σ') + X⊄M_σ' ⟹ X⊄C_{M_σ}(E)。
   E₁E'=E なら C_{M_σ}(E)=C_{M_σ}(E₁)⊓C_{M_σ}(E') ⊇ X (step1,2)、矛盾。
   要補題: `C_{M_σ}(E₁⊔E') = C_{M_σ}(E₁) ⊓ C_{M_σ}(E')`。
4. **E₂ ≠ 1**: E=E₁⊔E₂⊔E₃ (SubgroupESetup から要確認) かつ **E₃ ≤ E'** (要 pin: τ₃-Hall ⊆ derived?)。
   E₂=⊥ なら E=E₁⊔E₃ ≤ E₁⊔E' ⟹ E₁E'=E、step3 と矛盾。
5. **A 構成**: E₂≠1 ⟹ ∃ p∈τ₂(M), A∈ℰ_p²(E)。`elemAb_normal_in_E_of_tau2` で A◁E、
   `Msigma_nilpotent_of_tau2` の第4 conjunct で `M_σ⊓C(A)=⊥`。
6. **A が X を中心化**: A = A₀ × [A,E₁] (E₁ の A への coprime 作用分解、Prop 1.6(d)/Isaacs Ch04)。
   - A₀ = C_A(E₁) が X 中心化: 各 line R∈ℰ_p¹(A₀) は R≤C_E(E₁)、Thm 13.4 (P=E₁,r=p) で
     C_{M_σ}(E₁)≤C_{M_σ}(R) ⟹ X≤C_{M_σ}(R) ⟹ R 中心化 X。lines が A₀ を生成。
   - [A,E₁] ≤ E₁ (E₁◁E + A≤E)。X≤C_{M_σ}(E₁) (step1) ⟹ E₁ 中心化 X ⟹ [A,E₁] 中心化 X。
7. **矛盾**: A 中心化 X ⟹ X ≤ M_σ⊓C(A) = ⊥ (step5)、X≠⊥ (|X|=q) に矛盾。

## 未 pin の補助事実 (step ごと要確認)

- step3: `C_{M_σ}(H⊔K) = C_{M_σ}(H)⊓C_{M_σ}(K)` (centralizer of join)
- step4: `E = E₁⊔E₂⊔E₃` (SubgroupESetup field? E_compl_sup は M_σ⊔E=M のみ); **`E₃ ≤ derivedInG E`**
- step6: coprime 分解 `A = C_A(E₁) ⊔ [A,E₁]` + `[A,E₁] ≤ E₁` + line 生成の assembly

## 完了条件

`maximalContaining_eq_singleton_of_E1` が sorry-free + build-green + axiom-clean。
13.6 完成で AxiomsCheck 登録 + hub 連絡 (下流 13.9-13.13 解禁)。

## 参照

- BG L3604-3624 (Lemma 13.6), [[issue 8002]] (reduction 分岐・faithful Cor 12.14)
- commit 99d7d053 (reduction half + transfer helper)
- S13_PrimeAction:559 (定理), :410 (E1_actsPrime), S12_E:72/:270, S12_Corollary126:379,
  S13_Theorem134:532, Isaacs ForwardFromCh03:440
