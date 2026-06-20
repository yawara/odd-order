---
id: 8016
slug: prop142-kappa-compl-centralizer
title: "BG Prop 14.2(b1)(e): C_M(H) is a κ'-group (Cor 15.3 / A(8) axiom-clean の真の blocker)"
created: 2026-06-20
---

# BG Prop 14.2(b1)(e): C_M(H) is a κ'-group (Cor 15.3 / A(8) axiom-clean の真の blocker)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 背景 (2026-06-20 issue 8015 から分岐)

A(8) FittingIsTI chain (sorry-free declaration) の**唯一の axiom gap** = `mf_hall_centralizer_control`
(BG **Cor 15.3**, `S15_MF:2488` literal sorry) を `fitting_decomposition` (Cor 15.5) が H=M_σ で cite。
他は全 axiom-clean (検証済)。

**真の blocker = BG Prop 14.2(b1)(e)「C_M(H) は κ'-group」** (H Hall of M_σ、特に H=M_σ)。これがあれば
Cor 15.3(a) は assemble 可 (κ'-group → Schur-Zassenhaus σ/σ' Hall 分解 →
`typeP_hall_small_subgroup_cyclic_tau2` [S14:2234, sorry-free] で X cyclic τ₂)。

## 核心の難所: type-P2 K-faithfulness (K*⊊M_σ)

κ'-group ⟸ C_K(M_σ)=1 ⟸ **K*=C_{M_σ}(K)⊊M_σ** (+ ActsPrimeOn + κ-prime cyclic Sylow + Sylow 共役)。
- **type-F** (κ=∅): vacuous。
- **type-P1**: `msigma_eq_commutator_kappa_of_isComplement'` ([M_σ,K]=M_σ, **axiom-clean**) で K*⊊M_σ ✅。
- **type-P2** (M=KUM_σ): ⛔ **非循環 route 無し**。
  - Cor 15.6 (`typeP_kstar_in_mf`: K* cyclic + M_F not cyclic) は **sorryAx 保持** (fitting_decomposition
    経由) ⟹ 循環で使用不可。
  - `[M_σ,KU]=M_σ` は出る (E=KU complement) が K 単独の非自明作用を与えず。
  - 「M_σ non-cyclic / M''≠1 / M_σ non-abelian for type-P2」も全て循環。
  - typeP_structure (Prop 14.2 partial) は (b1)(e) の κ'-group 句を expose せず。

## やること
- [ ] type-P2 で「C_M(M_σ) κ'-group」(or K*⊊M_σ) を §14 の E-setup/Frobenius-normalizer 機構から
      **非循環**に証明 (Prop 14.2(b1)(e) 本体)。
- [ ] κ'-group → Cor 15.3(a) `ha` を assemble (clean な部品: typeP_hall_small_subgroup_cyclic_tau2,
      typeP_duality, Schur-Zassenhaus)。
- [ ] `fitting_decomposition` を refactor (mf_hall_centralizer_control → 新 ha-lemma) → A(8) 完全 axiom-clean。

## 完了条件
`fitting_isTI_of_mf_ne_msigma` (A(8) FittingIsTI) が axiom-clean (`#assert_only_allowed_axioms` 通過)。

## 参照
- issue 8015 (親、2026-06-20⁷ 深掘り結論)。
- `mf_hall_centralizer_control_of_inputs` (S15:2420, proven engine)。
- `typeP_hall_small_subgroup_cyclic_tau2` (S14:2234)。
