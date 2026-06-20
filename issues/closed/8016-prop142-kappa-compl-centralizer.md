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
- [x] **K*⊊M_σ を §13 機構から非循環に証明** (`kstar_ne_msigma_aux`, S14, commit 77c5eb33)。
      type-P2 の Frobenius-faithful 経路は**不要**だった: BG (e) は **Lemma 13.13**
      (`mem_sigma_of_tau1_tau3_centralize`, axiom-clean) ⟹ `ℳ(K*)≠{M}` と **Lemma 13.6**
      (`maximalContaining_eq_singleton_of_E1`, axiom-clean) ⟹ `ℳ(Syl_p M_σ)={M}` を使う;
      `K*=M_σ` なら Sylow `S≤M_σ=K*≤Mi` (Mi≠M) で矛盾。circular な Cor 15.6 route は回避。
      `typeP_structure` に 7th conjunct `Kstar ≠ M_σ` を追加 (両 case 枝で discharge)。
- [x] **C_M(M_σ) κ'-group** (`centralizer_msigma_isPiSubgroup_kappa_compl`, S14, commit c5fc73a5)。
      p∈κ | |C_M(M_σ)| ⟹ X₀=⟨x⟩ を K に入れ (b1) で M_σ≤K⊔K* ⟹ (Dedekind, `inf_mul_assoc`)
      M_σ=K* ⟹ K*≠M_σ と矛盾。BG が Cor 15.3 冒頭 (mmd L4209) で cite する文そのもの。
- [x] **κ'-group → Cor 15.3(a) `ha` assemble** (`mf_centralizer_msigma_decomp`, S15, commit 4cfa844a)。
      Schur-Zassenhaus (normal Hall σ-subgroup M_σ⊓C + complement X; [C:M_σ⊓C]∣[M:M_σ] σ' via
      `relIndex_dvd_index_of_normal`) + Hall D (X→(κ∪σ)'-Hall U) + Lemma 15.1(c)
      (`typeP_hall_small_subgroup_cyclic_tau2`)。
- [x] **`fitting_decomposition` refactor → A(8) 完全 axiom-clean** (commit 4cfa844a)。
      Case I の `mf_hall_centralizer_control` cite を `mf_centralizer_msigma_decomp` に置換。
      一般 Cor 15.3 (`mf_hall_centralizer_control`, 任意 Hall H) は S16 fusion-control / S15:2791 が
      `.2` で cite 継続ゆえ残置 (de-axiom には不要)。

## 完了条件 ✅ ACHIEVED (2026-06-21)
`fitting_isTI_of_mf_ne_msigma` (A(8) FittingIsTI) + `theoremA8_structure` (A(8) 完全形) が
**axiom-clean** (`#assert_only_allowed_axioms` 通過、AxiomsCheck 登録済)。

## 結論 (2026-06-21)
2026-06-20⁷ の「type-P2 K-faithfulness の自然 route 循環」診断は**正しかった**が、解決経路は
Frobenius-faithful argument ではなく **BG の (e) proof (Lemma 13.6 + 13.13) をそのまま形式化**する
ことだった (両 §13 lemma は既に axiom-clean で在庫)。「K*⊊M_σ を直接」狙うと循環だが、「(e) =
Syl_p(M_σ)⊄K*」を経由すると非循環。実 sorry 数は不変 (`mf_hall_centralizer_control` の sorry は
他 consumer のため残置) だが、A(8) FittingIsTI の **transitive sorryAx が完全消滅** = 実質的前進。

## 参照
- issue 8015 (親、2026-06-20⁷ 深掘り結論)。
- `mf_hall_centralizer_control_of_inputs` (S15:2420, proven engine)。
- `typeP_hall_small_subgroup_cyclic_tau2` (S14:2234)。
