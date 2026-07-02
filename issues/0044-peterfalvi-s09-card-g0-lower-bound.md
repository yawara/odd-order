---
id: 44
slug: peterfalvi-s09-card-g0-lower-bound
title: "Peterfalvi (7.10) card_G0_lower_bound を証明する"
created: 2026-05-28
---

# Peterfalvi (7.10) card_G0_lower_bound を証明する

## 背景

`OddOrder/Peterfalvi/S09_NonexistenceCertain.lean` の `card_G0_lower_bound`
(Peterfalvi (7.10), pp. 42-43) は §9 の **数値定理** で, (7.11) 主非存在定理を
(7.10) の系として導く出発点になる。statement は既に書かれており (`72a9864`),
(7.11) も (7.10) modulo で sorry-free にできている。残るは (7.10) 本体の証明。

`isometry_difference_pair_structure` (issue 0025) が sorry-free になったので,
§3 (1.4) 経由の §5 (3.2) / §6 (4.5) / §7 (5.6) の使用前提は整っている。

## 進捗 (2026-05-30)

(7.9) の最重 blocker だった **Peterfalvi (1.1) pointwise (奇位数 ⇒ 非自明既約は非実)** を
sorry-free 実装。`OddOrder/GroupTheory/RepresentationTheory/BrauerPermutationUnconditional.lean` に
`not_isReal_of_ne_trivial_of_odd_card'` (`Odd (Nat.card G) → χ ≠ 1 → ¬ IsReal (χ:CF G ℂ)`,
unconditional) + 補助 `realIrreducibleCharacter_eq_trivial_of_odd_card'` を追加。既存の
unconditional 系 `card_realIrreducibleCharacters_eq_one_of_odd_card'` (`# real Irr = 1`) から
subsingleton 一意性 (`Nat.card_eq_one_iff_exists`) で導出。AxiomsCheck clean, full build green。
note `notes/peterfalvi/s09_nonexistence_certain.md` の blocker 1 / plan 1 を更新済。

## 進捗 (2026-06-02, Lane D)

`FrobeniusFamily` の純群論 counting 側を前進。`kernelSpread i = (H_i^#)^G` を
`G ⧸ L_i` の代表による disjoint union として分解し,

```lean
F.card_kernelSpread_eq_index_mul i :
  Nat.card (F.kernelSpread i) = (F.L i).index * (Nat.card (F.H i) - 1)
```

を sorry-free で追加。あわせて partition 公式へ接続する
`sum_card_kernelSpread_eq_sum_index_mul`, `card_G0_eq_card_G_sub_sum_index_mul`,
`sum_index_mul_eq_card_G_sub_card_G0` も landed。

これで (7.10)(d) の `G₀ = G - ⋃(H_i^#)^G` から `|G₀|` を
`[G:L_i]` と `|H_i|` で直接展開できる。

さらに `h_i = |H_i|`, `e_i = [L_i:H_i]` への有理比率変換を追加し,

```lean
F.card_kernelSpread_div_card_G_eq_h_sub_one_div_h_mul_e i
F.card_kernel_sharp_div_card_L_eq_h_sub_one_div_h_mul_e i
F.sum_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G
```

で `|(H_i^#)^G| / |G| = (h_i - 1)/(h_i e_i)` および
`∑_i (h_i - 1)/(h_i e_i) = 1 - |G₀|/|G|` まで Lean 化済み。

また (7.10) 後半の最小 kernel order と `𝓑`-sum 評価に対応する

```lean
F.exists_min_h_index
F.h_add_two_le_h_of_min
F.h_sub_one_div_h_mul_e_le_h_sub_one_div_e_div_min_add_two
F.sum_h_sub_one_div_h_mul_e_le_e_sub_one_div_min_add_two
F.lowerBoundTerm_of_penultimate
F.exists_lowerBoundTerm_of_exists_penultimate
```

を追加。これで「`h = min h_i` なら `i ≠ j` で `h + 2 ≤ h_j`」から
`∑_{j∈𝓑} (h_j - 1)/(h_j e_j) ≤ (e - 1)/(h + 2)` への純算術部分と,
penultimate inequality から (7.10) 表示形への最終 rearrangement が Lean 化済み。

さらに erased-index と非負性の bridge として

```lean
F.h_sub_one_div_h_mul_e_nonneg
F.h_sub_one_div_e_nonneg
F.sum_erase_h_sub_one_div_h_mul_e_eq_one_sub_card_G0_div_card_G_sub
F.sum_h_sub_one_div_h_mul_e_le_sum_erase
F.sum_h_sub_one_div_e_le_sum_erase
```

も追加。これで最小 index `i` を外した和を全体 balance
`∑_j (h_j - 1)/(h_j e_j) = 1 - |G₀|/|G|` から直接抑えるための
集合和の単調性補題が Lean 化済み。

続いて (7.5)/(7.8) 由来の base estimate と (7.9) 由来の `𝓑`-sum bound を
最終表示形へ接続する bridge として

```lean
F.penultimate_of_Bsum_bound
F.lowerBoundTerm_of_Bsum_bound
F.exists_lowerBoundTerm_of_exists_Bsum_bound
```

を追加。これにより、残りの指標論側が「最小 index `i` と `𝓑` に対する
base inequality + `∑_{j∈𝓑}(h_j-1)/e_j ≤ e_i-1`」を渡せば、(7.10) の
表示下界は `F.exists_lowerBoundTerm_of_exists_Bsum_bound` で閉じられる。
また (7.9) の faithful statement interface として

```lean
Hypothesis79
Hypothesis79.conclusion
Hypothesis79.conclusion_swap
```

を追加。これは (7.8) package 2 本 + odd order + disjoint Dade supports から
`(β₁, ζ₂^{ν₂}) ≠ 0 ∨ (β₂, ζ₁^{ν₁}) ≠ 0` を named target にするだけで、
(7.10) 本体へ新しい仮定を足すものではない。

さらに (7.8.a) の standalone target として

```lean
Hypothesis78.weightedNuSum
Hypothesis78.BetaDecomp
```

を追加。`BetaDecomp` は `β = 1_G - ζ^ν + aΣ + Γ` と直交条件を
future proof 用に named target 化するだけで、`Hypothesis78` の証明書フィールドは増やしていない。

あわせて (7.8.b) の standalone target として

```lean
Hypothesis78.kernelOrder
Hypothesis78.complementIndex
Hypothesis78.smallIndex
Hypothesis78.zetaNuRho
Hypothesis78.zetaNuRhoNormSq
Hypothesis78.gammaNormSq
Hypothesis78.NormEstimates
```

を追加。`NormEstimates` は `2e+1≤h` から `‖(ζ^ν)^ρ‖² ≥ 1-e/h` と
`‖Γ‖² ≤ e-1` を named target 化するだけで、これも `Hypothesis78` の仮定にはしていない。
さらに (7.8.b) の純算術部分

```lean
Hypothesis78.quadraticTerm_nonneg_of_smallIndex
```

を sorry-free で追加。これは `u=(1/e)(1-1/h)`, `v=1/h`, `a∈ℤ`, `2e+1≤h` から
`0 ≤ u a² - 2 v a` を出す補題。

また `‖β‖²=e+1` blocker の Dade-isometry bridge として

```lean
Hypothesis78.betaNormSq
Hypothesis78.sourceDiffNormSq
Hypothesis78.beta_inner_self_eq_sourceDiff_inner_self
Hypothesis78.betaNormSq_eq_sourceDiffNormSq
Hypothesis78.sourceDiff_inner_self_expand
Hypothesis78.sourceDiffNormSq_expand
Hypothesis78.SourceDiffNormEvaluation
Hypothesis78.betaNormSq_eq_complementIndex_add_one
Hypothesis78.sourceDiffNormEvaluation_of_inner_values
Hypothesis78.zetaDistinct_inner_self_eq_one_of_irreducible
Hypothesis78.sourceDiffNormEvaluation_of_inner_values_of_zeta_irreducible
Hypothesis78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal
Hypothesis78.sourceDiffNormEvaluation_of_zeta_ind_orthogonal_of_zeta_irreducible
Hypothesis78.betaNormSq_eq_complementIndex_add_one_of_inner_values
Hypothesis78.betaNormSq_eq_complementIndex_add_one_of_inner_values_of_zeta_irreducible
Hypothesis78.betaNormSq_eq_complementIndex_add_one_of_zeta_ind_orthogonal_of_zeta_irreducible
```

を sorry-free で追加。`SourceDiffNormEvaluation` は standalone target として
`sourceDiffNormSq = e+1` を名前付けし、
`betaNormSq_eq_complementIndex_add_one` は既存の Dade bridge から `‖β‖²=e+1` を即座に戻す。
`sourceDiffNormEvaluation_of_inner_values` は、`⟨Ind1H,Ind1H⟩=e`, `⟨ζ,Ind1H⟩=0`,
`⟨Ind1H,ζ⟩=0`, `⟨ζ,ζ⟩=1` の 4 評価から source target を作る。
2026-06-02 追記: `zetaDistinct_inner_self_eq_one_of_irreducible` と
`*_of_zeta_irreducible` bridge を追加し、`⟨ζ,ζ⟩=1` は
`IsIrreducibleCharacter ζ` から即座に得られる形に縮小。さらに
`sourceDiffNormEvaluation_of_zeta_ind_orthogonal` 系で Hermitian symmetry から
`⟨Ind1H,ζ⟩=0` を自動生成し、source-side 入力を
`⟨Ind1H,Ind1H⟩=e`, `⟨ζ,Ind1H⟩=0`, `IsIrreducibleCharacter ζ` まで縮小。
これで `‖β‖²=e+1` 側は、Dade isometry bridge、source norm の
4 inner-product 展開、4 source 評価から beta target への接続まで Lean 化済み。残りは source 側 character computation と、
(7.7.b)/(7.8.a) から `u,v,w` 形へつなぐ指標論側。
残る (7.10) 本体は依然として (7.8.a/b) proof, (7.9) proof,
(6.8) coherence 本体, および Thompson/Frobenius-family bridge の合成が必要。

## 全体構造 (Peterfalvi §9 mmd `04.9_pp_38_43_*.mmd` より)

(7.10) は次の構成ブロックの **合成定理**:

| # | 役割 | 状態 |
|---|------|------|
| (7.1) Hypothesis | (2.2) + `ρ : CF(G) → CF(L,A)` (`χ^ρ(a) = |H(a)|⁻¹ Σ_{x∈H(a)} χ(ax)`), `A^τ = ⋃_{a∈A} (aH(a))^G` | ✅ `Hypothesis71` (issue 0045) |
| (7.2) Lemma | (a) `α ∈ CF(L,A) ⇒ α^{τρ} = α`. (b) `‖χ^ρ‖² ≤ ‖χ‖²`, 等号 ⟺ `χ ∈ im τ`. | ✅ `chiRho_dadeImage_eq`, `chiRho_norm_sq_le` (issue 0045, 等号条件は後回し) |
| (7.3) Lemma | `|G|⁻¹ Σ_{A^τ} \|χ\|² ≥ ‖χ^ρ‖²`, 等号 ⟺ `χ` が `aH(a)` 上定数 | ✅ `chiRho_integral_inequality` (issue 0045, 等号条件は後回し) |
| (7.4) Hypothesis | 部分群族 `(L_i)`, 各 (7.1), `A_i^{τ_i}` pairwise disjoint, `G_0 = G - ⋃ A_i^{τ_i}` | ✅ `FamilyHypothesis71` |
| (7.5) Theorem | `|G|⁻¹(Σ_{G_0}\|χ\|² - |G_0|) + Σ_i (‖χ^{ρ_i}‖² - |A_i|/|L_i|) ≤ 0` | ✅ `family_inequality` (sorry-free) |
| (7.6) Hypothesis | normal `H ⊴ L`, `A = H^#`, `|H|=h`, `|L:H|=e`, `T = {Ind_H^L θ}` | ✅ `Hypothesis76` |
| (7.7) Lemma | `χ^ρ(x) = Σ c̄_i/‖ζ_i‖² · ζ_i(x)` の explicit formula, `‖χ^ρ‖²` 二重和 | ✅ (7.7.a) `chiRho_explicit_formula` (certificate field `chiRho_decomp`) + (7.7.b) `chiRho_norm_sq_double_sum` (proved) |
| (7.8) Lemma | (a) `β = 1_G - ζ^ν + a·Σ + Γ` の形, `a ∈ ℤ`. (b) `‖ζ^{νρ}‖² ≥ 1 - e/h`, `‖Γ‖² ≤ e-1`. (c) `χ ⊥ S^ν ⇒ ‖χ^ρ‖² = |A|/|L|·(β,χ)²`. | 🟡 (7.8.c) `Hypothesis78` + `chiRho_eq_inner_beta_on_A` (certificate field) + `chiRho_norm_sq_eq_card_ratio_mul` (proved); (7.8.a) `Hypothesis78.weightedNuSum` + `Hypothesis78.BetaDecomp` target, proof 未; (7.8.b) `Hypothesis78.NormEstimates` target + `quadraticTerm_nonneg_of_smallIndex` and beta norm Dade/source expansion proved; remaining proof 未 |
| (7.9) Key Lemma | `I={1,2}`, `G` 奇位数, coherent ⟹ `(β_1, ζ_2^{ν_2}) ≠ 0` または `(β_2, ζ_1^{ν_1}) ≠ 0` | 🟡 `Hypothesis79` + `conclusion` predicate; proof 未 |
| (6.8) Theorem | 直交族分解 `Ind_{L_i}^G (ζ_{it} - d_{it}ζ_{i1}) = χ_{it} - d_{it}χ_{i1}` | 🟡 `sibleySetup_is_coherent` stmt + `IndChainDecomposition` (issue 0046, 本体 proof 別途) |
| Thompson kernel-nilpotent | Frobenius kernel 冪零 | ✅ Isaacs Ch.6 |
| (7.10) | 上記の合成 + 算術操作 | 🟡 `FrobeniusFamily.CharacterEstimateData` target + `lowerBoundTerm_of_characterEstimateData` bridge; `card_G0_lower_bound` sorry は character-estimate data 構成に局所化 |

各内部依存: (7.2)←(2.7),(2.6); (7.3)←(7.2); (7.5)←(7.3); (7.7)←(7.6);
(7.8)←(7.7),(1.5),(2.7); (7.9)←(7.8),(5.9),(1.1),(4.1); (7.10)←(7.5),(7.8),(7.9),(6.8) + Thompson; (7.11)←(7.10).

## やること (粒度別)

サブ issue 0045+ で分割予定。本 issue は roof tracker。

- [x] sub-issue 0045: (7.1) `Hypothesis71` + (7.2.a/b) + (7.3) integral inequality (sorry-free)
- [x] sub-issue 0046: (6.8) `sibleySetup_is_coherent` statement + `IndChainDecomposition` consumer interface (proof 本体は別 issue)
- [x] sub-issue: (7.4) family hypothesis + (7.5) main inequality (sorry-free, 2026-05-29)
- [x] sub-issue: (7.6) `Hypothesis76` + (7.7.a/b) `χ^ρ` explicit formula + norm-square double sum (2026-05-29; (7.7.a) は `chiRho_decomp` 証明書フィールド, (7.7.b) は proved)
- [ ] sub-issue: (7.8.a/b/c) norm estimates — (7.8.c) `Hypothesis78` + `chiRho_eq_inner_beta_on_A` (証明書) + `chiRho_norm_sq_eq_card_ratio_mul` (proved) done 2026-05-29; (7.8.a) `Hypothesis78.weightedNuSum` + `Hypothesis78.BetaDecomp` target は 2026-06-02 に追加済み, proof 未; (7.8.b) `Hypothesis78.NormEstimates` target も 2026-06-02 に追加済み, `quadraticTerm_nonneg_of_smallIndex` と beta norm Dade/source expansion は proved, `⟨ζ,ζ⟩=1` は `IsIrreducibleCharacter ζ` bridge まで proved, `⟨Ind1H,ζ⟩=0` は Hermitian symmetry bridge まで proved, 残り proof 未 (`‖ζ^{νρ}‖² ≥ 1-e/h`, `‖Γ‖² ≤ e-1`) — 精密 spec + blocker は `notes/peterfalvi/s09_nonexistence_certain.md` 2026-05-30 節 (B: 整数射影 / `‖β‖²=e+1` / ~~Burnside (1.5.d)~~ / `nu↔coherence` 未組立)。**Burnside (1.5.d) building block は 2026-05-30 解消** → `ColumnOrthogonality.lean` の `sumIrreducibleDegreeSq` (`Σ χ(1)²=|G|`) + `sumNontrivialIrreducibleDegreeSq` (`Σ_{χ≠1} χ(1)²=|G|−1`), AxiomsCheck clean
- [ ] sub-issue: (7.9) 2-family non-orthogonality — `Hypothesis79` + `Hypothesis79.conclusion` statement interface は 2026-06-02 に追加済み。proof blocker は同ノート 2026-05-30 節 ((5.9) nu 接続; **disjoint-support inner=0 補題は 2026-05-30 解消** → `ClassFunction.inner_eq_zero_of_disjoint_support` (+ `innerSum_eq_zero_of_disjoint_support`); **`Odd card ⇒ ¬IsReal χ` も 2026-05-30 解消**)
- [ ] sub-issue: (6.8) 本体 proof ((6.1)-(6.7), (5.2), (4.6) の積み上げ)
- [ ] (7.10) 最終 assembly: (7.5)(7.8)(7.9)(6.8)+Thompson の連立 + 算術（counting/ratio, minimal-index, erased-sum arithmetic, B-sum→displayed-bound bridge は 2026-06-02 までに実装済み）。2026-06-02 追記: `FrobeniusFamily.CharacterEstimateData` と `lowerBoundTerm_of_characterEstimateData` を追加し、残りを `CharacterEstimateData` 構成に局所化。

## 完了条件

- `OddOrder.Peterfalvi.S09.card_G0_lower_bound` の `sorry` が消える。
- `lake build OddOrder.Peterfalvi.S09_NonexistenceCertain` が通る。
- (7.11) 主定理が依然 sorry-free。

## ✅ HUB 裁定 + 現況更新 (2026-07-02 全体レビュー) — **owner = lane a、spine 上の orphan を解消**

**spine 状態 (コード検証済)**: `card_G0_lower_bound` は **feitThompson spine 上の on-path sorry**:
`theorem88_caseB_holds → not_all_maximal_typeI (S14:5780) → S09.not_trivial_G0 (S09:6778) →
card_G0_lower_bound (S09:6478)`。bypass assembly (`not_trivial_G0_of_family_source_decomposition` /
`_of_characterEstimateData`) は存在するが wired route は本定理経由。**どのレーンのプランにも
載っていなかった** (本レビューで検出した唯一の orphaned on-path sorry)。

**stale 行の更新**: (6.8) `sibleySetup_is_coherent` = ✅ sorry-free (S08 帯 全 0 sorry)。
(7.7.a) certificate = ✅ discharge 済 (`chiRho_decomp_proof`, S09_CertificateDischarge:303, issue 1013)。
(7.8.b) の witness 側 = `witness_L_zeta_bound` (S14:5372) 等 landed (issue 1015 で hzeta0nu も解消)。
`Hypothesis78.nu_isometry` は family 版に弱化受理 (issue 0091)。⟹ 残 = **(7.8.a/b) proof 本体 +
(7.9) proof + `CharacterEstimateData` 構成** ((6.8) gate は消滅)。

**裁定: owner = lane a**。S09 は a 所有、かつ文書順で **Pf §7 < §9 (σ-tail) < §11.8** — 上流優先+
文書順により、lane a は現行 11.8.3 チェーンの一段落後、**σ-tail (issue 9000) より先に本 issue を
queue に入れる**。lane b の §7 certificate infra (0090 = S09_CertificateDischarge) と S14 witness 系は
cite してよい (再構築しない)。

## 参照

- depends on: `issues/closed/0025-peterfalvi-isometry-difference-core.md` (済)
- file: `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
- file: `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean` (SibleySetup)
- file: `OddOrder/Peterfalvi/S07_Coherence.lean`
- note: `notes/peterfalvi/s09_nonexistence_certain.md`
- mmd: `references/peterfalvi/04.9_pp_38_43_Non-existence_of_a_Certain_Type_of_Group_of_Odd_Order.mmd`
