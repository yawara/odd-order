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

## 2026-07-03 (lane-a) — (7.8.a) projection blocker RESOLVED by 11.8.2 infra; (7.8.a) = concrete next entry

11.8.5 extension-一般化 (S12) 完遂の副産物として、**(7.8.a) `exists_betaDecomp` の 2026-05-30 blocker (ii)
「整数係数直交射影 ... repo 未組立」が解消**。`OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
の `exists_intProjection_of_orthonormal_ZIrr` (`φ∈ZIrr` を orthonormal `R⊆ZIrr` へ整数係数射影 + 残余 Y⊥R)
が丁度その道具。`nu_mem_ZIrr_of_isCoherent` (S09:2077) が nu-ZIrr gap も解消 (nu=coherence extension 時)。

**`exists_betaDecomp` の残ギャップ (assembly task)**:
1. **coefficient-relation (単一整数 a)**: `⟨β, ν(ζ_i)⟩` が全 i で `a·weight_i` (単一 a) になること。
   `β=τ(Ind1H−ζ)`、`ν`=coherence ゆえ coherence↔Dade adjoint (`IsCoherent.extension_inner_eq`,
   S07:1665 の lattice-relative isometry) で `⟨τ(w),ν(φ)⟩=⟨w,φ⟩` を出し、source 側 `⟨Ind1H−ζ,ζ_i⟩` に
   帰着。既 bridge `beta_inner_zetaImage_eq_int_sub_one_of_irreducible_source_data` (S09:3569) +
   `weightedNuSum_inner_zetaImage_eq_one_of_irreducible_source_data` (S09:3081) が distinguished 列を供給済。
2. **`orth_one` (S^ν⊥1_G)**: coherence が非principal ζ_i (degree ζ_i(1)=e·θ(1)>1) を signed irreducible
   χ≠1_G に写す ⟹ `⟨ν(ζ_i),1_G⟩=0`。coherence の degree/sign API (S07/S08 signedIrreducible) 要確認。
3. 射影残余 Y を `Γ = Y` として BetaDecomp フィールドに詰める (Gamma_orth_nu/one は射影の Y⊥R から)。

⟹ **(7.8.a) は現 tractable な entry** (projection tool + coherence adjoint + 既 bridge の assembly、
新 scaffold field 追加は不要 = doneness OK)。(7.8.b)/(7.9)/`CharacterEstimateData` 構成は (7.8.a) の後。

## 2026-07-03 cont. (lane-a, /loop) — 真の frontier = Hypothesis76/78-from-Frobenius 構成 (abstract は Ind 構造を捨てている)

(7.8.a) を abstract `Hypothesis78` 上で attack した結果、**abstract 層では原理的に不能**と判明 (深く engage 済):
- `Hypothesis76.zeta : Fin(n+1) → CF L` は **opaque な class function** (support on H + degree-ratio
  `zeta_one_eq_d_mul` のみ)。`ζ_i = Ind_H^L θ_i` という induced 構造を**保持していない**。
- ⟹ `BetaDecomp.orth_one` (⟨ν(ζ_i),1_G⟩=0)・`⟨Ind1H,Ind1H⟩=e`・`⟨ζ,Ind1H⟩=0` は abstract fields から
  **導出不能** (実際 `characterEstimateData_of_family_source_decomposition` はこれらを **hypothesis 引数**に取り、
  `BetaDecomp.orth_one` は **field** = 構成者が establish すべき入力)。
- coherence の degree 保存も abstract `IsCoherent` (isometry + ZIrr-codomain のみ) には無い。

**⟹ 真の on-spine 作業 = `FrobeniusFamily i` から `Hypothesis76`/`Hypothesis78` を Ind 構造込みで構成する**
(ζ_i := Ind_H^L θ_i を実体化)。これで source 側事実が provable になる:
- `⟨1_L, Ind_H^L θ⟩ = ⟨1_H, θ⟩` (Frobenius reciprocity `inner_induce_eq_inner_restrict`, 既存
  `InducedCharacter.lean:785`) ⟹ θ_i≠1 で `⟨1_L,ζ_i⟩=0`、`⟨Ind1H,Ind1H⟩=[L:H]=e` (Mackey, H⊴L)。
- (2.7) adjoint `⟨χ^ρ,α⟩_L=⟨χ,τ(α)⟩_G` を χ=1_G に適用 ⟹ orth_one (source 側 ⟨1_L,ζ_i⟩=0 経由)。
- Frobenius (θ≠1 ⟹ Ind_H^L θ irreducible) で `hirr` を establish。

**次 iteration**: `hypothesis76_of_frobenius` 系の constructor に着手 (Ind_H^L θ family + coherence)。
これは (7.8.a/b)/(7.9) を abstract で attack するより上流の genuine foundation。既存の abstract 層
scaffold (constructor 群) は Ind-carrying な具体構成が完成すれば consumer になる。

## 2026-07-03 cont.² (lane-a, /loop) — first foundation block landed; 7.10 = multi-week construction

**Landed** (`692a8ba4`): `induce_inner_trivial` (`⟨Ind_H^G θ,1_G⟩=⟨θ,1_H⟩`, RepTheory base file) — the
first genuine building block: gives `⟨ζ_i,1_L⟩=0` for θ_i≠1, source input to `orth_one`.

**⚠ 進捗の透明性 (feedback-flag-poor-progress)**: 7.10 は **multi-week の §6-7 foundation** と確定。
全 constructor 層は最終的に (7.7)/(7.8.b)/(7.9) の char 内容 + (7.1)/(7.4) の Dade ρ-setup を要求。
induced-char 算術 (degree `induce_apply_one`・vanishing・reciprocity `inner_induce_eq_inner_restrict`・
今回 `induce_inner_trivial`) は**既存/整備済**だが、深い trunk は未着手:
- **Hypothesis71-from-TI** ((7.1) Dade ρ-setup を TI/Frobenius から構成) = §2/§4 Dade 機構。
- **coherence** (induced family `{Ind_H^L θ}` の (5.6)/(6.8) Sibley coherence) = §5-6。
- **(7.8.b) `chiRhoNormSq` 下界** + **(7.9) 2-family 非直交**。

**次 block 候補** (leaf 先行, 上流 trunk へ): `⟨Ind_H^L 1_H, Ind_H^L 1_H⟩=[L:H]=e` (`⟨Ind1H,Ind1H⟩=e`
source fact; reciprocity + normal-H Mackey `Res_H Ind_H^L 1 = e•1_H`)、その後 Hypothesis71-from-TI trunk。
/loop は 1 iteration = 1 genuine block で漸進中 (scaffold 追加はしない = doneness)。

## 2026-07-03 cont.³ (lane-a, /loop) — 2nd block landed; leaves ~done, next = trunk

**Landed** (`233ce907`): `induce_trivial_inner_self` (`⟨Ind_H^G 1_H, Ind_H^G 1_H⟩=[G:H]` for H⊴G) —
the `⟨Ind1H,Ind1H⟩=e` source norm (via `induce_apply_of_mem_normal_of_const` + reciprocity).

**状態**: induced-char **leaves** (degree/vanishing/reciprocity/trivial-inner/trivial-norm) は既存+今回
2 本で概ね揃った。残る 7.10 は **deep trunk** (fresh context 推奨):
1. **`Hypothesis71`-from-TI/Frobenius** = (7.1) Dade ρ-setup を TI 構造から構成 (§2/§4 Dade)。次 iteration の第一目標。issue 0045 が (7.1) を sorry-free 化済ゆえ、既存 `Hypothesis71` 補題群から constructor が組めるか要調査。
2. coherence ((5.6)/(6.8) Sibley、induced family)。
3. (7.8.b) `chiRhoNormSq` 下界 + (7.9) 2-family 非直交。

## 2026-07-03 cont.⁴ (lane-a, /loop) — 🎯 (7.1) trunk layer DONE: Hypothesis71-from-TI wireable

**Landed** (`5d3b03f3`): `Hypothesis71.of_isTISubset` — the (7.1) Dade ρ-setup **constructible from any
TI-subset**. Key discovery: the Dade-isometry-existence machinery **already exists in S04**
(`Hypothesis.of_isTISubset` (2.3) + `dadeMap` + `isDadeMap_dadeMap` + `HConjInvariant.of_forall_H_eq_bot`),
so (7.1) is a genuine **wiring** of real content, NOT a from-scratch build. **7.10 trunk is more
tractable than the "multi-week from scratch" estimate** — the Dade layer is done.

**次 (tractable wiring 継続)**:
1. `FrobeniusFamily i` → `Hypothesis71 G (H_i^#) (L_i)`: `isTI` field が `IsTISubset` を、`normalizer_eq`
   が L=N(H) を供給。残り `hA_sharp`(H^#⊆sharp)/`hA_L`(H^#⊆L)/`hL_norm` は Frobenius から。
2. **Hypothesis76** (induced family {Ind_H^L θ} + coherence): coherence は S08 Sibley ((6.8) sorry-free
   per 0044) が wireable か要調査。degree-ratio/support fields は induced-char leaves (今セッション) で埋まる。
3. (7.8.b)/(7.9)/assembly。

## 2026-07-03 cont.⁵ (lane-a, /loop) — (7.1) family-member wiring DONE

**Landed** (`11f44fa2`): `FrobeniusFamily.hypothesis71` — each member `i` → `Hypothesis71 G (H_i^#) L_i`
(side conditions all from family fields: mem_sharp / kernel_le / mem_kernel_sharp_conj_iff_of_mem_L / isTI).
**次**: (7.4) `FamilyHypothesis71` 束ね (per-member Hypothesis71 + disjoint A_i^{τ_i} 台 ← coprime_kernel)、
その後 **Hypothesis76** (induced family {Ind_H^L θ} + coherence = trunk の残りの deep part、S08 Sibley wireable か調査)。

## 2026-07-03 cont.⁶ (lane-a, /loop) — 🎯 (7.1)/(7.4) 構造層 完全 wired

**Landed** (`2976980b`): `FrobeniusFamily.familyHypothesis71` + bridge `dadeSupport_hypothesis71_eq_kernelSpread`.
**`FrobeniusFamily` → `FamilyHypothesis71` (7.4) が完成** (per-member hyp71 + isDadeIsometry_of_isDadeMap +
pairwise_disjoint ← dadeSupport=kernelSpread + 既存 kernelSpread_disjoint)。**card_G0_lower_bound の構造
foundation (7.1/7.4) は wiring で done** — `characterEstimateData_of_family71_*` に `F.familyHypothesis71`
を渡せる。

**残 = genuine char content のみ** (Hypothesis76 coherence 系):
- (7.8.b) `chiRhoNormSq` 下界 (`hi`/`hgood` in characterEstimateData_of_family71_reduced_estimates)。
- signed-irreducible χ (exceptional character) の選択。
- (7.9) 𝓑-sum bound (`hBsum`)。
これらは Hypothesis76 (induced family {Ind_H^L θ} + (5.6)/(6.8) coherence) を要する char 解析。次 iteration
は Hypothesis76-from-Frobenius の wireability 調査 (S08 Sibley coherence が使えるか)。

## 2026-07-03 cont.⁷ (lane-a, /loop) — Hypothesis76 (7.6) は wireable と確定 (hypothesis76OfDade); 残 = instance detail

**発見**: `S09.Cert.hypothesis76OfDade` (S09_CertificateDischarge:859, lane-b carve-out 0090, downstream)
が **(7.7.a) `chiRho_decomp` 証明書を discharge 済**で Hypothesis76 を「no certificate assumed」で構成
(`H71` + `IsDadeIsometry` + `H≤L` + `hHnorm` + `A=H^#` から induced family {Ind_H^L θ} を内部 enumerate)。
S15 `H_sharp_hypothesis76` が同 constructor の使用例。⟹ **Hypothesis76-from-Frobenius も wiring で可能**。

**アーキテクチャ**: hypothesis76OfDade は S09_CertificateDischarge (NonexistenceCertain の**下流**) に
あるため、`FrobeniusFamily.hypothesis76` は**新 downstream leaf** に置く。card_G0 の最終 assembly も
下流で `not_trivial_G0_of_exists_Bsum_bound` 系 bypass (S09:6607, 「still-open card_G0_lower_bound を
迂回」) 経由が正道 (card_G0_lower_bound の sorry は displayed form のまま、spine consumer not_trivial_G0
を下流で honest 実証)。

**次 iteration の残**: `FrobeniusFamily.hypothesis76` を新 leaf で作る際、per-member の
`Invertible (Nat.card ↥(F.L i):ℂ)` instance が hypothesis76OfDade の search に通らない技術的 quirk
(letI/haveI/@ 全て試行、L-invertibility が見つからない) を解消する。`familyHypothesis71` では field 値
として同 instance が通った (fun i => invertibleOfNonzero ...) ので、その pattern を downstream constructor
に写すか、instance を def の `[...]` binder 化する。数学は完了、instance 解決のみ。

**次 iteration の instance fix 案** (cont.⁷ 補足): `familyHypothesis71` は `fintypeL`/`invertibleL` を
**field** として保持済。downstream の `FrobeniusFamily.hypothesis76` は fresh instance でなく
`(F.familyHypothesis71).fintypeL i` / `.invertibleL i` を `letI` で使えば、hypothesis76OfDade が期待する
instance と確実に一致する見込み (field 値は familyHypothesis71 で build 済ゆえ)。

## 2026-07-03 cont.⁸ (lane-a, /loop) — 🎯 (7.6) 層 landed; 構造 trunk 完全 wired (7.1/7.4/7.6)

**Landed** (`73a7cd7b`): `FrobeniusFamily.hypothesis76` (新 leaf `S09_FrobeniusHypothesis76`) — (7.6)
induced-family datum を certificate discharged で構成 (hypothesis76OfDade)。**instance quirk 解決**:
per-member `[Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i):ℂ)]` を **explicit binder** 化すれば
synthesis の coercion-form mismatch を回避。

**構造 trunk 完了**: (7.1) hypothesis71 + (7.4) familyHypothesis71 + (7.6) hypothesis76 全て
FrobeniusFamily から wired。**残 = (7.8.b)/(7.9) character estimate のみ** (genuine deep 部):
- (7.8.b) `chiRhoNormSq` 下界 `1-e/h ≤ ‖ζ^{νρ}‖²` + `‖Γ‖² ≤ e-1`。Hypothesis78/BetaDecomp/NormEstimates
  machinery が部分的に存在 (S09 の cont.⁶⁷〜、witness_L_zeta_bound 等) だが実 bound は open。
- (7.9) 2-family 非直交 (𝓑-sum bound)。
- assembly: `characterEstimateData_of_family71_reduced_estimates` に上記 bound + signed-irred χ を渡す →
  `not_trivial_G0_of_exists_Bsum_bound` bypass で spine 実証。
次 iteration は (7.8.b) chiRhoNormSq 下界の tractability 精査 (Hypothesis78 machinery が Frobenius family に
適用できるか)。これが 7.10 の実質的な最終 deep 部。

## 2026-07-03 cont.⁹ (lane-a, /loop) — (7.8.b) source orthogonalities 全 landed; 残 = coherence ν (deep gate)

**Landed** (`310448b4`): `induce_inner_induce_trivial` (`⟨Ind φ,Ind 1⟩=[G:H]·⟨φ,1⟩`) +
`induce_inner_induce_trivial_eq_zero_of_irreducible` (`⟨ζ,Ind1H⟩=0`, ζ irr≠1) + `restrict_induce_trivial`
(dedup)。**(7.8.b) `‖β‖²=e+1` の source 事実 (⟨Ind1H,Ind1H⟩=e / ⟨ζ,Ind1H⟩=0 / ⟨ζ,ζ⟩=1) 全て available**。

**残 deep gate = Frobenius induced-family の coherence ν**: `hypothesis78OfDade` は ν (+ isometry
hnu_isometry + agreement hagree) を**入力**に取る。NormEstimates も未構成 hypothesis。⟹ Hypothesis78 →
BetaDecomp → NormEstimates → chiRhoNormSq bound の chain は全て ν に gated。この ν = {Ind_H^L θ} の
(5.6)/(6.8) Sibley coherence が S07/S08 から wireable かが 7.10 完遂の鍵 (次 iteration の第一調査)。

**現状総括**: 7.10 の構造 trunk (7.1/7.4/7.6) + (7.8.b) source facts = wiring/elementary で landed。
残 = coherence ν + NormEstimates + (7.9) = genuine deep §5-8 char analysis (multi-week 級の可能性)。

## 2026-07-03 cont.¹⁰ (lane-a, /loop) — coherence ν = deep (5.6) gate 確定; tractable work 完了

**調査結論**: 7.10 の残 (7.8.b full NormEstimates / 7.9 / assembly) は**全て coherence ν に gated**。
`hypothesis78OfDade` は ν + `hnu_isometry` + `hagree` を入力に取り、ν が無ければ Hypothesis78 →
BetaDecomp → NormEstimates chain が始まらない。

**ν = Ind_L^G は不可** (検証済): TI-subgroup H の Mackey 公式は `g∉L` の double coset から
**degree-product 余剰項**を生む ⟹ Ind_L^G は induced character 上で等長でない。また induced family
{Ind_H^L θ} は degree 変動 (θ(1) 変動) ゆえ `coherentEqualDegree_fromDade` (S07、等次数専用) も不適。
⟹ **ν は genuine な Peterfalvi (5.6) coherence** (§5-6 Sibley、varying-degree) を要する = deep 部。

**7.10 の tractable work は完了** (この session で landing):
- 構造 trunk: `Hypothesis71.of_isTISubset` / `FrobeniusFamily.{hypothesis71, familyHypothesis71, hypothesis76}`
  + `dadeSupport_hypothesis71_eq_kernelSpread`。
- (7.8.b) source facts: `induce_{inner_trivial, trivial_inner_self, inner_induce_trivial}` +
  `⟨ζ,Ind1H⟩=0` corollary + `restrict_induce_trivial`。
**残 = coherence ν (deep (5.6)) → NormEstimates → chiRhoNormSq bound → (7.9) → assembly**。ν 以降は
既存 machinery (betaDecompOfDade / zetaNuRhoNormSq_ge_of_facts) が多く、ν が最大の単一 gate。

**推奨**: coherence ν の (5.6) 構成は独立した focused effort (multi-iteration/session 級)。次 iteration は
S07 coherentPair/coherentPairChain engine が {Ind_H^L θ} に適用可能かの精査から (適用可なら wireable、
不可なら (5.6) を Frobenius induced family 向けに実証する新規 deep work)。

## 2026-07-03 cont.¹¹ (lane-a, /loop) — 🎯🎯 coherence ν は WIREABLE (cont.¹⁰ 評価を revise)

**cont.¹⁰ の「ν = deep (5.6) from-scratch」評価は誤り**。`S08_CoherenceTheorems.sibleySetup_is_coherent`
(**sorry-free**) が `SibleyDadeHypothesis G L H` から `CoherenceTarget` = **`IsCoherent`** (= ν の実体) を
`S = {Ind_H^L θ | θ∈Irr H, θ≠1}` に対して生成する。しかも構造の docstring が明言: **Frobenius case (c1) の
SibleyDadeHypothesis producer は「§9 (7.10) application」= まさに本 issue** (「(4.6)-construction obligation を
SibleyDadeHypothesis producer に移した」)。

⟹ **ν は wiring で入手可能** (deep from-scratch でない):
1. `SibleyDadeHypothesis G (F.L i) ((F.H i).subgroupOf (F.L i))` を Frobenius case で構成
   (fields: W1/H_normal/split/W1_nontrivial ← `F.isFrobenius i`; H_nilpotent ← Thompson (Isaacs Ch6);
    card_L_odd ← G odd; H_sharp_ti ← `F.isTI`; dade/hconj/dade_H_eq_bot ← `of_isTISubset` (=hypothesis71 の dade);
    S/S_eq ← induced family; cases ← `Or.inl (F.isFrobenius i の IsFrobeniusGroup)`)。
2. `sibleySetup_is_coherent` → `IsCoherent`、`.extension` = ν。
3. `hnu_isometry` ← `IsCoherent.extension_inner_eq`、`hagree` ← `extends_on_supported` → `hypothesis78OfDade` へ。
4. その後 `betaDecompOfDade` + `zetaNuRhoNormSq_ge_of_facts` (既存) + 今 session の source facts で (7.8.b)、
   (7.9)、assembly。

**⟹ 7.10 全体が wiring/既存 machinery で finishable** (SibleyDadeHypothesis 構成 = 最大の残作業、~12 field
の substantial だが tractable constructor)。次 iteration: 新 leaf で `sibleyDadeHypothesis_of_frobenius` (c1)
の構成に着手 (H_nilpotent の Thompson + sharpImage 座標合わせが要点)。

## 2026-07-03 cont.¹² (lane-a, /loop) — Sibley wiring 着手: coordinate lemma landed

**Landed** (`0017e521`): 新 leaf `S09_FrobeniusSibley` + `sharpImage_subgroupOf_eq`
(`sharpImage ((H_i).subgroupOf L_i) = (H_i)^#`、`subgroupOf_map_subtype`+`inf_of_le_left`)。
SibleyDadeHypothesis の support 座標を `of_isTISubset`/hypothesis71 に揃える foundational lemma。

**確認**: `H_nilpotent` は `frobeniusKernelIsNilpotent` (BG Thm 3.7, S03c、solvable G 版) で入手可
(FT spine の L_i は minimal-simple の proper subgroup ゆえ solvable)。Isaacs Ch6 の一般 Thompson は
未着手だが solvable 版で足りる。

**残 = SibleyDadeHypothesis constructor (Frobenius c1) の ~13 field**:
W1/H_normal/split/W1_nontrivial ← `F.isFrobenius i`; H_nilpotent ← frobeniusKernelIsNilpotent (要 solvable 入力);
card_L_odd ← G odd; H_sharp_ti ← `F.isTI` + coordinate lemma; dade/hconj/dade_H_eq_bot ← of_isTISubset
(座標翻訳要); S/S_eq ← induced family; cases ← `Or.inl (F.isFrobenius i)`。次 iteration 継続。

## 2026-07-03 cont.¹³ (lane-a, /loop) — 🎯🎯🎯 sibleyDadeHypothesis_of_frobenius LANDED — coherence gate crossed

**Landed** (`368ff614`): `FrobeniusFamily.sibleyDadeHypothesis_of_frobenius` — SibleyDadeHypothesis
(case c1) を Frobenius member から全 field 構成 (full build green)。
- W1/H_normal/split/H_ne_bot/W1_nontrivial ← `IsFrobeniusGroup` (isNormal/isComplement/ne_bot_*)
- dade/hconj/dade_H_eq_bot ← `of_isTISubset` on sharpImage coord (`sharpImage_subgroupOf_eq` で各条件を FrobeniusFamily field へ)
- card_L_odd ← Lagrange; H_sharp_ti ← isTI+coord; S/S_eq ← induced family (rfl); cases ← Or.inl hFrob
- 入力: hnilp (kernel nilpotency、solvable L_i から frobeniusKernelIsNilpotent)、hodd、(C, hFrob)。

⟹ **`sibleySetup_is_coherent (sibleyDadeHypothesis_of_frobenius ...)` で coherence ν 入手可能**。
当初「multi-week deep」と恐れた coherence gate は **wiring で crossed**。

**残** (全て既存 machinery + wiring):
1. ν = `(sibleySetup_is_coherent ...).extension` を抽出、`hnu_isometry` ← `IsCoherent.extension_inner_eq`、
   `hagree` ← `extends_on_supported` → `hypothesis78OfDade` へ (座標: dade0 と CoherenceTarget の Dade map 一致確認)。
2. `betaDecompOfDade` + `zetaNuRhoNormSq_ge_of_facts` (既存) + source facts → (7.8.b) chiRhoNormSq bound。
3. (7.9) 𝓑-sum、assembly → `not_trivial_G0_of_exists_Bsum_bound` bypass。
次 iteration: ν 抽出 + hypothesis78OfDade 接続。

## 2026-07-03 cont.¹⁴ (lane-a, /loop) — sibleyHypothesis71 (H71') landed; 残 = hypothesis78OfDade 接続

**Landed** (`9c5feb74`): `sibleyHypothesis71` — sharpImage 座標の `Hypothesis71 G (sharpImage H) L`
(coherence の Dade map τ に一致する H71')。

**残の接続 chain (hypothesis78OfDade、~20 引数)**:
`hypothesis78OfDade (H71' := sibleyHypothesis71) (hτ) (H) (hHL) (hHnorm) (hAH) (θ) (hinj) (hcover)
(d) (psi_support) (hdeg) (ind1H) (hind1H) (hzeta_ind1H) (hdeg_match) (ν) (hnu_isometry) (hagree)`:
- θ/hinj/hcover ← `S08.distinctInducedFamily ((F.H i).subgroupOf L_i)` (hypothesis78OfDade 内部で使う既存 enumerator、S09_CertificateDischarge:872 参照)。
- ν ← `(F.coherence i ...).extension` (IntegralCharacterMap → hypothesis78OfDade の ν は `→ₗ[ℤ]`; `.toLinearMap` or coercion 要確認)。
- hnu_isometry ← `IsCoherent.extension_inner_eq` (induced family が zSpan S に入ることを確認)。
- hagree ← `IsCoherent.extends_on_supported` (ζ_i−d_iζ_0 が supported、τ₁=hyp.tau)。**要: sibleyHypothesis71.τ = coherence の hyp.tau** の一致確認 (両者 of_isTISubset(sharpImage H).dadeMap ゆえ defeq 見込み)。
- d/hdeg/ind1H 等 ← induced family の degree data。

**その後**: `betaDecompOfDade` + `zetaNuRhoNormSq_ge_of_facts` → (7.8.b) `chiRhoNormSq` bound →
`characterEstimateData_of_family71_reduced_estimates` (要 hi/hgood/hBsum) → `not_trivial_G0_of_exists_Bsum_bound`。
(7.9) 𝓑-sum は別途。次 iteration: ν 抽出 (型変換) + hypothesis78OfDade の引数を距離順に埋める。

## 2026-07-04 cont.¹⁵ (lane-a, /loop) — nu handle landed; hypothesis78OfDade 接続の完全 map (crux 判明)

**Landed** (`30540996`): `FrobeniusFamily.nu` = `coherence.extension`。`IntegralCharacterMap L G` は
`CF(L)→ₗ[ℤ]CF(G)` に unfold ゆえ hypothesis78OfDade の ν 型と直接一致 (変換不要)。

**接続 crux 判明 (hyp.tau vs H71'.τ)**: `SibleyDadeHypothesis.tau` は **def** = `dadeIntegralCharacterMap
hyp.dade hyp.hconj` (IntegralCharacterMap = →ₗ[ℤ]、CF(L) 全体)。対して `sibleyHypothesis71.τ` は
**bare DadeMap field** (supported 上のみ)。**型が違う**。coherence は `IsCoherent hyp.tau ...` ゆえ:
- `hagree` (H71'.τ(ζ_i−d_iζ_0) = ν(ζ_i)−d_iν(ζ_0)): ν linear + `coherence.extends_on_supported`
  (ν=hyp.tau on supported) + **`dadeIntegralCharacterMap_apply_of_support`** (S07:5342、hyp.tau=DadeMap
  値 on supported = H71'.τ 値) で bridge。ζ_i−d_iζ_0 supported は `induce_diff_support`。
- `hnu_isometry`: `coherence.extension_inner_eq (Ind θ_i) (Ind θ_j) (∈zSpan S) (∈zSpan S)` — Ind θ_i∈S
  (θ_i≠1) ← S_eq。zSpan S 所属は `Submodule.subset_span`。

**接続の残 monolithic assembly** (~20 args、1 focused effort):
`hypothesis78OfDade sibleyHypothesis71 (isDadeIsometry) (F.H i).subgroupOf... (kernel_le の subgroupOf 版)
(hHnorm) (hAH=coordinate) θ hinj hcover d psi_support hdeg ind1H hind1H hzeta_ind1H hdeg_match nu
hnu_isometry hagree`。θ/hinj/hcover/d/hdeg/ind1H = `distinctInducedFamily` (S09_CertificateDischarge:872
が hypothesis76OfDade 内部で使う enumerator) の公開 API 化 or 再構成が要 (これが最大の未知)。

**その後**: `betaDecompOfDade` + `zetaNuRhoNormSq_ge_of_facts` → chiRhoNormSq bound →
characterEstimateData → not_trivial_G0_of_exists_Bsum_bound。この monolithic 接続は fresh focused
session 向き (distinctInducedFamily API + degree data + 型 bridge を一括で組む)。全 intermediate は landed。

## 2026-07-04 cont.¹⁶ (lane-a, /loop) — ★ hypothesis78 COMPLETE: `Hypothesis78 G H_i^# L_i` 実証明・build green

**Landed** (`S09_FrobeniusHypothesis78.lean`, sorry-free, 4.7s leaf build): 各 Frobenius member `i` の
**Peterfalvi (7.8) 構造 `Hypothesis78 G (H_i^#) (L_i)`** を完全組み立て。cont.¹⁵ で「最大の未知・fresh
session 向き」とした monolithic 接続を **1 iteration で突破**。§14 `witness_L_hypothesis78` (5447-5531) が
逐語ブループリントだった。

**cont.¹⁵ の crux 解決** — 既存の §12→§7 bridge を発見・再利用 (再構成不要だった):
- **`Cert.coherence_hagree_dadeMap`** (S09_CertDischarge:2559): `IsCoherent` から `hagree` shape を直接
  産出。出力 = `(dade.fullDadeIsometryData hconj).toDadeIsometryData.toDadeMap ⟨ζ_i−d_iζ_0,_⟩ =
  ν ζ_i − d_i ν ζ_0`。
- **`Cert.coherence_extension_inner_eq_on_family`** (2586): `hnu_isometry` を `extension_inner_eq` から。
- **crux の正しい解**: `SibleyDadeHypothesis.tau` は `abbrev` = `dadeIntegralCharacterMap dade
  (dade.fullDadeIsometryData hconj)` (S08_CoherenceCorePart2:31)。ゆえ `F.coherence i` の型は
  `coherence_hagree_dadeMap` が要求する `IsCoherent (dadeIntegralCharacterMap dade (fullData hconj)) S
  (supportInSubgroup (sharpImage H) L)` と **完全一致**。H71' は §14 `toHypothesis71` 流に τ =
  `fullData.toDadeIsometryData.toDadeMap` で作る (`sibleyToHypothesis71`) → `coherence_hagree_dadeMap`
  が defeq で match (of_isTISubset.dadeMap 経由の bridge は不要だった)。
- **distinctInducedFamily は非公開のままで良い**: `Cert.exists_placed_induced_family` (generic、任意の
  distinguished `χdist` を index 0 に配置) を再利用。distinguished char = 非自明 linear char の induced
  (degree `[L_i:K_i]`)、`exists_sibley_distinguished_char` で構成 (K_i nilpotent 非自明 ⟹ 非 perfect ⟹
  `exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`)。

**新規 (S09_FrobeniusHypothesis78.lean)**:
- `sibleyToHypothesis71` — §14 流 H71' (τ = coherence Dade map、`coherence_hagree_dadeMap` と defeq)。
- `exists_sibley_distinguished_char` — 非自明 linear induced (degree [L:K])。
- `hypothesis78 (F)(i)(hodd)[inst](hnilp)(C)(hFrob) : Nonempty (Hypothesis78 G (sharpImage((H_i).subgroupOf L_i)) L_i)`
  — 完全 assembly (hAH=sharpImage_subgroupOf_eq, hHnorm=mem_kernel_conj_iff, placed family, d/hdeg/
  hdeg_match/psi_support, hnu_isometry, hagree)。

**次 (下流、cont.¹⁷ 予定)**: `Hypothesis78` を consume する (7.8.b) норм bound
`zetaNuRhoNormSq_ge_of_facts` + `betaDecompOfDade` → chiRhoNormSq bound →
`characterEstimateData_of_family71_reduced_estimates` → `not_trivial_G0_of_exists_Bsum_bound` (7.10)。
coherence gate は突破済、(7.8) 構造も landed。残るは (7.8.b)/(7.9) の norm 評価の per-member 適用と assembly。

## 2026-07-04 cont.¹⁷ (lane-a, /loop) — 残チェーン完全 map: (7.8.b) は `zetaNuRhoNormSqGeOfDade` で 4-fact に縮約

hypothesis78 landing 後、`card_G0_lower_bound` (6552、sole sorry@6560) までの残チェーンを精査:
```
card_G0_lower_bound  ← F.CharacterEstimateData
  ← characterEstimateData_of_family71_reduced_estimates (5809): P=F.familyHypothesis71, χ, i(min-h),
      B(𝓑-set), hi/hgood(P.chiRhoNormSq 下界), hBsum(7.9), hG0sum, hL/hA/hG0(coordinate)
    ← hi/hgood ← (7.8.b) `P.chiRhoNormSq χ j` 下界
      ← **`zetaNuRhoNormSqGeOfDade` (S09_CertDischarge:2347)** = bundled (7.8.b):
         `hypothesis78OfDade` の全引数 (=hypothesis78 で組済) + **追加 4 fact のみ**で
         `1 - e/h ≤ H78.zetaNuRhoNormSq` を産出 (係数 identity・betaDecomp・hGsum は内部処理)。
         追加 4 fact = hzeta0nu(⟨νζ_0,1_G⟩=0) / hζ0norm(‖ζ_0‖²=1) / a·ha / hsmall。
      + bridge `H78.zetaNuRhoNormSq = P.chiRhoNormSq χ_i` (7.8.b→7.5 glue)
```

**追加 4 fact の producer は全て存在** (§14 5747-5985 が完全テンプレ = 2nd zetaNuRhoNormSqGeOfDade 適用):
- hzeta0nu ← `coherence_extension_orthogonal_constOne` (2660) + ζ_0⊥ζ̄_0。
- hζ0norm ← `isIrreducibleCharacter_induce_of_frobeniusGroup` (InducedIrreducible:465、shared 済) →
  odd Frobenius で Ind θ_lin irreducible → norm 1。
- a·ha ← `exists_betaDecomp_a` (1668)。
- hsmall ← §14:5982 に構成テンプレ。

**次 iteration (cont.¹⁸) の第一手 = hoist**: `inner_induce_conj_eq_zero_of_frobenius_of_odd`
(現 S14:5652、S09 の下流ゆえ import 不可) は純 rep-theory (odd Frobenius: 非自明 induced ⊥ その共役) →
`OddOrder/GroupTheory/RepresentationTheory/` へ hoist (S14 は shared 版を import に切替)。その後
`FrobeniusFamily.zetaNuRhoNormSq_ge` を `zetaNuRhoNormSqGeOfDade` + 4-fact で構築、`chiRhoNormSq` へ bridge。
その後 (7.9) 𝓑-sum + min-index 選択 + `characterEstimateData_of_family71_reduced_estimates` で assembly。
**coherence gate + (7.8) 構造は landed**; 残りは (7.8.b) の per-member norm 評価適用 + (7.9) + final assembly。

## 2026-07-04 cont.¹⁸ (lane-a, /loop) — (7.8.b) の 4-fact のうち 2 つ landed: conj-orth + hzeta0nu

**Landed** (`S09_FrobeniusEstimate.lean`, sorry-free, 4.3s):
- `inner_induce_conj_eq_zero_of_frobenius_of_odd` — odd Frobenius で非自明 `⟨Ind θ, Ind θ̄⟩ = 0`
  (一般 rep-theory fact)。§14:5652 のローカル copy を移送 (issue 9007)。**共有 RepresentationTheory
  ホストは不可**と判明: `ClassFunction.induce_conj` が S08 定義 (S08 上流の shared から到達不可)。
  → lane-a leaf S09_FrobeniusEstimate に配置 (S08 の induce_conj に到達可、S09 名前空間)。
  真の共有化 = induce_conj chain を InducedCharacter へ relocate する別refactor (issue 9007 で defer)。
- `FrobeniusFamily.hzeta0nu` — **(7.8.a) `⟨ν ζ_0, 1_G⟩ = 0`**。§14 `witness_L_hzeta0nu` (5717-5807) を
  逐語 mirror (θ̄_0 opaque obtain で whnf 保護)。`coherence_extension_orthogonal_constOne` に
  hmem0/hmem0'/hnorm0/hnorm0'/horth(=conj-orth)/hsupp/h1_0/h1_0'/htau1/hτ_smul を供給。全 helper は
  S09 到達可 (`inner_self_induce_eq_one_of_frobeniusGroup`/`inner_induce_constOne_eq_zero`/
  `inner_tau_supported_constOne`/`dadeIntegralCharacterMap_smul_complex/_apply_of_support`)。

**`zetaNuRhoNormSqGeOfDade` 4-fact 進捗**: hzeta0nu ✅ / 残 = hζ0norm (‖ζ_0‖²=1、
`inner_self_induce_eq_one_of_frobeniusGroup` そのもの、ほぼ即) / a·ha (`exists_betaDecomp_a`、要 hdiffZ/hζ0nuZ
virtual char) / hsmall (`frobenius_two_mul_card_complement_add_one_le_card_kernel` §14:5817 が e≤(h-1)/2 を
供給、これも §14 ローカルゆえ hoist or 再証明要)。

**次 (cont.¹⁹)**: 残 3-fact (hζ0norm 即 / a·ha / hsmall) を揃え `FrobeniusFamily.zetaNuRhoNormSq_ge` を
`zetaNuRhoNormSqGeOfDade` で構築 → `H78.zetaNuRhoNormSq = P.chiRhoNormSq χ` bridge → hi/hgood。
hsmall の `frobenius_two_mul_card_complement_add_one_le_card_kernel` は "hoistable to Ch06" と §14 が明記、
Isaacs Ch06 へ hoist が筋 (issue 9007 と同様の shared 判断; ただし純群論ゆえ Ch06 が正所在)。

## 2026-07-04 cont.¹⁹ (lane-a, /loop) — ★ (7.8.b) COMPLETE: FrobeniusFamily.zetaNuRhoNormSq_ge 実証明

**Landed** (sorry-free、build green):
- `IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel` (**Isaacs Ch06 OddComplement**、
  commit 9f41b6f7): odd Frobenius で 2|A|+1 ≤ |N|。§14 ローカル copy ("hoistable to Ch06") を正所在へ hoist
  (純群論、card_kernel_modEq_one のみ依存)。hsmall の producer。
- `FrobeniusFamily.zetaNuRhoNormSq_ge` (**S09_FrobeniusEstimate.lean**): 各 member の **(7.8.b) 下界
  `1 − e_i/h_i ≤ H78.zetaNuRhoNormSq`**。`zetaNuRhoNormSqGeOfDade` に hypothesis78OfDade 全引数
  (hypothesis78 と同一、placed family/d/psi_support/hdeg/hnu_isometry/hagree) + 4-fact
  (hzeta0nu=F.hzeta0nu / hζ0norm=inner_self_induce_eq_one / a·ha=exists_betaDecomp_a / hsmall) を供給。
  §14 `witness_L_zeta_bound` を逐語 mirror。返り値 = `∃ H78, 1−e/h ≤ H78.zetaNuRhoNormSq`。

**修正 note**: (1) `H78.kernelOrder = Nat.card hyp76.H` ゆえ `set H78` 経由の hke は `show` で unfold
(rfl 不可)。(2) `set coh with hcoh` + `rw [← hcoh] at hz0` で F.hzeta0nu (literal F.coherence) を
coh に fold (ν=coh.extension と一致させる)。

**(7.10) 残チェーン**: `zetaNuRhoNormSq_ge` (per-member (7.8.b)) → **bridge
`H78.zetaNuRhoNormSq = P.chiRhoNormSq χ`** + `H78.complementIndex=e_i` / `kernelOrder=h_i`
(`characterEstimateData_of_family71_reduced_estimates` の hi/hgood 形へ) → (7.9) 𝓑-sum + min-index
選択 → `characterEstimateData_of_family71_reduced_estimates` → `card_G0_lower_bound`。
次 (cont.²⁰): chiRhoNormSq bridge (H78.zetaNuRhoNormSq と P.chiRhoNormSq χ_i の同一視; χ = ν ζ_0 = 
被評価 signed irreducible)。これが (7.8.b)→(7.5) glue の核。

## 2026-07-04 cont.²⁰ (lane-a, /loop) — (7.8.b)→(7.5) chiRhoCF bridge landed

**Landed** (S09_FrobeniusEstimate.lean、sorry-free):
- `chiRho_apply_of_trivial_local` (一般): TI Dade datum (local subgroup H(a)=⊥、`of_isTISubset`) では
  `χ^ρ(a) = χ(a)` on A (coset average が単項に collapse)。`chiRho` は τ でなく `H71.hyp` (support +
  local subgroups) のみに依存。
- `FrobeniusFamily.sibleyToHypothesis71_chiRhoCF_eq`: **`sibleyToHypothesis71 i` と `hypothesis71 i` の
  chiRhoCF が一致**。両者 `of_isTISubset` on 同一 TI subset H_i^# (support は `sharpImage_subgroupOf_eq`
  で一致、local subgroup ⊥)、ゆえ chiRho = χ|_{H_i^#} で同一。これで
  `H78.zetaNuRhoNormSq = ‖sibley.chiRhoCF (νζ_0)‖²` と `P.chiRhoNormSq (νζ_0) i = ‖hypothesis71.chiRhoCF (νζ_0)‖²`
  が同一視可能に (`P = F.familyHypothesis71`、`hyp71 = F.hypothesis71`)。

**残 (cont.²¹)**: `hi : 1 − e_i/h_i ≤ P.chiRhoNormSq χ i` を組む — (a) `zetaNuRhoNormSq_ge` +
`sibleyToHypothesis71_chiRhoCF_eq` で `H78.zetaNuRhoNormSq = P.chiRhoNormSq (νζ_0) i` (norm は両辺
`.re` で同じ instance)、(b) `H78.complementIndex = F.e i` / `H78.kernelOrder = F.h i` (F.e/F.h 定義と
complementIndex/kernelOrder = |L|/|H|, |H| の対応)。χ = coh.extension (Ind θ_0) = 被評価 signed irr。
その後 (7.9) 𝓑-sum + hgood (j≠i の good estimate) + min-index → characterEstimateData → card_G0_lower_bound。

## 2026-07-04 cont.²¹ (lane-a, /loop) — ★ hi 完成: exists_chiRhoNormSq_ge (family coordinate の (7.8.b) 下界)

**Landed** (S09_FrobeniusEstimate.lean、sorry-free):
- `zetaNuRhoNormSq_ge` を **refactor**: 返り値を `∃ H78, 1−e/h ≤ H78.zetaNuRhoNormSq` から
  **`∃ χ, ⟨χ,χ⟩=1 ∧ 1−e_i/h_i ≤ ⟨(F.hypothesis71 i).chiRhoCF χ, ·⟩.re`** へ変更。χ = νζ_0 =
  `coh.extension (Ind θ_0)` を露出、norm-1 (coherence isometry + inner_self_induce) も返す。bound は
  H78 が `set`-transparent な内部で `H78.zetaNuRho = sibley.chiRhoCF χ` を unfold →
  `sibleyToHypothesis71_chiRhoCF_eq` で hypothesis71 form へ bridge。**opaque H78 問題を回避** (∃ で
  obtain すると H78 が opaque で unfold 不可だった → 内部で bridge 済ませて form ごと返す)。
- `exists_chiRhoNormSq_ge`: **`∃ χ, ⟨χ,χ⟩=1 ∧ 1−e_i/h_i ≤ (F.familyHypothesis71).chiRhoNormSq χ i`** —
  `characterEstimateData_of_family71_reduced_estimates` の **hi/hχ 直接入力形**。証明は
  `letI := familyHypothesis71.fintypeL/invertibleL` で instance を pin → zetaNuRhoNormSq_ge の inner
  form が chiRhoNormSq と **defeq** (両者 F.fintypeL instance、chiRhoCF は bridge 済) → そのまま返す。

**instance 対処の要**: `chiRhoNormSq` は内部 `letI := F.fintypeL i` (=Fintype.ofFinite)、
`zetaNuRhoNormSq_ge` は ambient `[Fintype ↥L_i]` binder。呼出時に `letI := familyHypothesis71.fintypeL i`
で ambient を pin すれば両 inner が同一 instance → defeq。

**残 (cont.²²+)**: card_G0_lower_bound (7.10) の `CharacterEstimateData` 完成に:
- **hgood** (j≠i, j∉B: `(h_j−1)/(e_j h_j) ≤ P.chiRhoNormSq χ j`) — 同一 χ の j≠i での ρ-projection 下界。
  hi と別ソース (7.3-type weak bound、`|A_j|/|L_j| ≤ ‖χ^{ρ_j}‖²`)。
- **hBsum** (7.9 𝓑-sum: `∑_{j∈B}(h_j−1)/e_j ≤ e_i−1`) — 組合せ。
- **min-index i** 選択 + **hG0sum** (χ signed irr ⟹ `one_le_G0_norm_sum_of_signed_irreducible`)。
- これら + exists_chiRhoNormSq_ge の χ を `characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible`
  へ。χ = νζ_0 ∈ ZIrr かつ norm-1 ⟹ signed irr (5.9.a)。

## 2026-07-04 cont.²² (lane-a, /loop) — hgood core: chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero

**Landed** (S09_FrobeniusEstimate.lean、sorry-free、H78-level 一般 lemma):
- `chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero`: χ ∈ Irr G が S^ν に直交 (`hχ_orth`) かつ (β,χ)≠0
  (`hbeta_ne`、χ は (7.8.a) β の constituent) ならば **`|A|/|L| ≤ ‖χ^ρ‖²`**。証明 = (7.8.c.ii)
  `chiRho_norm_sq_eq_card_ratio_mul` (‖χ^ρ‖² = (|A|/|L|)·(β,χ)·(β,χ)‾) + (β,χ)∈ℤ
  (`inner_mem_ZIrr_int`、β∈ZIrr via `beta_mem_ZIrr_of_sourceDiff_mem_ZIrr`、χ∈Irr) ⟹ |(β,χ)|²≥1 ⟹
  (|A|/|L|)·m² ≥ |A|/|L| (ratio≥0)。**hgood の数学的核**を honest に isolate。

これで hgood = `(h_j−1)/(e_j h_j) ≤ P.chiRhoNormSq χ j` は (a) `card_kernel_sharp_div_card_L_eq_h_sub_one_div_e_mul_h`
(ratio = (h−1)/(eh)) + (b) 本 lemma (ratio ≤ ‖χ^ρ‖²) に帰着。残る caller 責務 = **χ=νζ_0 が member j
(≠i) で S^ν_j ⊥ かつ (β_j,χ)≠0** の cross-member coherence 事実 (これが (7.10) の深部)。

**残チェーン**: hgood の cross-member 事実 (χ⊥S^ν_j + β_j constituent) → hgood 完成 → (7.9) 𝓑-sum →
min-index + hG0sum (signed irr) → `characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible`
→ card_G0_lower_bound。cont.²³ は cross-member orthogonality/constituent の調査 (textbook 7.9-7.10 + coq PF7)。

## 2026-07-04 cont.²³ (lane-a, /loop) — ★ 再スコープ: (7.9) machinery は完成済 (sorry-free)、残 (7.10) は wiring

**発見**: coq PFsection7 で (7.9)/(7.10) 構造を精査 → Lean 側に **(7.9) machinery が既に完全形式化・
sorry-free** (S09_NonexistenceCertain:3770-4260) と判明。これで hgood の「深い cross-member 事実」は
**新規証明でなく既存 infra の wiring** に再スコープ。

**既存 (7.9) infra (sorry-free)**:
- `Hypothesis79` (2-member setup、`first`/`second : Hypothesis78` + `dadeSupport_disjoint`)。
- `conclusion H79 = (β₁,ζ₂^ν)≠0 ∨ (β₂,ζ₁^ν)≠0` (dichotomy = Peterfalvi (7.9))。
- `zetaImage_cross_eq_zero_of_support_subset` / `beta_inner_beta_eq_zero` (disjoint support ⟹ cross ⊥)。
- `conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity` 等 (coherence+parity から dichotomy 産出、
  = coq `Dade_sub_lin_nonorthogonal`)。
- `sum_weights_le_of_orthogonal_integer_decomposition` / `sum_rat_weights_le` ((7.10) sum bound の核)。

**coq 対応 (PFsection7)**: `disjoint_coherent_ortho` (= hχ_orth: ζ_i^ν ⊥ S^ν_j)、
`Dade_sub_lin_nonorthogonal` (= (7.9) dichotomy → hbeta_ne)、`odd_Frobenius_index_ler`
(= 既 hoist 済 Ch06 two_mul_card_complement_add_one_le_card_kernel)。

**残 (7.10) = wiring チェーン** (深い新規数学ではない):
1. **per-member concrete Hypothesis78** (現 `F.hypothesis78` は Nonempty → data 化: def 化 or .some)。
2. **`F.hypothesis79 i j`** (pair setup) = 2 member の Hypothesis78 + `dadeSupport_disjoint`
   (= `dadeSupport_hypothesis71_eq_kernelSpread` + `kernelSpread_disjoint`、既存)。
3. (7.9) `conclusion_of_...parity` で pair ごと dichotomy。
4. **𝓑-set** B = {j≠i | (β_i,ζ_j^ν)≠0}; j∉B は dichotomy で (β_j,ζ_i^ν)≠0 = hbeta_ne。
5. **hgood** = cont.²² core (`chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero`) + 一般 cross-ortho
   (ζ_i^ν ⊥ ν_j(S_j)、要 (4.1) orthonormal-diff、`zetaImage_cross_...` は distinguished のみゆえ一般化要) +
   hbeta_ne。**hi** = cont.²¹ done。
6. **hBsum** (7.9 sum) + **min-index** (Finset.min) + **hG0sum** (signed irr、`one_le_G0_norm_sum_of_signed_irreducible`) →
   `characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible` → `lowerBoundTerm_of_characterEstimateData` →
   card_G0_lower_bound。

**cont.²⁴**: hypothesis78 を data 化 → `F.hypothesis79 i j` 構築 (最上流 wiring)。一般 cross-ortho
(`disjoint_coherent_ortho` 相当) が唯一の未形式化 piece の可能性 — 要確認。

## 2026-07-04 cont.²⁶ (lane-a, /loop) — (7.9) conclusion 適用の scope 精査: 深部 = 2 つの §1 primitive

**Landed** (S09_FrobeniusHypothesis79.lean): `hypothesis78_nu_eq` — `(F.hypothesis78 i).nu =
(F.coherence i).extension` (rfl、(7.9) の hnu 入力)。

**精査結果 — (7.9) `conclusion` producer の未充足入力**: `conclusion_of_..._parity` (4094) は
hcoh/hnu/hindZ/hzeta_irr/hBD/**hzeta_cross**/**hdelta_even** を要求。うち **hzeta_cross と hdelta_even は
全 producer で仮説のまま (既存コードで一度も discharge されていない)**。両者の Lean analog は無し:
- **hzeta_cross** (`⟨ν_iζ_i, ν_jζ_j⟩ = 0`): support-subset route (`zetaImage_cross_eq_zero_of_support_subset`)
  は **不適用** — ν_iζ_i は irreducible character (ZIrr, norm-1) で Dade support に載らない。coq は
  `orthonormal_vchar_diff_ortho` (§1 (4.1)) 経由 (`disjoint_coherent_ortho`): {νχ,νχ̄}/{ν'χ',ν'χ'̄} が
  orthonormal かつ差が直交 (Dade image で disjoint support) ⟹ families 直交。**Lean に primitive 無し**
  (`IsometryDifferencePair.lean` = §3 (1.4) core は関連するが未 wiring)。
- **hdelta_even** (`⟨δ_i,δ_j⟩ = even ℤ`): coq `cfdot_real_vchar_even` (§7:509、real virtual char で
  ⟨D,1⟩=1 ⟹ ⟨D₁,D₂⟩ even)。**Lean に無し**。

**残 = 深部 §1 formalization** (multi-iteration): (1) orthonormal-diff cross-ortho primitive →
hzeta_cross、(2) real-vchar parity → hdelta_even、(3) BetaDecomp 構成 (betaDecompOfDade/Facts wiring)、
(4) zetaDistinct irr / ind1H ZIrr 入力 (F.hypothesis78 の pf.θ internals 露出要)、(5) 𝓑-set 構成、
(6) min-index + hG0sum + assembly。**cont.²⁷ = cross-ortho primitive (orthonormal_vchar_diff_ortho 相当)
の formalization に着手** (gateway、genuine deep work)。

**進捗総括 (cont.¹⁶–²⁶)**: (7.8) 層完全 + hi + hgood core + (7.9) two-family datum は landed・merged。
残は Peterfalvi の genuine 難所 (§1 (4.1)/parity primitives) — easy wiring は概ね尽き、深部 formalization
フェーズへ移行。

## 2026-07-04 cont.²⁸ (集中掘り, ユーザー "一気に掘る" 指示) — ★ parity primitive cfdot_real_vchar_even 完成

**Landed** (S09_ParityPrimitive.lean、190行、sorry-free、commit ebee613b): (7.9) の深部 §1 primitive
`cfdot_real_vchar_even` (real vchar φ,ψ over odd G で ⟨φ,ψ⟩ ≡ ⟨φ,1⟩⟨ψ,1⟩ mod 2) を完全形式化。
構成: inner_conj_right → inner_conjPerm_eq_of_real → sum_conjPerm_invariant_sub_trivial_even
(ZMod2 + Finset.sum_involution) → cross-Parseval → cfdot_real_vchar_even。**hdelta_even の producer 完成**。

**cross-ortho primitive の数学解明 (次の §1 piece、着手準備完了)**:
coq `orthonormal_vchar_diff_ortho` = 「orthonormal ±irr pair {a,b},{c,d} が **同次数** (a(1)=b(1),
c(1)=d(1); coq `Dade1`: Dade image 差は 1 で消える) かつ差直交 ⟨a-b,c-d⟩=0 ⟹ ⟨a,c⟩=0」。
**同次数条件が必須** (無いと μ=ν,μ'=ν',符号相殺の反例あり; 同次数で ε=ε'・μ(1)=μ'(1) が pin され反例消滅)。
証明 = exists_zsmul_irreducibleCharacter (a=εμ 等) + 4-char ±irr case analysis (既存
`inner_constOne_eq_zero_of_orthonormal_pair` @S09_CertDischarge:2606 と同パターン、~80-100行)。
μ=ν 仮定 → hdiff 展開 (εδ[μ=ν]-εδ'[μ=ν']-ε'δ[μ'=ν]+ε'δ'[μ'=ν']=0) + 両次数条件 → δ=δ' かつ δ=-δ' 矛盾。

**残 (7.10 endpoint)**: cross-ortho primitive → hzeta_cross (Frobenius: a=ν_iζ_i, b=ν_iζ̄_i,
差=τ_i(ζ_i-ζ̄_i) Dade image, disjoint support で ⟨a-b,c-d⟩=0) → (7.9) conclusion 適用 (hcoh/hnu/hindZ/
hzeta_irr/hBD も要) → 𝓑-set → min-index/hG0sum → characterEstimateData → card_G0_lower_bound。

## 2026-07-04 cont.²⁹ (集中掘り続行) — ★ 両 §1 primitive + hzeta_cross bridge 完成

**Landed (3 commit, all sorry-free)**:
1. `orthonormal_vchar_diff_ortho` (S09_CrossOrthogonality.lean, 120行, commit 5069691a) —
   cross-ortho primitive。coq `orthonormal_vchar_diff_ortho` (PFsection4)。a=ε·μ 展開 +
   同次数⟹同符号 (`sign_eq_of_mul_pos_cast` via `irreducibleCharacter_apply_one_eq_pos_natCast`) +
   μ=ν 矛盾。**両次数条件必須** (符号相殺反例)。
2. `zetaImage_cross_eq_zero_of_conjugate_images` (S09_FrobeniusCrossOrtho.lean, commit 8cb8ed2f) —
   Hypothesis79-level bridge。coq `disjoint_coherent_ortho` (PFsection7)。共役像 b=ζ̄₁^ν, d=ζ̄₂^ν を
   与え、差 ζ_i^ν−ζ̄_i^ν が disjoint dadeSupport に supported ⟹ ⟨a−b,c−d⟩=0
   (`inner_eq_zero_of_disjoint_support`、beta_inner_beta_eq_zero と同型) + 1∉dadeSupport で vanish
   (`one_notMem_dadeSupport`) ⟹ orthonormal_vchar_diff_ortho 適用。
   (parity primitive `cfdot_real_vchar_even` は前 session commit ebee613b で完成済)。

**残 = Frobenius 共役 discharge (次の大 sub-project、enabling lemma 全同定済)**:
bridge の仮説 (b=ζ̄₁^ν, d=ζ̄₂^ν の hbZ/hbn/hab/hab_supp) を F.hypothesis78 から供給する。
- **enabling lemmas (全存在確認済)**: `conj_induce` (CliffordDecomposition:363、(induce K θ).conj =
  induce K θ.conj) → 誘導族の共役閉性; `IsIrreducibleCharacter.conj` (BrauerPermutation:136);
  `not_isReal_of_ne_trivial_of_odd_card'` (BrauerPermutation:233、Pf 1.1 奇位数非実、ζ≠ζ̄ を保証);
  `coherence_hagree_dadeMap` (S09_CertDischarge:2559、ν(ζ−dζ₀)=τ(ζ−dζ₀)); `nu_isometry` (H78 field);
  placedInducedFamily の `cover`/`inj` (共役指標の族内 index を供給)。
- **設計の急所**: `F.hypothesis78 i` は **opaque** (`choose`+`let pf := placedInducedFamily` で構成、
  返り値 Hypothesis78 は不透明)。hyp76.zeta = `fun j => induce K (pf.θ j)` だが**外から露出していない**。
  → discharge には (F.hypothesis78 i).hyp76 の族を placedInducedFamily に結びつける **projection 補題**
  (`(F.hypothesis78 i ...).hyp76.zeta = fun j => induce K (θ j)` 等) が必要。hypothesis78 の
  リファクタ (族を data で露出) or 等式補題群の追加。ここが次 session の主タスク。
- **decomposition (次 session)**: (a) hypothesis78 の hyp76 族露出 (projection lemma or 構成 refactor);
  (b) 共役 index 補題 `∃ j ≠ ind1H, zeta j = (zeta zetaDistinct).conj` (conj_induce+cover);
  (c) ζ≠ζ̄ (not_isReal odd) → nu_isometry で hbn/hab; (d) hab_supp = coherence_hagree_dadeMap で
  ν(ζ)−ν(ζ̄)=τ(ζ−ζ̄) supported; (e) bridge 適用で hzeta_cross。
- その後: (7.9) conclusion 適用 (hcoh/hnu/hindZ/hzeta_irr/hBD/hdelta_even も要) → 𝓑-set →
  min-index/hG0sum → characterEstimateData → card_G0_lower_bound (endpoint sorry
  @S09_NonexistenceCertain:6552)。

## 2026-07-04 cont.³⁰ (Frobenius discharge scoping — construction-ready) — 全 API 確認済

深部 scoping 完了。opaque `let pf` (hypothesis78 内) が唯一の真の障害と特定。最クリーン分解:
**中間 bridge `zetaImage_cross_eq_zero_of_conjIndex`** で refactor を「共役 index の供給」だけに隔離。

### 次 iteration = 純構築 (再調査不要、全 API 下記で確認済)

**Unit B1 (S09_FrobeniusCrossOrtho.lean 追記)**: `Hypothesis79.zetaImage_cross_eq_zero_of_conjIndex`
共役 **index** j₁,j₂ を仮説に取り、nu_isometry で orthonormality を導出して既存 bridge
`zetaImage_cross_eq_zero_of_conjugate_images` に流す。仮説:
- coherence: `(hcoh₁ : IsCoherent τ₁ H79.first.sourceSet A'₁) (hnu₁ : H79.first.nu = hcoh₁.extension)` ×2
- `(hz₁irr : IsIrreducibleCharacter (H79.first.hyp76.zeta H79.first.zetaDistinct))` ×2
- 共役 index: `(j₁ : Fin (H79.first.hyp76.n+1)) (hj₁ne_ind : j₁ ≠ H79.first.ind1H)`
  `(hj₁ne_dist : j₁ ≠ H79.first.zetaDistinct)`
  `(hj₁ : H79.first.hyp76.zeta j₁ = (H79.first.hyp76.zeta H79.first.zetaDistinct).conj)` ×2
- Dade agreement 差 support (Hyp78 は agreement を carry せぬため仮説): `(hab_supp : (H79.firstZetaImage
  - H79.first.nu (H79.first.hyp76.zeta j₁)).support ⊆ H79.first.hyp76.hyp71.hyp.dadeSupport)` ×2
- 導出: b := H79.first.nu (zeta j₁); `haZ/hcZ` = `nu_zetaDistinct_mem_ZIrr_of_isCoherent`;
  `hbZ/hdZ` = `nu_zeta_mem_ZIrr_of_isCoherent hcoh₁ hnu₁ hj₁ne_ind`;
  `han` = nu_isometry zetaDistinct zetaDistinct + `hz₁irr.inner_self_eq_one`;
  `hbn` = nu_isometry j₁ j₁ + (zeta j₁ = ζ.conj, `(hz₁irr.conj).inner_self_eq_one` 経由、conj norm=1);
  `hab` = nu_isometry zetaDistinct j₁ = ⟨ζ, ζ.conj⟩ = 0 (distinct irr; ζ irr + ζ.conj irr + ζ≠ζ.conj
  ← hj₁ne_dist+injectivity or bundle IrreducibleCharacter で `irreducibleCharacter_inner`)。
  → `exact H79.zetaImage_cross_eq_zero_of_conjugate_images haZ hbZ hcZ hdZ han hbn hcn hdn hab hcd
  hab_supp hcd_supp`。

**Unit B2 (Frobenius refactor, S09_FrobeniusHypothesis78.lean)**: opaque 解消。
- `let pf := placedInducedFamily ...` と `choose χ ...` を **named def** に抽出
  (`F.sibleyDistinguishedChar i`, `F.sibleyPlacedFamily i`)、`hypothesis78` を書き換え (green 維持)。
- projection: `(F.hypothesis78 i ...).hyp76.zeta = fun j => induce K ((F.sibleyPlacedFamily i).θ j)`
  (hypothesis78OfDade→hypothesis76OfFamily の `zeta := ζ` は `set`、rfl 見込み; 要 build 確認)。
- 共役 index: `conj_induce` ((induce K θ).conj = induce K θ.conj) + `pf.cover` +
  `pf.inj` で j₁ を構成 (∃j', zeta j' = ζ.conj; j'≠ind1H ← ζ.conj≠triv, j'≠0=zetaDistinct ← ζ≠ζ.conj
  ← `not_isReal_of_ne_trivial_of_odd_card'`、L odd ← `Subgroup.card_subgroup_dvd_card`+`Odd.of_dvd`)。
- hab_supp: `coherence_hagree_dadeMap` で ν(ζ)−ν(ζ.conj)=τ(ζ−ζ.conj)、`map_eq_zero_of_not_mem_dadeSupport`
  で support ⊆ dadeSupport。

**確認済 API**: nu_zeta_mem_ZIrr_of_isCoherent (S09_Nonexistence:2120), IsIrreducibleCharacter.
inner_self_eq_one (CharacterProduct:195), IsIrreducibleCharacter.conj (BrauerPerm:136),
not_isReal_of_ne_trivial_of_odd_card' (BrauerPerm:233), conj_induce (CliffordDecomp:363),
coherence_hagree_dadeMap (S09_CertDischarge:2559), zeta_mem_sourceSet (1580), one_notMem_dadeSupport
(S04:397), Subgroup.card_subgroup_dvd_card, hypothesis78OfDade zetaDistinct:=0 (S09_CertDischarge:1641)。

**cont.³⁰ 修正 (Unit B1 signature)**: `Hypothesis76` は zeta injectivity を carry せぬ →
hab の ζ≠ζ.conj は `j₁≠zetaDistinct` から導けない。よって `hj₁ne_dist` を捨て、直接
`(hζ₁neconj : H79.first.hyp76.zeta H79.first.zetaDistinct ≠ (H79.first.hyp76.zeta
H79.first.zetaDistinct).conj)` を仮説化 (Frobenius 側 Unit B2 で not_isReal_of_ne_trivial_of_odd_card'
により discharge)。⟨ζ,ζ.conj⟩=0 は ζ,ζ.conj を `IrreducibleCharacter` に bundle (⟨ζ,hz₁irr⟩) して
`irreducibleCharacter_inner` (=if χ=ψ then 1 else 0) + hζ₁neconj (bundle 等号は ClassFunction 等号に
帰着) で。次 turn 冒頭で IrreducibleCharacter の bundling/coe API を 1 回 grep してから純構築。

## 2026-07-04 cont.³¹ — ★ Unit B1 (conjIndex bridge) 完成、残 = Unit B2 (Frobenius refactor)

**Landed** (S09_FrobeniusCrossOrtho.lean, commit c12aeeab, sorry-free, 1.0s):
`Hypothesis79.zetaImage_cross_eq_zero_of_conjIndex` — 共役 **index** j₁,j₂ (+coherence+irr+
ζ≠ζ.conj+hab_supp) から hzeta_cross を導出。orthonormality は nu_isometry field で、distinct-irr
直交は top-level helper `inner_eq_zero_of_ne_of_isIrreducible` で。**perf 教訓**: distinct-irr helper を
local `have` (∀+instance binder) にすると大 context で isDefEq heartbeat 爆発 (800k でも timeout) →
top-level private lemma 抽出で 1.0s (maxHeartbeats 不要)。[[lean-local-have-instance-blowup]]。

**残 = Unit B2 (Frobenius refactor)** — opaque `let pf` 解消して conjIndex bridge の残仮説
(j₁, hj₁, hζ₁ne_conj, hab_supp) を `F.hypothesis78 i` から供給:
- (a) `S09_FrobeniusHypothesis78.lean` の `hypothesis78` 内 `choose χ...`/`let pf := placedInducedFamily`
  を named def (`F.sibleyDistinguishedChar i`, `F.sibleyPlacedFamily i`) に抽出、`hypothesis78` 書換
  (green 維持)。projection `(F.hypothesis78 i).hyp76.zeta = fun j => induce K (θ j)` (rfl 見込み)。
- (b) 共役 index: `conj_induce` + `pf.cover` で ∃ j₁, zeta j₁ = ζ.conj。hj₁ne_ind (j₁≠ind1H ←
  ζ.conj≠Ind1 ← ζ≠triv), hζ₁ne_conj (ζ≠ζ.conj ← `not_isReal_of_ne_trivial_of_odd_card'`, L odd ←
  `Subgroup.card_subgroup_dvd_card`+Odd.of_dvd)。
- (c) hab_supp: `coherence_hagree_dadeMap` で ν(ζ)−ν(ζ.conj)=τ(ζ−ζ.conj)、`map_eq_zero_of_not_mem_
  dadeSupport` で support ⊆ dadeSupport。
- (d) conjIndex bridge 適用で F レベル hzeta_cross → (7.9) conclusion → 𝓑-set → characterEstimateData
  → card_G0_lower_bound。

## 2026-07-04 cont.³² — ★ hypothesis78 de-opaque 完了 (Unit B2 の linchpin)

**Landed** (S09_FrobeniusHypothesis78.lean, commit 671c2995, full build green 3915 jobs):
- `sibleyPlacedFamily i` : `hypothesis78` 内部の induced family を named def で露出 (χdist =
  `Classical.choose (exists_sibley...)`、内部 `let pf` と proof-irrelevance で defeq)。
- `hypothesis78` を `let pf := F.sibleyPlacedFamily i ...` 使用に refactor (behavior-preserving)
  → `(F.hypothesis78 i).hyp76.n` が **syntactically** `(F.sibleyPlacedFamily i).n` に (dependent Fin
  index の一致に必須)。
- `hypothesis78_hyp76_zeta_eq : (F.hypothesis78 i).hyp76.zeta = fun j => induce K (pf.θ j)` **rfl で成立**。

これで opaque 障害が消え、`sibleyPlacedFamily.cover/.inj` + `conj_induce` で共役 index が構成可能に。

**残 = 共役 index 構成 + hab_supp (次 iteration、全 API 済)**:
- **共役 index** `∃ j₁, zeta j₁ = (zeta 0).conj` (zetaDistinct=0): (zeta 0).conj = (induce K (θ 0)).conj
  = induce K ((θ 0).conj) [`conj_induce`]、`pf.cover ((θ 0).conj)` で ∃ j₁, induce K (θ j₁) =
  induce K ((θ 0).conj)。projection で zeta j₁ に translate。
- **hj₁ne_ind** (j₁≠ind1H): zeta j₁ = (zeta 0).conj ≠ zeta ind1H = induce K triv ⟸ (θ 0).conj ≠ triv
  ⟸ θ 0 ≠ triv (← `pf.inj` + ind1H≠0 + θ ind1H = triv)。
- **hζ₁ne_conj** (zeta 0 ≠ (zeta 0).conj): zeta 0 = induce K (θ 0) は L の非自明既約 (degree [L:K]>1)、
  L odd (`Subgroup.card_subgroup_dvd_card`+`Odd.of_dvd`) → `not_isReal_of_ne_trivial_of_odd_card'`
  (bundle IrreducibleCharacter)。
- **hab_supp**: `coherence_hagree_dadeMap` で ν(zeta 0)−ν(zeta j₁) = τ(zeta 0 − zeta j₁) (equal degree:
  conj は degree 保存、supported ⟸ zeta 0 − zeta j₁ が A-supported)、`map_eq_zero_of_not_mem_dadeSupport`
  で support ⊆ dadeSupport。
- 適用: `zetaImage_cross_eq_zero_of_conjIndex` → F レベル hzeta_cross → (7.9) conclusion → ... →
  card_G0_lower_bound。

## 2026-07-04 cont.³³ — ★ 共役 index 構成 完了 (exists_conjIndex_hypothesis78)

**Landed** (S09_FrobeniusConjIndex.lean, commit, sorry-free 1.0s):
`exists_conjIndex_hypothesis78` — `∃ j₁ ≠ ind1H, zeta j₁ = (zeta zetaDistinct).conj`。
sibleyPlacedFamily.cover + conj_induce + conjPerm で j₁ 構成、j₁≠ind1H は zeta 単射
(sibleyPlacedFamily.inj + projection) + ζ_ind1H=Ind 1_K が実 で。dependent Fin index は型 ascription
で defeq 強制。**技法**: j₁≠ind1H は raw `pf.inj` でなく zeta 実値上の単射で (raw inj は非θ項で whnf loop)。

**残 = Unit B2 最終ストレッチ (非実性 + hab_supp + assembly)**:
1. **hz₁irr** (ζ=Ind K θ_lin 既約): `isIrreducibleCharacter_induce_of_frobeniusGroup`
   (InducedIrreducible:459) を θ 0 に適用 (Frobenius kernel からの誘導は既約)。
2. **hζ₁ne_conj** (ζ≠ζ.conj): hz₁irr + ζ≠triv(degree [L:K]>1) + L odd
   (`Subgroup.card_subgroup_dvd_card`+Odd.of_dvd) → `not_isReal_of_ne_trivial_of_odd_card'` (bundle)。
3. **hab_supp** ((ζ^ν−ζ̄^ν).support ⊆ dadeSupport): nu 線形 → nu(ζ−ζ̄); `coherence_hagree_dadeMap`
   で = τ(ζ−ζ̄) (equal degree: conj は degree 保存 → ζ−ζ̄ が A-supported); `map_eq_zero_of_not_mem_
   dadeSupport` で support ⊆ dadeSupport。※ hnu (nu=coh.extension) は hypothesis78_nu_eq。
4. **assembly**: `F.hypothesis79 i j hij ...` に `zetaImage_cross_eq_zero_of_conjIndex` 適用
   (両族 i,j の 1-3 を供給) → F レベル hzeta_cross → (7.9) conclusion producer → hgood → 𝓑-set →
   characterEstimateData → card_G0_lower_bound (endpoint sorry @S09_NonexistenceCertain:6552)。

## 2026-07-04 cont.³⁴ — ★ 既約性+非実性 完了、残 hab_supp + assembly

**Landed** (S09_FrobeniusConjIndex.lean, sorry-free): `hypothesis78_zeta_irreducible` (ζ_0=Ind K θ_0 が
Frobenius kernel 誘導で既約), `hypothesis78_zeta_ne_conj` (ζ≠ζ̄: 奇位数 L の非自明既約 [degree
[L:K]>1, kernel proper via ne_bot_complement+isComplement.disjoint] → not_isReal (1.1))。
`exists_conjIndex_hypothesis78` と合わせ conjIndex bridge の hz_irr/hζne_conj/j₁/hj₁ne_ind/hj₁ 済。

**残 = hab_supp (最大の残ピース) + assembly**:
- **hab_supp**: `(ν(ζ_zd) − ν(ζ_j₁)).support ⊆ dadeSupport` (H79.first level, ζ_j₁=(ζ_zd).conj)。
  - `coherence_hagree_dadeMap` (S09_CertDischarge:2559): `toDadeMap ⟨ζi−di•ζ0, hsupp⟩ =
    coh.extension ζi − di•coh.extension ζ0`。di=1 (equal degree), ζi=ζ_zd, ζ0=ζ_j₁。
    → ν(ζ_zd)−ν(ζ_j₁) = toDadeMap ⟨ζ_zd−ζ_j₁, _⟩ (Dade image)。
  - support ⊆ dadeSupport: `IsDadeMap.map_eq_zero_of_not_mem_dadeSupport` (S04:3425)。
  - **要 plumbing**: (a) F.coherence i の IsCoherent が coherence_hagree_dadeMap の要求形
    `IsCoherent (dadeIntegralCharacterMap hyp (fullDadeIsometryData hconj)) S (supportInSubgroup A L)`
    に一致することの確認 (F.coherence の定義 = sibleySetup_is_coherent、S09_FrobeniusSibley:125)。
    hnu (nu=coh.extension) = `hypothesis78_nu_eq` (S09_FrobeniusHypothesis79:94、= rfl)。
    (b) ζ_zd, ζ_j₁ ∈ sourceSet (= S \ {Ind 1_H})。ζ_zd: zetaDistinct_mem_sourceSet。ζ_j₁: j₁≠ind1H →
    zeta_mem_sourceSet。(c) **equal-degree A-support**: (ζ_zd − ζ_j₁).support ⊆ supportInSubgroup A L。
    ζ_j₁=(ζ_zd).conj は同次数 (conj は degree 保存) → 差は 1 で消える; さらに両者 H 上 supported
    (induced from H) → 差 H\{1}=A supported。※ conj の induce/H-support は conj_induce +
    zeta_eq_zero_of_not_mem_H。
- **assembly**: `F.hypothesis79 i j hij hodd ...` に `zetaImage_cross_eq_zero_of_conjIndex` 適用
  (両族 i,j に hcoh/hnu/hz_irr/j/hjne_ind/hj/hζne_conj/hab_supp 供給) → F レベル hzeta_cross。
  hcoh は F.coherence i の再パッケージ、hij で i≠j。→ (7.9) conclusion producer (別途 hindZ/hBD 等) →
  hgood → 𝓑-set → characterEstimateData → card_G0_lower_bound。

## 2026-07-04 cont.³⁵ — ★ ζ−ζ̄ A-support 完了 (hypothesis78_zeta_sub_conj_support)

**Landed** (S09_FrobeniusConjIndex.lean, sorry-free): `hypothesis78_zeta_sub_conj_support` —
`(ζ_zd − ζ_j₁).support ⊆ supportInSubgroup (sharpImage K) L` (equal-degree; conj は H外消失+degree
[L:K]実で 1消失; `S04.mem_sharp` で H^# membership)。

**残 = hab_supp の coherence connection + assembly**:
- **hab_supp 本体**: `(ν(ζ_zd)−ν(ζ_j₁)).support ⊆ dadeSupport`。
  - hnu: `hypothesis78_nu_eq` (h78.nu = F.coherence.extension、rfl)。
  - S membership: ζ_zd, ζ_j₁ ∈ F.coherence の S (= sibleyDade.S)。hypothesis78 内 `hSmem` パターン
    (S09_FrobeniusHypothesis78:171 `hSmem j hj : induce K (θ j) ∈ sibleyDade.S` for j≠ind1H) を
    Frobenius-level に露出 or 再証明。ζ_zd: zetaDistinct(=0)≠ind1H。ζ_j₁: j₁≠ind1H (exists_conjIndex より)。
  - `coherence_hagree_dadeMap (sibleyDade.dade) (.hconj) (F.coherence) (S-mem ζ_zd) (S-mem ζ_j₁)
    (m0:=1)(mi:=1)(by norm_num)(di=1)(A-support)` → `toDadeMap ⟨ζ_zd − ζ_j₁, _⟩ = ν(ζ_zd) − 1•ν(ζ_j₁)`。
  - `IsDadeMap.map_eq_zero_of_not_mem_dadeSupport` で toDadeMap image の support ⊆ dadeSupport。
  - ※ h78.hyp76.hyp71.hyp = sibleyDade.dade (sibleyToHypothesis71.hyp より) → dadeSupport 一致。
    toDadeMap = (dade.fullDadeIsometryData hconj).toDadeMap; その isDadeMap は fullDadeIsometryData
    から。1•ν = ν (one_smul)。
- **assembly**: `zetaImage_cross_eq_zero_of_conjIndex` を `F.hypothesis79 i j hij ...` に適用、両族に
  hcoh(=F.coherence 再パッケージ)/hnu/hz_irr/j/hjne_ind/hj/hζne_conj/hab_supp 供給 → hzeta_cross →
  (7.9) conclusion → card_G0_lower_bound。

## 2026-07-04 cont.³⁶ — ★ hab_supp 完了 (全 conjIndex-bridge input 完備)

**Landed** (S09_FrobeniusConjIndex.lean, sorry-free): `hypothesis78_nu_zeta_sub_conj_support` (hab_supp)
— ν(ζ)−ν(ζ̄) = τ(ζ−ζ̄) (coherence_hagree_dadeMap, di=1, S-membership via inj) → Dade image が
dadeSupport 外で消失 (fullDadeIsometryData.toDadeIsometryData.isDadeMap.map_eq_zero_of_not_mem_dadeSupport)。
これで conjIndex bridge の全 input (hz_irr / j₁/hj₁ne_ind/hj₁ / hζne_conj / hab_supp) が Frobenius
レベルで揃った。

**残 = 最終 assembly (sourceSet↔S 接続 + bridge 適用)**:
- **sourceSet = sibleyDade.S** (sub-lemma): sourceSet = {ζ_i | i≠ind1H} = {induce K θ_i | θ_i≠triv};
  sibleyDade.S = {induce K φ | φ≠triv}。⊆: θ_i≠triv (i≠ind1H)。⊇: cover で induce K φ = induce K θ_j、
  φ≠triv → induce K φ≠induce K triv=ζ_ind1H → j≠ind1H (inj) → ∈sourceSet。
- **F.coherence を sourceSet に transport**: `IsCoherent τ S A` + (S = sourceSet) → `IsCoherent τ
  sourceSet A` (Eq.mpr/▸)。※ IsCoherent (S07_Coherence:1659) の S 依存を確認。τ = sibleyDade.tau =
  dadeIntegralCharacterMap (bridge の要求 τ と一致、hypothesis78 discharge で確認済)。A_prime =
  supportInSubgroup (sharpImage H) L。
- **hnu** (H79.first.nu = hcoh.extension): hypothesis78_nu_eq (H79.first = F.hypothesis78 i)。
- **bridge 適用**: `H79 := F.hypothesis79 i j hij hodd ...`; `zetaImage_cross_eq_zero_of_conjIndex H79
  hcoh₁ hnu₁ hcoh₂ hnu₂ (hz_irr i) (hz_irr j) hj₁ne_ind hj₁ hζne_conj_i ... (hab_supp i) (hab_supp j)`
  → `⟨H79.firstZetaImage, H79.secondZetaImage⟩ = 0` = F レベル hzeta_cross。
- → (7.9) conclusion producer (別途 hindZ/hzeta_irr/hBD 供給) → hgood → 𝓑-set →
  characterEstimateData → card_G0_lower_bound (endpoint sorry @S09_NonexistenceCertain:6552)。

## 2026-07-04 cont.³⁷ — ✅★ Frobenius hzeta_cross 完成 (両 §1 primitive + cross-ortho 完結)

**Landed** (commit 2b967fa6, full build green 3916 jobs AxiomsCheck OK):
`hypothesis79_zetaImage_cross_eq_zero` — `⟨ζ_i^{ν_i}, ζ_j^{ν_j}⟩ = 0` (i≠j Frobenius member)。
`zetaImage_cross_eq_zero_of_conjIndex` に本 session の全 Frobenius-level input を供給して組み上げ:
hypothesis78_isCoherent_sourceSet + hypothesis78_nu_eq / hypothesis78_zeta_irreducible /
exists_conjIndex_hypothesis78 / hypothesis78_zeta_ne_conj / hypothesis78_nu_zeta_sub_conj_support。

**本 session で構築した hzeta_cross chain 全体** (全 sorry-free):
parity primitive (cfdot_real_vchar_even) → cross-ortho primitive (orthonormal_vchar_diff_ortho) →
hzeta_cross bridge (zetaImage_cross_eq_zero_of_conjugate_images) → conjIndex bridge
(zetaImage_cross_eq_zero_of_conjIndex) → hypothesis78 de-opaque (sibleyPlacedFamily +
hypothesis78_hyp76_zeta_eq refactor) → 共役 index / 既約性 / 非実性 / A-support / hab_supp →
sourceSet=S / coherence transport → **Frobenius hzeta_cross**。

**残 = (7.9) conclusion 適用 + (7.10) assembly (次フェーズ)**:
- (7.9) `conclusion` producer に hzeta_cross + (hindZ/hzeta_irr/hBD/hdelta_even) を供給
  → `⟨β_i, ζ_j^ν⟩≠0 ∨ ⟨β_j, ζ_i^ν⟩≠0`。hdelta_even は cfdot_real_vchar_even 経由 (parity primitive、
  producer 済 @S09_NonexistenceCertain)。
- → hgood (chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero) → 𝓑-set → min-index/hG0sum →
  characterEstimateData_of_family71_reduced_estimates_of_signed_irreducible → card_G0_lower_bound
  (endpoint sorry @S09_NonexistenceCertain:6552)。

## 2026-07-04 cont.³⁸ — 次フェーズ: (7.10) CharacterEstimateData assembly のスコープ

hzeta_cross 完成 (cont.³⁷) で **深部 §1 frontier は完結**。残る endpoint sorry
(@S09_NonexistenceCertain:6552, `hdata : F.CharacterEstimateData`) は (7.10) 定量 assembly:

- **BetaDecomp (hBD)**: `betaDecompOfDade` (S09_CertDischarge:2216) が
  `(hypothesis78OfDade ARGS).BetaDecomp` を供給。ARGS = θ/ν/hagree/hnu_isometry/hzeta0nu/hζ0norm/a/ha
  (hypothesis78 内部と同じ) → **sibleyPlacedFamily で re-thread** (hzeta_cross と同種の opacity plumbing;
  hzeta0nu は本 session 前半で完成済 @S09_FrobeniusEstimate、a は exists_betaDecomp_a、hagree は
  coherence_hagree_dadeMap、hnu_isometry は coherence_extension_inner_eq_on_family)。
- **(7.9) conclusion (Frobenius)**: `conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity`
  に hcoh/hnu (済) + hindZ (zeta ind1H = Ind 1_K ∈ ZIrr、character) + hzeta_irr (済
  hypothesis78_zeta_irreducible) + hBD + **hzeta_cross (済 hypothesis79_zetaImage_cross_eq_zero)** +
  hdelta_even (parity primitive cfdot_real_vchar_even + delta_orth_one @2822 → ⟨δ_i,δ_j⟩ even) 供給
  → H79.conclusion (⟨β_i,ζ_j^ν⟩≠0 ∨ ⟨β_j,ζ_i^ν⟩≠0)。
- **hgood**: `chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero` (S09_FrobeniusEstimate:124) に (7.9)
  conclusion の非零を供給 → good-index norm bound。**hi** = exists_chiRhoNormSq_ge (S09_FrobeniusEstimate:488、済)。
- **CharacterEstimateData**: hi/hgood/hBsum/hG0sum/min-index を束ねる (F.CharacterEstimateData 構造;
  lowerBoundTerm_of_characterEstimateData で card_G0_lower_bound へ)。𝓑-set の min-index 選択が残の主眼。

次 iteration: BetaDecomp re-thread (betaDecompOfDade を F.hypothesis78 に適用) から着手。

## 2026-07-04 cont.³⁹ — BetaDecomp 構築の精密プラン (betaDecompOfFacts)

**BetaDecomp は `betaDecompOfFacts` (S09_CertDischarge:2150) が clean 構築** — `(H78 : Hypothesis78)
+ 11 facts → H78.BetaDecomp` (OfDade re-thread 不要、任意 H78 に適用可 → F.hypothesis78 i に直接)。
11 facts の Frobenius-level 供給:
- **済/容易**: hzd (rfl), hz0 (zeta 0 (1)=index≠0), hP_real (degree 実 = star_natCast),
  hzeta0nu (F.hzeta0nu @FrobeniusEstimate:170), hζ0norm (hypothesis78_zeta_irreducible.inner_self_eq_one),
  hagree (coherence_hagree_dadeMap、FrobeniusEstimate:396 パターン), a/ha (exists_betaDecomp_a @418、
  hindZ = `ClassFunction.induce_mem_ZIrr` @420)。
- **要新規証明**: horth (∀i≠j ⟨ζ_i,ζ_j⟩=0、誘導既約の直交; i or j=ind1H 含む — Ind 1_K vs Ind θ),
  hN (∀i ⟨ζ_i,ζ_i⟩≠0; i=ind1H は Ind 1_K norm=軌道数≠0 via card_mul_inner_self_induce),
  hzeta_orth_one (∀i≠ind1H ⟨ζ_i,1_L⟩=0、Frobenius 相反 ⟨Ind θ,1_L⟩=⟨θ,1_K⟩=0 for θ≠triv),
  hβ1 (⟨β,1_G⟩=1、(7.8.a); FrobeniusEstimate/hBD 系に既存の可能性 — 要確認)。
- **注意**: F.hypothesis78 i の defeq (proof-irrelevance) — betaDecompOfFacts は H78 引数なので
  F.hypothesis78 i を直接渡せる (OfDade re-thread 不要)。ζ = hyp76.zeta を projection で induce K θ に。

**その後**: BetaDecomp → (7.9) conclusion (hzeta_cross 済 + hdelta_even[parity] + hindZ) → hgood
(chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero) → CharacterEstimateData (hi 済 exists_chiRhoNormSq_ge +
hgood + hBsum + hG0sum + 𝓑-set min-index) → card_G0_lower_bound。

次 iteration: betaDecompOfFacts を F.hypothesis78 i に適用、11 facts を供給 (新規 4 facts を証明)。

## 2026-07-04 cont.⁴⁰ — BetaDecomp construction-ready (全 abstract lemma 同定)

`betaDecompOfDade` (S09_CertDischarge:2309-2315) が `betaDecompOfFacts H78 rfl <11 facts>` で構築する
パターンを **F.hypothesis78 i に mirror** すれば良い。11 facts の abstract lemma (全確認済):
- horth = `induce_family_orthogonal_of_injective K θ hinj` (S09_CertDischarge:403)
- hN = `induce_norm_ne_zero K (θ j)` (:350)
- hP_real = `induce_apply_one_star K (θ i)` (:376)
- hzeta_orth_one = `inner_induce_constOne_eq_zero K (θ i) (θ_i≠triv)` (:930)
- hβ1: `H78.beta_def` → `inner_tau_supported_constOne` (:974) → `inner_sub_left` →
  `inner_induce_trivialChar_constOne_eq_one` (:944) + `inner_induce_constOne_eq_zero` (θ_0≠triv) → 1−0
  (betaDecompOfDade:2305-2308 と同一)
- hagree = `coherence_hagree_dadeMap` (FrobeniusEstimate:396 パターン; d-matching は betaDecompOfDade
  hdeq:2274 と同型)
- hzeta0nu = `F.hzeta0nu i ... (θ 0) hθ0_ne` (FrobeniusEstimate:446)
- hζ0norm = `(hypothesis78_zeta_irreducible i ...).inner_self_eq_one`
- a/ha = `exists_betaDecomp_a H78 hindZ hζ0nuZ` (hindZ = `induce_mem_ZIrr`, FrobeniusEstimate:418-422)
- hzd = rfl, hz0 = `induce_apply_one_ne_zero`

**要 projection bridge**: 各 fact は `(F.hypothesis78 i).hyp76.zeta a` を `hypothesis78_hyp76_zeta_eq`
(congrFun) で `induce K (sibleyPlacedFamily.θ a)` に rw してから abstract lemma 適用。~70-80 行。

**注**: betaDecompOfFacts は H78 引数を直接取る → F.hypothesis78 i をそのまま渡せ、OfDade defeq 不要。
d-matching (H78.hyp76.d vs induced degree) だけ betaDecompOfDade hdeq パターンで橋渡し。

次 iteration: この construction を書いて build。その後 (7.9) conclusion (hBD 完成で全 input 揃う)。

## 2026-07-04 cont.⁴¹ — ✅★ BetaDecomp (7.8.a) 完成 — (7.9) conclusion 全 input 揃う

**Landed** (S09_FrobeniusConjIndex.lean, commit, full build green 3916 jobs):
`hypothesis78_betaDecomp` — `(F.hypothesis78 i).BetaDecomp` を `betaDecompOfFacts` で構築、11 facts を
誘導族 ζ_j=Ind_K θ_j (projection) から discharge。hagree d-matching (H78.hyp76.d j = deg_j/deg_0、
zeta_one_eq_d_mul + induce_apply_one で index 相殺、linear_combination) が最難関だったが完了。
※ **技法**: `0 : Fin (h78.n+1)` と `0 : Fin (pf.n+1)` の defeq-but-syntactic mismatch は index annotation
で解決 ([[lean-instance-defeq-traps]] 系)。

**(7.9) conclusion (Frobenius) の全 input が揃った**:
- hcoh/hnu = hypothesis78_isCoherent_sourceSet + hypothesis78_nu_eq ✅
- hindZ = ClassFunction.induce_mem_ZIrr ✅ (BetaDecomp で使用済)
- hzeta_irr = hypothesis78_zeta_irreducible ✅
- **hBD = hypothesis78_betaDecomp ✅ (今回)**
- **hzeta_cross = hypothesis79_zetaImage_cross_eq_zero ✅ (cont.³⁷)**
- 残 hdelta_even = ∃z, ⟨δ_i,δ_j⟩=z ∧ Even z: parity primitive cfdot_real_vchar_even + delta_orth_one
  (@S09_NonexistenceCertain:2822, ⟨δ,1⟩=0) → ⟨δ_i,δ_j⟩ ≡ ⟨δ_i,1⟩⟨δ_j,1⟩ = 0 mod 2 → even。
  ※ δ_i real vchar (要確認: delta ∈ ZIrr + cfReal)。

次 iteration: hdelta_even 構築 → (7.9) conclusion producer 適用 (Frobenius H79) → hgood → 𝓑-set →
CharacterEstimateData → card_G0_lower_bound。

## 2026-07-04 cont.⁴² — 残 hdelta_even の要 = delta-reality (Dade-conj 両立)

(7.9) conclusion producer `conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity`
(@S09_NonexistenceCertain:4094) の全 input 中、**hdelta_even のみ未** (他は済: hcoh/hnu/hindZ[induce_mem_ZIrr]/
hzeta_irr/hBD/hzeta_cross)。

**hdelta_even = ∃z, ⟨δ_i,δ_j⟩=z ∧ Even z**:
- parity primitive `cfdot_real_vchar_even` (S09_ParityPrimitive) を δ_i,δ_j に適用 → m,a,b with
  ⟨δ_i,δ_j⟩=m, ⟨δ_i,1⟩=a, ⟨δ_j,1⟩=b, Even(m−a·b)。`delta_orth_one` (@2822, ⟨δ,1⟩=0) で a=b=0 →
  Even m。⟨m, hm, Even m⟩。
- **要件**: δ_i,δ_j ∈ ZIrr (済 delta_mem_ZIrr) **+ δ real (cfReal/IsReal)** ← これが未証明の deep piece。
- **delta-reality**: δ = β − 1_G + ν(ζ)。real ⟺ (β + ν(ζ)) real (1_G real)。coq `Dade_sub_lin_nonorthogonal`
  の `cfReal D` 証明 (PFsection7:625-640) = `cfConjC_Dade_coherent` (Dade map が coherent set 上で共役両立)
  + `conj_cfInd` (Ind が共役両立) + `Dade_conjC` + `nu_tau`。Lean 側の対応:
  - Ind-conj: `conj_induce` (済、使用中)。
  - τ-conj / Dade_conjC: S04 の dadeMap 共役両立 (要探索; S07_Coherence:1234 `tau1_agrees` 系や
    S04 dadeMap 性質)。
  - 共役拡張 ν(ζ).conj = ν(ζ̄): coherent extension の共役両立 (S07_Coherence:1137 `nu_eq_mu_conj` 系)。
  → **delta_isReal を Frobenius level で構築** (hab_supp と同程度の深さの sub-lemma)。

**その後**: hdelta_even → (7.9) conclusion → hgood (chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero) →
CharacterEstimateData (hi[exists_chiRhoNormSq_ge]/hgood/hBsum/hG0sum/𝓑-set min-index) →
card_G0_lower_bound (@6552)。

**本 session 実績**: 深部 §1 frontier (hzeta_cross 全 chain) + (7.8.a) BetaDecomp 完成 (~22 sorry-free
commits)。残りは delta-reality → hdelta_even → (7.9) conclusion → 定量 assembly。

## 2026-07-04 cont.⁴³ — delta-reality の clean reduction (τ/ν conj-compat + agreement)

**delta = β − 1_G + ν(ζ) の reality を clean に reduce**:
`delta.conj − delta = (β.conj − β) + (ν(ζ).conj − ν(ζ))`。
- **(A) τ-conj-compat** (τ(φ).conj = τ(φ.conj)) 前提で: β = τ(Ind1_K − ζ) → β.conj = τ(Ind1_K − ζ̄)
  → β.conj − β = τ((Ind1_K−ζ̄)−(Ind1_K−ζ)) = τ(ζ − ζ̄)。
- **(B) ν-conj-compat** (ν(φ).conj = ν(φ.conj)) 前提で: ν(ζ).conj = ν(ζ̄) →
  ν(ζ).conj − ν(ζ) = ν(ζ̄ − ζ) = −ν(ζ − ζ̄)。
- **(C) coherence agreement** (ν(ζ−ζ̄) = τ(ζ−ζ̄)、既有 coherence_hagree, ζ−ζ̄ は A-supported):
  → delta.conj − delta = τ(ζ−ζ̄) − ν(ζ−ζ̄) = 0。**delta real**。

**残 = (A) τ-conj-compat + (B) ν-conj-compat** (両方 未 in Lean; coq `Dade_conjC` +
coherent-extension conj-compat)。深い sub-lemma:
- (A) Dade map の複素共役両立: S04 dadeMap 定義 (mobius/α_B) レベル。`Hypothesis.dadeMap` の conj 挙動。
- (B) coherent extension の共役両立: S07 hcoh.extension の conj。誘導族 conj-closed (sourceSet=S、
  conj_induce) を利用できる可能性。

これらが揃えば delta_isReal → cfdot_real_vchar_even (parity, 済) + delta_orth_one → hdelta_even →
(7.9) conclusion (他 input 全済) → hgood → CharacterEstimateData → card_G0_lower_bound。

**本 session 実績 (深部完了)**: hzeta_cross 全 chain (深部 §1 frontier) + BetaDecomp (7.8.a)、
~22 sorry-free commits, full build green。残りは delta-reality (τ/ν conj-compat) + 定量 assembly。

## 2026-07-04 cont.⁴⁴ — ★ (A) dadeMap_conj 完成、残 (B) ν-conj-compat が deep

**Landed** (S09_FrobeniusConjIndex.lean, commit, sorry-free): `dadeMap_conj` — Dade map の複素共役両立
`τ(φ.conj) = (τ φ).conj` (IsDadeMap の map_eq_of_isConj_hCoset + map_eq_zero から直接、reusable、
coq `Dade_conjC`)。delta-reality reduction の **(A)** 完成。

**残 = (B) ν-conj-compat** (`ν(ζ).conj = ν(ζ̄)`): agreement + dadeMap_conj からは **導けない** (検証済:
両辺 anti-real だが等号は強制されない; τ(ζ−ζ̄) = ν(ζ)−ν(ζ).conj が (B) と同値で循環)。
→ **retarget/coherent-extension の共役構造が必要** (coq `cfConjC_Dade_coherent`; S07_RetargetScaled の
`conjImage = X − τ(χ−χ.conj)` が χ.conj の像だが `X̄ = X.conj` は retarget で明示されておらず、構築レベルで
確立が必要)。deep sub-project (S07 extension 構築レベル)。

**その後**: (A)+(B)+agreement → delta_isReal → cfdot_real_vchar_even (parity, 済) + delta_orth_one →
hdelta_even → (7.9) conclusion (他全 input 済) → hgood → CharacterEstimateData → card_G0_lower_bound。

**本 session 実績 (深部)**: hzeta_cross 全 chain + BetaDecomp (7.8.a) + dadeMap_conj (A)、
~23 sorry-free commits, full build green。残 = (B) ν-conj-compat (retarget 共役) + 定量 assembly。

---

## cont.⁴⁵ — (B) ν-conj-compat DONE (cont.⁴⁴ の "deep sub-project" 判定は誤り) + delta-reality 完全特定

**cont.⁴⁴ の (B) 評価を訂正**: 「(B) は retarget 共役構造を要する deep sub-project (S07 extension
構築レベル)」は **誤り**。(B) は **`IsCoherent.extension_mapRingEquiv_comm` (Peterfalvi (5.9)(a)) を
σ = complex conjugation で適用するだけ**の tractable な application だった。教訓: 「anti-real 両辺が
等号強制されない」= 追加構造が要る、は正しいが、その構造は**既に `extension_mapRingEquiv_comm` として
存在**していた (retarget を新規構築する必要は無い)。[[feedback-dont-mislabel-formalization-as-research]]。

**commit `a f726ec93`**: `coherence_extension_conj` (S09_FrobeniusConjIndex, sorry-free, leaf-green):
`(ν χ).conj = ν χ.conj` for χ ∈ Sibley S。証明 = `extension_mapRingEquiv_comm` at `Complex.conjAe`、
`Hypothesis.SHC_extension_conj` (S12:1209) を template に。5 つの Sibley input は全て既存:
- S ⊆ Irr L: `SibleyDadeHypothesis.isIrreducibleCharacter_of_mem_S_of_frobenius` (hyp.W1 = C rfl)
- S conj-closed (hSu): `S_closedUnderConjugate` + bridge `X.conj = mapRingEquiv conjAe X`
- vanish-at-1 support (hspan): `zSpan_S_support_subset_of_apply_one_eq_zero` (ちょうど A' を返す)
- extension ∈ ZIrr (hlat): `IsCoherent.extension_mem_ZIrr`
- |S| ≥ 2 (h2): caller 供給 (ζ̄ ∈ S, ≠ ζ)

**delta-reality (`delta_isReal`) 完全特定** — 全 tool 所在確認済、betaDecomp に pattern 確立済:
`delta = beta − constOne + nu(ζ)`, `beta = hyp76.hyp71.τ ⟨ζ_ind1H − ζ_dist⟩`。
**重要**: `Hypothesis71.τ : S04.DadeMap` (S09_Nonex:115) ゆえ (A) `dadeMap_conj` が beta.conj に**直接**適用
(IntegralCharacterMap 層を経由不要)。calc:
- `delta.conj = beta.conj − constOne + (nu ζ).conj` (conj 加法的, constOne real)
- `beta.conj = τ⟨(ζ_ind1H − ζ_dist).conj⟩ = τ⟨ζ_ind1H − ζ̄⟩` ← (A) dadeMap_conj + ζ_ind1H real (Ind 1_H)
- `(nu ζ).conj = nu ζ̄` ← (B) coherence_extension_conj via `hypothesis78_nu_eq`
- `τ⟨ζ_ind1H − ζ̄⟩ − τ⟨ζ_ind1H − ζ⟩ = τ⟨ζ − ζ̄⟩` ← DadeMap 線形性
- `τ⟨ζ − ζ̄⟩ = nu ζ − nu ζ̄` ← agreement `coherence_hagree_dadeMap` (ζi=ζ, ζ0=ζ̄=conjIndex, di=1
  ∵ 等次数) — betaDecomp:494-529 に pattern
- ⟹ `delta.conj − delta = τ⟨ζ−ζ̄⟩ + (nu ζ̄ − nu ζ) = (nu ζ − nu ζ̄) + (nu ζ̄ − nu ζ) = 0` ∴ delta real
残作業 = multi-wrapper 型 plumbing (DadeMap ↔ fullDadeIsometryData.toDadeMap defeq, conjIndex の
ζ̄ = zeta(conjIndex) 同定) — deep math でなく betaDecomp と同種の配管。

**その後**: delta_isReal (両 family) + delta_orth_one → `cfdot_real_vchar_even hodd hδZ hδR hδZ' hδR'`
(S09_ParityPrimitive:144, a=b=⟨δ,1⟩=0 ゆえ Even m) → hdelta_even → (7.9) `conclusion_of_ind_mem_ZIrr_
of_zeta_irreducible_of_isCoherent_parity` (S09_Nonex:4094, 他 input 全済) → hgood → **CharacterEstimateData
の Bsum_le field** (5 field bundle: i/hmin/B/B_avoids_min/Bsum_le/base_estimate; S09_Nonex:5560) → hdata →
`card_G0_lower_bound` (6561 の sorry)。定量 assembly (min-index 選択 + 𝓑-set + base_estimate via (7.5))
は別 strand で残る。

---

## cont.⁴⁶ — generic delta_isReal DONE (commit); hbeta_conj_sub 完全 mapped (全 bridge 所在確認)

**commit (delta_isReal)**: generic `Hypothesis78.delta_isReal` (S09_FrobeniusConjIndex, sorry-free)。
`hbeta_conj_sub : β̄−β = νζ−νζ̄` と `hnu_conj : (νζ)‾=ν(ζ̄)` から純代数で `Δ=β−1_G+νζ` real:
`Δ̄−Δ = (β̄−β)+((νζ)‾−νζ) = (νζ−νζ̄)+(νζ̄−νζ) = 0` (conj_add/conj_sub + abel、1_G real は drop)。
delta-reality の代数核を wrapper-plumbing から分離。2 input は Frobenius caller 供給。

**残 = Frobenius `hbeta_conj_sub` (`β̄−β = νζ_dist − νζ_dist.conj`) — 全 bridge 所在確認済、~80 行 multi-defeq**:
route (additivity 要ゆえ dadeIntegralCharacterMap LinearMap 経由):
- `beta = dadeIntegralCharacterMap hyp dade (ζ_ind−ζ_dist)` — bridge:
  `sibleyToHypothesis71.τ = (fullDadeIsometryData hconj).toDadeIsometryData.toDadeMap`
  `= hyp.dadeMap` (**`Hypothesis.dadeIsometryData_toDadeMap` S04:4124** + toDadeIsometryData defeq S04:4317)
  `= dadeIntegralCharacterMap hyp dade ·` (**`dadeIntegralCharacterMap_apply_of_support`** S07)
- `beta.conj = dadeIntegralCharacterMap hyp dade (ζ_ind−ζ̄)` — **`dadeIntegralCharacterMap_mapRingEquiv_comm`**
  (S07_CoherenceGalois:51) at conjAe + ζ_ind real (`induce_apply_one_star` / Ind 1_H real) + bridge
  `X.conj = mapRingEquiv conjAe X`
- `β̄−β = dadeIntegralCharacterMap hyp dade ((ζ_ind−ζ̄)−(ζ_ind−ζ_dist)) = ·(ζ_dist−ζ̄)` — **`LinearMap.map_sub`**
- `·(ζ_dist−ζ̄) = νζ_dist − νζ_dist.conj` — **`coherence_hagree_dadeMap`** (ζi=ζ_dist, ζ0=ζ̄, di=1 ∵ 等次数;
  ζ_dist,ζ̄∈S ✓ ∵ `exists_conjIndex_hypothesis78`+`S_closedUnderConjugate`) + `hypothesis78_nu_eq` +
  support `hypothesis78_zeta_sub_conj_support` (S09_FrobeniusConjIndex:224)
注意: ζ_ind∉S ゆえ agreement を ζ_ind に直接使えない → additivity で ζ_dist−ζ̄ (両∈S) に畳む route が必須。

**その後**: hbeta_conj_sub + hnu_conj ((B) via nu_eq) → delta_isReal (両 family) + delta_orth_one →
`cfdot_real_vchar_even` → hdelta_even → (7.9) conclusion → hgood → CharacterEstimateData.Bsum_le →
hdata → card_G0_lower_bound。定量 assembly (min-index/𝓑-set/base_estimate via (7.5)) は別 strand。

---

## cont.⁴⁷ — delta-reality COMPLETE (Frobenius Δ real, sorry-free) ✅

**delta-reality sub-project 完了** (cont.⁴⁴ で「deep blocker」と flag した strand が全て解けた)。全 sorry-free commit:
1. (A) `dadeMap_conj` — Dade map が共役と可換 (S09_FrobeniusConjIndex)
2. (B) `coherence_extension_conj` — coherent extension が共役と可換 (`extension_mapRingEquiv_comm` at conjAe)
3. generic `Hypothesis78.delta_isReal` — `hnu_conj`+`hbeta_conj_sub` から純代数で Δ real
4. `hypothesis78_beta_conj_sub` — `β̄−β = νζ−νζ̄` (dadeIntegralCharacterMap LinearMap 経由の
   additivity-fold + mapRingEquiv_comm + coherence_hagree_dadeMap di=1; wrapper 全 defeq 確認)
5. `hypothesis78_delta_isReal` — Frobenius Δ real (3+4 を wire; (B) を nu_eq で hnu_conj に橋渡し)

**残 = hdelta_even assembly + 定量 CharacterEstimateData** (deep math でなく assembly):
`hdelta_even : ∃z, ⟨δ₁,δ₂⟩=z ∧ Even z` (H79 level) の全 input 所在確認済:
- δ real: `hypothesis78_delta_isReal` ✅ (本 milestone)
- δ ∈ ZIrr: `delta_mem_ZIrr_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent` (S09_Nonex:2175;
  input = hcoh `hypothesis78_isCoherent_sourceSet` / hnu `hypothesis78_nu_eq` / hindZ `induce_mem_ZIrr` /
  hzeta_irr `hypothesis78_zeta_irreducible`)
- ⟨δ,1⟩=0: `delta_orth_one` (S09_Nonex:2822; input = hBD `hypothesis78_betaDecomp`)
- parity: `cfdot_real_vchar_even hodd δ₁Z δ₁R δ₂Z δ₂R` (a=b=⟨δ,1⟩=0 ⟹ Even m)

**次 iteration**: Frobenius Hypothesis79 を 2 family (F.hypothesis78 i,j) から組む → 上記で hdelta_even →
(7.9) `conclusion_of_ind_mem_ZIrr_of_zeta_irreducible_of_isCoherent_parity` (S09_Nonex:4094、hzeta_cross =
`hypothesis79_zetaImage_cross_eq_zero` 済) → hgood → CharacterEstimateData (5-field bundle) → hdata →
card_G0_lower_bound。定量側 (min-index/𝓑-set/base_estimate via (7.5)) は別 strand で残る。

---

## cont.⁴⁸ — ⚠ card_G0 (7.10) は 2026-07-04 再々編で OFF-PATH 判定 / pivot-pending

**2026-07-04 3 レーン再々編** (`ft_lane_reallocation_2026_06_28.md` 末尾 + merge_monitor) の audit
(2 Explore + spine 検証) が確定: **feitThompson の唯一の bare sorry = `S12.exists_zeta_residual_not_
orthogonal` (Pf 11.8)** (S12_MaximalIII_IV_V.lean:3633)。feitThompson は §12→§16 route で最終矛盾に到達。
**card_G0 (7.10) は off-path**: consumer は S09 assembly 内のみ、feitThompson spine 上に無い。

**本 issue (card_G0 delta-reality) は完遂寸前だが off-path**: delta-reality は全 sorry-free 完了
(cont.⁴⁷)。残 = hdelta_even + CharacterEstimateData assembly (全 input 所在済) のみ。**ただし現 spine
の前進には寄与しない**ため、A-レーン on-path 焦点は **S12 (11.8)** に pivot 推奨 (ユーザー確認 2026-07-04:
「いったん区切り」)。**次 session は loop 再開前にこの判定を確認**し、S12 (11.8) か card_G0 完遂かを選ぶ。
delta-reality 成果 (dadeMap_conj/coherence_extension_conj/delta_isReal/hbeta_conj_sub/
hypothesis78_delta_isReal) は genuine・保存済で再利用可。

---

## cont.⁴⁹ — 再開 (2026-07-13): ON-PATH 復帰確定、frontier = CharacterEstimateData assembly

**cont.⁴⁸ の OFF-PATH 判定は stale 化** (9087 RULING #4 3/3 landing、2026-07-13):
(12.17) TypeICovering carve-out 完遂により live spine trace が復活 —
`card_G0_lower_bound` (7.10) → `not_trivial_G0` (7.11) → `not_all_maximal_typeI` →
`theorem88_caseB_holds` → **FeitThompsonSetup:548 (spine)**。#print axioms 全数 probe で
(12.17) chain の残 dirty root は (7.10) と (12.6)(c1) `sibleyTarget_frobI` (b territory) の
正確に 2 本 (9087 追記参照)。lane a は upstream-first + 文書順 + a-territory (S09) により本 issue を再開。

**再開時 frontier (確認済)**:
- S09 cluster の sorry は `card_G0_lower_bound` 本体の 1 本のみ
  (`hdata : F.CharacterEstimateData := sorry`、FrobeniusFamily.lean:1021)。
- cont.⁴⁷ 計画 step 1 (`hypothesis79` 2-family datum) は **landed 済**
  (S09_FrobeniusHypothesis79.lean、dadeSupport_disjoint = kernelSpread_disjoint 経由)。
- 残 = `CharacterEstimateData` (6 fields: i/hmin/B/B_avoids_min/Bsum_le/base_estimate) の
  concrete assembly。入口は `characterEstimateData_of_family71_coherent_zeta_source_data`
  (concrete (7.5) FamilyHypothesis71 + coherent image + (7.8.b) source data +
  (7.9) decomposition を一括接続、notes 2026-06-05 pass) — 残る義務は
  「教科書の concrete source-data package を存在させる」こと:
  (a) minimal index i の選択 (argmin h)、(b) 𝓑-set 構成 ((7.9) dichotomy `hypothesis79`
  conclusion → good index)、(c) (7.9) orthogonal integer decomposition (v/x/Γ₁)、
  (d) (7.8.b) source data (hind_norm/hzeta_ind/irr/distinct/degree/hsmall)、
  (e) FamilyHypothesis71 instance。hdelta_even assembly (cont.⁴⁷ 残) は (d)-(7.9) parity 側。

## cont.⁵⁰ — (7.9) family-level conclusion 完成 (hypothesis79_conclusion、sorry-free axiom-clean) ✅

**新 leaf `S09_FrobeniusParity.lean`** (S09_FrobeniusConjIndex + S09_ParityPrimitive 下流):
1. `hypothesis78_ind1H_mem_ZIrr` — hindZ 供給 (hyp76_zeta_eq projection + induce_mem_ZIrr)。
2. `hypothesis79_delta_even` — **cont.⁴⁷ 残の hdelta_even 完成**: δ∈ZIrr
   (delta_and_zetaImages_mem_ZIrr、Sibley coherence 経由) + δ real (hypothesis78_delta_isReal)
   + ⟨δ,1⟩=0 (delta_orth_one; constOne = trivialIrreducibleCharacter は defeq で exact 一発)
   + cfdot_real_vchar_even ⟹ Even ⟨Δ_i,Δ_j⟩。
3. `hypothesis79_conclusion` — **(7.9) 本体**: parity route consumer に全 supplier
   (isCoherent_sourceSet/nu_eq/ind1H_ZIrr/zeta_irreducible/betaDecomp/zetaImage_cross/delta_even)
   を wire。⟨β_i, ζ_j^ν⟩ ≠ 0 ∨ ⟨β_j, ζ_i^ν⟩ ≠ 0 for all i ≠ j。

検証: leaf 一発 green (3781 jobs) + AxiomsCheck assert 2 本 (4167 jobs) + full build green
(4189 jobs)。両定理 axiom-clean `[propext, Classical.choice, Quot.sound]`。

**残 (7.10) assembly** (次 iteration 以降、入口 =
`characterEstimateData_of_family71_coherent_zeta_source_data`):
- (a) min-index `i` 選択 (argmin F.h) + `hsmall : 2e_i+1 ≤ h_i` (奇数位数 Frobenius の数値事実)。
- (b) `hbeta_ne` (= hypothesis79_conclusion) → good-index norm 下界
  `chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero` (S09_FrobeniusEstimate:51) → hgood/hi。
- (c) 𝓑-set 構成 + (7.9) orthogonal integer decomposition (v/x/Γ₁: Γ の Irr 展開)。
- (d) (7.8.b) source data 群 (hind_norm/hzeta_ind/hirr/hdistinct/hzeta_degree/hdegree_sum/
  hzeta_uv) — Ind θ family の直接計算。
- (e) concrete `FamilyHypothesis71` instance (P) + hP_L/hP_A/hP_G0 識別。

## cont.⁵¹ — (7.10) 定量 assembly の原文 blueprint (mmd pp. 42-43 精読、実装マップ)

**原文の構造** (Lean 対応付き):
1. **index 選択**: h 最小の member を 1 に取る (Lean: argmin `F.h`、`hmin`)。
   χ₁ := ν₁ζ₁ (= 選択 member の distinguished coherent image = `H78.nu (zeta zetaDistinct)`)。
2. **𝓐/𝓑 分割**: 𝓐 = {i>1 : ⟨β_i, χ₁⟩ ≠ 0}、𝓑 = 残り。Lean の entry
   (`characterEstimateData_of_family71_coherent_zeta_source_data`) の `B` = 𝓑、
   `hgood` の対象 = 𝓐 (j ∉ B)。
3. **𝓐 側 (hgood)**: (7.8.c) = `chiRhoNormSq_ge_ratio_of_inner_beta_ne_zero`
   (S09_FrobeniusEstimate:51、H78 := member j、χ := χ₁、hbeta_ne = 𝓐 定義)。
   hχ_orth (χ₁ ⊥ member-j の全 ν_jζ_r) = cross-orthogonality (disjoint kernel spread、
   S09_FrobeniusCrossOrtho に既存のはず — 要確認)。
4. **𝓑 側 (hx_nonzero)**: (7.9) = `hypothesis79_conclusion` (cont.⁵⁰ ✅)。
   𝓑 定義 ⟨β_j, χ₁⟩ = 0 → dichotomy 他枝 ⟨β₁, ν_jζ_j⟩ ≠ 0 → x_j ≠ 0。
5. **Γ 分解 (hΓ/horth/hΓ₁)**: x_j := ⟨Γ, ν_jζ_{j1}⟩ ∈ ℤ (Γ ∈ ℤ[Irr G])、
   v_j := member-j の weightedNuSum (Σ_t d_{jt}·ν_jζ_{jt})、weight ⟨v_j,v_j⟩ =
   Σ_t d_{jt}² = (h_j−1)/e_j = `BsumWeight`。⟨Γ, ν_jζ_{jt}⟩ = d_{jt}x_j は
   「β と χ_{jt}−d_{jt}χ_{j1} の support 非交差」(原文 (4.1) 経由) から。
   Γ₁ := Γ − Σ_{𝓑} x_j v_j (構成的、hΓ₁ は展開計算)。
6. **hsmall**: e | h−1 (Frobenius) + h 奇数 ⟹ e ≤ (h−1)/2 ⟹ 2e+1 ≤ h。純数値。
7. **hi**: (7.8.b) ‖χ₁^ρ‖² ≥ 1 − e/h — hzeta_uv 経由 (`zetaNuRhoNormSqGeOfDade` 系)。
8. **source data (hind_norm 等)**: H normal in L ⟹ Ind_H^L 1 = Σ_{λ∈Irr(L/H)} λ ⟹
   ⟨Ind1,Ind1⟩ = e。他も Ind θ family の直接計算。
9. **P : FamilyHypothesis71**: F からの instance (既存 producer 要確認)。

**次 iteration の実装順**: (α) S09_FrobeniusCrossOrtho の cross-orthogonality 在庫確認
(3 の hχ_orth と 5 の support 非交差)、(β) 6 の数値補題 + 1 の argmin、(γ) 5 の Γ 分解
(x/v/Γ₁ 構成 + horth)、(δ) 4+3 の 𝓐𝓑 wiring、(ε) 7-9 の残 source data。

## cont.⁵² — family-wide weighted orthogonality 完成 (2026-07-14) ✅

**新 leaf S09_FrobeniusFamilyOrthogonality.lean** に、(7.10) の 𝓑-family 全体で必要な
直交性を上流 API として実証明した。

1. 任意の non-principal index r について、誘導指標 ζ_r の既約性、共役 index r' の存在、
   奇数位数による ζ_r ≠ ζ̄_r、ζ_r − ζ̄_r の sharp-kernel support を証明。
2. coherence agreement から νζ_r − νζ̄_r が Dade support に載ること、各 νζ_r の norm 1、
   共役対の内積 0 を証明。
3. 異なる family member i ≠ j の任意の source indices r,s について
   hypothesis79_zeta_cross_eq_zero_at を証明。共役差の supports は
   hypothesis79.dadeSupport_disjoint で disjoint なので、
   orthonormal_vchar_diff_ortho が全組合せの内積 0 を与える。
4. 双方の有限和を展開し、
   hypothesis79_weightedNuSum_cross_eq_zero を証明。
5. 同一 member の weighted sum は、誘導族の pairwise orthogonality +
   family_degree_sum から norm を (h_i−1)/e_i と評価し、
   hypothesis78_weightedNuSum_inner_self_eq_BsumWeight で既存の
   BsumWeight interface へ接続。

検証: leaf green、代表3定理の AxiomsCheck green
([propext, Classical.choice, Quot.sound])。これで cont.⁵¹ の (α) と、Γ 分解で必要な
horth : ⟨v_j,v_l⟩ = if j=l then BsumWeight j else 0 の character-side supplier は完成。

**次 frontier**: 原文 (7.9) の係数関係
⟨Γ, ν_j ζ_{jt}⟩ = d_{jt} x_j を証明し、x_j・v_j・Γ₁ を構成して
Bsum_le_of_orthogonal_integer_decomposition へ渡す。続いて 𝓐/𝓑 wiring と残 source data を組む。
