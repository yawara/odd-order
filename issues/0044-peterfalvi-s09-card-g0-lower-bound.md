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
