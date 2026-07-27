---
id: 155
slug: pf-six-six-general-kernel
title: "Peterfalvi (6.6) coherence 半分の一般 kernel 化 — 残りは τ-general な X-chain engine"
created: 2026-07-27
---

# Peterfalvi (6.6) coherence 半分の一般 kernel 化 — 残りは τ-general な X-chain engine

## 背景

**Peterfalvi の残り特殊化債務のうち唯一の深い項目** (survey
[`three_books_full_survey_2026_07_16.md`](../notes/meta/three_books_full_survey_2026_07_16.md)
の「(6.5)/(6.6) の general-`K` 化」節)。書籍 (6.6) (p.31-32):

> Suppose that Hypothesis (6.4) holds with `M = 1`.  Let `Z` be a normal subgroup of `L` such
> that `1 ≠ Z ⊆ Z(K)` and let `𝒳 = 𝒮 − 𝒮(Z)`.  Suppose that `𝒳 ⊆ Irr L`.  Then
> `𝒳 = {χ ∈ Irr L | Z ⊄ Ker χ}` and **`𝒳` is coherent**.

- **集合同一性**は一般 `K` で完済 (`inducedKernelFamily_sdiff_eq_irreducible_not_subset_characterKernel`,
  `S08_InducedKernelFamily`、2026-07-27 朝)。
- **coherence 半分**が本 issue。Sibley (`K = H`) 版 =
  `S08_CoherenceBasic.Xset_isCoherent_of_irreducible_X` (すでに `Z` については generic)。

## 完了済 (2026-07-27、`S08_SixSixGeneral.lean`)

| 層 | 内容 | 宣言 |
|---|---|---|
| 1 | `𝒳 = 𝒮 − 𝒮(Z)` と (5.2.a)/(5.2.c) 一式 | `xSet` / `xSet_closedUnderConjugate` / `xSet_hasNoRealCharacters` / `xSet_pairwise_orthogonal` / `xSet_finite` |
| 1 | 書籍 p.32 の算術 2 本 | `exists_index_primePow_degree_of_mem_inducedKernelFamily` (次数 `\|L:K\|·p^k`) / `exists_source_primePow_centralBound_of_mem_xSet` ([Is] Cor 2.30 の中心界。`Z ⊆ Z(K)` はここで効き、`Z = [K,K]` では破綻する) |
| 1 | `𝒳` の Hypothesis (5.2) | `InducedFamilyImageData.xSetHypothesis` (= `hypothesisOfSubfamily` の instance) |
| 2 | 次数平方和恒等式 `∑_{𝒳} χ(1)² = \|L:K\|·(\|K\| − \|K:Z\|)` | `sum_re_sq_xSet_eq` (+ `xSetFinset` / `coe_xSetFinset` / `mem_xSetFinset`) |
| 3 | 最小次数 base block `𝒮₀` | `xBaseBlock` / `_subset` / `_finite` / `_closedUnderConjugate` / `_degree_re_eq` / `natDegree_le_of_xBaseBlock_anchor` / `two_le_xBaseBlock_ncard` / `exists_xBaseBlock_anchor_index` |

上流の (6.5) 一般形も同日に完成 (`S08_SixFiveGeneral.lean`、(a)(b)(c) すべて)。

## やること — **τ-general な X-chain engine**

Sibley 側の入口 `Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X`
(`S08_CoherenceCorePart2/SibleyBounds.lean:1276`) が使うのは次の 4 つだけ:

1. `xSet_finite` / `Xset_closedUnderConjugate` / `Xset_hasNoRealCharacters` /
   `xBaseBlock_closedUnderConjugate` → **一般版は上記で完済**
2. `exists_conjugatePairCover` — `(X, S₀)` を集合として取る**汎用の組合せ補題**、そのまま使える
3. `hyp.xBaseBlock_isCoherent_of_irreducible_X` — base coherence ((1.1)+(1.4) → `coherentEqualDegree`)
4. **`xChainCoherent hyp.dade …` と `XAdjoinStepInput hyp.dade hcoh (χs i)`**

(1)(2) は済み。**(3)(4) が残りで、(4) が本丸**: `xChainCoherent` / `XAdjoinStepInput` は
**`S04.Hypothesis` (Dade datum) でパラメータ化**され、`τ = dadeIntegralCharacterMap hyp …` に
固定されている。

⟹ **やること = [issue 0154](closed/0154-pf-weighted-adjoin-abstract-tau.md) とまったく同じ形の一般化**。
0154 は加重 (5.6) engine (`xAdjoinStepW`) を `S07.xAdjoinStepW_k_general` へ
「抽象 τ + (5.2.b) の 2 節 (`hisom` = `A₀`-supported 部分格子上の等長、`htauZ` = 値域 `ℤ[Irr G]`)」
で一般化した。同じことを `XAdjoinStepInput` / `xChainCoherent` /
`xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums` に対して行う。

- [ ] **step 1**: `XAdjoinStepInput` / `xChainCoherent` / `xAdjoinStepInput_of_pairUnion_*` の
      `dade` / `dadeIntegralCharacterMap` **実使用箇所を grep して数える**
      ([[generalize-by-measuring-which-carrier-fields-are-used]])。0154 の実績では
      「Dade を真に使う helper は実測で 4 つだけ」だった。
- [ ] **step 2**: `_general` 版を新設 (抽象 τ + `hisom` + `htauZ`、必要なら
      `htau1` = 値域 `ℤ[Irr G, G^#]`)。Dade 版は特殊化に置換 (0154 の型どおり)。
      ⚠ 本 tick で `InducedFamilyImageData` に **`tau_apply_one`** を追加済 — (5.3.a) を
      使う場面ではこの節が要る (無いと `τ(χ−χ̄) = μ + ν` を排除できない)。
- [ ] **step 3**: base coherence (3) の一般版 (`coherentEqualDegree` 自体は既に τ-general の
      はず。要実測)。
- [ ] **step 4**: 一般 `K` の `xSet_isCoherent_of_irreducible_X` を組み上げ、Sibley 版を
      その特殊化に置換。

## 完了条件

一般 `K` (可解正規・冪零・`p` 群) と中心的 `Z` に対する
`xSet_isCoherent_of_irreducible_X` が sorry-free・axiom-clean で landing し、
`S08_CoherenceBasic.Xset_isCoherent_of_irreducible_X` (Sibley 版) が
その特殊化に置き換わること。AxiomsCheck 登録 + survey の該当行を更新。

## 参照

- 完了済コード: `OddOrder/Peterfalvi/S08_SixSixGeneral.lean`,
  `OddOrder/Peterfalvi/S08_SixFiveGeneral.lean`
- Sibley 版: `S08_CoherenceBasic.lean` / `S08_CoherenceCorePart2/SibleyBounds.lean` /
  `S08_DegreeSums.lean`
- 手本: [0154](closed/0154-pf-weighted-adjoin-abstract-tau.md) (加重 (5.6) の τ 一般化),
  [0153](closed/0153-pf-56-reducible-break.md)
- 周辺に残る別の特殊化債務 (本 issue の対象外、survey に記録済):
  - repo の (5.7) `coherent_of_constant_degree` が member の**既約性**を要求する
    (書籍の (5.7)/(5.2) は要求しない) — orthonormal な `coherentEqualDegree` builder 由来。
  - (6.3)/(6.5) が `K` 冪零を取る (書籍は `K/M` 冪零) — `six_three_descent` 由来。
    `M = 1` では一致し、(6.6) が使うのはその場合。
