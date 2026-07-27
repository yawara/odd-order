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

- [x] **step 1 — 実測 (2026-07-27 完了)**: `dade` はほぼ**型シグネチャ**にしか現れなかった。
      chain レベルで真に Dade を使うものは**ゼロ**:
      `exists_conjugatePairCover` は抽象群の**集合**についての補題で τ が出てこず、
      accumulator fold `S07.coherentOfPairChainCover` は**元から任意の τ**で述べられている。
      Sibley の `xChainCoherent` はそれを Dade に pin しただけの包装だった。
- [x] **step 2 — chain fold の τ 一般化 (2026-07-27 完了)**:
      `xSet_isCoherent_of_adjoinSteps` (`S08_SixSixGeneral`)。一般 `K`・任意の τ で、
      base coherence と per-step adjoining を与えれば `𝒳` の coherence が出る。axiom-clean。
- [x] **step 3 — base coherence (2026-07-27 完了)**: `xBaseBlock_isCoherent`。
      書籍の「By (1.1) and (1.4), `{χ₁,…,χₖ}` is coherent」は一般 `K` では
      **(5.7) `S07.coherent_of_constant_degree` を部分族 `𝒮₀` に当てるだけ**だった
      (`𝒮₀` は構成上の等次数族、Hypothesis (5.2) は `hypothesisOfSubfamily`)。
      Sibley 版は orthonormal 像族を Dade から組んでいた (`coherentEqualDegree_fromDade`) が、
      (5.7) 経由なら τ-general のまま。axiom-clean。
- [ ] **step 4 — per-step adjoining の組み立て (残り)**: `xSet_isCoherent_of_adjoinSteps` の
      `hstep` を実際に供給する。Sibley 側の対応物は
      `xAdjoinStepInput_of_pairUnion_baseAnchor_commonIndexPrimePowerSums`
      (`S08_CoherenceCorePart2/SibleyBounds.lean`) で、書籍 p.32 の次数簿記
      (共通指数 `p`-冪次数・[Is] Cor 2.30 の中心界・次数平方和 `total` の可除性) を
      `xAdjoinStepW_general` の仮説へ流し込む部分。
      **engine 自体は 0154 の `S07.xAdjoinStepW_general` がそのまま使える**
      (可約 member 対応、破断対の (5.2.d) image family `Rχ` を引数に取る)。
      本 leaf に既に在る材料: `exists_index_primePow_degree_of_mem_inducedKernelFamily` /
      `exists_source_primePow_centralBound_of_mem_xSet` / `sum_re_sq_xSet_eq` /
      `natDegree_le_of_xBaseBlock_anchor` / `exists_xBaseBlock_anchor_index`。

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
