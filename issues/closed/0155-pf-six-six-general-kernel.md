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
- [x] **step 4 — per-step adjoining (2026-07-27 本体完了)**: `xAdjoinStep_of_degreeRatios`。
      **Sibley の `XAdjoinStepInput`/`xAdjoinStep` 層は移植せず迂回**し、`S07.xAdjoinStepW_general`
      に直結した (その層が唯一の真に Dade 依存な部分だったので、迂回が最短だった)。axiom-clean。
      **残るのは最終組み上げのみ**: `xSet_isCoherent_of_adjoinSteps` の `hstep` に
      `xAdjoinStep_of_degreeRatios` を流し込み、書籍 p.32 の次数データ (共通指数 `p`-冪次数・
      [Is] Cor 2.30 の中心界・次数平方和 `total` の可除性 → `2a < ∑ deg²`) を各 step で構成する。
      算術 4 本は元から一般 (下記)。
- [x] ~~**step 4 — per-step adjoining の組み立て (残り)**~~ (旧記述、上に置換): `xSet_isCoherent_of_adjoinSteps` の
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

      **⚠ 実測 (2026-07-27): 書籍 p.32 の可除性論法の数学的中身は既に全部一般だった。**
      Sibley 側 `xAdjoinStepInput_of_memberFamily_commonIndexPrimePowerSums`
      (`S08_SibleyHypothesisBasic.lean:343`) の本体が呼ぶ 4 本は、いずれも
      **抽象群 + 素の数値データ**で述べられており `SibleyDadeHypothesis` も Dade も τ も取らない:
      - `S08.degreeDivisibilityInputs_of_commonIndex_primePowerData` (`S08_CoherenceCorePart2:301`)
      - `S08.sq_dvd_natDegreeSquareSum_of_commonIndex` (`S08_CoherenceCorePart1:734`)
      - `S07.sq_dvd_head_of_commonIndex_primePower_sums` (`S07_Coherence/NormInequalities:1056`)
        ← 書籍の「`θᵢ(1)²` は `∑_{j≥i} χⱼ(1)²` を割る」がこれ
      - `S08.natDegreeSquareSum_pos_of_memberFamily` (`S08_CoherenceCorePart1:718`)
      - **`S08.normalizedDegreeGap_of_natDegreeSumPrimePowerGap`**
        (`S08_CoherenceCorePart2:221`) ← **`2a < ∑ deg²` そのものの producer**。
        可除性 `dχ·dχ ∣ D` + `dχ = q·d₁` (`q = p^m`) + `3 ≤ p` + `d₁ < dχ` から出す。
        これも抽象群 + 素の数値データのみ。

      `hyp` を取るのは最後の梱包
      `xAdjoinStepInput_of_memberFamily_degreeDivisibility_commonIndexNatGap`
      (`XAdjoinStepInput hyp.dade hcoh …` を返す) **だけ**。
      ⟹ **step 4 は新しい数学を必要とせず、`xAdjoinStepW_general` への再梱包**に尽きる。
      作業量は「多数のパラメータを正しく並べ替える」ことが中心 (routine だが分量あり)。

      **必要な部品はすべて τ-general 形で既に在る (2026-07-27 実測)**:
      | 役割 | τ-general の実体 |
      |---|---|
      | (5.6) engine | `S07.xAdjoinStepW_general` (0154) |
      | per-member 分解 `Dmem` | `S08.memberExtensionDecomposition_general` (`S08_GeneralAdjoin:515`) — 抽象 τ + `OrthonormalCharacterImageFamily` を取る |
      | 破断/member の像族 `Rχ` | `InducedFamilyImageData.R` |
      | (5.2.b) 等長 `hisom` | `InducedFamilyImageData.adjoinHisom` |
      | 可除性の算術 | 上記 4 本 (元から一般) |
      | chain fold / base coherence | `xSet_isCoherent_of_adjoinSteps` / `xBaseBlock_isCoherent` (step 2,3) |

      ⚠ Sibley 側の `inducedKernelFamily_memberDatum_of_irreducible`
      (`S08_SixTwoGeneral:871`) は結論に `dadeOrthonormalCharacterImageFamilyOfDiff` との
      一致を含むので Dade 固定。一般側は `memberExtensionDecomposition_general` を直接使う。

## 最終結線の部品表 (2026-07-27 時点、すべて landing 済・axiom-clean)

`S08_SixSixGeneral.lean` (778 行) に一般 `K` 版が、それ以外は元から一般。
**残作業 = これらを 1 本の定理に結線するだけ**。

| 書籍 p.32 の要素 | 一般 `K` での実体 | 所在 |
|---|---|---|
| 各 member の次数 `\|L:K\|·p^k` | `exists_index_primePow_degree_of_mem_inducedKernelFamily` | 本 leaf |
| [Is] Cor 2.30 の中心界 `θ(1)² ≤ \|K:Z\|` | `exists_source_primePow_centralBound_of_mem_xSet` | 本 leaf |
| 次数平方和 `total` | `sum_re_sq_xSet_eq` (+`xSetFinset`/`coe_xSetFinset`/`mem_xSetFinset`) | 本 leaf |
| anchor 上の次数比 (`p`-冪) | `exists_primePow_degree_ratio_of_xBaseBlock_anchor` | 本 leaf |
| tail 側の次数下界 `htail_le` | `characterDegree_re_le_of_notMem_pairUnion` | 本 leaf |
| accumulator の性質 | `pairUnion_subset_xSet` / `pairUnion_finite` / `xBaseBlock_subset_pairUnion` | 本 leaf |
| accumulator の有限列挙 | `exists_finEnum_irreducible` | 元から一般 (抽象群) |
| 和の member/tail 分割 | `natSum_partition_of_realSum` | 元から一般 (抽象型 α) |
| 可除性 `dχ·dχ ∣ D` | `S07.sq_dvd_head_of_commonIndex_primePower_sums` + `S08.sq_dvd_natDegreeSquareSum_of_commonIndex` + `S08.degreeDivisibilityInputs_of_commonIndex_primePowerData` | 元から一般 (抽象群+数値) |
| `2a < ∑ deg²` | `S08.normalizedDegreeGap_of_natDegreeSumPrimePowerGap` | 元から一般 (抽象群+数値) |
| member/break の orthonormality | `xMember_characterFacts` / `xMember_inner_eq_zero_of_notMem` | 本 leaf |
| `hSgen` | `span_le_span_zSupportedSpan_union_anchor` | 本 leaf |
| **per-step 継ぎ足し** | **`xAdjoinStep_of_degreeRatios`** | 本 leaf |
| **X-chain fold** | **`xSet_isCoherent_of_adjoinSteps`** | 本 leaf |
| **base coherence** | **`xBaseBlock_isCoherent`** | 本 leaf |

### 結線の手順 (次セッション向け)

1. `xSet_isCoherent_of_adjoinSteps` を呼び、`h0 := xBaseBlock_isCoherent`。
2. `hstep` の中で: accumulator を `exists_finEnum_irreducible` で `Fin k` 列挙 →
   anchor は `exists_xBaseBlock_anchor_index` (基底ブロックは常に prefix 内)。
3. 次数データ: 各 member と break に `exists_primePow_degree_ratio_of_xBaseBlock_anchor`
   → `deg`/`a`、`exists_index_primePow_degree_of_mem_inducedKernelFamily` → 共通指数形。
4. tail-set = `xSetFinset K Z \ (列挙の像)`、`natSum_partition_of_realSum` で
   `sum_re_sq_xSet_eq` を member 側 `D` と tail 側に分割、`htail_le` は
   `characterDegree_re_le_of_notMem_pairUnion`。
5. `sq_dvd_head_of_commonIndex_primePower_sums` → `dχ·dχ ∣ D` →
   `normalizedDegreeGap_of_natDegreeSumPrimePowerGap` → `2a < ∑ deg²`。
6. `xAdjoinStep_of_degreeRatios` に流し込む (`hSgen` は
   `span_le_span_zSupportedSpan_union_anchor`)。

## 完了 (2026-07-27)

**`xSet_isCoherent_of_irreducible_X` が landing・sorry-free・axiom-clean・AxiomsCheck 登録済**
(`S08_SixSixGeneral.lean`, 1026 行):

> `RD : InducedFamilyImageData A₀ K` (= 書籍が (6.1) で仮定する Hypothesis (5.2))、
> `K` が `p` 群 (`p` 奇素数、`|L:K|` と互いに素)、`Z ⊆ Z(K)` 正規、`𝒳 = 𝒮 − 𝒮(Z) ⊆ Irr L` 非空
> ⟹ `𝒳` は `RD.tau` について coherent

最終結線で追加した構造補題 3 本: `pairUnion_closedUnderConjugate` (accumulator の共役閉性) /
`xBaseBlock_nonempty` / `natDegree_lt_of_xBaseBlock_anchor_of_notMem` (base block 外の member の
狭義次数ギャップ)。純 Finset 補題 `natSum_partition_of_realSum` は Sibley 側と共有するため
`S08_CoherenceBasic` → `S08_YsetInner/CharacterBreaks` へ移設。

### ⚠ 当初の完了条件の後半は誤りだった (実測 2026-07-27)

「`S08_CoherenceBasic.Xset_isCoherent_of_irreducible_X` (Sibley 版) がその特殊化に置き換わる」は
**そのままでは達成不能**。Sibley 版は一般版の instantiation ではなく、**より弱い仮説を持つ別定理**:

| | 一般版 (本 issue) | Sibley 版 |
|---|---|---|
| (5.2.d)/(5.2.e) | `InducedFamilyImageData.R` = **𝒮 の全 member** の像族 (書籍 (6.1) の仮定) | 持たない。Dade 写像から**既約 member についてのみ**その場で構成 (`dadeOrthonormalCharacterImageFamilyOfDiff`) |
| 可約 member の像族 | 呼び出し側が供給 (§13 の μ-grid 列族) | 不要 (𝒳 ⊆ Irr L しか使わない) |

`SibleyDadeHypothesis` は像族フィールドを持たないので `InducedFamilyImageData` を作れない。
⟹ 統合するには「**既約な部分族については (5.2.d)/(5.2.e) を (5.2.b) から導出する**」経路が要る。
これは書籍 (6.6) より**強い**定理になる (仮説がより弱い) ので、やる価値はある。

材料と欠けている部品 (実測):

- `characterDifferenceImage_of_irreducible` (`S08_SixFiveGeneral:137`) — τ の等長性だけから
  既約非実 `χ` の (5.3.a) 符号付き 2 元対 `τ(χ−χ̄) = ε·(μ−ν)` を作る。**既にある**。
- `orthogonal_of_tau_conjDiff_inner_eq_zero` + `tau_conjDiff_inner_eq_zero_of_orthogonal`
  (同 leaf) — (5.2.e) も τ だけから出る。**既にある**
  (`hypothesisOfSubfamily` が現にこの経路で `S07.Hypothesis` を組んでいる)。
- **欠けているのは変換 `CharacterDifferenceImage → OrthonormalCharacterImageFamily`**
  (`R(χ) = {ε·μ, −ε·ν}`; 和が `ε·(μ−ν) = τ(χ−χ̄)`、`μ ≠ ν` 既約 + `ε² = 1` で正規直交)。
  adjoining engine (`S07.xAdjoinStepW_general`) が消費するのは後者の形。
- 加えて `InducedFamilyImageData` を **τ 部 (`tau`/`tau_isometry`/`tau_mem_ZIrr`/`tau_apply_one`)**
  と像族部に分け、(6.6) の chain を τ 部だけで述べ直す必要がある
  (`hypothesisOfSubfamily` / `tau_conjDiff_inner_eq_zero_of_orthogonal` / `adjoinHisom` は
  実測で **τ 部しか使っていない**)。

⟹ **重複解消として [issue 0156](0156-five-two-d-from-irreducibility.md) に切り出す**
(書籍被覆のギャップではなくアーキテクチャ課題)。本 issue は上記の完了をもって close。

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
