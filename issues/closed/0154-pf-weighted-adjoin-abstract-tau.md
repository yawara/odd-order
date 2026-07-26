---
id: 154
slug: pf-weighted-adjoin-abstract-tau
title: "Pf (5.6) norm-weighted engine を抽象 τ へ一般化 (特殊化債務)"
created: 2026-07-27
---

# Pf (5.6) norm-weighted engine を抽象 τ へ一般化 (特殊化債務)

issue 0153 から分離。0153 本体 (「(6.2)/(6.3) の h56 oracle を除去」) は完了・close 済。

## 債務の内容

書籍 **Hypothesis (5.2.b)** は「`τ` は `ℤ[𝒮, L^#] → ℤ[Irr G, G^#]` の**任意の**線形等長」。
repo の (5.6) には 2 系統ある:

| engine | τ | 状態 |
|---|---|---|
| 非加重 adjoin (`adjoinPairCoherent_general`) | **抽象 τ** | ✅ 一般 (`S08_GeneralAdjoin`, issue 1049) |
| **norm-weighted** (`xAdjoinStepW_k` / `coherentDegreeSqNormBound_of_not_coherentW_k`) | FT の Dade 写像固定 | ❌ 特殊化 |

加重版は `S08_CoherenceWeighted.lean` (850 行) で `dadeIntegralCharacterMap hyp
(hyp.fullDadeIsometryData)` と `supportInSubgroup A L` をハードコードしている
(Dade 固有語の出現 103 箇所)。この結果 (6.2)/(6.3) の書籍形
(`S08_SixTwoThreeFromImageFamilies`) も FT の Dade 設定に縛られている。

⚠ 「member/break の可約性 (`mc i ≠ 1`)」は既に一般 — 債務は **τ の固定**だけ。

## やること

`S08_GeneralAdjoin` が非加重版でやったのと同じことを加重版に:

1. **Dade を真に使う helper を特定して一般版を作る** (非加重では 4 つだった):
   * `inner_dade_extension_of_supported` → 一般版 `inner_tau_extension_of_supported` **既存**
   * `crux1_of_memberFamilyW` → `crux1_of_memberFamily_general` の**加重版**が要る
   * `inner_Y_extension_member_eq` → `inner_Y_extension_member_eq_general` の**加重版**
   * `retarget_isCoherent_of_extensionImage_k` → `..._general` の**加重版**
2. `xAdjoinStepW_k_general` (抽象 τ + 加重) を組み、既存 `xAdjoinStepW_k` をその特殊化にする。
3. `coherentDegreeSqNormBound_of_not_coherentW_k` の一般版 (対偶) と、
   `S08_SixTwoGeneral` / `S08_SixTwoThreeFromImageFamilies` の τ 一般化。

## 完了条件

`six_two_of_imageData` / `six_three_of_imageData` が「`τ : IntegralCharacterMap ↥L G` +
supported set `A0` + Hypothesis (5.2) データ」だけで述べられる (Dade 依存なし)。
既存の FT consumer (`S13_SixTwoImageData` の instance、§11/§13/§15) は特殊化で通ること。
フルビルド green + `--strict` 警告ゼロ + sorry 非退行。

## 任意の付帯作業

`S13_Lemmas113To115.coherent_quotient_bound_of_noncoherent` (Peterfalvi (11.4)) は今も
`six_two_dichotomy_bound` (§11 dichotomy producer) 経由。`S12.Hypothesis.sixTwo_of_hypothesis`
に付け替えれば `ChiefFactorData` / `TypePNontrivialCore` の供給が不要になる
((11.3) は 2026-07-27 に付け替え済 = commit e5a1acc29)。トレースの `≠ ⊤` → `< M'` 変換が要る。

## 参照

* `OddOrder/Peterfalvi/S08_CoherenceWeighted.lean` (加重 engine、債務の本体)
* `OddOrder/Peterfalvi/S08_GeneralAdjoin.lean` (非加重版の一般化。手本と、流用できる `_general` 群)
* `OddOrder/Peterfalvi/S08_SixTwoThreeFromImageFamilies.lean` (書籍形 (6.2)/(6.3))
* `OddOrder/Peterfalvi/S13_SixTwoImageData.lean` (§11 での (5.2.d)/(5.2.e) 実構成)
* closed issue 0153 / 1049

---

## ✅ 完了 (2026-07-27)

完了条件「`six_two_of_imageData` / `six_three_of_imageData` が `τ` + `A₀` + Hypothesis (5.2)
データだけで述べられる」を達成。commit 3 本 + 付帯 1 本。

### 1. 加重 engine の τ 一般化 (`59defaf9b`, `c00ca1fd7`)

新 leaf **`S08_GeneralAdjoinWeighted.lean`** (namespace S07 / 射影補題のみ S08)。
Dade を真に使う helper は実測で **4 つだけ**で、それぞれ一般化した:

| Dade 版 | 一般版 |
|---|---|
| `inner_dade_extension_of_supported` | 既存 `inner_tau_extension_of_supported` を engine 内で inline |
| `inner_Y_extension_member_eq` | `inner_Y_extension_member_eq_intRatio_general` (scaled 版の `d₁ = 1`) |
| `crux1_of_memberFamilyW` | `crux1_of_memberFamilyW_general` (Dade 版の `hyp`/`_hτ` は未使用だった) |
| `retarget_isCoherent_of_extensionImage_k` | `..._k_general` (等長 3 箇所を `hisom` に) |

engine = `xAdjoinStepW_k_general` (可約 break) / `xAdjoinStepW_general` (既約 break、
break の (5.2.d) 族をパラメータ化) と各対偶。Dade 版 4 本は `Samb = univ` 特殊化に置換
(`mem_zSupportedSpan_univ_iff`: Dade は「全 A₀-supported 関数」上の等長なのでこれが正しい)。

### 2. break chain の τ 一般化 (`572b9368a`)

`S08_SixTwoGeneral` の Dade 依存は実測 **2 箇所だけ**だった (加重 engine 呼び出しと
`dadeIntegralCharacterMap_mem_ZIrr_of_supported`)。3 本を `_general` 化し Dade 版は特殊化:
`inducedKernelFamily_degreeSqNormReBound_of_break_k` /
`inducedKernelFamily_SA_sum_le_two_psi_k` / `exists_source_index_le_two_psi_of_break`。

### 3. `InducedFamilyImageData` が Hypothesis (5.2) を丸ごと持つ (`572b9368a`)

引数を `(hyp : S04.Hypothesis G A L) (K)` → `(A₀ : Set ↥L) (K)` に変え、**(5.2.b)** を
3 フィールド (`tau` / `tau_isometry` / `tau_mem_ZIrr` = 書籍の値域 `ℤ[Irr G, G^#]` 節) で担う。
Dade は **bundle の witness の一つ** (`S12.Hypothesis.inducedFamilyImageData`) になった。
§11/§13/§15 の consumer は無変更。

### 4. 付帯: (11.4) の付け替え (`1565698cd`)

`coherent_quotient_bound_of_noncoherent` を `sixTwo_of_hypothesis` 経由に。
`≠ ⊤` → `< M'` は `Subgroup.subgroupOf_eq_top` で変換。⟹ producer 用に担いでいた
**型仮説 `IsTypeIII M ∨ IsTypeIV M` を除去** (statement が真に弱い仮説に)。

### gate

フルビルド green (4802 jobs) / AxiomsCheck OK (**一般形 9 本を新規登録**、全て axiom-clean) /
`--strict` 警告ゼロ / sorry census 1 (凍結 Q₈ `RankOneAffineModel:299`) 非退行。
