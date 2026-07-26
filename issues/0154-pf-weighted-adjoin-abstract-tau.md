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
