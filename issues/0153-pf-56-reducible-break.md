---
id: 153
slug: pf-56-reducible-break
title: "Pf (6.2)/(6.3) の h56 oracle を除去 — 書籍の仮説は (5.2.d)/(5.2.e)"
created: 2026-07-27
---

# Pf (6.2)/(6.3) の h56 oracle を除去 — 書籍の仮説は (5.2.d)/(5.2.e)

## ⚠ 当初の診断は誤りだった (2026-07-27 訂正)

初版はこの issue を「`coherentDegreeSqNormBound_of_not_coherentW` が break を
`χ : IrreducibleCharacter ↥L` で取るのが根本原因」と書いていた。**これは実測ミス**:

* 同ファイルに **`coherentDegreeSqNormBound_of_not_coherentW_k`** が既に在り、break を
  `χ : ClassFunction ↥L ℂ` + `⟨χ,χ⟩ ≠ 0` で取る (= 可約 break 可)。
  `S08_SixTwoGeneral` の producer 鎖はそちらを使っている。
* `S07_RetargetScaled` の scaled Gram–Schmidt も既に消費済み。

実際に残っていた oracle は **`hdatum` = Hypothesis (5.2.d)/(5.2.e) の image family データ**
だった。

## 書籍が実際に仮定していること

**(6.1) Hypothesis** (p. 30, `references/peterfalvi/pages/peterfalvi-p030.png`):

> **Assume that Hypothesis (5.2) holds.**  We assume that `K` is a solvable normal subgroup of
> `L` and that `𝒮 = {Ind_K^L θ | θ ∈ Irr K, θ ≠ 1_K}`.

**(5.2)** (p. 25, `peterfalvi-p025.png`) のうち *データ*なのは 2 つだけ:

* **(5.2.d)** `χ ∈ 𝒮` に対し `(χ − χ̄)^τ = ∑_{α ∈ R(χ)} α` なる正規直交 `R(χ) ⊆ ℤ[Irr G]`
* **(5.2.e)** `φ ⊥ {χ, χ̄}` なら `R(φ) ⊥ R(χ)`

⟹ `h56` (「`𝒮(A)` coherent かつ `𝒮(B)` not なら `|K:A| − 1 ≤ 2ψ(1)`」) は**書籍の仮説ではない**
— (6.2) の結論から √ 算術を除いただけのもの。正しい仮説は (5.2.d)/(5.2.e)。

## 完了分 (commit d22c3980c)

新 leaf **`OddOrder/Peterfalvi/S08_SixTwoThreeFromImageFamilies.lean`**:

| 宣言 | 内容 |
|---|---|
| `InducedFamilyImageData` | `𝒮 = inducedKernelFamily K ⊥` に対する (5.2.d)/(5.2.e) |
| `InducedFamilyImageData.datum` | → h56 producer の `hdatum` 節 (break・member とも可約可) |
| `exists_source_index_le_two_psi_of_imageData` | `h56` が**定理**に |
| `six_two_of_imageData` / `six_three_of_imageData` | 書籍の (6.2)/(6.3)、oracle 無し |
| `commutator_quotient_ne_top_of_lt` | `K` 可解 + `X < K` ⟹ anchor と `S(X) ≠ ∅` |

AxiomsCheck 5 件登録 (allowlist 3 公理のみ)、フルビルド green、`--strict` 警告ゼロ。

## 残件 1 — `InducedFamilyImageData` の構成可能性を**実際に構成して**示す

doneness は「仮説が構成可能か」で測る ([[scaffold-sorry-free-not-done]]) ので、FT の実文脈で
インスタンスを組むまでが本件の完了。書籍 (5.3.b) は Hypothesis (4.6) の下でこれを discharge する
(可約な元は certain-type column `μ_j`、`R(μ_j) = {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ}` は Thm (4.9))。
repo 側の部品も揃っている:

* 既約 member/break → `S07.dadeOrthonormalCharacterImageFamilyOfDiff`
* 可約 (column) → `S06.certainTypeR` (§6 版) / `S12.Hypothesis.columnImageFamilyCohFree` (§10 版)
* 分岐 + 直交性の実例 = `S11.sOf_memberRFamily` / `sOf_memberRFamily_orthogonal` (§9 の族)、
  `S12.Hypothesis.sixTwoDecompositionData` (§11/§13、~470 行がインライン)

やること: `S12.Hypothesis.inducedFamilyImageData : S08.InducedFamilyImageData …` を組む。
鍵は「可約 member の column 添字 `k` を χ から**正準に**取る」こと
(`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` は存在しか言わないので、
`columnSum` の単射性を経由して canonical にする)。組めたら §13 の consumer を
`six_three_of_imageData` に付け替えて `sixTwoDecompositionData*` のインライン展開を畳める。

## 残件 2 — 抽象 τ への一般化 (特殊化債務)

書籍 (5.2.b) は「`τ` は `ℤ[𝒮, L^#] → ℤ[Irr G, G^#]` の線形等長」だが、本 leaf の `τ` は FT の
Dade 写像 (`dadeIntegralCharacterMap`)、supported set も `supportInSubgroup A L` 固定。
adjoin engine は既に τ 一般 (`S07.adjoinPairCoherent_general`, `S08_GeneralAdjoin`) なので、
残るのは **norm-weighted engine (`coherentDegreeSqNormBound_of_not_coherentW_k` /
`xAdjoinStepW_k`) の τ 一般化**。`S08_GeneralAdjoin` の docstring いわく Dade 構造を真に使う
helper は 4 つだけ。

## 参照

* 書籍: Pf (5.1)–(5.3) p.25 / (6.1)–(6.3) pp.30–31
  (画像: `references/peterfalvi/pages/peterfalvi-p025.png`, `-p030.png` 〜 `-p037.png`。
  §6 の 8 ページは本 issue の作業で新規レンダリング)
* `OddOrder/Peterfalvi/S08_SixTwoThreeFromImageFamilies.lean` (本件の成果)
* `OddOrder/Peterfalvi/S08_SixTwoGeneral.lean` (`exists_source_index_le_two_psi_of_break`)
* `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean` (旧 oracle 形、consumer 用に残す)
* `OddOrder/Peterfalvi/S13_SixTwoBridge.lean` (§11/§13 の `hdatum` 実 discharge)
* `OddOrder/Peterfalvi/S06_CertainTypeCoherence.lean` (`certainTypeR` — (5.3.b)/(4.9) の可約 `R`)
* 旧分析: closed issue 2022
