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

## 完了分 2 — 構成可能性の実証 (commit a0852c6b9)

doneness は「仮説が構成可能か」で測る ([[scaffold-sorry-free-not-done]]) ので、FT の実文脈で
インスタンスを組むまでが完了条件。新 leaf **`OddOrder/Peterfalvi/S13_SixTwoImageData.lean`**
が `S12.Hypothesis M` (kernel `K = M'`) で実際に組んだ:

| 宣言 | 内容 |
|---|---|
| `memberColumn` / `memberColumnConj` | 可約 member の正準な列添字対 (書籍 (5.3.b) の (4.4)/(4.5)) |
| `irrRFamily` | 既約 member の 2 元 Dade 族 |
| `colRFamily` | 可約 member の μ-grid 列族 `R(μ_j)` (Thm (4.9)、`columnImageFamilyCohFree`) |
| `memberRFamily` (+`_of_irr`/`_of_red`) | (5.2.d) の分岐 |
| `memberRFamily_orthogonal` | **(5.2.e) 4 ケース全部** |
| `inducedFamilyImageData` | 束ね = 構成可能性の証拠 |
| `sixTwo_of_hypothesis` / `sixThree_of_hypothesis` | §11 での oracle 無し (6.2)/(6.3) |

(5.2.e) の col×col で必要な「4 つの列添字が相異なる」は、§13 の `sixTwoDecompositionData` が
`S₁` 帰属から取っていたのに対し、ここでは (5.2.e) の仮説 `φ ⊥ {χ, χ̄}` から直接出る
(族のノルムが非零)。`columnSum` の単射性は不要だった。

付随: `S07.OrthonormalCharacterImageFamily.congrChi` (`congrTau` の χ 版)。

AxiomsCheck 8 件登録、フルビルド green (4801 jobs)、`--strict` 警告ゼロ。

## 完了分 3 — (11.3) consumer の付け替え (commit e5a1acc29)

`S13_Lemmas113To115.coherent_S_of_coherent_SH0C` (Peterfalvi (11.3)) の (6.3) cite を
`sixThree_of_hypothesis` に変更。`h56` 分岐 (~40 行) と `ChiefFactorData` /
`TypePNontrivialCore` の供給が丸ごと不要に。新 API が実 call site で使えることの検証も兼ねる。

## 完了条件 — 全て満たした (close)

* `six_three` が Hypothesis (6.1) (= (5.2.d)/(5.2.e) + `K` 可解正規) だけから oracle 無しで
  sorry-free に出る → `six_three_of_imageData`
* その仮説が FT 文脈で**実際に構成できる** → `S12.Hypothesis.inducedFamilyImageData`
* AxiomsCheck 13 件登録 (全て allowlist 3 公理のみ)
* フルビルド green (4801 jobs)、`--strict` 警告ゼロ、sorry 非退行

**繰越 = [issue 0154](0154-pf-weighted-adjoin-abstract-tau.md)**: norm-weighted engine の
抽象 τ 一般化 (書籍 (5.2.b) に対する特殊化債務) と、(11.4) consumer の付け替え (任意)。

## 参照

* 書籍: Pf (5.1)–(5.3) p.25 / (6.1)–(6.3) pp.30–31
  (画像: `references/peterfalvi/pages/peterfalvi-p025.png`, `-p030.png` 〜 `-p037.png`。
  §6 の 8 ページは本 issue の作業で新規レンダリング)
* `OddOrder/Peterfalvi/S08_SixTwoThreeFromImageFamilies.lean` (書籍形の (6.2)/(6.3))
* `OddOrder/Peterfalvi/S13_SixTwoImageData.lean` (§11 での (5.2.d)/(5.2.e) 実構成)
* `OddOrder/Peterfalvi/S08_SixTwoGeneral.lean` (`exists_source_index_le_two_psi_of_break`)
* `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean` (旧 oracle 形、consumer 用に残す)
* `OddOrder/Peterfalvi/S13_SixTwoBridge.lean` (§11/§13 の `hdatum` 実 discharge)
* `OddOrder/Peterfalvi/S06_CertainTypeCoherence.lean` (`certainTypeR` — (5.3.b)/(4.9) の可約 `R`)
* 旧分析: closed issue 2022
