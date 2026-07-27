---
id: 161
slug: five-eight-abstract-dichotomy
title: "Pf (5.8) の μ-column 二分律を (4.6) 一般へ (survey packaging gap)"
created: 2026-07-27
---

# Pf (5.8) の μ-column 二分律を Hypothesis (4.6) 一般で述べる

survey [`three_books_full_survey_2026_07_16.md`](../notes/meta/three_books_full_survey_2026_07_16.md)
の packaging gap 残 8 件のうち **§5 内で最上流**。issue 0159/0160 で (5.3)(b) が
(4.6) 一般で landing したので、(5.8) の前提はすべて抽象版で揃った。

## 書籍 (p. 28–29, `04.7_pp_25_29_Coherence.txt` L163)

> **(5.8)** Suppose that the hypothesis of (5.3.b) holds, that `𝒮 ∩ Irr(L) ≠ ∅` and that
> `μ_k ∈ 𝒮` for some `k > 1`. Let `μ_j = μ̄_k`, and let `τ₁` be an isometry from `ℤ[𝒮]` to
> `ℤ[Irr G]` which coincides with `τ` on `ℤ[𝒮, L^#]`. Then
> **`μ_k^{τ₁} = δ_k ∑_{0≤i<w₁} ω_{ik}^σ` または `μ_k^{τ₁} = −δ_k ∑_{0≤i<w₁} ω_{ij}^σ`**。
> 第 2 の場合、`j` と `k` は `ℓ > 1`, `μ_ℓ ∈ 𝒮`, `μ_ℓ(1) = μ_k(1)` を満たす唯一の添字。

証明の骨格 (どれも 0159/0160 で抽象版が揃った):

1. (5.5) で `μ_k^{τ₁} = ∑ᵢ a_{ik} ω_{ik}^σ + ∑ᵢ a_{ij} ω_{ij}^σ`、`a_{ik} ∈ {0, δ_k}`,
   `a_{ij} ∈ {0, −δ_k}`。
2. `χ ∈ 𝒮 ∩ Irr(L)` に対し **(5.3)(b) と (5.5)** から `χ^{τ₁}` は σ の像と直交
   ⟹ (3.2.d) で `V` 上消滅。
   ⟹ **これは 0159 で landing した `S06.dadeOfDiff_imageSet_orthogonal_chiFam` そのもの**。
3. **(4.7)** で `χ(1)μ_k − μ_k(1)χ ∈ ℤ[𝒮, A]`、`A ∩ V = ∅` ⟹ `μ_k^{τ₁}` も `V` 上消滅。
   ⟹ **`S06.dadeICM_apply_eq_zero_of_mem_ticVdiffV` (0159) の射程**。
4. (3.7) の加法分離で `a_{ik} = a_{0k}`, `a_{ij} = a_{0j}` (∀i)。
5. `‖μ_k^{τ₁}‖² = w₁` から二分律。

## 実測 (2026-07-27) — 既存 instance と抽象化の可否

**`S12.typeII_nu_tau2_dichotomy`** (`S12_TypeIIColumnPin.lean:790`、証明本体 ~430 行) が
**書籍 (5.8) の二分律そのもの**を型-II instance で述べている。結論は既に
`h46 := typeIIHypothesis46 …` で書かれており、抽象化は**機械的**:

| 本体中の型-II 依存 | 出現数 | 抽象化 |
|---|---|---|
| `typeIIHypothesis46 hG hSmax hSII data.typeP` (+ `data.typeP`) | 129 | **h46 変数への textual 置換だけ** |
| `typeII_T2_extension_columnSum_eq_sum` | 1 (冒頭 `obtain`) | **仮説化**。結論が既に抽象: `∃ E ⊆ (certainTypeR h46 hχ₂ne _).imageSet, c.extension ν = ∑ α ∈ E, α ∧ (E.card : ℂ) = (Nat.card h46.W1 : ℂ)` |
| `typeII_T2_extension_nu_apply_eq_zero_of_mem_V` | 1 | **仮説化** (`∀ v ∈ (ticVdiff h46).V, ν v = 0`) |

**それ以外の型-II 依存はゼロ** (`Msigma` / `IsTypeII` / `sOf` / `typePV` /
`centralizerSupport` の出現なしを確認済)。

## やること

1. `S12_TypeIIColumnPin.lean` 内に抽象版を新設 (同ファイルなら補題の可視性が保証される):

```lean
theorem certainTypeR_subsum_dichotomy (h46 : S06.Hypothesis46 A L) [instances]
    {χ₂} (hχ₂ne : χ₂ ≠ 1) {ν : ClassFunction G ℂ}
    {E : Finset (ClassFunction G ℂ)}
    (hEsub : E ⊆ (S06.certainTypeR h46 hχ₂ne _).imageSet)
    (hEsum : ν = ∑ α ∈ E, α)
    (hEcard : (E.card : ℂ) = (Nat.card h46.W1 : ℂ))
    (hvanish : ∀ v ∈ (S06.ticVdiff h46).V, ν v = 0)
    (i₀ : Fin (Nat.card h46.W1)) :
    ν = δ • ∑ p, chiFam … χ₂ i₀ ∨ ν = -δ • ∑ p, chiFam … χ₂⁻¹ i₀
```

   本体は既存 430 行を `typeIIHypothesis46 … data.typeP` → `h46` で置換して移すだけ。
2. `typeII_nu_tau2_dichotomy` を上の適用 (~40 行) に縮める。2 入力は既存補題で供給。
   ⟹ **ファイル行数はほぼ不変** (本体が移動するだけ)。
3. 抽象版が S06/S05 だけに依存するなら、後続 tick で上流 leaf へ移設してよい (任意)。
4. **第 2 の場合の一意性 rider** (「`j`, `k` が唯一の添字」) は survey が
   「直接の対応物なし」と言っている部分。1–2 が済んでから別途。

## 完了条件

書籍 (5.8) の二分律が Hypothesis (4.6) 一般で sorry-free・axiom-clean に述べられ、
型-II 版がその特殊化になること。build green + AxiomsCheck OK + lint --strict clean +
sorry 非退行。rider は別 step (未達でも二分律が抽象化できれば survey の gap は縮む)。

## 参照

* 前提の抽象版: [issue 0159](closed/0159-five-three-b-general-hypothesis.md) (5.3)(b) 本体 + rider + anchor
* [issue 0160](closed/0160-five-three-b-downstream-rewiring.md) anchor dedup + §13 bridge + columnR 統合
* 解析コア: `S05_SigmaTrichotomy` / `S05_GridTrichotomy` ((3.7)/(3.8)) は既に
  `TICyclicHypothesis` レベルで完全に一般

## ✅ step 1–2 完了 (2026-07-27) — 二分律が (4.6) 一般で landing

`S12_TypeIIColumnPin.lean` に **`certainTypeR_subsum_dichotomy`** を新設。
`typeII_nu_tau2_dichotomy` はその特殊化 3 行に縮んだ (証明本体 ~430 行が抽象版へ移動)。
ファイル行数 1269 → 1324 (ほぼ不変、見積りどおり)。両方 sorry-free / axiom-clean、
AxiomsCheck 登録済。full build green (4875 jobs)、lint --strict clean、sorry 349 非退行。

抽象版の仮説 (書籍の証明ステップと 1:1):

| 仮説 | 書籍側 |
|---|---|
| `hEsub`/`hEsum`/`hEcard` | (5.5): `μ_k^{τ₁}` は `R(μ_k)` の濃度 `w₁` の部分和 |
| `hψV` | V-消滅。書籍は (5.3.b)+(4.7) から導く ⟹ **issue 0159 で抽象版を landing 済** |

### 移植で踏んだ罠 (記録)

1. **`str.replace(…, 1)` が別定理の同名 `have` に当たった** — `hνT2` が 3 定理に
   **同一テキスト**で存在し、意図した最後のものでなく最初のものを削除していた。
   `git diff -U6` で位置を特定して復元。テキスト置換リファクタでは
   「同一テキストが複数定理に散在する」を先に数えること。
2. **norm の導出が型-II 依存だった** — 元は coherence 等長 `c.extension_inner_eq` 経由。
   実は `ψ = ∑E` + E 正規直交 + `|E| = w₁` から直接出る。**既存の
   `RepresentationTheory.inner_self_sum_orthonormal_eq_card` を grep で発見**して差し替え
   (新規に書かずに済んだ — [[grep-before-writing-transport-defs]] の実践)。
3. σ-grid の添字は **2 つの指標群の積**なので Fintype が 2 つ要る。W2 側は型に現れないので
   linter の指摘どおり `[Finite …]` + 証明冒頭の `Fintype.ofFinite` にした。

## 残り — step 4: 第 2 の場合の一意性 rider

> In the second case, `j` and `k` are the only indices `ℓ` such that `ℓ > 1`, `μ_ℓ ∈ 𝒮` and
> `μ_ℓ(1) = μ_k(1)`.

survey が「直接の対応物なし (applications derive sign alignment by other proven routes)」と
している部分。原文の証明は p.29 冒頭 (`04.7_pp_25_29_Coherence.txt` の "Suppose that there is
an index ℓ > 1 such that ℓ ≠ j, ℓ ≠ k, μ_ℓ ∈ 𝒮 and …" 以降)。

⚠ step 3 (抽象版を上流 leaf へ移設) は任意。現状 `S12_TypeIIColumnPin.lean` 内にあるが、
型-II 依存はゼロなので S06/S07 側へ移せる。行数に余裕がなくなったら実施する。
