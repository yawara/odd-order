---
id: 159
slug: five-three-b-general-hypothesis
title: "Pf (5.3)(b) を GeneralHypothesis で述べる — 可変長 R の制約が解けた"
created: 2026-07-27
---

# Pf (5.3)(b) を `GeneralHypothesis` で述べる

## なぜ今なのか — 繰延の理由が消えた

survey は (5.3)(b)/(5.8) を「真に開いている」に分類しつつ、こう注記していた:

> **意図的な設計判断**でもある (固定 2 要素の `R` レコードは可変長 `R` を保持できず、
> consumer は general-family (5.7) engine を使う)

この制約は **[issue 0157](closed/0157-five-seven-drop-unit-norm.md) で解消済**。
`S07.GeneralHypothesis` (2026-07-27) の (5.2.d) フィールドは

```lean
  difference_image :
    ∀ ⦃χ⦄, χ ∈ S → OrthonormalCharacterImageFamily (L := L) (G := G) tau χ
```

で **サイズ自由**。⟹ (5.3)(b) が扱えるようになった。

## 書籍 (p. 26、`04.7_pp_25_29_Coherence.txt` L22)

> **(5.3)(b)** Assume Hypothesis (4.6), (5.2.a) and that
> `𝒮 ⊆ {Ind_H^L θ | θ ∈ Irr H, H ⊄ Ker θ}`.
> Then **Hypothesis (5.2) holds**, with the isometry `τ` of (5.2) being the restriction to
> `ℤ[𝒮, L^#]` of the isometry `τ` of Hypothesis (4.6).  If `φ ∈ 𝒮 ∩ Irr L`, then `R(φ)` is
> orthogonal to `ω^σ` for all `ω ∈ Irr(W)`.

証明 (p. 26) の構造:
- `ℤ[𝒮, L^#] = ℤ[𝒮, A]` by (4.7) ⟹ `τ` が定義される。
- (5.2.c) は (1.5.c) から。
- (5.2.d): `χ` 既約なら (a) と同じ (2 元)。可約なら (4.4)+(4.5) より `χ = μ_j` の形で、
  **(4.9) より `R(μ_j) = {δ_j ω_{ij}^σ, −δ_j ω_{ik}^σ | 0 ≤ i < w₁}`** (= `2w₁` 元)。
- (5.2.e): 既約×既約は (4.1)、可約×可約は `R(μ_j)` の形から、混合は
  `NC((φ − φ̄)^τ) ≤ 2` + (3.8)。

## 材料 (実測 2026-07-27) — すべて在る

| 役割 | 実体 |
|---|---|
| (4.6) carrier | `S06.Hypothesis46` (`S06_CertainHypothesis46.lean`) |
| 可約 member の `R(μ_j)` | **`S06.certainTypeR`** (`S06_CertainTypeCoherence.lean:648`) — 戻り値が既に `OrthonormalCharacterImageFamily`、`imageSet := Finset.univ.image (certainTypeRImage …)` で**可変長** |
| 可約×可約の (5.2.e) | `S06.certainTypeR_imageSet_orthogonal_certainTypeR` |
| 既約 member の `R(χ)` | `characterDifferenceImage_of_irreducible` → `toOrthonormalImage` |
| 既約×既約の (5.2.e) | `orthogonal_of_tau_conjDiff_inner_eq_zero` + `tau_conjDiff_inner_eq_zero_of_orthogonal` |
| 混合の (5.2.e) | (3.8) 経由。§11 dispatch は `S11.sOf_memberRFamily`、§11/§13 discharge は `S12.Hypothesis.sixTwoDecompositionData` |
| 既存の類似構成 | **`S13_SixTwoImageData.inducedFamilyImageData`** — §12 hypothesis から `InducedFamilyImageData` を組む。実質 (5.3)(b) の §11 instance。⟹ **これを (4.6) レベルへ持ち上げるのが本 issue** |

## `certainTypeR` の実測 (2026-07-27) — 呼び出しに必要なもの

```lean
noncomputable def certainTypeR (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i) 1) = (∑ i, ((h.columnFamily χ₂⁻¹).mu i) 1)) :
    S07.OrthonormalCharacterImageFamily
      (S07.dadeIntegralCharacterMap h.dade0 h.tau) (columnSum h χ₂)
```

⟹ **member ごとに `χ₂` を復元する必要がある**。可約 member `χ` に対し
「`χ = columnSum h χ₂` となる `χ₂ ≠ 1` が存在する」を与えるのが (4.4)+(4.5) の分類部分で、
`difference_image` の dispatch はそこを経由する。degree 条件 `hdeg` も member ごとに要る。

⟹ 本 issue の主作業は「(4.4)/(4.5) の分類を `Hypothesis46` レベルで member → `χ₂` の
関数として取り出し、`certainTypeR` を適用できる形に整えること」。
`S13_SixTwoImageData.inducedFamilyImageData` は §12 側で**この復元を既に済ませた**データ
(`params.mu = hyp.muGrid …`, `memberColumn`) を使って組んでいるので、
そこがどう `χ₂` を供給しているかを読むのが最短。

## ⟹ 経路が確定した (2026-07-27 実測)

§12 側の可約-member 分類

```lean
theorem Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum
    (hG : IsMinimalSimpleOdd G) (hyp : Hypothesis M) … (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ k : Fin hyp.w2, k ≠ 0 ∧ ψ = ∑ i, hyp.muGrid hG hG.odd i k
```
(`S12_HcBound.lean:587`) は、証明の 3 行目で

```lean
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis   -- :597
```

として **(4.6) レベルの certain-type hypothesis に落としている**。
⟹ **分類の中身は既に (4.6) レベル**で、§12 は `Hypothesis46` の instance を供給しているだけ。

⟹ 本 issue の作業は「`S12_HcBound:597` 以降の本体を `Hypothesis46` レベルの補題として
切り出し、それを使って `Hypothesis46.toGeneralHypothesis` の `difference_image` を
dispatch する」。§12 版はその特殊化になる。

⚠ 前 tick に書いた「§13 の `inducedFamilyImageData` を読むのが最短」は**外れ** —
§13 は分類済みデータ (`memberColumn`) の消費側で、分類そのものは §12 → S06 に在る。

## ⟹ (4.6) レベルの原始概念は既に揃っている (2026-07-27 実測、決定版)

§12 の分類補題の**中身**は次の 1 行に尽きる (`S12_HcBound:620`):

```lean
  obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
```

そして

```lean
theorem induce_not_isIrreducible_iff [NeZero (Nat.card h.W1)] (χ : IrreducibleCharacter ↥h.K) :
    ¬ IsIrreducibleCharacter (ClassFunction.induce h.K χ) ↔ ∃ χ₂, h.chiRestrict χ₂ = χ
```
(`S06_CertainTypeClifford.lean:1099`) は **`Hypothesis46` レベルの定理**。

⟹ **切り出すべき (4.6) レベルの補題は存在しない — 既に在る**。
§12 の `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` の残りは、
§12 の `Fin w₁ / Fin w₂` 添字と §6 の指標群添字の間の**再添字づけ**
(`finCongr hcardW1` / `hcardW2sub` / `finCardEquivCharacterGroup`) にすぎない。

### 従って `Hypothesis46.toGeneralHypothesis` の構成は

`difference_image χ hχ` を `χ = Ind_K^L θ` について:
- `IsIrreducibleCharacter χ` なら `characterDifferenceImage_of_irreducible` → `toOrthonormalImage`
- そうでなければ `induce_not_isIrreducible_iff` で `χ₂'` を取り (`θ = h.chiRestrict χ₂'`)、
  `induce_restrict_certainType_eq` / `coe_chiRestrict` で `χ = columnSum h χ₂'` を出し、
  **`certainTypeR h hχ₂'ne hdeg`** を当てる。

⚠ 残る唯一の未確認点は `certainTypeR` の **degree 条件 `hdeg`**
(`∑ (columnFamily χ₂).mu i (1) = ∑ (columnFamily χ₂⁻¹).mu i (1)`)。
`S06_CertainTypeCoherence` 内に同型の等式が複数ある (`:132` / `:283` / `:472`) ので、
そこから (4.6) レベルで供給できる見込み。**着手時にまずここを確認すること。**

## `hdeg` の供給元 (2026-07-27 実測、最後の未確認点も解消)

`certainTypeR` の `hdeg : ∑ (columnFamily χ₂).mu i (1) = ∑ (columnFamily χ₂⁻¹).mu i (1)` は、
`columnSum_apply_one` (`S06_CertainTypeCoherence:279`)

```lean
    (columnSum h χ₂ : ClassFunction ↥L ℂ) 1 = ∑ i, ((h.columnFamily χ₂).mu i) 1
```

により **`μ_j(1) = μ̄_j(1)`** と同値。`columnSum h χ₂⁻¹` が `(columnSum h χ₂).conj` である
ことは `certainTypeR` の docstring が `columnSum_conj_eq` として言及しているので、
共役が次数を保つことから discharge できる。⟹ **(4.6) レベルで供給可能**。

## ⟹ 部品は全て特定済 (着手可能)

| (5.2.d) の分岐 | 使う部品 |
|---|---|
| 既約 member | `characterDifferenceImage_of_irreducible` → `.toOrthonormalImage`。τ 側の入力 ((5.2.b) の等長・`ℤ[Irr G]` 値域・`τφ(1) = 0`) は `dadeIntegralCharacterMap_{inner_eq_on_supported_span, mem_ZIrr_of_supported, apply_one_eq_zero}` |
| 可約 member | `induce_not_isIrreducible_iff` (`S06_CertainTypeClifford:1099`) で `χ₂'` を取る → `certainTypeR` (`S06_CertainTypeCoherence:648`)、`hdeg` は上記 |
| (5.2.e) 既約×既約 | `orthogonal_of_tau_conjDiff_inner_eq_zero` + `tau_conjDiff_inner_eq_zero_of_orthogonal` |
| (5.2.e) 可約×可約 | `certainTypeR_imageSet_orthogonal_certainTypeR` |
| (5.2.e) 混合 | 書籍は `NC((φ−φ̄)^τ) ≤ 2` + (3.8)。§11 dispatch は `S11.sOf_memberRFamily` |

⚠ **実装上の注意**: `certainTypeR` は instance 引数が多い
(`NeZero (Nat.card h.W1)` / `Invertible (Nat.card ↥h.K : ℂ)` /
`Fintype ↥(h.W1 ⊔ h.W2)` / `Invertible …` / `Fintype (ticVdiff h).W` / `Invertible …`)。
`toGeneralHypothesis` の signature にそのまま並べる必要があり、build-fix が数ラウンド要る。
**まず可約分岐だけを独立した def として landing させ、その後で全体を組む**のが安全。

## やること

1. `S06.Hypothesis46` (+ 必要な補助データ) から `S07.GeneralHypothesis` を構成する
   `Hypothesis46.toGeneralHypothesis` を書く。
   member の既約/可約で `difference_image` を dispatch (既約 → `toOrthonormalImage`、
   可約 → `certainTypeR`)。
2. (5.2.e) の 4 ケース分岐を `difference_images_orthogonal` に詰める。
3. 書籍の後半「`φ ∈ 𝒮 ∩ Irr L` なら `R(φ) ⊥ ω^σ`」も別 statement で出す。
4. 既存の `S13_SixTwoImageData.inducedFamilyImageData` を、可能なら本構成の特殊化に置換
   (§13 側は `InducedFamilyImageData` = 2 元固定でなく一般族を持つので、そのまま載る見込み)。
5. AxiomsCheck 登録 + survey の「(5.3)(b) は設計上の理由で繰延」注記を撤回。

⚠ **survey の該当注記は本 issue の landing 時に必ず書き換える** — 「固定 2 要素の R レコード」
という前提が既に偽になっている。

## 完了条件

`Hypothesis46` から `GeneralHypothesis` が構成でき、(5.3)(b) の書籍 statement が
sorry-free・axiom-clean で landing すること。build green + lint --strict clean。

## ✅ landing (2026-07-27) — `Hypothesis46.toGeneralHypothesis` が sorry-free・axiom-clean で成立

新 leaf [`OddOrder/Peterfalvi/S06_CertainTypeSubcoherent.lean`](../OddOrder/Peterfalvi/S06_CertainTypeSubcoherent.lean)。

| 実装 | 内容 |
|---|---|
| `exists_ne_one_induce_eq_columnSum` | (4.4)+(4.5) の分類。θ ≠ 1_K の induction が可約 ⟹ 源は非自明 column χ₂ ≠ 1 で `Ind θ = columnSum χ₂` |
| `columnR` | 可約分岐の `R(μ_j)`。`certainTypeR` を `φ = columnSum χ₂` に沿って移送 |
| `inducedR` | (5.2.d) の dispatcher (既約 → 2 元 Dade 像 / 可約 → `columnR`) + `imageSet` 読み出し補題 2 本 |
| `memberR` | 族 `𝒮` の member 版 (membership が持つ presentation を `inducedR` に流す) |
| **`toGeneralHypothesis`** | **(5.3)(b) 本体** — `S07.GeneralHypothesis 𝒮 (supportSet h)` を構成 |

### 判明した事実 (着手前の見積りより易しかった点)

1. **`hdeg` は無条件** — `columnSum_inv_apply_one` (共役 column は同次数) がそのまま `certainTypeR`
   の次数条件。⟹ `certainTypeR` の `hdeg` 引数は**元から冗長** (instance 文脈だけで導出可能)。
2. **(5.2.b) 等長も無条件** — `dadeIntegralCharacterMap_inner_eq_of_supported` は 2 つの
   `A₀`-supported 関数に対して無条件に等長。`zSupportedSpan` の membership が supportedness を
   含むので `hφ.2 hψ.2` を渡すだけ。仮説不要。
3. **(5.2.e) の 4 層は全て (4.6) レベルで既存**。特に混合層
   `S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV` (+ swap) は
   `S08_CrossOrthogonality` が既に一般形にしてあった。
4. 可約×可約の副条件 (`χ₂ ≠ χ₂'`, `χ₂ ≠ χ₂'⁻¹`) は Gram 行列から読める
   ⟹ `S06.columnSum_inner_columnSum` / `ne_of_columnSum_inner_eq_zero` を新設。
5. 付随して **`S06.columnSum_injective` を (4.6) レベルで新設**し、既存の
   `S12.Hypothesis.columnSum_injective` を**その特殊化に置換**した (特殊化債務の解消)。

### ✅ 追記 (同日): anchor も (4.6) レベルで導出でき、書籍強度版が landing した

⚠ 下記「残る 1 点」は**同じ tick 内で解消**した。原文 (p. 26) を PDF text で読み直したところ、
族の条件は `𝒮 ⊆ {Ind_K^L θ | θ ∈ Irr K, **H ⊄ Ker θ**}` = **(4.7) の族**であり
(`inducedKernelFamily h.K ⊥` の `θ ≠ 1_K` より強い)、証明本文も

> By (4.7), Supp((φ − φ̄)) ⊆ A. By the definition of τ, (φ − φ̄)^τ vanishes on V.

と、anchor を (4.7) から**導いて**いた。⟹ 実装:

* `inducedNonKernelFamily` — 書籍の族 `{Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}`
* `inducedNonKernelFamily_conjDiff_support_subset` — (4.7) の差分形 `Supp(χ̄ − χ) ⊆ A`
  (1 での消滅は `induce_apply_one` で次数が正整数だから)
* **`dadeICM_apply_eq_zero_of_mem_ticVdiffV`** — **anchor を (4.6) レベルで証明**。
  `V ⊆ A₀` ゆえ `v` は Dade base point ⟹ (2.5) 評価 `dadeValue_eq` (witness `a = v`, `h = 1`) で
  `α^τ(v) = α(v)`、そして `v` は `K` に共役でない (`ticVdiffV_not_mem_conjugatesOfSet_K`) ので
  `α(v) = 0`。⟹ 既存 3 サイト (Sibley §8 / type-P §13 / type-II §12) の個別証明の一般化。
* **`toGeneralHypothesisOfInducedFamily`** — **書籍 statement そのもの**。追加仮説は無く
  (5.2.a)/(5.2.c) のみ。`toGeneralHypothesis` は「2 入力を別ルートで供給できる呼び出し元」向けの
  parametrized engine として残す。

以下は解消前の記録 (経緯として保持):

### ⚠ (解消済) anchor `hvanish` は書籍の statement に無い追加仮説

`toGeneralHypothesis` は次を仮説として取る:

```lean
(hvanish : ∀ ⦃χ⦄, χ ∈ S → IsIrreducibleCharacter χ →
  ∀ v ∈ (ticVdiff h).V, dadeIntegralCharacterMap h.dade0 h.tau (χ - χ.conj) v = 0)
```

書籍 (5.3)(b) の証明では混合ケースを `NC((φ−φ̄)^τ) ≤ 2` + (3.8) で片づけており、この V-消滅は
**(4.6) の帰結であって追加仮説ではない**。本リポでは `S08_CrossOrthogonality` が
「anchor が唯一の ambient 入力」と明示したうえで、3 つの呼び出し元 (Sibley §8 / type-P §13 /
type-II §12) が**それぞれ別ルートで**discharge している。⟹ [[repo-stronger-hypothesis-is-specialization-not-gap]]
の意味で**本リポ側の特殊化債務**であり、書籍の gap ではない。

### 次の作業 (0159 の残り) — anchor を (4.6) レベルで導出する

材料は揃っている:

* **Sibley ルート** (`S08_CaseBCoherence2/ConstituentPinning.lean:684`
  `tau_apply_eq_zero_of_mem_ticVdiffV`): α が `K^#`-supported (= Peterfalvi (4.7)) ⟹ Dade 像は
  `conjugatesOfSet K^G` の外で 0 (`map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot`)、
  かつ `V` は `conjugatesOfSet K^G` と交わらない (**`ticVdiffV_not_mem_conjugatesOfSet_K` は
  既に (4.6) レベル**)。⚠ ただし `hH : ∀ a ∈ A, hyp.H a = ⊥` を要求するので、
  `Hypothesis46` 単体からは出ない (Sibley の `dade_H_eq_bot` に依存)。
* **type-II ルート** (`S12_TypeIIFrobenius.lean:374 付近`): `V ⊆ A₀` なので `dadeValue_eq`
  (witness `a = v`, `h = 1`) で `α^τ(v) = α(v)`、α は `A`-supported で `v ∉ A` ⟹ 0。
  こちらは `H a = ⊥` を要求しない ⟹ **(4.6) レベルで一般化できる見込みが高い**。

⟹ 着手順: type-II ルートを `Hypothesis46` レベルの補題に持ち上げ ((4.7) の `K^#`-supportedness
と `V ⊆ A₀` から)、`toGeneralHypothesis` の `hvanish` を落とす。落ちれば書籍 (5.3)(b) の
statement と完全一致になる。3 つの既存 discharge 元もその特殊化に置換できる。

### 残りの step (元の「やること」から)

3. 書籍後半「`φ ∈ 𝒮 ∩ Irr L` なら `R(φ) ⊥ ω^σ` (∀ ω ∈ Irr W)」— **完了**
   (`dadeOfDiff_imageSet_orthogonal_chiFam`)。`Supp(φ − φ̄) ⊆ A` ⟹ anchor ⟹
   `NC((φ − φ̄)^τ) ≤ ‖φ − φ̄‖² = 2 < 2·min(w₁,w₂)` ⟹ (3.8)
   (`inner_smul_chiFam_eq_zero_of_diff_vanishOnV`)。これは書籍が混合 (5.2.e) を導く経路そのもの
   (可約 `R(μ_j)` の `2w₁` 元は全て符号つき `ω^σ` なので、この rider から直ちに従う)。
4. `S13_SixTwoImageData.inducedFamilyImageData` を本構成の特殊化に置換 — **未着手**
   (§13 側は §12 hypothesis から `InducedFamilyImageData` を組む消費点。本構成に載る見込みだが
   3 サイトの再配線を伴うので別 tick)。
5. survey の「(5.3)(b) は設計上の理由で繰延」注記の撤回 — **完了**
   (`notes/meta/three_books_full_survey_2026_07_16.md` の 3 箇所を書き換え)。

### ⟹ issue の完了条件は満たした

書籍 (5.3)(b) の statement (本体 + rider) が (4.6) 一般で sorry-free・axiom-clean で landing。
残るのは下流の再配線 (step 4) と、既存 3 サイトの anchor を
`dadeICM_apply_eq_zero_of_mem_ticVdiffV` の特殊化へ寄せる dedup — どちらも本 issue の
完了条件外の follow-up。
