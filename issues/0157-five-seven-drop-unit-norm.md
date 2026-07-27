---
id: 157
slug: five-seven-drop-unit-norm
title: "Peterfalvi (5.7) から unit-norm 仮説を外す — 書籍は Hypothesis (5.2) + 等次数のみ"
created: 2026-07-27
---

# Peterfalvi (5.7) から unit-norm 仮説を外す

## 書籍 (p. 27、`04.7_pp_25_29_Coherence.txt` L138)

> **(5.7)** Assume Hypothesis (5.2) and that `χ(1)` is independent of `χ` for `χ ∈ 𝒮`.
> Then `𝒮` is coherent.

**仮説は Hypothesis (5.2) と等次数だけ**。member の既約性 (= `‖χ‖² = 1`) は要求していない。
証明中に `‖χ‖²` が変数として現れる (`|E| = ‖χ‖² = (χ−χ₁, χ−χ₂) = (X−χ, X′−χ) = (X, X′) = |E ∩ E′|`)
ので、**可約 member (`‖χ‖² > 1`) を明示的に扱っている**。

## repo の現状 — unit-norm を要求している

`S07_CoherenceConstantDegree.coherent_of_constant_degree` (L607):

```lean
theorem coherent_of_constant_degree
    (hyp : Hypothesis (L := L) (G := G) S A) (hSfin : S.Finite) (hcard : 2 ≤ S.ncard)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)      -- ⚠ 書籍に無い
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hconst : ∀ a ∈ S, ∀ b ∈ S, a 1 = b 1)
    (hdeg0 : ∀ a ∈ S, a 1 ≠ 0) (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, (a - b).support ⊆ A) :
    Nonempty (IsCoherent hyp.tau S A)
```

`hirr` は orthonormal な `coherentEqualDegree` builder から継承した債務 (survey の
「残っている特殊化」項目 2)。(6.4) の応用では (6.4.c) から既約性が出るので実害は無いが、
**(5.7) 自体が書籍より狭い**。しかも (6.6) の base coherence (`xBaseBlock_isCoherent`,
issue 0155) はこの (5.7) を経由するので、そこにも同じ制限が伝播している。

## 材料 — (5.4) は既に一般ノルムで在る

`S07_Coherence/NormInequalities.lean`:

- `CharacterPsiDecomposition` — (5.4) の setup を bundle。`imageFamily` は
  `OrthonormalCharacterImageFamily`、`tau1` の等長性は **lattice-relative**
  (`ℤ[χ−χ̄, χ−ψ]` 上)。`‖χ‖² = 1` は**どこにも要求されていない**。
- (5.4.a) `‖X‖² ≥ ‖χ‖²` / (5.4.b) `‖Y‖² ≥ ‖ψ‖² ⟹ ‖X‖² = ‖χ‖², ‖Y‖² = ‖ψ‖²,
  X = ∑_{α ∈ E} α (E ⊆ R(χ))` — いずれも一般ノルム形。

⟹ **書籍の (5.7) 証明をそのまま Lean に書ける材料が揃っている**。

## 書籍の証明 (p. 27、要点)

1. `|𝒮| = 2` なら (5.2.d) から直ちに従う。
2. `𝒮 = 𝒮₁ ∪ {χ, χ̄}` で `𝒮₁ ≠ ∅` が `{χ, χ̄}` と直交、`χ₁ ∈ 𝒮₁` を取る。
   (5.2.e) より `R(χ) ⊥ R(χ₁)`。
3. `(χ − χ₁)^τ = X − X₁ + Y` (`X ∈ ℤ[R(χ)]`, `X₁ ∈ ℤ[R(χ₁)]`, `Y ⊥ R(χ), R(χ₁)`)。
   (5.4.a) を両側に当てて `‖X‖² ≥ ‖χ‖²`, `‖X₁‖² ≥ ‖χ₁‖²`、よって `‖X₁ − Y‖² ≥ ‖χ₁‖²`。
4. (5.4.b) より `‖X‖² = ‖χ‖²`、`‖X₁ − Y‖² = ‖χ₁‖²`、ゆえに `Y = 0`、
   かつ `X = ∑_{α ∈ E} α` (`E ⊆ R(χ)`)。
5. **`X` は `χ₁ ∈ 𝒮₁` の取り方に依らない**: 別の `χ₂ ∈ 𝒮₁ − {χ₁, χ̄₁}` に対し
   `(χ − χ₂)^τ = X′ − X₂` とすると
   `|E| = ‖χ‖² = (χ − χ₁, χ − χ₂) = (X − X₁, X′ − X₂) = (X, X′) = |E ∩ E′|`
   ⟹ `E = E′`、`X = X′`。**← ここが `‖χ‖²` を一般値として使う核心**。
6. `τ₁ : ℤ[𝒮] → ℤ[Irr G]` を `χ^{τ₁} = X`、`χᵢ^{τ₁} = X − (χ − χᵢ)^τ` で定義。
   `‖X‖² = ‖χ‖²` と `(X, (χ − χᵢ)^τ) = ‖χ‖²` から `τ₁` は等長。
   `ℤ[𝒮]` は `χ` と差 `χ − χᵢ` で生成されるので結論。

## やること

1. 書籍の上記論法を一般ノルムで Lean 化し、`coherent_of_constant_degree` から `hirr` を落とす。
   現行版は新版の 1 行特殊化に置き換え、コンパイラに同値性を検証させる
   (CLAUDE.md「一般化は旧版を特殊化に置換」)。
2. 下流の伝播を外す: `xBaseBlock_isCoherent` (`S08_SixSixGeneral`) が渡している
   `fun ζ hζ => (hirr₀ ζ hζ).inner_self_eq_one` が不要になる。
   ただし (6.6) 側は別途 `𝒳 ⊆ Irr L` を仮定しているので、そちらの緩和は本 issue の対象外。
3. AxiomsCheck 登録 + survey の「残っている特殊化」項目 2 を更新。

⚠ 現行証明は `DiffPair` による場合分け (`|𝒮| ≥ 4` は `commonImage` + `coherentEqualDegree` へ
retarget) を使っている。書籍の論法とは構成が違うので、**新規に書き下ろす**方が早い可能性が高い。
着手時に現行証明を通読して判断すること。

## 進捗 (2026-07-27)

- [x] **土台 1 — 加重 Parseval** (`S07_Coherence/PsiDecomposition.lean`)。
      正規直交 (`⟨χᵢ,χⱼ⟩ = δᵢⱼ`) を「**対直交 + 各自の非零ノルム** `wⱼ = ⟨χⱼ,χⱼ⟩`」に緩めた 3 本:
      `eq_sum_inner_div_norm_smul_of_mem_span` (`φ = ∑ⱼ (⟨φ,χⱼ⟩/wⱼ)•χⱼ`) /
      `inner_eq_sum_inner_mul_conj_div_norm` (`⟨φ,ψ⟩ = ∑ⱼ ⟨φ,χⱼ⟩·conj⟨ψ,χⱼ⟩/wⱼ`) /
      `coherentImageMapW_inner_eq` (rescale した Fourier 写像
      `ν = coherentImageMap χ (fun j => wⱼ⁻¹ • Xⱼ)` が `ℤ[range χ]` 上で等長)。
- [x] **土台 2 — 加重 coherence builder** `coherentEqualDegreeW`
      (`S07_Coherence/CoherenceExtensionTau2.lean`)。
      `IsCoherent` が要求するのは**等長性であって像の正規直交性ではない** (構造体を実測) ので、
      target 族には `⟨Xᵢ,Xⱼ⟩ = ⟨χᵢ,χⱼ⟩` (**Gram 行列の一致**) だけを課せばよい。
      extension は `wⱼ⁻¹` で rescale した再構成 (`coherentImageMap_apply_eq_of_orthogonal` で
      `ν χₖ = Xₖ`)。
      ⚠ 旧 `coherentEqualDegree` は**そのまま残す**: その `extension` が
      `coherentImageMap χ X` と **definitional** (`coherentEqualDegree_extension := rfl`) で、
      複数の下流がその API に依存している。`1⁻¹ • X j` は `X j` と defeq でないため
      「旧を新の特殊化に置換」は `rfl` を壊す。両者は別構成として併存させる。
- [ ] **残り — `commonImage` 連鎖の一般化**

### 残作業の実測 (2026-07-27)

`coherent_of_constant_degree` の本体で `hirr` が効いているのは 4 箇所:

| 箇所 | 用途 | 一般形 |
|---|---|---|
| `hB` | `⟨β, (χ₀−χⱼ)^τ⟩ = 1 − ⟨χ₀,χⱼ⟩` | `= ⟨χ₀,χ₀⟩ − ⟨χ₀,χⱼ⟩` |
| `horthχ` | `⟨χᵢ,χⱼ⟩ = δᵢⱼ` (`coherentEqualDegree` 用) | 対直交 + 非零ノルム (`coherentEqualDegreeW` 用) |
| `commonImage_self` | `⟨β,β⟩ = 1` | `= ⟨χ₀,χ₀⟩` |
| 基底ケース `isCoherent_pair_of_differenceImage` | `S = {χ₀,χ̄₀}` | `‖χ₀‖² = c` で `E ⊆ R(χ₀)`, `|E| = c` を選ぶ |

⟹ 具体的な残作業:

1. **`xFamily_inner`** (`S07_CoherenceConstantDegree:562`) の `1` を `⟨χ₀,χ₀⟩` に置換。
   恒等式は一般 `c` で成立 (手計算で確認済 — `c` が実数であることは
   `inner_conj_symm (χ 0) (χ 0)` から無料)。呼び出しは (5.7) 本体の 1 箇所のみ。
2. **`commonImage` 連鎖** (`S07_CoherenceConstantDegree:409-558`) の `hirr` を外す:
   `commonImage_self` / `_inner_ref` / `_inner_conj` / `_inner_refconj` / `_inner_other` /
   `_inner` の 6 本と、その土台 `pairDecomp'_two_sided`。いずれも結論の `1` が `⟨χ₀,χ₀⟩` になる。
   ⚠ (5.4) 側 (`CharacterPsiDecomposition`) は**元から一般ノルム**なので、
   土台の再証明は不要で「`1` を `c` に置き換えて式を追う」作業のはず — ただし
   `pairDecomp'_two_sided` が `hirr` を `ψ` 側 (`‖ψ‖²`) にも使っていないか要確認。
3. **基底ケース** `isCoherent_pair_of_differenceImage` の一般化
   (`|R(χ₀)| = ‖χ₀−χ̄₀‖² = 2c` から `|E| = c` の部分集合を取る)。
4. 本体の組み上げ (`coherentEqualDegree` → `coherentEqualDegreeW`)。

## ⚠ 根本原因の発見 (2026-07-27) — repo の `S07.Hypothesis` 自体が書籍 (5.2) より狭い

`commonImage` 連鎖を一般化した後に基底ケースを見て判明。**`hirr` は (5.7) の制限ではなく、
carrier `S07.Hypothesis` が既に強制している帰結**だった:

```lean
  difference_image :
    ∀ ⦃χ⦄, χ ∈ S → CharacterDifferenceImage (L := L) (G := G) tau χ
```

`CharacterDifferenceImage` は **2 元の符号付き対** `τ(χ−χ̄) = ε·(μ−ν)` (`μ ≠ ν` 既約) を持つ構造。
ゆえに `‖τ(χ−χ̄)‖² = 2`。一方 (5.2.b) の等長性と `⟨χ,χ̄⟩ = 0`・`‖χ̄‖² = ‖χ‖²` から
`‖χ−χ̄‖² = 2‖χ‖²`。差が `A`-supported なら等長性が効いて **`‖χ‖² = 1`**。

⟹ **書籍の (5.2.d) は `R(χ)` のサイズを縛らない** (`‖χ−χ̄‖² = 2‖χ‖²` 個の元を持ちうる) のに、
repo の carrier は 2 元に固定しており、**全 member の既約性を暗に課している**。
(5.7) の `hirr` を外しても carrier がそれを再導入するので、**単独では意味がない**。

なお (5.4) 層は既に一般: `CharacterPsiDecomposition.imageFamily` は
`OrthonormalCharacterImageFamily` (任意サイズ) を持つ。狭いのは `Hypothesis.difference_image`
の 1 フィールドだけ。

### 本当にやるべきこと (issue の再定義)

`S07.Hypothesis.difference_image` の型を
`CharacterDifferenceImage` → `OrthonormalCharacterImageFamily` に**広げる**。

- 既存の witness (Dade 側・§12 μ-grid 側) は 2 元形しか作れない場所があるので、
  [issue 0156 step 1](pending/0156-five-two-d-from-irreducibility.md) の
  `CharacterDifferenceImage.toOrthonormalFamily` で持ち上げる (既に landing 済)。
- `difference_images_orthogonal` も同様に
  `toOrthonormalFamily_orthogonal` 経由で移送できる (これも landing 済)。
- ⚠ `Hypothesis` は §5-§8 の中核 carrier で consumer が多い。フィールド型変更は
  広範囲に波及するので、**edge ごとに build 検証**すること。

## 進捗 (2026-07-27、続き)

- [x] **`pairDecomp_two_sided` の一般化**: `hχχ`/`hζζ` (unit norm) を削除し、結論を
      `⟨D.X, D.X⟩ = ⟨χ, χ⟩ ∧ D.Y = D'.X` に。証明は「`1` を代入しない」だけで通った
      ((5.4.a)/(5.4.b) が元から一般ノルムなので)。
- [x] **`commonImage` 連鎖 6 本の一般化**: `commonImage_self` / `_inner_ref` / `_inner_conj` /
      `_inner_refconj` / `_inner_other` / `_inner` から `hirr` を削除し、結論の `1` を
      `⟨χ₀, χ₀⟩` に。
- [x] **`xFamily_inner` の一般化**: `1` → `⟨χ 0, χ 0⟩` (`star c = c` は
      `inner_conj_symm (χ 0) (χ 0)` から無料)。
- [ ] `coherent_of_constant_degree` 本体の `hirr` は**残したまま**。残っている用途は
      `horthχ` (→ `coherentEqualDegreeW` に差し替えれば不要) と**基底ケース**
      `isCoherent_pair_of_differenceImage` (2 元形に本質的に依存) の 2 箇所だけで、
      どちらも上記の carrier 拡幅が前提。

## 完了条件

`coherent_of_constant_degree` が `hirr` 無しで成立し、旧版がその特殊化になること。
build green + AxiomsCheck OK + lint --strict clean + sorry 非退行。
