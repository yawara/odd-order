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

## 完了条件

`coherent_of_constant_degree` が `hirr` 無しで成立し、旧版がその特殊化になること。
build green + AxiomsCheck OK + lint --strict clean + sorry 非退行。
