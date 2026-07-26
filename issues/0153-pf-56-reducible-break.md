---
id: 153
slug: pf-56-reducible-break
title: "Pf (5.6) の break 元の既約性は repo 側の制限 — 書籍は可約 break を許す"
created: 2026-07-27
---

# Pf (5.6) の break 元の既約性は repo 側の制限 — 書籍は可約 break を許す

## 書籍 (p. 26, `references/peterfalvi/pages/peterfalvi-p026.png`)

> **(5.6) Theorem.** Assume Hypothesis (5.2).  Let `𝒮₁ = {χ₁, …, χₙ}` be a subset of `𝒮`
> closed under complex conjugation, where `|𝒮₁| = n`, and let `𝒮₂ = {χ, χ̄}` be a subset of
> `𝒮` such that `𝒮₁ ∩ 𝒮₂ = ∅`.  Assume that
> (a) `𝒮₁` is coherent,
> (b) `χ₁(1)` divides `χ(1)`,
> (c) `2χ(1)χ₁(1) < Σᵢ χᵢ(1)²/‖χᵢ‖²`.
> Then `𝒮₁ ∪ 𝒮₂` is coherent.

**break 元 `χ` に既約性の要求は無い** — `χ ∈ 𝒮` だけ。仮説 (5.2) の `𝒮` の元は既約とは限らず、
(c) の分母 `‖χᵢ‖²` はまさに可約な元を許すために置かれている。

## repo の現状 (2026-07-27 実測)

`S08_CoherenceWeighted.coherentDegreeSqNormBound_of_not_coherentW` は break を
**`χ : IrreducibleCharacter ↥L`** で取る。これが (6.2)/(6.3) の一般形が oracle を必要とする
根本原因:

* `S08_Theorem62_63_Standalone.six_two_general` / `six_three_of_six_two_oracle` は
  **(5.6) break-member oracle `h56` を明示仮説**に取る (「`𝒮(A)` coherent かつ `𝒮(B)` not なら
  `θ ∈ Irr K` で `B ⊆ Ker θ` かつ `|K:A| − 1 ≤ 2·(Ind_K^L θ)(1)` なるものが在る」)。
* `S08_Theorem65c2` の module docstring が原因を明記している:
  「The only genuinely new ingredient is **break-irreducibility**: the (5.6) brick demands the
  break `ψ` be irreducible.」FT spine の 2 インスタンス (c1 Frobenius / c2 certain-type) では
  可約な元 (certain-type column) が `𝒮(A)` の外に落ちるので既約性が回復するが
  (`member_isIrreducible_of_W2_le`)、**一般の可解 `K` にはその構造が無い**。

⟹ survey が「§10–§12 の muGrid/columnSum と entangle する cross-lane oracle」と書いていたのは
**repo 側の (5.6) が書籍より狭いことの帰結**であって、書籍側の困難ではない。

## 既に在る部品

`S07_RetargetScaled.lean` が**可約 break 用の scaled Gram–Schmidt**を持っている
(module docstring: 「These feed the reducible-break (5.6) coherence bound needed by the
case-(c2) (6.2)/(6.3) chain」):

| 定理 | 内容 |
|---|---|
| `inner_block_expand_gen` | 可変ノルム `‖e‖² = ee` に対する block 内積展開 |
| `orthoResidualMapS` / `retargetS` | `(⟨χ,χ⟩)⁻¹` 倍を担う scaled 残差・再標的化 |
| `retargetS_inner_eq_on{,_zSpan_union}` | Gram 条件が `⟨X,X⟩ = ⟨χ,χ⟩` (≠ 1 を許す) の格子等長性 |

整数性の議論も書かれている: `χ ⊥ 𝒮₁`, `χ ⊥ χ̄` の下で `⟨φ, χ⟩ = m‖χ‖²` なので
`⟨φ,χ⟩/‖χ‖² = m ∈ ℤ`。

## やること

1. `coherentDegreeSqNormBound_of_not_coherentW` の `χ : IrreducibleCharacter ↥L` を
   「`χ ∈ 𝒮`、`⟨χ,χ⟩` は 1 とは限らない」形に緩める。既約性を使っている箇所を全数 grep し、
   `retargetS` 系で置換できるか / 別の入力が要るかを判定する。
   ⚠ `hχχ : ⟨χ,χ⟩ = 1` / `hχbarχbar` / `hχχbar = 0` の Gram 仮説がどこで効いているかが鍵。
2. 緩めた版で `h56` を証明する: 「`𝒮(A)` coherent, `𝒮(B)` not」から maximal coherent
   conjugation-closed `𝒮₁` (`𝒮(A) ⊆ 𝒮₁ ⊆ 𝒮(B)`) と隣接不能な共役対 `{ψ, ψ̄}` を取り出し
   (有限性による極大元の存在)、(5.6) の対偶で degree 不等式を得る。書籍 (6.2) の証明冒頭そのまま。
3. `six_two_general` / `six_three_of_six_two_oracle` から `h56` 仮説を除去し、
   `six_two` / `six_three` を無条件の書籍形にする。

## 完了条件

`six_three` が Hypothesis (6.1) だけから (oracle 無しで) sorry-free に出る。AxiomsCheck 登録。
フルビルド green + `--strict` 警告ゼロ + sorry 非退行。

## 参照

* 書籍: Pf (5.6) p.26 / (6.1)–(6.3) pp.30–31
  (画像: `references/peterfalvi/pages/peterfalvi-p026.png` ほか。§6 は未レンダリング)
* `OddOrder/Peterfalvi/S08_CoherenceWeighted.lean` (`coherentDegreeSqNormBound_of_not_coherentW`)
* `OddOrder/Peterfalvi/S07_RetargetScaled.lean` (可約 break 用 scaled 再標的化)
* `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean`
  (`six_two_general`, `six_three_of_six_two_oracle`)
* `OddOrder/Peterfalvi/S08_Theorem65c2.lean` (既約性回復の構造的理由)
* 旧分析: closed issue 2022 (「一般の可解 K で induced member が可約」)
