---
id: 3009
slug: lem27-elem-abelian-aut
title: "BG Lem 2.7: (Z/q)² ⊆ Aut((Z/p)²), p≠q ⟹ q|p−1 + scalar 元 (Nougat MISSING, PDF 復元要)"
created: 2026-07-18
---

# BG Lem 2.7: elementary abelian p²/q² automorphism action

## 背景

BG §2 の最後の numbered result (2.1–2.6 は 2026-07-18 までに全て済; Lem 2.3 = issue 3008,
Prop 2.2 = char-free 化)。**§2 = 7 結果、残りは Lem 2.7 のみ**。

⚠ **Nougat MISSING page**: `references/bg/*.mmd` は Lem 2.7 の **statement と証明前半を欠落**。
生き残っているのは証明末尾 (mmd L790–792) のみ:
> `v₁^β = λ₁ v₁`, `v₂^β = λ₂ v₂` for some `λ₁, λ₂ ∈ F_p` with `λ₁^q = λ₂^q = 1`,
> and then (a) and (b) follow.
直後に `## 3 Actions of Frobenius Groups` (L795) が続く。

**まず PDF から statement を復元**すること (Nougat 再実行でなく `Read pages=N` で BG PDF の
§2/§3 境界ページ = Thm 2.6 の後、§3 の前。[[nougat-missing-page-recovery]])。

## 推定 statement (survey L309 より、PDF で確認要)

`p ≠ q` primes, `P ≅ (Z/p)²` elementary abelian, `Q ≅ (Z/q)²`, `Q ⊆ Aut(P)` faithful ⟹
(a) `q ∣ p − 1`; (b) ある `α ∈ Q^#` が `P` 上 scalar として作用 (survived tail の `λ^q=1` と整合:
`Q` の作用は各 eigen-line 上 `q` 乗根 scalar、`F_p^×` の `q`-torsion ゆえ `q | p−1`)。

## やること

- [ ] PDF で Lem 2.7 の正確な statement (hypotheses・(a)(b) の正確な形) を復元。
- [ ] 形式化: `P`/`Q` を elementary abelian (= `(ZMod p) × ZMod p` 型 or `IsElementaryAbelian`)
      とし、`Q → Aut P` faithful から (a) `q ∣ p−1`、(b) scalar 作用の元の存在。
      おそらく `Q` abelian ⟹ `P` 上 simultaneously diagonalizable (F_p alg 拡大)、各 eigenvalue が
      `q` 乗根 ⟹ `F_p^×` に位数 q 元 ⟹ `q | p−1`。
- [ ] survey 正本 Lem 2.7 行を「済」に更新、§2 完成を記録。

## 完了条件

BG Lem 2.7 (a)(b) を book strength・sorry-free・axiom-clean で。§2 全 7 結果完成。

## 参照

- survey 正本 `notes/meta/three_books_full_survey_2026_07_16.md` L303 (§2 summary), L309 (Lem 2.7 行)
- 優先度: 低 (BG 内で cited nowhere, Coq FT unused) だが in-scope (恒久除外でない、[[feedback-generalize-specialized-fully]])
- 関連 infra: `OddOrder/GroupTheory/ElementaryAbelian.lean`, `IsElementaryAbelian`
