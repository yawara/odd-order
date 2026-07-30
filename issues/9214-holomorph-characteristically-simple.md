---
id: 9214
slug: holomorph-characteristically-simple
title: "shared infra claim: OddOrder/GroupTheory/Holomorph.lean (G ⋊ Aut(G) と characteristic 対応)"
created: 2026-07-29
---

# shared infra claim: OddOrder/GroupTheory/Holomorph.lean (G ⋊ Aut(G) と characteristic 対応)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## claim (lane a, 2026-07-29)

**新設ファイル**: `OddOrder/GroupTheory/Holomorph.lean`

**動機**: Isaacs Problem 9A.8 (characteristically simple ⟹ 同型な単純群の直積, 書籍 p. 277)
の書籍 hint が `G ⋊ Aut(G)` を使う。holomorph は **repo にも mathlib にも無い**
(検索済: `grep -rl "Holomorph\|holomorph" OddOrder/ mathlib/GroupTheory/` は
`AxiomsCheck.lean` / `FixedPointFreeOrderThree.lean` の別文脈のみ)。

**中身**:
* `Holomorph G := SemidirectProduct G (MulAut G) (MonoidHom.id (MulAut G))`
* `Holomorph.inl` の range が正規 (`range_inl_eq_ker_rightHom` でカーネルなので自動)
* **核心の対応**: `K ≤ inl.range` が `Hol(G)`-normal ⟺ `K.comap inl` が `G` で
  **characteristic** (`inl_aut` で `inr σ * inl x * inr σ⁻¹ = inl (σ x)`)
* 帰結: `G` characteristically simple ⟺ `inl.range` が `Hol(G)` の極小正規部分群
* さらに Lemma 9.6 経由で **characteristically simple ⟹ abelian または semisimple**

**所有**: lane a。汎用群論なので `OddOrder/GroupTheory/` 配下に置く
(consumer は当面 `Isaacs/Ch09_MoreSubnormality/Problems9A.lean` のみ)。
