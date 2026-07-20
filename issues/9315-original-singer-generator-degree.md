---
id: 9315
slug: original-singer-generator-degree
title: "Original cyclic actor generator field model and odd degree"
created: 2026-07-20
---

# Original cyclic actor generator field model and odd degree

## 背景

Higman, *Suzuki 2-groups*, Section 6 (p. 87) は、元の cyclic actor
`ξ` の位数が `q - 1` を割る素数だけで割れると仮定して Lemma 11 を進める。
別の prime-supported subgroup へ制限すると第一層の既約性は一般には保存されないため、
元 actor の生成元をそのまま Singer field model に入れる必要がある。

`FrobeniusCoordinates.lean` の
`finrank_eq_of_faithful_irreducible_and_faithful_transitive_nonzero` 内には、
生成元の像が全 Galois field を生成する実証明が既にあるが公開 API になっていない。
この部分を抽出し、位数の divisibility / prime-support から次数が odd multiple になる
既存 arithmetic endpoint へ接続する。

## やること

- [x] faithful irreducible cyclic representation の field model で、actor 生成元の像が
      base field 上に全 Galois field を生成することを公開定理にする
- [ ] `2^n - 1 ∣ |Y|` と同じ prime support から、元生成元の固有値の位数が `|Y|`、
      `n ∣ m`、`Odd (m / n)` を返す Higman source endpoint を構成する
- [ ] Higman Lemma 11 の source assembly から元 actor `Y` のまま呼び出す

## 完了条件

- 新規 `sorry` / `axiom` / opaque carrier なし
- `OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates` の targeted build が通る
- prime-supported subgroup への irreducibility restriction を仮定しない

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `issues/closed/9310-prime-supported-mersenne-order.md`
- `OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean`
- `references/higman/suzuki-2-groups.pdftotext.txt` (Section 6, pp. 87--89)
