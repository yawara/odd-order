---
id: 9312
slug: nonfaithful-transitive-singer-basis
title: "Build Singer eigenbasis from a transitive nonfaithful representation"
created: 2026-07-20
---

# Build Singer eigenbasis from a transitive nonfaithful representation

## 背景

Higman Lemma 11 (pp. 88--89) の proper-extension 段階では、第一層の
faithful action が作る体 `L = F₂(λ)` の次数を `m`、第二層の次数を `n` とし、
まだ `m = n` を仮定できない。第二層の cyclic action は非零ベクトル上推移的
だが、元の actor 上で faithful とは限らない。従来の
`exists_singerFrobeniusEigenbasis_of_faithful_irreducible` を直接使うと
faithfulness または `m = n` を先取りして循環する。

representation の実際の像を actor として取り直せば、その作用は faithful で
transitivity を保つ。元の cyclic generator の像が位数 `2^n - 1` の Singer 元
になることを証明し、元の operator に対する Frobenius eigenbasis を返す。

## やること

- [ ] representation image actor と faithful image representation の汎用 API
- [ ] commutative actor の像が commutative で transitivity を保つこと
- [ ] cyclic generator の像の位数が `2^n - 1` であること
- [ ] 元の generator operator に対する Singer--Frobenius eigenbasis
- [ ] Higman Lemma 11 の第二層で faithfulness を仮定せず利用できる signature

## 完了条件

- 汎用な像 API は `OddOrder/GroupTheory/RepresentationTheory/**` に置く
- Higman 固有の既存 Singer basis API との接続は topic-coherent な既存 leaf に置く
- 対象 leaf build が通る
- 新規 `sorry` / `axiom` / opaque carrier がない
- 第一層次数 `m` と第二層次数 `n` を同一視しない

## 参照

- Higman, “Suzuki 2-groups,” pp. 88--89
- `OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralSpectrum.lean`
- `/tmp/HigmanImageRepresentation5.lean` (green prototype)
- issues 9310, 9311
