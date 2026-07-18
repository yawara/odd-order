---
id: 9152
slug: projective-fpf-two-dim
title: "Generic 2D projective FPF cyclicity and line bound"
created: 2026-07-18
---

# Generic 2D projective FPF cyclicity and line bound

## 背景

Peterfalvi Part II, Ch. I §3 Lemma 5 の `W ≤ GL(2,q)` から
`W` cyclic かつ `|W| ∣ q + 1` を得る段階を、一般有限体上の2次元表現として実証明する。
既存の `odd_two_dim_abelian`、Singer cyclicity、free-action orbit count を再利用し、
不足している projective fixed-point-free action から irreducibility への bridge のみを追加する。

> **CLAIM (lane b, 2026-07-18)**: shared leaf
> `OddOrder/GroupTheory/RepresentationTheory/ProjectiveFreeTwoDim.lean` を lane b が所有する。
> issue 9000 の Singer machinery は再実装せず cite する。

## やること

- [ ] 2次元表現の projective FPF から、群が非自明なら irreducibility を証明する
- [ ] BG Theorem 2.6(a) で奇数位数作用群の可換性を得る
- [ ] 既存 Singer cyclicity から作用群の巡回性を得る
- [ ] projective line の自由作用と `card_of_finrank_two` から `|E| ∣ |F| + 1` を得る
- [ ] `AxiomsCheck` と root import に配線する

## 完了条件

- 新規 `sorry` / `axiom` / opaque carrier なし
- 対象 leaf build-green
- Peterfalvi Lemma 5 が要求する一般有限体 `F_q` に適用可能

## 参照

- issue 2048
- issue 9000 (`SingerField.lean`, `SingerLineBound.lean`)
- `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`
- `OddOrder/GroupTheory/RepresentationTheory/ElemAbelianAutAction.lean`
