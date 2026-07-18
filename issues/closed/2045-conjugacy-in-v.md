---
id: 2045
slug: conjugacy-in-v
title: "Peterfalvi I.3 Lemma 2 conjugacy inside V"
created: 2026-07-19
---

# Peterfalvi I.3 Lemma 2 conjugacy inside V

## 背景

Peterfalvi Part II, Ch. I §3 Lemma 2 を、原文どおり任意の集合
`X, Y ⊆ V` について形式化する。`G` 内の共役元を
`C_G(Y)` の二重推移性で `D` 内へ修正し、`D = K ⋊ V` の正準準同型
`D → V` を適用して `V` 内の共役元を得る。

## やること

- [x] `K.subgroupOf D` と `V.subgroupOf D` が complement であることを証明する
- [x] 原文の canonical homomorphism `D → V` と `V` 上での恒等性を構成する
- [x] `closure X`, `closure Y` を用いて固定点を共役で移送する
- [x] `C_G(Y)` の二重推移性から `D` 内の共役元を構成する
- [x] `D → V` を集合共役等式へ適用して `V` 内共役を証明する
- [x] `AxiomsCheck` と全体ビルドを通す

## 完了条件

`X, Y : Set G`、`X ⊆ V`、`Y ⊆ V`、`Y = X^g` から
`Y = X^v` となる `v ∈ V` を、新しい axiom・opaque carrier・sorry なしで証明し、
`lake build OddOrder` が成功すること。

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
- `notes/peterfalvi/suzuki_ch1.md`
- `OddOrder/Peterfalvi/Appendices/Suzuki/ConjugacyInV.lean`
