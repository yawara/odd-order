---
id: 9133
slug: standard-rank-one-root-structure
title: "Standard PSL/Sz/PSU root subgroup structure and distinguished products"
created: 2026-07-18
---

# Standard PSL/Sz/PSU root subgroup structure and distinguished products

## 背景

Peterfalvi Part II, Ch. I §3 Proposition 1(c) は、帰納法で得た
`PSL(2,ℓ)` / `Sz(ℓ)` / `PSU(3,ℓ)` の標準作用から、点安定化群の
Sylow `2`-部分群の型・位数と distinguished involution `s` に対する
`orderOf (s * t) = 3/5/3` を読み戻す。既存の concrete standard-action
実装には根群・Borel・Weyl 元と群位数はあるが、この読み戻しに必要な
公開 root-Sylow API と distinguished-product API がまだ無い。

これは三標準群に共通して再利用される未所有 shared infra なので、
issue 2043 の下流 leaf を書く前に本 issue で claim する。

## やること

- [ ] characteristic two の `PSL(2,F)` について公開 unipotent root model を構成し、
      elementary abelian、exact card、標準 Borel 内 Sylow `2`、標準 Weyl 元との積の
      位数 `3` を証明する。
- [ ] Suzuki standard action について root range が標準 Borel の Sylow `2` であること、
      concrete `RootGroup m` が Appendix III Definition 1 の Suzuki `2`-groupかつ
      explicit type-A model であること、involution line の位数、標準積の位数 `5` を証明する。
- [ ] PSU standard action について Hermitian root group の involution line とその位数、
      root range の Sylow `2` 性、Appendix III Definition 1 の Suzuki `2`-group性、
      標準積の位数 `3` を証明する。
- [ ] 各 endpoint を `OddOrder.AxiomsCheck` に追加する。

## 完了条件

- 上記 API が concrete root/Weyl data から導かれ、opaque `Prop` field、free carrier、
  新 `axiom`、`sorry` を含まない。
- 各 leaf、対応 standard-model hub、`OddOrder.AxiomsCheck`、full `lake build OddOrder`
  が通る。
- issue 2043 の Proposition 1(c) transport leaf から直接利用できる。

## 参照

- `issues/2043-centralizer-trichotomy-c.md`
- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`, lines 177--193
- `OddOrder/GroupTheory/SpecificGroups/Suzuki/`
- `OddOrder/GroupTheory/SpecificGroups/ProjectiveUnitary/`
- `OddOrder/Isaacs/Ch08_PermutationGroups/PSLSimple.lean`
