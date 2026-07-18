---
id: 2048
slug: pf-suzuki-lemma5
title: "Peterfalvi I.3 Lemma 5: cyclic W and Suzuki type B"
created: 2026-07-18
---

# Peterfalvi I.3 Lemma 5: cyclic W and Suzuki type B

## 背景

Peterfalvi Part II, Ch. I §3 Lemma 5 (p. 107) の形式化。`|st| = 3`、
`Q` が位数 `q^3` (`q = |Q₀|`) の Suzuki 2-group であるとき、`W` が
巡回、`|W| ∣ q + 1`、さらに `W ≠ 1` なら `Q` が Appendix III
Definition 3 の type B であることを示す。

既存 `Suzuki2Groups.SuzukiTypeData.typeB` と `higman_classification` は
任意の `Prop` carrier を持つ scaffold であり、この補題には引用しない。原文が使う
Appendix III Theorem (d),(e) の `K`-module 分解・type-B 同値・有限体座標と、
2 次元有限体表現の結論を具体的データとして構成する。

## やること

- [x] `w ∈ W#` に対して §3 Proposition 1(c) と忠実性から
      `Q ∩ C_G(w) = Q₀` を証明する
- [x] Appendix III Lemma 1(b) の quadratic central extension を実体化する
- [x] Definition 3 の具体的 `TypeBData` を実体化する
- [ ] Higman Theorem (d),(e) の Lemma 5 用 payload を実体化する
  - [x] quotient の2つの不変 summand・同変同型と位数 `q²` の逆像を実体化する
  - [ ] type-B 同値と actual `Q/Q₀`, `K` action を接続する
- [x] invariant `Q₀`-coset の coprime fixed-point lifting から
      自由作用と位数整除を得る一般補題を証明する
- [ ] `K`-不変な位数 `q²` 部分群 `X` と `X^w ≠ X` を証明する
- [ ] `W` の projective-line 上の自由作用から `|W| ∣ q+1` を証明する
- [ ] 一般有限体上の 2 次元表現 API から `W` の巡回性を証明する
- [ ] type-B 結論を含む Lemma 5 の最終定理を組み立てる

## 完了条件

- `W` の巡回性、位数の割り切り、`W ≠ 1 → TypeBData Q` を一つの
  source-facing theorem として証明する
- 新規 `sorry` / `axiom` / opaque-Prop carrier を導入しない
- `OddOrder`, `OddOrder.AxiomsCheck` が build-green

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
- `references/peterfalvi/08.0_pp_139_143_On_Suzuki_2-Groups.mmd`
- `OddOrder/Peterfalvi/Appendices/Suzuki/OrderThreeSuzukiCentralizer.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/QuadraticExtensions.lean`
