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
- [ ] Peterfalvi Appendix III Theorem (d),(e) (Higman) の Lemma 5 用 payload を構成する
  - [x] `OrderQModuleSplit` / `IsomorphicOrderQModuleSplit` という結論データ型と、
        位数 `q²` の inverse-image API を定義する
  - [x] ambient `K` action の忠実性・固定点自由性、`Q₀`-不変性、actual actor の
        involution 上の正則性と `|K| = q - 1` を証明する
  - [x] quotient の固定点自由性から summand 上の推移性・単純性・
        distinct summands の complementarity を得る一般 bridge を証明する
  - [x] actual `K` action を `Q/Q₀` へ降ろし、固定点自由性と
        order-`q` invariant summand の推移性・単純性を証明する
  - [x] Higman p. 79 の easy direction: 有限 Suzuki `2`-groupの全 involution が
        中心に入り、involution と単位元からなる具体的 elementary-abelian
        `2`-subgroupを構成する
  - [ ] Higman Lemmas 4, 6--9 と分類終端を形式化して中心の逆包含を証明し、
        `Z(Q) = Q₀` を確立する。その後 Lemmas 11--12 (pp. 89--92) から
        actual two-summand split を構成する
  - [ ] summands が同型 iff type B を証明し、type-B 有限体座標を
        actual `Q/Q₀`, `K` action に接続する
- [x] invariant `Q₀`-coset の coprime fixed-point lifting から
      自由作用と位数整除を得る一般補題を証明する
- [ ] `K`-不変な位数 `q²` 部分群 `X` と `X^w ≠ X` を証明する
- [ ] `W` の projective-line 上の自由作用から `|W| ∣ q+1` を証明する
- [ ] 一般有限体上の 2 次元表現 API から `W` の巡回性を証明する
  - [x] projective FPF から cyclicity と `|E| ∣ |F| + 1` を得る一般定理を証明する
- [ ] type-B 結論を含む Lemma 5 の最終定理を組み立てる

## 完了条件

- `W` の巡回性、位数の割り切り、`W ≠ 1 → TypeBData Q` を一つの
  source-facing theorem として証明する
- 新規 `sorry` / `axiom` / opaque-Prop carrier を導入しない
- 変更した leaf が build-green。`OddOrder` / `OddOrder.AxiomsCheck` の統合 gate は
  main / hub 側で実行する

## 参照

- `references/peterfalvi/pdftotext/05.3_pp_100_107_General_Properties_of_G.txt`
- `references/peterfalvi/pdf/05.3_pp_100_107_General_Properties_of_G.pdf`
- `references/peterfalvi/pdftotext/08.0_pp_139_143_On_Suzuki_2-Groups.txt`
- `references/peterfalvi/pdf/08.0_pp_139_143_On_Suzuki_2-Groups.pdf`
- `references/higman/suzuki-2-groups.pdftotext.txt`
- `references/higman/suzuki-2-groups.pdf`
- `references/higman/SOURCE.md`
- `OddOrder/Peterfalvi/Appendices/Suzuki/OrderThreeSuzukiCentralizer.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/QuadraticExtensions.lean`
