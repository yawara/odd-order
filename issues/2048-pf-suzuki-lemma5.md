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
  - [x] Higman Lemma 1 (p. 83): 中心を homocyclic とし、actual `K`-不変部分群を
        Agemo 層として分類する。具体的 `Q₀` は最終非自明層であり、残る中心逆包含を
        `Agemo Z(Q) 2 1 = ⊥` と正確に同値化する
  - [x] Higman Lemma 2 (p. 83): 非自明 normal abelian `K`-subgroup `A` と
        `u ∉ A` に対する `u² ∈ A²` と `[u,A] ≤ A⁴` の同時成立を排除する
  - [x] Higman Lemma 3 (pp. 83--84): normal invariant subgroup `C` が `A` を
        cover し `Φ(C) = Φ(A)` なら `exp(A) ≤ 4` を証明する
    - [x] normal actor-invariant subgroup の subtype 上で honest な cover を定義し、
          `Φ(C) ≤ A` と原文 p. 83 の `Φ(C) = A ∨ Φ(C) = Φ(A)` を証明する
    - [x] `Φ(C) = Φ(A)` から `[C,A] ≤ A²`、`C² ≤ A²`、
          `[C,A²] ≤ A⁴` を ambient subgroup として証明する
    - [x] homocyclic `ZMod` 座標の基底上で平方値 endomorphism を半分にし、
          線形延長して `α ≡ 1 mod A²` から honest に `α = 1 - 2ν` を構成する
    - [x] 実際の共役自己同型を `α = 1 - 2ν` と `α² = 1` に接続し、
          `4(ν² - ν) = 0` を導く
    - [x] homocyclic `ZMod` 座標で `ν mod 2` の冪等性を証明し、有限可換
          idempotent 族の common `0`/`1` eigenvector と推移作用の一般帰結を証明する
    - [x] 実際の `A/A²` 上で `u ↦ ν̄(u)` を加法準同型として構成し、
          その像が pairwise commuting な冪等作用素族であることを証明する
    - [x] ambient `X`-作用から `ν̄` の共変性を導き、common-eigenvector 論と
          involution 推移性から各 `ν̄(u)` が `0` または `1` であることを証明する
    - [x] Lemma 2 により `ker ν̄ = A` を示す
    - [x] `0`/`1` dichotomy と第一同型定理から像の位数 `2`、
          従って `C/A` の位数 `2` を証明する
    - [x] 原文 p. 84 の二場合分けを接続し、
          `NormalInvariantCover.pow_four_eq_one_of_frattini_map_eq` として
          `∀ a : A, a ^ 4 = 1` を結論する
  - [ ] Higman Lemmas 4--9 を形式化し、Lemma 12 冒頭で用いる
        maximal abelian / Frattini chain と `Φ(Q) = Q₀` を構成する
    - [x] 原文の `Lᵢ = Hᵢ / (Hᵢ² Hᵢ₊₁)` を actual lower-central quotient として
          構成し、ambient denominator、elementary-abelian 性、標準 `F₂`-module、
          誘導作用・表現を `HigmanLowerCentralGraded` に実装する
    - [ ] commutator から alternating・作用同変な `L₁ × L₁ → L₂` を構成し、
          その値が `L₂` を span することを証明する
    - [ ] 非零 `L₂` 上の推移性から Higman Lemma 4 と直後の scalar-extension
          corollary を証明する
  - [ ] Higman Lemmas 10--12 (pp. 87--92) の分類終端から
        `Agemo Z(Q) 2 1 = ⊥`、従って `Z(Q) = Q₀` を証明し、同時に
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
- `references/higman/p83_84_lemmas_1_3.layout.txt`
- `references/higman/p84_85_lemmas_3_6.layout.txt`
- `references/higman/p85_lemmas_4_6.raw.txt`
- `references/higman/pages/suzuki-2-groups-p085.png`
- `references/higman/suzuki-2-groups.pdf`
- `references/higman/SOURCE.md`
- `OddOrder/Peterfalvi/Appendices/Suzuki/OrderThreeSuzukiCentralizer.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/QuadraticExtensions.lean`
