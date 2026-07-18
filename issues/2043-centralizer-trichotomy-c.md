---
id: 2043
slug: centralizer-trichotomy-c
title: "Peterfalvi Ch I §3 Proposition 1(c): centralizer residual and trichotomy"
created: 2026-07-18
---

# Peterfalvi Ch I §3 Proposition 1(c): centralizer residual and trichotomy

## 背景

Peterfalvi Part II, Ch. I §3 Proposition 1(c) (pp. 105–106) を原文強度で形式化する。
`X ≤ V`, `X ≠ 1`, `2-rank C_G(X) ≥ 2` の下で `L=C_G(X)`,
`F=O^{2′}(L)`, `ℓ=|C_{Q₀}(X)|` と置き、
`C_{Q₁}(X)=1`, `𝒩(L)∩F=Z(F)`、および PSL/Sz/PSU の三分岐を得る。

§3 Prop 1(a) は `CentralizerInduction.lean`、(b) は
`CentralizerNormalizer.lean` で axiom-clean。原文が (c) で使う `Q₁` は §2 Prop 1
直後の standing notation `Q=S×Q₁` であり、追加仮定ではなく nilpotent `Q` の一意な
正規 `2`-補群として構成する。

## やること

- [x] `Q₁` を `Q` の正規 `2`-補群として実構成し、任意の `S : Sylow 2 Q` に対する
      complement、characteristic、odd order、`S × Q₁ ≃* Q` を証明する
      (`SylowDecomposition.lean`)。
- [x] Lemma 1/induction から `C_Q(X)` が `2`-group と分かったとき
      `C_{Q₁}(X)=1` を導く exact bridge を証明する。
- [x] 分類非依存の構造核
      `𝒩(L) ∩ ⟨C_Q(X)^L⟩ = Z(⟨C_Q(X)^L⟩)` を原文どおり証明する。
- [x] quotient action `L/𝒩(L)` の honest な Hypothesis/induction carrier と
      `F=O^{2′}(L)=⟨C_Q(X)^L⟩`、residual の quotient transport を構成する。
  - [x] A1 構造式から `C_Q(X)` 内の Sylow `2`-subgroupを構成し、
        `C_Q(X)` が `2`-group ならそれ自身が Sylow と証明。
  - [x] その `IsPGroup` 入力から residual = normal closure と
        `O^{2′}(L)/Z ≃* O^{2′}(L/𝒩(L))` を実構成。
  - [x] `L/𝒩(L)` の実 quotient action を構成し、`H̄`, `Q̄`, `D̄`, `t̄` を
        image として輸送して (A1)、exact kernel から (A2)、odd kernel から
        four-subgroup (A3) を証明した honest `Hypothesis` carrier を構成。
  - [x] `X ≠ 1` から `|L/𝒩(L)| < |G|` を証明。
  - [x] Suzuki Theorem A の結論を、正規・奇数指数の subgroup と
        PSL/Sz/PSU 各標準作用への concrete equivariant coordinates からなる
        `TheoremAConclusion` として構成。quotient `Hypothesis` と strict card bound を
        source induction hypothesis へ接続し、Lemma 1 から quotient root group が
        `2`-group であることを導いた。さらに kernel ≤ `C_D(X)` と
        `C_Q(X) ∩ C_D(X) = 1` から `centralizerQQuotientEquiv : C_Q(X) ≃ Q̄` を
        実構成し、`centralizer_cQ_isPGroup_of_induction` で
        `IsPGroup 2 C_Q(X)` まで戻した (`CentralizerInductionBridge.lean`)。
- [ ] PSL(2,ℓ), Sz(ℓ), PSU(3,ℓ) 各標準モデルについて Sylow `2` 構造、
      `|C_Q(X)|`、distinguished involution と `orderOf(st)=3/5/3` を実証明し、
      三分岐を輸送する。opaque `Prop` scaffold や free target field は使わない。

## 完了条件

- Proposition 1(c) の全結論が原文の仮定から導かれ、三分岐が実際の `MulEquiv` と
  標準モデル data を返す。
- 新しい `axiom`、`sorry`、opaque carrier field、未充足の分類仮定を導入しない。
- leaf build、Suzuki hub、`OddOrder.AxiomsCheck`、full `lake build OddOrder` が通る。
- `notes/peterfalvi/suzuki_ch1.md` の frontier を次の番号付き結果へ更新し、issue を close。

## 参照

- `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`, lines 177–193
- `OddOrder/Peterfalvi/Appendices/Suzuki/CentralizerInduction.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki/CentralizerNormalizer.lean`
- `OddOrder/Peterfalvi/Appendices/Suzuki/InductionHypothesis*.lean`
- `OddOrder/GroupTheory/PrimeComplementResidual.lean`
- `notes/peterfalvi/suzuki_ch1.md`
