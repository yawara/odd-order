---
id: 2042
slug: centralizer-normalizer-b
title: "Peterfalvi Ch I §3 Proposition 1(b): centralizer-normalizer factorization"
created: 2026-07-18
---

# Peterfalvi Ch I §3 Proposition 1(b): centralizer-normalizer factorization

## 背景

Peterfalvi Part II, Ch. I §3 Proposition 1(a) の centralizer action / normal-core
同定を issue 2041 (41764eb86) で構成した。原文の次の主張 (b) は、
X ≤ V に対する ambient normalizer の因数分解
N_G(X) = C_G(X) N_V(X) である。

右作用で書かれた原文を Lean の左作用へ移すため、二重可移性から得る補正元は
f * g の順に合成する。また N_V(X) は V ∩ N_G(X)、§1 の反転積補題は
N_D(X) に適用し、逆元分解を通して原文順 N_K(X) N_V(X) を得る。

## やること

- [x] 二重可移性から N_G(X) = C_G(X) N_D(X) を証明する
- [x] §1 invertedProdEquiv から N_D(X) = N_K(X) N_V(X) を証明する
- [x] X ∩ K = 1 を構成し N_K(X) ≤ C_G(X) を証明する
- [x] Proposition 1(b) の最終因数分解を証明する
- [x] Suzuki hub / AxiomsCheck / 章ノートへ配線する
- [x] strict leaf build、OddOrder.AxiomsCheck、OddOrder 全体を通す

## 完了条件

原文の三段論法に対応する genuine subgroup / set-product 定理が sorry / 新 axiom
なしで構成され、最終 endpoint が許可された 3 公理だけに依存し、全ビルドが通る。

## 参照

- references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd, lines 169--185
- OddOrder/Peterfalvi/Appendices/Suzuki/CentralizerInduction.lean
- OddOrder/Peterfalvi/Appendices/Suzuki/KCyclic.lean
- OddOrder/Peterfalvi/Appendices/Suzuki/InvertedProduct.lean
- notes/peterfalvi/suzuki_ch1.md

## 実装記録

- 実装: `OddOrder/Peterfalvi/Appendices/Suzuki/CentralizerNormalizer.lean`
- 原文照合: Peterfalvi Part II, Ch. I §3 Prop 1(b), pp. 105–106
- strict compile: `lake env lean -DwarningAsError=true .../CentralizerNormalizer.lean` 成功
- leaf build: 4277 jobs 成功
- `OddOrder.AxiomsCheck`: 4367 jobs 成功
- `OddOrder` 全体: 4423 jobs 成功
- placeholder scan: `sorry` / `admit` / `axiom` / `TODO` / `test_` なし
