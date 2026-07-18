---
id: 2049
slug: appendix-iii-quadratic-extension
title: "Peterfalvi Appendix III Lemma 1(b): quadratic central extensions"
created: 2026-07-18
---

# Peterfalvi Appendix III Lemma 1(b): quadratic central extensions

## 背景

Peterfalvi Appendix III Lemma 1(b) (pp. 139--140)。有限次元 `F₂`-vector
spaces `V`, `W` と quadratic map `q : V → W` から、中心核 `W`、商 `V`、
平方写像 `q` を持つ具体的 central extension を構成する。Lemma 5 の honest な
type-B model を定義するための最上流 prerequisite。

## やること

- [x] bilinear map による twisted-product group を構成する
- [x] central embedding と quotient projection の short exactness を証明する
- [x] `QuadraticMap.toBilin` から quadratic extension を構成する
- [x] squaring map が元の `q` と一致することを証明する
- [x] hub と `AxiomsCheck` に配線する

## 完了条件

- `QuadraticExtensions.lean` が `sorry` / 新 `axiom` なしで build-green
- centrality、short exactness、square-map recovery が公理監査される

## 参照

- `references/peterfalvi/08.0_pp_139_143_On_Suzuki_2-Groups.mmd`
- `OddOrder/Peterfalvi/Appendices/Suzuki2Groups/QuadraticExtensions.lean`
- issue 2048
