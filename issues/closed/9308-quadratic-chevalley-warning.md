---
id: 9308
slug: quadratic-chevalley-warning
title: "Nonzero zero of a low-codimension quadratic map"
created: 2026-07-20
---

# Nonzero zero of a low-codimension quadratic map

## 背景

Higman, *Suzuki 2-groups*, Lemma 10 の有限体 trace 方程式は、標数 2 の
有限次元空間上の二次写像に Chevalley--Warning を適用すれば、原文の
subfield 分解とは独立に閉じられる。この次数・次元論は Higman 固有で
ないため、`OddOrder/Algebra` の source-neutral API として claim する。

## やること

- [x] 双線形写像 `B` と線形自己同型 `T` から座標二次式を構成する
- [x] `2 * finrank W < finrank V` のとき非零 `x` で `B x (T x) = 0` を証明する
- [x] Higman Lemma 10 の有限体 trace 写像から利用する

## 完了条件

新しい Algebra leaf と Higman consumer の対象 build が通り、sorry / axiom を
追加せず Lemma 10 の exact statement を閉じる。

完了: `OddOrder.Algebra.exists_ne_zero_bilinear_twist_zero` を `dbcc7c182`、
Higman consumer `higmanLemmaTen` を `42e744a4f` で landing。両対象 build は green。

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/Higman/Suzuki2Groups/HigmanFiniteFieldTrace.lean`
- `Mathlib.FieldTheory.ChevalleyWarning`
