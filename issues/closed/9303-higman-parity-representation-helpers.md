---
id: 9303
slug: higman-parity-representation-helpers
title: "Shared representation helpers for Higman Lemma 6 parity"
created: 2026-07-19
---

# Shared representation helpers for Higman Lemma 6 parity

## 背景

Higman, *Suzuki 2-groups*, Lemma 6 の parity step は、faithful irreducible
作用および nonzero vectors 上で transitive な faithful 作用から、非自明な
actor が fixed vector を持たないことを使う。また偶数次元なら Singer actor
の位数が 3 で割れるため、Cauchy により位数 3 の actor を選ぶ。

これらは lower-central layer 固有ではないため、既存の topic-coherent な
`OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean` に置く。
Higman の multiplicative layer action への adapter と `H/H₄` consumer は
`OddOrder/Higman/Suzuki2Groups/HigmanLemmaSix.lean` に残す。

## やること

- [x] faithful irreducible commutative action の fixed-vector lemma
- [x] faithful transitive-on-nonzero action の fixed-vector lemma
- [x] 偶数 `𝔽₂`-dimension から位数 3 actor を構成する Singer/Cauchy lemma
- [x] Higman Lemma 6 の lower-central layer consumer へ接続する

## 完了条件

- 新 `axiom` / `sorry` / opaque carrier なし
- [x] 汎用表現論 leaf の targeted build が通る
- [x] Higman consumer の targeted build が通る
- [x] public endpoints を `OddOrder/AxiomsCheck.lean` の監査対象へ追加する

## 2026-07-19 checkpoint

`FrobeniusCoordinates.lean` に二つの generic fixed-vector lemma と
even-dimensional Singer/Cauchy lemma を追加した。`HigmanLemmaSix.lean` では
これらを actual lower-central layer actions へ移し、`H/H₄` 上の位数 3
fixed-point-free automorphism を構成して Neumann の class-two theorem と
矛盾させた。これにより原文 p. 85 の `dim L₂` odd の段落が閉じた。

B レーンでは上記二つの targeted leaf build を確認し、main が担当する
full build / AxiomsCheck build は重ねて実行していない。

## 参照

- G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 6, p. 85.
- `issues/2048-pf-suzuki-lemma5.md`
- `issues/closed/9301-faithful-transitive-singer-dimension.md`
- `issues/closed/9302-fixed-point-free-order-three-class-two.md`
