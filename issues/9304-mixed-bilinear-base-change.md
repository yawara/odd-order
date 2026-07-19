---
id: 9304
slug: mixed-bilinear-base-change
title: "Scalar extension of mixed bilinear maps"
created: 2026-07-19
---

# Scalar extension of mixed bilinear maps

## 背景

Higman, *Suzuki 2-groups*, Lemma 6 の三重交換子消去では、actual mixed
commutator pairing `L₂ → L₁ → L₃` を分解体へ scalar extension する必要がある。
既存の `LinearMap.BilinMap.baseChange` は同一 source `M → M → N` の場合に限られ、
異なる source module を持つ `M → N → P` には適用できない。

この構成は lower-central layer 固有ではないため、既存の topic-coherent な
`OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean` に一般 API として置く。
Higman の eigenspace・三重交換子 consumer は既存の
`OddOrder/Higman/Suzuki2Groups/` leaves に残す。

## やること

- [x] `M →ₗ[R] N →ₗ[R] P` の二入力 scalar extension を構成する
- [x] pure tensor 上の評価公式を証明する
- [ ] Higman Lemma 6 の mixed commutator pairing へ接続する

## 完了条件

- 新 `axiom` / `sorry` / opaque carrier なし
- [x] shared base-change leaf の targeted build が通る
- [ ] Higman consumer leaf の targeted build が通る
- [x] public endpoints を `OddOrder/AxiomsCheck.lean` の監査対象へ追加する

## 2026-07-19 checkpoint

`LinearMap.baseChange₂` と pure-tensor 評価式に加え、equivariance と full-span
の保存定理を `BaseChange.lean` に実装した。B レーンでは同 leaf の targeted
build を確認し、main が担当する full build / AxiomsCheck build は重ねて
実行していない。次は actual `L₂ × L₁ → L₃` consumer へ接続する。

## 参照

- G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 6, p. 86.
- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanLowerCentralDegreeThree.lean`
