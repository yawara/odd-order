---
id: 9300
slug: frobenius-conjugate-coordinates
title: "Frobenius conjugate-coordinate basis for finite-field Singer models"
created: 2026-07-19
---

# Frobenius conjugate-coordinate basis for finite-field Singer models

## 背景

Higman, *Suzuki 2-groups*, Lemma 5 (p. 85) の表示公式では、scalar
extension 上の基底 `b_i` に対して
`1 ⊗ x = ∑ x^(2^i) • b_i` となる normalized Frobenius-conjugate
coordinates が必要である。既存の固有基底定理は固有値だけを与え、座標の
正規化までは保証しない。また candidate の actor-equivariance には、Singer
field model の全作用素を同一基底で対角化する共有 API が必要である。

この内容は Higman 固有ではなく有限体上の Singer 表現で再利用できるため、
`OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean` に置く。
consumer は issue 2048 の Higman Lemma 5。

## やること

- [x] `K ⊗[F₂] K →ₗ[K] (Fin [K:F₂] → K)` を
      `a ⊗ x ↦ (a * x^(2^i))_i` として構成し、Frobenius 準同型族の
      線形独立から bijective を証明する
- [x] `Basis.ofEquivFun` により normalized basis を構成し、
      `1 ⊗ x = ∑ x^(2^i) • b_i` を証明する
- [x] faithful irreducible abelian `F₂`-representation を
      `GaloisField 2 n` 上の乗法作用へ移す linear field model を構成する
- [x] multiplication の base change が座標ごとに重み `u^(2^i)` を持つことを
      証明する
- [x] field model を移送した基底で全 actor の同時対角化 API を証明する
- [x] Higman の upper-triangular candidate へ接続し、issue 2048 の consumer を
      対象ビルドする

## 完了条件

- 新規 `sorry` / `axiom` / opaque carrier なし
- `lake build OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates`
  が成功する
- Higman Lemma 5 の actual formula consumer が normalized basis と
  simultaneous diagonalization を直接 cite する

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/GroupTheory/RepresentationTheory/SingerField.lean`
- `OddOrder/Higman/Suzuki2Groups/HigmanSquareMap.lean`
- `references/higman/pages/extracts/suzuki-2-groups-p085-lemma5.png`
