---
id: 9314
slug: common-overfield-conjugate-basis
title: "Normalize Frobenius conjugate coordinates in a common overfield"
created: 2026-07-20
---

# Normalize Frobenius conjugate coordinates in a common overfield

## 背景

Higman, *Suzuki 2-groups*, Lemma 11 (pp. 88--89) は第一層の有限体
`K = F₂(λ)` と第二層の Singer field を共通有限体 `L` に埋め、第一層の
共役基底を Frobenius cycle として正規化する。既存 issue 9300 の API は
`K ⊗[F₂] K` 上でのみこの基底を構成しており、任意の埋め込み
`ι : K →ₐ[F₂] L` に沿う `L ⊗[F₂] K` の座標・基底・actor 対角化はまだない。

内容は Higman 固有でなく有限体表現に再利用できるため、既存
`OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean` に置く。
consumer は issue 2048 の Higman Lemma 11。

## やること

- [x] Frobenius 埋め込み族 `ι ∘ Frob^i` から
      `L ⊗[F₂] K ≃ₗ[L] (Fin [K:F₂] → L)` を構成する
- [x] その双対基底で exact ground expansion
      `1 ⊗ x = ∑ ι(x^(2^i)) • b_i` を証明する
- [x] ground-field multiplication と transported actor を同じ基底で対角化する
- [x] scalar Frobenius が基底添字を cyclic successor へ送ることを証明する
- [x] Higman Lemma 11 leaf から正規化済み共役基底を直接利用できることを確認する

## 完了条件

- 新規 `sorry` / `axiom` / opaque carrier なし
- `lake build OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates`
  と Higman Lemma 11 の対象 leaf build が成功する
- 既存 leaf を 1500 行 trigger 以下に保つ

## 参照

- `issues/closed/9300-frobenius-conjugate-coordinates.md`
- `issues/2048-pf-suzuki-lemma5.md`
- `OddOrder/Higman/Suzuki2Groups/HigmanLemmaEleven.lean`
- `references/higman/suzuki-2-groups.pdf`, pp. 88--89
