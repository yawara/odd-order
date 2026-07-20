---
id: 9316
slug: cross-field-scalar-normalization
title: "Cross-field scalar-intertwiner normalization"
created: 2026-07-20
---

# Cross-field scalar-intertwiner normalization

## 背景

Higman Lemma 12 p. 89 で、左右 type-A factor の kernel 座標を一つの
ambient `Φ(P)` Singer 座標へ合わせる際、実際に得られる transition は一般に
field isomorphism そのものではなく、非零 scalar と field isomorphism の積である。
同一 field 上の additive automorphism を ring automorphism へ上げる API は
`SemilinearFieldAut.lean` にあるが、異なる有限体間の additive equivalence を
正規化する cross-field 版が無い。濃度一致から任意の transition を ring equivalence
へ昇格するのは誤りなので、actor scalar intertwining と additive generation を使う。

## やること

- [x] `addEquiv_mul_of_mul_scalars` と
      `ringEquivOfAddEquivOfMulScalars` を cross-field に一般化する
- [x] scalar actions を intertwine する `α : F ≃+ K` を
      `α(x) = α(1) * e(x)` (`e : F ≃+* K`) と正規化する theorem を証明する
- [x] existing same-field callers が変更なしで build することを確認する

## 完了条件

新 theorem が標準 axiom のみで、変更 leaf と Higman consumer leaf が target-build
green。issue 2048 の prescribed-kernel coordinate construction から直接利用できる。

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldAut.lean`
- `issues/2048-pf-suzuki-lemma5.md`
- Higman, “Suzuki 2-groups,” p. 89
