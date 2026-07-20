---
id: 9313
slug: frobenius-descent-trace-coordinates
title: "Relate scalar Frobenius orbits to finite-field trace coordinates"
created: 2026-07-20
---

# Relate scalar Frobenius orbits to finite-field trace coordinates

## 背景

Higman Lemma 11 (p. 89) は、共通 splitting field `L` 上の conjugate
coordinates を Frobenius で巡回させ、gap-supported bracket の係数を一つの
`ε` の Frobenius orbit に正規化する。続いて `m = d * n` 個の係数を
residue class modulo `n` ごとに束ね、`Tr[L/K]` の座標に読み替える。

必要な二事実は特定の群に依存しない。scalar factor の Frobenius が ground-field
bilinear map の base change と可換であること、および Frobenius-coordinate sum を
relative trace に再添字化することを reusable representation/finite-field API とする。

## やること

- [ ] `L ⊗[F₂] V` の scalar factor Frobenius linear map と pure tensor 公式
- [ ] ground-field bilinear map の base change に対する Frobenius covariance
- [ ] `m = d*n` の Frobenius coordinate sum を residue modulo `n` で再添字化
- [ ] 再添字化した係数を `FiniteField.algebraMap_trace_eq_sum_pow` で trace に同定

## 完了条件

- 汎用 API は `OddOrder/GroupTheory/RepresentationTheory/**` に置く
- 対象 leaf builds が通る
- 新規 `sorry` / `axiom` / opaque carrier がない
- Higman Lemma 11 leaf が群固有の gap collapse だけを追加すれば利用できる

## 参照

- Higman, “Suzuki 2-groups,” p. 89
- `OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean`
- `OddOrder/GroupTheory/RepresentationTheory/FrobeniusCoordinates.lean`
- `/tmp/HigmanFrobeniusDescentGreen.lean`
- `/tmp/HigmanTraceReindexGreen.lean`
- issue 2048
