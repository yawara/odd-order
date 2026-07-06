---
id: 9026
slug: minimal-ainvariant-normal-commutative
title: "claim: GroupTheory minimal A-invariant normal commutativity API (lane d)"
created: 2026-07-06
---

# claim: GroupTheory minimal A-invariant normal commutativity API (lane d)

## 背景

BG §1 has a private `isMulCommutative_of_minimal_normal_aInvariant`: in a finite
solvable group, a minimal nontrivial `A`-invariant normal subgroup is
commutative. After 9025 exposed the minimal witness, this commutativity step is
the next shared `MinimalInvariantNormal` API rather than BG-local proof body.

## やること

- [x] Add public `isMulCommutative_of_minimal_aInvariant_normal`.
- [x] Refactor `exists_aInvariant_normal_isElementaryAbelian` to cite it.
- [x] Build `OddOrder.GroupTheory.MinimalInvariantNormal`.

## 完了条件

`OddOrder.GroupTheory.isMulCommutative_of_minimal_aInvariant_normal` is
sorry-free, the existing elementary-abelian theorem still builds, and this issue
is moved to `issues/closed/`.

## 完了メモ

2026-07-06 lane d: added public `isMulCommutative_of_minimal_aInvariant_normal` and refactored the elementary-abelian proof to cite it.
`lake build OddOrder.GroupTheory.MinimalInvariantNormal` passed.

## 参照

- issue 9025: public minimal invariant normal witness
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private
  `isMulCommutative_of_minimal_normal_aInvariant`
