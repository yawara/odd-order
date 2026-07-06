---
id: 9025
slug: minimal-ainvariant-normal-witness
title: "claim: GroupTheory minimal A-invariant normal witness API (lane d)"
created: 2026-07-06
---

# claim: GroupTheory minimal A-invariant normal witness API (lane d)

## 背景

BG §1 has a private `exists_minimal_normal_aInvariant` for the induction in
Prop. 1.5(b). `OddOrder.GroupTheory.MinimalInvariantNormal` already constructs
such a witness internally before proving the stronger elementary-abelian version,
but the minimal witness itself was not public API.

## やること

- [x] Add public `exists_minimal_aInvariant_normal`.
- [x] Refactor `exists_aInvariant_normal_isElementaryAbelian` to cite it.
- [x] Build `OddOrder.GroupTheory.MinimalInvariantNormal`.

## 完了条件

`OddOrder.GroupTheory.exists_minimal_aInvariant_normal` is sorry-free, the
existing elementary-abelian theorem still builds, and this issue is moved to
`issues/closed/`.

## 完了メモ

2026-07-06 lane d: added public `exists_minimal_aInvariant_normal` and refactored the existing elementary-abelian theorem to use it.
`lake build OddOrder.GroupTheory.MinimalInvariantNormal` passed.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private
  `exists_minimal_normal_aInvariant`
- `OddOrder/GroupTheory/MinimalInvariantNormal.lean`
