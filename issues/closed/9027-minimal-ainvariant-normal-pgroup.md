---
id: 9027
slug: minimal-ainvariant-normal-pgroup
title: "claim: GroupTheory minimal A-invariant normal p-group witness API (lane d)"
created: 2026-07-06
---

# claim: GroupTheory minimal A-invariant normal p-group witness API (lane d)

## 背景

BG §1 has a private `exists_prime_isPGroup_of_minimal_normal_aInvariant`: after
commutativity, a Sylow subgroup of a minimal nontrivial `A`-invariant normal
subgroup is characteristic, so its image is again normal and invariant; minimality
forces the Sylow subgroup to be all of the subgroup. 9025/9026 exposed the
minimal witness and commutativity steps, so this p-group witness is the next
shared `MinimalInvariantNormal` API.

## やること

- [x] Add public `exists_prime_isPGroup_of_minimal_aInvariant_normal`.
- [x] Refactor `exists_aInvariant_normal_isElementaryAbelian` to cite it for the
  prime choice.
- [x] Build `OddOrder.GroupTheory.MinimalInvariantNormal`.

## 完了条件

`OddOrder.GroupTheory.exists_prime_isPGroup_of_minimal_aInvariant_normal` is
sorry-free, the existing elementary-abelian theorem still builds, and this issue
is moved to `issues/closed/`.

## 完了メモ

2026-07-06 lane d: added public `exists_prime_isPGroup_of_minimal_aInvariant_normal` and refactored the elementary-abelian proof to take the prime from it.
`lake build OddOrder.GroupTheory.MinimalInvariantNormal` passed.

## 参照

- issue 9025: public minimal invariant normal witness
- issue 9026: public minimal invariant normal commutativity
- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private
  `exists_prime_isPGroup_of_minimal_normal_aInvariant`
