---
id: 9044
slug: complement-prime-normal-le
title: "Public prime complement normal-subgroup containment API"
created: 2026-07-06
---

# Public prime complement normal-subgroup containment API

## 背景

BG S03d has a private group-theoretic helper
`normal_le_of_complement_prime_of_inf_eq_bot`: if `K ◁ G` has a coprime
prime-order complement `R`, then every normal `N` with `N ⊓ R = ⊥` lies in `K`.
This is the upstream step used before quotient induction in BG Theorem 3.4.

Dup scan:

- No public exact theorem with this statement exists in `OddOrder/Mathlib`,
  `OddOrder/Isaacs`, `OddOrder/GroupTheory`, or mathlib.
- Related BG Frobenius quotient lemmas are public but assume a Frobenius package
  or prove different conclusions.
- The statement uses only generic finite-group/Sylow/complement API, so Ch03 is
  an appropriate shared home.

## やること

- [x] Add public `OddOrder.Isaacs.Ch03.normal_le_of_complement_prime_of_inf_eq_bot`.
- [x] Build `OddOrder.Isaacs.Ch03_SplitExtensions.Main`.
- [x] Close this issue and commit the feature unit.

## 完了条件

`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main` passes with the new sorry-free theorem.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean`

## 完了メモ

Implemented `OddOrder.Isaacs.Ch03.normal_le_of_complement_prime_of_inf_eq_bot`
as a sorry-free Ch03 shared theorem.
Verification: `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main`.
