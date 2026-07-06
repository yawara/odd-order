---
id: 9041
slug: subgroup-zpowers-prime-card
title: "Public prime-card subgroup generator API"
created: 2026-07-06
---

# Public prime-card subgroup generator API

## 背景

BG S03d has a local/public helper
`OddOrder.BG.Ch1.S03d.zpowers_eq_of_prime_card`: if `R ≤ G` has prime order,
then any nonidentity `r ∈ R` generates `R`.  S03e already consumes it, and the
same pattern appears repeatedly in BG/Peterfalvi prime-order cyclic arguments.

Dup scan:

- mathlib has the type-level `zpowers_eq_top_of_prime_card`.
- No `Subgroup.zpowers_eq_of_prime_card` exists in `OddOrder/Mathlib`,
  `OddOrder/Isaacs`, `OddOrder/GroupTheory`, or mathlib.
- Existing BG S03d theorem is in a downstream S-file, so lane d should expose the
  ambient-subgroup form in shared infra rather than editing BG/Peterfalvi files.

## やること

- [x] Add public `Subgroup.zpowers_eq_of_prime_card` in `OddOrder/Mathlib/Subgroup.lean`.
- [x] Build `OddOrder.Mathlib.Subgroup`.
- [x] Close this issue and commit the feature unit.

## 完了条件

`lake build OddOrder.Mathlib.Subgroup` passes with the new sorry-free theorem.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean`
- `OddOrder/BG/Ch1_Preliminary/S03e_Thm35.lean`
- `notes/bg/s03_thm34.md`

## 完了メモ

Implemented `Subgroup.zpowers_eq_of_prime_card` in shared Mathlib-side infra.
Verification: `lake build OddOrder.Mathlib.Subgroup`.
