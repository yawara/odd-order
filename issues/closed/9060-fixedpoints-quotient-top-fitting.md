---
id: 9060
slug: fixedpoints-quotient-top-fitting
title: "Move quotient fixed-points top criterion to Isaacs Ch04"
created: 2026-07-07
---

# Move quotient fixed-points top criterion to Isaacs Ch04

## 背景

BG S03h contains a generic converse-to-step-1 criterion: if `R` normalizes `K` and
`⁅K, R⁆ ≤ F(K)`, then the induced conjugation action on `K/F(K)` has all quotient elements fixed.
After 9059 moved the conjugation-action commutator bridge into Ch04, this proof no longer needs any
BG-local dependency and belongs with the Ch04 action-commutator quotient API.

## やったこと

- Added `OddOrder.Isaacs.Ch04.fixedPoints_quotient_eq_top_of_commutator_le_fitting`.
- Used `actionCommutator_conj_map_subtype`, `actionCommutator_quotient_eq_map`, and
  `actionCommutator_eq_bot_iff_acts_trivially` from Ch04.
- Left BG/Peterfalvi S-files untouched.

## 完了条件

- [x] Shared API is in `OddOrder/Isaacs/Ch04_Commutators/Main.lean`.
- [x] No BG/Peterfalvi S-file was edited.
- [x] `lake build OddOrder.Isaacs.Ch04_Commutators.Main` succeeds.

## 参照

- Original local theorem: `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`.
- Depends on closed issue 9059's conjugation-action commutator bridge.
