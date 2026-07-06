---
id: 9059
slug: conj-action-subtype-bridges
title: "Move conjugation action subtype bridges to Isaacs Ch04"
created: 2026-07-07
---

# Move conjugation action subtype bridges to Isaacs Ch04

## 背景

BG S06 provides generic bridges identifying the abstract `actionCommutator` and
`fixedPointsOfMulAut` for the conjugation action of `K` on a normalized subgroup `P` with ambient
subgroups in `Γ`.  These bridges are cited by S03h, S12/S13, and S15, so they belong with the Ch04
action-commutator API rather than in a BG S-file.

## やったこと

- Added `OddOrder.Isaacs.Ch04.actionCommutator_conj_map_subtype`.
- Added `OddOrder.Isaacs.Ch04.fixedPointsOfMulAut_conj_map_subtype`.
- Left BG/Peterfalvi S-files untouched.

## 完了条件

- [x] Shared API is in `OddOrder/Isaacs/Ch04_Commutators/Main.lean`.
- [x] No BG/Peterfalvi S-file was edited.
- [x] `lake build OddOrder.Isaacs.Ch04_Commutators.Main` succeeds.

## 参照

- Original local bridge: `OddOrder/BG/Ch1_Preliminary/S06_Additional.lean`.
- Known downstream references: BG S03h, S12/S13, and S15.
