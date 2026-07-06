---
id: 9058
slug: fixedpoints-quotient-mulaut-map
title: "Move quotient MulAut fixed-points map API to Isaacs Ch04"
created: 2026-07-07
---

# Move quotient MulAut fixed-points map API to Isaacs Ch04

## 背景

`fixedPointsOfMulAut_quotientMulAutHom_eq_map` is the subgroup form of Isaacs Corollary 3.28 / BG
Proposition 1.5(d): fixed points on an invariant quotient are the quotient image of fixed points
upstairs under coprime action.  It is currently a BG S03h-local theorem but is cited from multiple
BG consumers, so it belongs with the Ch04 coprime-action quotient API.

## やったこと

- Added `OddOrder.Isaacs.Ch04.fixedPointsOfMulAut_quotientMulAutHom_eq_map` next to the
  `quotientMulAutHom` API.
- Reused the existing element-level `coprime_fixedPoints_quotient` proof.
- Left BG/Peterfalvi S-files untouched.

## 完了条件

- [x] Shared API is in `OddOrder/Isaacs/Ch04_Commutators/Main.lean`.
- [x] No BG/Peterfalvi S-file was edited.
- [x] `lake build OddOrder.Isaacs.Ch04_Commutators.Main` succeeds.

## 参照

- Original local theorem: `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean`.
- Known downstream references: BG S03g and BG S15.
