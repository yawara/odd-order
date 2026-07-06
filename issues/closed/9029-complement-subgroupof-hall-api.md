---
id: 9029
slug: complement-subgroupof-hall-api
title: "claim: subgroupOf complement and Hall-from-complement API (lane d)"
created: 2026-07-06
---

# claim: subgroupOf complement and Hall-from-complement API (lane d)

## 背景

BG §1 `S01_Solvable.lean` has private helpers:

- `isComplement_subgroupOf_of_disjoint_mul_eq_univ`
- `isHallSubgroup_subgroupOf_of_complement_pi_pi'`

The first is a generic `Subgroup` ambient-subgroup complement packaging lemma. The second
belongs to the Ch03 Hall/π-group API and should cite the generic lemma and existing
`Subgroup.IsPiGroup.subgroupOf`/`IsComplement'.index_eq_card` facts.

## やること

- [x] Add public `Subgroup.isComplement'_subgroupOf_of_disjoint_mul_eq_univ`.
- [x] Add public `OddOrder.Isaacs.Ch03.isHallSubgroup_subgroupOf_of_complement_pi_pi'`.
- [x] Build `OddOrder.Mathlib.Subgroup`.
- [x] Build `OddOrder.Isaacs.Ch03_SplitExtensions.Main`.

## 完了条件

Both lemmas are sorry-free, both target leaf builds pass, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Mathlib/Subgroup.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`

## 完了メモ

2026-07-06 lane d: added the generic `Subgroup` complement packaging lemma and the
Ch03 Hall-from-π/π'-complement lemma. The Ch03 lemma is placed after
`Subgroup.IsPiGroup.subgroupOf` to respect Lean declaration order. Verified by:

- `lake build OddOrder.Mathlib.Subgroup`
- `lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main`
