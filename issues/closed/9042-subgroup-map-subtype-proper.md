---
id: 9042
slug: subgroup-map-subtype-proper
title: "Public subtype-map proper subgroup API"
created: 2026-07-06
---

# Public subtype-map proper subgroup API

## 背景

BG S03d uses a private helper `map_subtype_lt_of_ne_top`: if `N < ⊤` as a
subgroup of `K`, then `N.map K.subtype < K` in the ambient group.  The same
pattern appears locally in BG S04d as an inline proof with `range_subtype` and
`map_injective`.

Dup scan:

- No public `Subgroup.map_subtype_lt_of_ne_top` exists in `OddOrder/Mathlib`,
  `OddOrder/Isaacs`, `OddOrder/GroupTheory`, or mathlib.
- The existing occurrences are private/local proof fragments in BG S-files.
- This is generic subgroup API, so lane d can expose it upstream without
  editing BG/Peterfalvi S-files.

## やること

- [x] Add public `Subgroup.map_subtype_lt_of_ne_top` in `OddOrder/Mathlib/Subgroup.lean`.
- [x] Build `OddOrder.Mathlib.Subgroup`.
- [x] Close this issue and commit the feature unit.

## 完了条件

`lake build OddOrder.Mathlib.Subgroup` passes with the new sorry-free theorem.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean`
- `OddOrder/BG/Ch1_Preliminary/S04d_GorThm415.lean`

## 完了メモ

Implemented `Subgroup.map_subtype_lt_of_ne_top` in shared Mathlib-side infra.
Verification: `lake build OddOrder.Mathlib.Subgroup`.
