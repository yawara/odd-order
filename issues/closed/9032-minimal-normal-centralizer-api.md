---
id: 9032
slug: minimal-normal-centralizer-api
title: "claim: minimal normal not-contained and centralizer intersection API (lane d)"
created: 2026-07-06
---

# claim: minimal normal not-contained and centralizer intersection API (lane d)

## 背景

BG §1 `S01_Solvable.lean` has early private helpers for the proof of Hall's Fitting
self-centralizer proposition:

- `exists_minimal_normal_le_not_le`
- `inf_subgroupOf_le_center_of_le_centralizer`

Both are general shared infrastructure: the first is a finite normal-subgroup
minimality extraction, and the second is a subgroup/centralizer fact.

## やること

- [x] Add public `exists_normal_le_not_le_minimal` in Ch02.
- [x] Add public `Subgroup.inf_subgroupOf_le_center_of_le_centralizer`.
- [x] Build `OddOrder.Isaacs.Ch02_Subnormality.Main`.
- [x] Build `OddOrder.Mathlib.Subgroup`.

## 完了条件

Both lemmas are sorry-free, both target leaf builds pass, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch02_Subnormality/Main.lean`
- `OddOrder/Mathlib/Subgroup.lean`

## 完了メモ

2026-07-06 lane d: added public Ch02 finite normal-subgroup minimality API and a
public `Subgroup` centralizer/intersection helper. Verified by
`lake build OddOrder.Mathlib.Subgroup OddOrder.Isaacs.Ch02_Subnormality.Main`.
