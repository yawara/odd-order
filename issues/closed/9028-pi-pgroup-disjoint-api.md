---
id: 9028
slug: pi-pgroup-disjoint-api
title: "claim: Ch03 π/p-group membership and disjointness API (lane d)"
created: 2026-07-06
---

# claim: Ch03 π/p-group membership and disjointness API (lane d)

## 背景

BG §1 `S01_Solvable.lean` has private helpers:

- `subgroup_isPiGroup_of_isPGroup_of_mem`
- `inf_eq_bot_of_isPiGroup_of_isPGroup_not_mem`

D lane needs shared-infra output outside BG/Peterfalvi S-files. Existing public API has
singleton conversions in Ch04, but Ch03 owns `Subgroup.IsPiGroup` and cannot import Ch04
without a cycle. Port the small p-group-to-π-group proof directly to Ch03 and expose the
intersection consequence there.

## やること

- [x] Add public `Subgroup.IsPiGroup.of_isPGroup_of_mem`.
- [x] Add public `Subgroup.IsPiGroup.inf_eq_bot_of_isPGroup_not_mem`.
- [x] Build `OddOrder.Isaacs.Ch03_SplitExtensions.Main`.

## 完了条件

Both lemmas are sorry-free, the Ch03 leaf builds, and the issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`

## 完了メモ

2026-07-06 lane d: added both public Ch03 lemmas, with the intersection lemma placed after
`Nat.coprime_of_isPiGroup_of_isPiGroup_compl` to preserve Lean declaration order. Verified by
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main`.
