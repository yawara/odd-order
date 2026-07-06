---
id: 9033
slug: subgroup-map-nilpotent-api
title: "claim: subgroup image nilpotence API (lane d)"
created: 2026-07-06
---

# claim: subgroup image nilpotence API (lane d)

## 背景

BG §1 `S01_Solvable.lean` has private `isNilpotent_subgroup_map`. Repo-wide
search showed the same argument is otherwise repeated ad hoc via `nilpotent_of_surjective`.
The statement is generic subgroup infrastructure: if `K` is nilpotent, then `K.map f` is
nilpotent for any group homomorphism `f`.

## やること

- [x] Add public `Subgroup.isNilpotent_map`.
- [x] Build `OddOrder.Mathlib.Subgroup`.

## 完了条件

The lemma is sorry-free, the target leaf build passes, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Mathlib/Subgroup.lean`

## 完了メモ

2026-07-06 lane d: added public `Subgroup.isNilpotent_map`, proved by restricting the
homomorphism to a surjective map from `K` onto `K.map f` and applying
`nilpotent_of_surjective`. Verified by `lake build OddOrder.Mathlib.Subgroup`.
