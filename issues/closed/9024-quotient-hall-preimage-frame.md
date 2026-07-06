---
id: 9024
slug: quotient-hall-preimage-frame
title: "claim: Isaacs Ch04 quotient Hall preimage frame API (lane d)"
created: 2026-07-06
---

# claim: Isaacs Ch04 quotient Hall preimage frame API (lane d)

## 背景

BG §1 has a private `quotient_hall_preimage_frame`: after induction in `G/M`
produces an invariant `π`-Hall subgroup containing the image of `K`, its preimage
in `G` is invariant, contains `K`, and has `π`-free index. Existing Ch03 has
`IsHallSubgroup.map_quotient`, and 9023 added invariant quotient map/comap, but
no public preimage frame packages this recurring quotient step.

## やること

- [x] Add a public Ch04 lemma packaging invariant quotient-Hall preimages.
- [x] Build `OddOrder.Isaacs.Ch04_Commutators.Main`.

## 完了条件

`OddOrder.Isaacs.Ch03.IsAInvariant.exists_comap_quotient_hall` is sorry-free,
the Ch04 leaf build passes, and this issue is moved to `issues/closed/`.

## 完了メモ

2026-07-06 lane d: added `exists_comap_quotient_hall` in Ch04.
`lake build OddOrder.Isaacs.Ch04_Commutators.Main` passed.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private
  `quotient_hall_preimage_frame`
- issue 9023: invariant quotient map/comap transport
