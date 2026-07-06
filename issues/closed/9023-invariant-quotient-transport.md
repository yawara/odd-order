---
id: 9023
slug: invariant-quotient-transport
title: "claim: Isaacs Ch04 IsAInvariant quotient transport API (lane d)"
created: 2026-07-06
---

# claim: Isaacs Ch04 IsAInvariant quotient transport API (lane d)

## 背景

BG §1 has private quotient-action transport helpers for `IsAInvariant`:
`isAInvariant_map_mk'` and `isAInvariant_comap_mk'`. They are genuine shared
Isaacs/Ch04 API around `IsAInvariant.quotientMulAutHom`, not BG-specific proof
body. Open-9000 scan and existing API search found Hall/pi quotient APIs and
subgroup-of restriction APIs, but no public `IsAInvariant` quotient map/comap
transport.

## やること

- [x] Add public Ch04 lemmas for invariant image/preimage under
  `IsAInvariant.quotientMulAutHom`.
- [x] Build `OddOrder.Isaacs.Ch04_Commutators.Main`.

## 完了条件

`OddOrder.Isaacs.Ch03.IsAInvariant.map_quotient` and
`OddOrder.Isaacs.Ch03.IsAInvariant.comap_quotient` are sorry-free, the Ch04 leaf
build passes, and this issue is moved to `issues/closed/`.

## 完了メモ

2026-07-06 lane d: added `map_quotient` and `comap_quotient` in Ch04.
`lake build OddOrder.Isaacs.Ch04_Commutators.Main` passed.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: private
  `isAInvariant_map_mk'`, `isAInvariant_comap_mk'`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: `IsAInvariant.quotientMulAutHom`
