---
id: 9043
slug: ainvariant-map-subtype-normalizer
title: "Public A-invariant subtype-map normalizer API"
created: 2026-07-06
---

# Public A-invariant subtype-map normalizer API

## 背景

BG S03f exposes generic normalizer transport helpers for `IsAInvariant`, and
`OddOrder/GroupTheory/AInvariantComplement.lean` currently imports BG S03f only
to cite `OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_smul_val`.

Dup scan:

- The exact generic helper exists only in a BG S-file namespace.
- `GroupTheory/AInvariantComplement` is a shared consumer and should not depend
  on the S03f preliminary leaf for this generic transport step.
- The natural home is next to `IsAInvariant.smul_mem` / `inv_smul_mem` in
  `OddOrder.Isaacs.Ch03`.

## やること

- [x] Add public `IsAInvariant.mem_normalizer_map_subtype_of_smul_val` in
  `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`.
- [x] Rewire `OddOrder/GroupTheory/AInvariantComplement.lean` to cite the new API and narrow
  its BG import from S03f to S01.
- [x] Build `OddOrder.GroupTheory.AInvariantComplement`.
- [x] Close this issue and commit the feature unit.

## 完了条件

`lake build OddOrder.GroupTheory.AInvariantComplement` passes, with no direct
dependency on `OddOrder.BG.Ch1_Preliminary.S03f_Prelim`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03f_Prelim.lean`
- `OddOrder/GroupTheory/AInvariantComplement.lean`

## 完了メモ

Implemented `IsAInvariant.mem_normalizer_map_subtype_of_smul_val` in Isaacs Ch03 and rewired
`AInvariantComplement` to use it, replacing the direct S03f import with S01.
Verification: `lake build OddOrder.GroupTheory.AInvariantComplement`.
