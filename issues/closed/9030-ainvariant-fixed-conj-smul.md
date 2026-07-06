---
id: 9030
slug: ainvariant-fixed-conj-smul
title: "claim: Ch03 A-invariant fixed conjugation transport API (lane d)"
created: 2026-07-06
---

# claim: Ch03 A-invariant fixed conjugation transport API (lane d)

## 背景

BG §1 `S01_Solvable.lean` has private
`isAInvariant_mulAut_conj_smul_of_fixed`, used in the top-preimage branch of
BG Prop. 1.5(b). This is a general Ch03 `IsAInvariant` transport fact:
conjugating an invariant subgroup by an element fixed by every operator preserves
invariance.

## やること

- [x] Add public `IsAInvariant.mulAut_conj_smul_of_fixed` to Ch03.
- [x] Build `OddOrder.Isaacs.Ch03_SplitExtensions.Main`.

## 完了条件

The lemma is sorry-free, Ch03 leaf build passes, and this issue is moved to
`issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`

## 完了メモ

2026-07-06 lane d: added public `IsAInvariant.mulAut_conj_smul_of_fixed` in Ch03.
The proof uses the existing pointwise subgroup action definition directly, avoiding a new duplicate
public wrapper for `MulAut` subgroup images. Verified by
`lake build OddOrder.Isaacs.Ch03_SplitExtensions.Main`.
