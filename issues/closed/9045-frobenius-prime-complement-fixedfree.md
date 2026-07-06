---
id: 9045
slug: frobenius-prime-complement-fixedfree
title: "Public prime-complement fixed-free Frobenius API"
created: 2026-07-06
---

# Public prime-complement fixed-free Frobenius API

## 背景

BG S03d に局所的に置かれていた fixed-point-free prime complement から
`IsFrobeniusGroup` を構成する補題を、BG S-file 依存なしで再利用できるよう
Isaacs Ch06 Frobenius API へ上げる。

## やること

- [x] 既存 API と open 9000 issue を確認する
- [x] `OddOrder.Isaacs.Ch06.isFrobeniusGroup_of_prime_complement_fixedFree` を追加する
- [x] `lake build OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup` を通す

## 完了条件

Ch06 leaf build が通り、BG/Peterfalvi S-file を直接触らずに public API が利用可能になる。

## 参照

- `OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean`
- `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean`
