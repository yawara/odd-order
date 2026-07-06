---
id: 9046
slug: subrepresentation-prime-kernel
title: "Prime fixed-free subrepresentation kernel API"
created: 2026-07-06
---

# Prime fixed-free subrepresentation kernel API

## 背景

BG S03d の局所 helper `ker_subrep_inf_complement_prime_eq_bot` を、
prime-order subgroup が fixed-point-freely に作用する任意の非零 subrepresentation の
kernel API として `OddOrder.GroupTheory.RepresentationTheory` 側へ上げる。

## やること

- [x] open 9000 issue と既存 representation API を確認する
- [x] `SubrepresentationKernel.lean` に sorry-free 補題を追加する
- [x] representation aggregator から import する
- [x] leaf と aggregator build を通す

## 完了条件

`lake build OddOrder.GroupTheory.RepresentationTheory.SubrepresentationKernel` と
`lake build OddOrder.GroupTheory.RepresentationTheory` が通り、BG/Peterfalvi S-file に触らず
public shared-infra API が利用可能になる。

## 参照

- `OddOrder/GroupTheory/RepresentationTheory/SubrepresentationKernel.lean`
- `OddOrder/GroupTheory/RepresentationTheory.lean`
- `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean`
