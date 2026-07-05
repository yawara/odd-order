---
id: 9012
slug: class-two-square-index
title: "shared infra claim: faithful irr existence (|Z|=p) + class-2 square index (Pf 11.7 case-b kernel)"
created: 2026-07-05
---

# shared infra claim: faithful irr existence (|Z|=p) + class-2 square index (Pf 11.7 case-b kernel)

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

## 2026-07-05 lane-a: 納品済み (commit 12aca9b8)

`OddOrder/GroupTheory/RepresentationTheory/ClassTwoSquareIndex.lean` — 全部 sorry-free:
- exists_mem_center_of_normal_of_isPGroup (p-群 normal-meets-center, 存在形)
- exists_irreducibleCharacter_apply_ne (指標による z ≠ 1 分離)
- exists_faithful_irreducible_of_card_center_eq_prime (|Z|=p → 忠実既約存在)
- card_quotient_center_isSquare_of_class_two (|P:Z| 完全平方)
- even_of_isSquare_prime_pow / even_of_card_eq_prime_pow_succ_of_class_two ((11.7) 消費形)

consumer: S13 (11.7) H_elementaryAbelian の Galois case。S08 の
isNilpotent_normal_inf_center_ne_bot と役割が近い (nilpotent 一般 vs p-群+存在形) が、
GroupTheory→Peterfalvi の逆 import を避けるため p-群版を local に実証明 (重複でなく別 statement)。
