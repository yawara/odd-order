---
id: 9107
slug: prime-order-subgroup-lemmas
title: "shared: PrimeOrderSubgroups.lean — 位数 p 部分群の基礎 2 補題 (lane c claim)"
created: 2026-07-17
---

# shared: PrimeOrderSubgroups.lean (lane c claim)

Isaacs Thm 10.15 (issue 3007) の部品として lane c が新設 claim。

- `normal_le_center_of_card_eq_prime`: p-群 P の正規部分群 Y, |Y| = p ⇒ Y ≤ Z(P)。
  (conj 準同型 P →* MulAut Y の像は p-群かつ |MulAut Y| = p−1 と互いに素 ⇒ 自明)
- `subgroup_eq_of_card_eq_prime_of_isCyclic`: cyclic ambient H の位数 p 部分群は一意
  (元は全て x^p = 1、`IsCyclic.card_pow_eq_one_le` で高々 p 個)。

検索済: repo (`le_center` 系 grep)・mathlib (PGroup.lean / SpecificGroups/Cyclic.lean)
に既存なし (2026-07-17)。
