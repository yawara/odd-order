---
id: 9062
slug: action-commutator-fitting-fixed
title: "Move action commutator Fitting fixed-points theorem to Isaacs Ch04"
created: 2026-07-07
closed: 2026-07-07
---

# Move action commutator Fitting fixed-points theorem to Isaacs Ch04

## 背景

BG §1 Prop. 1.4 の kernel form は、coprime automorphism group が `F(G)` を pointwise に固定すれば可解群 `G` 全体への作用が自明になるという shared action-commutator theorem。
BG/Peterfalvi S-file を直接編集せず、allowed area の `OddOrder.Isaacs.Ch04` へ移して downstream から再利用可能にする。

## 重複確認

- open/closed 9000 issue scan: exact claim は本 issue のみ。
- allowed area scan: `OddOrder/Isaacs/**`, `OddOrder/GroupTheory/**`, `OddOrder/Mathlib/**` に exact `actionCommutator_eq_bot_of_fitting_le_fixedPoints` は未存在。
- related API: `actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime` と `centralizer_fitting_le_fitting` は Ch04 に存在し、本 theorem の証明入力として使用可能。

## 完了内容

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に public theorem
  `OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_fitting_le_fixedPoints` を追加。
- 証明は BG S01 の sorry-free proof を Ch04 API に合わせて移植し、`actionCommutator` が `C_G(F(G))` に入ること、`centralizer_fitting_le_fitting` による `≤ F(G)`、最後に coprime self-trivial criterion を使う形にした。
- BG/Peterfalvi S-file は未編集。

## 検証

- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` 成功。
  既存 linter warning のみ。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: original BG Prop. 1.4 theorem.
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: shared-infra destination.
- `issues/closed/9061-centralizer-fitting-self.md`: dependency moved immediately before this issue.
