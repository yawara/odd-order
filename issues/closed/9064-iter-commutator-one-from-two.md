---
id: 9064
slug: iter-commutator-one-from-two
title: "Move iterCommutator one-from-two coprime corollary to Isaacs Ch04"
created: 2026-07-07
closed: 2026-07-07
---

# Move iterCommutator one-from-two coprime corollary to Isaacs Ch04

## 背景

BG §1 Prop. 1.6(c) is the reusable Γ-form coprime action corollary: if the second iterated commutator is trivial, then the first is trivial.
It is a direct consequence of Isaacs Ch04 Lemma 4.29 and belongs in the Ch04 action-commutator API rather than remaining BG-local.

## 重複確認

- open/closed 9000 issue scan: exact claim は本 issue のみ。
- allowed area scan: exact `iterCommutator_inl_inr_one_eq_bot_of_two_eq_bot` は未存在。
- dependency `iterCommutator_inl_inr_two_eq_one` is already present in `OddOrder.Isaacs.Ch04`.

## 完了内容

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に public theorem
  `OddOrder.Isaacs.Ch04.iterCommutator_inl_inr_one_eq_bot_of_two_eq_bot` を追加。
- Proof is the same two-line consequence of `iterCommutator_inl_inr_two_eq_one` and the supplied second-commutator triviality.
- BG/Peterfalvi S-file は未編集。

## 検証

- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` 成功。
  既存 linter warning のみ。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: original BG Prop. 1.6(c) theorem.
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: shared-infra destination.
