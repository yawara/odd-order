---
id: 9065
slug: fixedpoints-action-commutator-complement
title: "Move fixed-points/action-commutator complement criterion to Isaacs Ch04"
created: 2026-07-07
closed: 2026-07-07
---

# Move fixed-points/action-commutator complement criterion to Isaacs Ch04

## 背景

BG §1 Prop. 1.6(d) packages Isaacs Ch04 coprime action results as an internal direct-product/complement statement for abelian `G`: `G = C_G(A) × [G,A]`.
The reusable Lean form is an `IsComplement'` criterion, so it belongs in Ch04 action-commutator API rather than remaining BG-local.

## 重複確認

- open/closed 9000 issue scan: exact claim は本 issue のみ。
- allowed area scan: exact `fixedPoints_isComplement_actionCommutator_of_abelian` は未存在。
- dependencies `fixedPoints_sup_actionCommutator_eq_top` and `fixedPoints_inf_actionCommutator_eq_bot_of_abelian` already exist in `OddOrder.Isaacs.Ch04`.

## 完了内容

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に public theorem
  `OddOrder.Isaacs.Ch04.fixedPoints_isComplement_actionCommutator_of_abelian` を追加。
- Proof packages the existing Ch04 sup and intersection facts into `Subgroup.IsComplement'`.
- BG/Peterfalvi S-file は未編集。

## 検証

- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` 成功。
  既存 linter warning のみ。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: original BG Prop. 1.6(d) theorem.
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: shared-infra destination.
