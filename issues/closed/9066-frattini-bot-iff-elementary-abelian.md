---
id: 9066
slug: frattini-bot-iff-elementary-abelian
title: "Move Frattini bot iff elementary abelian criterion to Isaacs Ch04"
created: 2026-07-07
closed: 2026-07-07
---

# Move Frattini bot iff elementary abelian criterion to Isaacs Ch04

## 背景

BG §1 Lemma 1.7(c) states the finite p-group criterion `Φ(R)=1 ↔ R is elementary abelian`.
The forward/reverse directions are a bottom-subgroup specialization of Isaacs Ch04 Lemma 4.5 plus the existing elementary-abelian quotient-bot transport, so the reusable iff belongs next to Lemma 4.5 in Ch04.

## 重複確認

- open/closed 9000 issue scan: exact claim は本 issue のみ。
- allowed area scan: exact `frattini_eq_bot_iff_isElementaryAbelian` は未存在。
- Existing supporting APIs:
  - `OddOrder.Isaacs.Ch04.frattini_le_iff_isElementaryAbelian_quotient_of_pgroup`
  - `OddOrder.GroupTheory.IsElementaryAbelian.quotient_bot`
- BG-local pure wrappers `quotient_frattini_isElementaryAbelian`, `isElementaryAbelian_of_frattini_eq_bot`, and `commutator_sup_pow_closure_le_frattini` are documented in issue 0037 and were not duplicated.

## 完了内容

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に public theorem
  `OddOrder.Isaacs.Ch04.frattini_eq_bot_iff_isElementaryAbelian` を追加。
- Proof uses the existing Ch04 Frattini quotient equivalence at `N = ⊥`, `QuotientGroup.quotientBot`, and `IsElementaryAbelian.quotient_bot`.
- BG/Peterfalvi S-file は未編集。

## 検証

- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` 成功。
  既存 linter warning のみ。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: original BG Lemma 1.7(c) theorem.
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: shared-infra destination.
- `issues/closed/9037-elementary-abelian-quotient-bot.md`: existing quotient-bot helper.
- `issues/0037-duplicate-wrapper-theorems.md`: wrappers intentionally not duplicated.
