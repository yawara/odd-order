---
id: 9067
slug: frattini-commutator-pow-closure
title: "Move Frattini commutator/power closure equality to Isaacs Ch04"
created: 2026-07-07
closed: 2026-07-07
---

# Move Frattini commutator/power closure equality to Isaacs Ch04

## 背景

BG §1 Lemma 1.7(d) gives the finite p-group formula `Φ(R) = R' ⊔ ⟨x^p | x ∈ R⟩`.
The reverse inclusion is an application of Isaacs Ch04 Lemma 4.5 to the quotient by
`K = R' ⊔ ⟨x^p | x ∈ R⟩`, so the reusable API belongs in Ch04 next to the Frattini quotient criterion.

## 重複確認

- open/closed 9000 issue scan: exact claim は本 issue のみ。
- allowed area scan: exact `frattini_le_commutator_sup_pow_closure` / `commutator_sup_pow_closure_eq_frattini` は未存在。
- Existing support used:
  - `OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup`
  - `OddOrder.Isaacs.Ch04.pow_p_mem_frattini_of_pgroup`
  - `OddOrder.Isaacs.Ch04.frattini_le_iff_isElementaryAbelian_quotient_of_pgroup`
  - `Subgroup.pow_closure_characteristic`
- Existing `OddOrder.GroupTheory.IsPGroup.commutator_sup_pow_closure_le_frattini` was not imported into Ch04; the Ch04 version is proved from Ch04 local facts rather than added as a wrapper.

## 完了内容

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に public theorem を追加:
  - `commutator_sup_pow_closure_le_frattini`
  - `frattini_le_commutator_sup_pow_closure`
  - `commutator_sup_pow_closure_eq_frattini`
- BG/Peterfalvi S-file は未編集。

## 検証

- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` 成功。
  既存 linter warning のみ。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: original BG Lemma 1.7(d) local theorem.
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: shared-infra destination.
- `issues/closed/9038-pow-closure-characteristic.md`: public power-closure characteristic support.
- `issues/closed/9066-frattini-bot-iff-elementary-abelian.md`: preceding Lemma 1.7(c) Ch04 API.
