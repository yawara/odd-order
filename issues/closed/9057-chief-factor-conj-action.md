---
id: 9057
slug: chief-factor-conj-action
title: "Move chief-factor conjugation action bridge to shared API"
created: 2026-07-07
---

# Move chief-factor conjugation action bridge to shared API

## 背景

BG §1 S03c/S03h use a generic conjugation action of `G` on a chief-factor quotient
`U/V` and the bridge identifying pointwise-trivial action with membership in
`chiefFactorCentralizer U V`.  The bridge belongs with the existing centralizer API in
`OddOrder.GroupTheory.ChiefFactor` so downstream lanes can cite it without rebuilding a local model.

## やったこと

- Added `chiefFactorConjAction` in `OddOrder.GroupTheory.ChiefFactor`.
- Added `chiefFactorConjAction_smul_mk` for coset-level conjugation reduction.
- Added `chiefFactorConjAction_smul_eq_self_iff_mem`, identifying trivial action on `U/V` with
  membership in `chiefFactorCentralizer U V`.

## 完了条件

- [x] Shared API is in `OddOrder/GroupTheory/ChiefFactor.lean`.
- [x] No BG/Peterfalvi S-file was edited.
- [x] `lake build OddOrder.GroupTheory.ChiefFactor` succeeds.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03c_Thm37.lean` has the original local bridge.
- `OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean` is a downstream consumer candidate.
