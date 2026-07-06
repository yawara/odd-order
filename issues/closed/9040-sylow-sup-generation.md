---
id: 9040
slug: sylow-sup-generation
title: "Public finite group Sylow supremum generation API"
created: 2026-07-06
---

# Public finite group Sylow supremum generation API

## 背景

BG §1 `S03d_Thm34.lean` has a private `sylow_choice_iSup_eq_top`, and Isaacs
Ch04 has a private `iSup_sylow_eq_top`. Both are generic finite Sylow generation
facts and belong in the Ch01 Sylow API.

## やること

- [x] Add public `OddOrder.Isaacs.Ch01.sylow_choice_iSup_eq_top`.
- [x] Add public `OddOrder.Isaacs.Ch01.iSup_sylow_eq_top`.
- [x] Build `OddOrder.Isaacs.Ch01_Sylow.Main`.

## 完了条件

Both lemmas are sorry-free, the target leaf build passes, and this issue is moved
to `issues/closed/`.

## 参照

- `OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean`
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`
- `OddOrder/Isaacs/Ch01_Sylow/Main.lean`


## 完了メモ

2026-07-06 lane d: added public Sylow supremum generation lemmas to Ch01.
Verified by `lake build OddOrder.Isaacs.Ch01_Sylow.Main`.
