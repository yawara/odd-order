---
id: 9306
slug: commutator-le-agemo-two-one
title: "G' ≤ Agemo G 2 1 shared lemma"
created: 2026-07-20
---

# G' ≤ Agemo G 2 1 shared lemma

## 背景

Higman, *Suzuki 2-groups*, Lemma 8 (p. 87) で、有限 `2`-group `C` の
平方部分群と導来部分群を比較する。任意の群について、平方で生成される商は
指数 `2`、従って可換なので `G' ≤ Agemo G 2 1` が成り立つ。Higman 固有でない
shared API として先に配置する。

## やること

- [x] mathlib / `OddOrder` 内の重複を検索する
- [x] `OddOrder/GroupTheory/OmegaSubgroup.lean` に一般補題を証明する
- [x] Higman Lemma 8 の cover bridge からこの補題を直接引用する

## 完了条件

- 新規 `sorry` / `axiom` なし
- reusable leaf と Higman consumer の対象 build が green

## 参照

- `issues/2048-pf-suzuki-lemma5.md`
- `references/higman/pages/suzuki-2-groups-p087.png`
- `OddOrder/GroupTheory/OmegaSubgroup.lean`
