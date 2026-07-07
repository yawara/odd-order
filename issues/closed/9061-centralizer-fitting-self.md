---
id: 9061
slug: centralizer-fitting-self
title: "Move Fitting self-centralizing theorem to Isaacs Ch04"
created: 2026-07-07
closed: 2026-07-07
---

# Move Fitting self-centralizing theorem to Isaacs Ch04

## 背景

BG §1 Prop. 1.3 の `centralizer_fitting_le_fitting` は有限可解群の Fitting subgroup が self-centralizing であることを述べる shared-infra theorem。
BG/Peterfalvi S-file を直接触らず downstream から再利用できるよう、allowed area の `OddOrder.Isaacs.Ch04` に移す。

## 重複確認

- open/closed 9000 issue scan: exact claim は本 issue のみ。
- allowed area scan: `OddOrder/Isaacs/**`, `OddOrder/GroupTheory/**`, `OddOrder/Mathlib/**` に exact `centralizer_fitting_le_fitting` は未存在。
- 近傍 API として `OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean` に minimal-normal/Fitting centralizer 系はあるが、self-centralizing conclusion そのものではない。

## 完了内容

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に public theorem
  `OddOrder.Isaacs.Ch04.centralizer_fitting_le_fitting` を追加。
- 証明は BG S01 の sorry-free proof を移植し、必要な局所 helper
  `exists_minimal_normal_le_not_le` と
  `inf_subgroupOf_le_center_of_le_centralizer` を Ch04 内 private helper として保持。
- BG/Peterfalvi S-file は未編集。

## 検証

- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` 成功。
  既存 linter warning のみ。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: original BG Prop. 1.3 theorem.
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: shared-infra destination.
