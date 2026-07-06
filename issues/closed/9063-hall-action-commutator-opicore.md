---
id: 9063
slug: hall-action-commutator-opicore
title: "Move A-invariant Hall action commutator oPiCore criterion to Isaacs Ch04"
created: 2026-07-07
closed: 2026-07-07
---

# Move A-invariant Hall action commutator oPiCore criterion to Isaacs Ch04

## 背景

BG §1 Prop. 1.5(a)/(e) の A-invariant Hall existence と action-commutator `≤ O_π(G)` criterion は、後続 BG/Peterfalvi で Hall complement と coprime action を接続する shared infra。
BG/Peterfalvi S-file を直接編集せず、allowed area の `OddOrder.Isaacs.Ch04` に reusable theorem として移す。

## 重複確認

- open/closed 9000 issue scan: exact claim は本 issue のみ。
- allowed area scan:
  - `OddOrder.Isaacs.Ch03.HallSubgroups`, `HallSubgroups.conjAction_pretransitive`, `IsHallSubgroup.mulAut_smul` は既に存在。
  - complementary Hall API `IsHallSubgroup.card_coprime_of_compl`, `index_coprime_of_compl`, `card_mul_of_compl`, `isComplement_of_compl` も既に存在。
  - exact `exists_aInvariant_hall` と `actionCommutator_le_oPiCore_of_fixedPoints_contains_hallComplement` は allowed area には未存在。

## 完了内容

- `OddOrder/Isaacs/Ch04_Commutators/Main.lean` に public theorem
  `OddOrder.Isaacs.Ch04.exists_aInvariant_hall` を追加。
- 同ファイルに public theorem
  `OddOrder.Isaacs.Ch04.actionCommutator_le_oPiCore_of_fixedPoints_contains_hallComplement` を追加。
- 証明は既存 Ch03 HallSubgroups action/pretransitivity API と complementary Hall API を再利用し、BG S01 の private helper 群を再作成しない形に整理。
- Hall subgroup pointwise action のため Ch04 で `open scoped Pointwise` を追加。
- BG/Peterfalvi S-file は未編集。

## 検証

- `lake build OddOrder.Isaacs.Ch04_Commutators.Main` 成功。
  既存 linter warning のみ。

## 参照

- `OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean`: original BG Prop. 1.5(a)/(e) theorem.
- `OddOrder/Isaacs/Ch03_SplitExtensions/Main.lean`: reused HallSubgroups and complementary Hall API.
- `OddOrder/Isaacs/Ch04_Commutators/Main.lean`: shared-infra destination.
- `issues/closed/9031-hall-subgroups-action-api.md`: existing HallSubgroups action API.
- `issues/closed/9020-complementary-hall-api.md`: existing complementary Hall API.
