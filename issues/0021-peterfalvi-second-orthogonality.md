---
id: 21
slug: peterfalvi-second-orthogonality
title: "Peterfalvi Part I: second orthogonality stubsを解消する"
created: 2026-05-25
---

# Peterfalvi Part I: second orthogonality stubsを解消する

## 背景

Peterfalvi §3 (1.2) と Brauer permutation lemma の proof route で使う
column orthogonality の stub を解消する。これが Wave 1a character-theory
stub 群の最初の依存で、issue 0022 より先に片付ける。

## やること

- [ ] `OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality.column_orthogonality_conj`
      を `sorry` なしにする。
- [ ] `OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality.column_orthogonality_not_conj`
      を `sorry` なしにする。
- [ ] 必要なら irreducible character indexing API を小さく追加する。
- [ ] 既存 statement の `[Fintype {φ // IsIrreducibleCharacter φ}]` 仮定が妥当か確認し、
      変更するなら downstream (`BrauerPermutation`) も同時に追従する。

## 完了条件

- `SecondOrthogonality.lean` の上記 2 theorem から `sorry` が消える。
- `lake build OddOrder.GroupTheory.RepresentationTheory.SecondOrthogonality` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0020-peterfalvi-part1-character-stubs.md`
- downstream: `issues/0022-peterfalvi-brauer-permutation.md`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
