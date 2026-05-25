---
id: 22
slug: peterfalvi-brauer-permutation
title: "Peterfalvi Part I: Brauer permutation lemma stubを解消する"
created: 2026-05-25
---

# Peterfalvi Part I: Brauer permutation lemma stubを解消する

## 背景

Peterfalvi §3 (1.1) と §6 (4.5.b) で使う Brauer permutation lemma
([Is] Thm 6.32) の stub を解消する。通常は second orthogonality /
character table の可逆性を使うため、issue 0021 の後続として扱う。

## やること

- [x] `ConjClasses.inv` / `ConjClasses.IsReal` API が proof に十分か確認する。
- [ ] `OddOrder.RepresentationTheory.brauer_permutation_lemma` を `sorry` なしにする。
- [x] Peterfalvi §3 (1.1) 用の odd-order specialization を追加するか、別 issue に切る。
- [ ] §6 (4.5.b) で再利用できる statement 名と namespace を維持する。

## 2026-05-25 update

- class-side odd-order API を追加:
  - `ConjClasses.eq_one_of_isConj_inv_of_odd_card`
  - `ConjClasses.eq_one_of_isReal_of_odd_card`
  - `ConjClasses.card_realClasses_eq_one_of_odd_card`
- これで Brauer permutation lemma の後に必要になる
  `Nat.card { C : ConjClasses G // ConjClasses.IsReal C } = 1` 側は
  `sorry` なしで利用できる。
- character-side の「実既約は trivial のみ」は
  `card_realIrreducibleCharacters_eq_one_of_odd_card` で cardinal 形まで追加した。
  unique real character が trivial character であることの明示は、trivial-character
  API の後続として残す。

## 完了条件

- `BrauerPermutation.lean` の `brauer_permutation_lemma` から `sorry` が消える。
- `lake build OddOrder.GroupTheory.RepresentationTheory.BrauerPermutation` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0020-peterfalvi-part1-character-stubs.md`
- depends on: `issues/0021-peterfalvi-second-orthogonality.md`
- `OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean`
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `notes/peterfalvi/s06_dade_certain_subgroup.md`
