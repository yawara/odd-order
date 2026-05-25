---
id: 20
slug: peterfalvi-part1-character-stubs
title: "Peterfalvi Part I Wave 1a character-theory stubsを解消する"
created: 2026-05-25
---

# Peterfalvi Part I Wave 1a character-theory stubsを解消する

## 背景

`peterfalvi-part1` branch で §3, §5, §6, §7, §8 の Lean 入口を追加した
(`952a1f5`). これにより Peterfalvi Part I (§1-§8) の import spine は
`lake build OddOrder` で通るが、§3-§8 の実証明へ進む前に Wave 1a
character-theory scaffold の deferred theorem を解消または明示的に下流 issue
へ分割する必要がある。

現時点の既知 stub はすべて `OddOrder/GroupTheory/RepresentationTheory/` 配下。
Peterfalvi §3 (1.1), (1.2), (1.4), (1.5) と §6 (4.5.b) の前提になる。

## やること

- [ ] `SecondOrthogonality.lean`: `column_orthogonality_conj`
- [ ] `SecondOrthogonality.lean`: `column_orthogonality_not_conj`
- [ ] `BrauerPermutation.lean`: `brauer_permutation_lemma`
- [ ] `Clifford.lean`: `clifford_decomposition`
- [ ] `IsometryDifferencePair.lean`: `isometry_difference_pair_structure`
- [ ] 必要なら上記を小 issue に分割し、この issue からリンクする。

## 完了条件

- 上記 5 つの declaration が `sorry` なしになる、または各 declaration が独立
  issue に移されて依存順が明示される。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。
- `lake build OddOrder` が通る。

## 参照

- `notes/peterfalvi/s03_preliminary_character.md`
- `notes/peterfalvi/s06_dade_certain_subgroup.md`
- `OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean`
- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`
- commit `952a1f5` (`Peterfalvi Part I: add S03-S08 interface modules`)
