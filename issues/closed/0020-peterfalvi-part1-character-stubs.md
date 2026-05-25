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

- [x] 上記 stub を依存単位の小 issue に分割する。
- [x] issue 0021: `SecondOrthogonality.lean`
- [x] issue 0022: `BrauerPermutation.lean`
- [x] issue 0023: `Clifford.lean`
- [x] issue 0024: `IsometryDifferencePair.lean`

## 2026-05-26 update

- 初期 Wave 1a stub 群はすべて、public API を `sorry` なしにするか、独立した
  proof-core issue に分割済み。
- 残る hard proof core は `issues/0022-peterfalvi-brauer-permutation.md`,
  `issues/0025-peterfalvi-isometry-difference-core.md`,
  `issues/0026-peterfalvi-clifford-core.md`,
  `issues/0027-peterfalvi-column-orthogonality-core.md` で追跡する。
- この parent issue は routing 完了として close する。上記 proof core の完了を
  主張するものではない。

## 完了条件

- 上記 5 つの declaration が `sorry` なしになる、または各 declaration が独立
  issue に移されて依存順が明示される。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。
- `lake build OddOrder` が通る。

## 参照

- `issues/closed/0021-peterfalvi-second-orthogonality.md`
- `issues/0027-peterfalvi-column-orthogonality-core.md`
- `issues/0022-peterfalvi-brauer-permutation.md`
- `issues/closed/0023-peterfalvi-clifford-decomposition.md`
- `issues/0026-peterfalvi-clifford-core.md`
- `issues/closed/0024-peterfalvi-isometry-difference-pair.md`
- `issues/0025-peterfalvi-isometry-difference-core.md`
- `notes/peterfalvi/s03_preliminary_character.md`
- `notes/peterfalvi/s06_dade_certain_subgroup.md`
- `OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean`
- `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean`
- commit `952a1f5` (`Peterfalvi Part I: add S03-S08 interface modules`)
