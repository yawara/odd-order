---
id: 24
slug: peterfalvi-isometry-difference-pair
title: "Peterfalvi Part I: isometry difference-pair stubを解消する"
created: 2026-05-25
---

# Peterfalvi Part I: isometry difference-pair stubを解消する

## 背景

Peterfalvi §3 (1.4), §5 (3.2), §6 (4.5), §7 (5.6) で使う
isometry difference-pair 構造 lemma の stub を解消する。§7 coherence の
`χ - χ.conj` route と直結するため、Part I coherence を実証明へ進める前の
主要依存。

## やること

- [x] `isometry_difference_pair_structure` の statement が §3 (1.4) と §7 (5.6)
      の両方に使える強さか確認する。
- [ ] second orthogonality / finite orthonormal indexing への依存を明示する。
- [ ] `isometry_difference_pair_structure` を `sorry` なしにする、または induction
      の combinatorial core を別 issue に分割する。
- [x] `OddOrder.Peterfalvi.S03.conjugateDifference` との接続 lemma の要否を確認する。

## 2026-05-25 update

- `OddOrder.Peterfalvi.S07.CharacterDifferenceImage` を追加して、§7 (5.2.d) で
  必要になる `χ - χ.conj` の像を `ε • (μ - ν)` として記録する interface にした。
- `Hypothesis.difference_image_eq` が
  `OddOrder.Peterfalvi.S03.conjugateDifference` との接続 lemma になる。

## 完了条件

- `IsometryDifferencePair.lean` の `isometry_difference_pair_structure` から
  `sorry` が消える、または proof core が独立 issue に分割されている。
- `lake build OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0020-peterfalvi-part1-character-stubs.md`
- related: `issues/0021-peterfalvi-second-orthogonality.md`
- `OddOrder/GroupTheory/RepresentationTheory/IsometryDifferencePair.lean`
- `OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean`
- `OddOrder/Peterfalvi/S07_Coherence.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `notes/peterfalvi/s07_coherence.md`
