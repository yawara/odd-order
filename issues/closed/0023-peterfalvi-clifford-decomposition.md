---
id: 23
slug: peterfalvi-clifford-decomposition
title: "Peterfalvi Part I: Clifford decomposition stubを解消する"
created: 2026-05-25
---

# Peterfalvi Part I: Clifford decomposition stubを解消する

## 背景

Peterfalvi §3 (1.5) と §3 (1.7) の Clifford theory route で使う
`clifford_decomposition` の stub を解消する。BG §2 representation route とも
共有されるため、Peterfalvi 専用名ではなく汎用 `RepresentationTheory`
module に置いたまま進める。

## やること

- [x] `OddOrder.RepresentationTheory.clifford_decomposition` の statement を現行
      downstream に合う形で再確認する。
- [x] 未使用 `[Fintype G]` warning を proof 方針に合わせて解消する。
- [x] `clifford_decomposition` を `sorry` なしにする、または必要な intermediate
      lemmas を別 issue として切る。
- [x] `clifford_orbit_subset_inertia` との接続を確認する。

## 2026-05-25 update

- 現行 statement は Peterfalvi §3 (1.5)/(1.7) と BG §2 の共通 API として維持する:
  `Res_H^G χ = e • ∑ θ_i`、各 `θ_i` は irreducible、かつ `θ_0` の `G`-orbit にある。
- `clifford_orbit_subset_inertia` は
  `ClassFunction.subgroup_le_inertia` そのもので、Clifford orbit/inertia setup の
  basic connection として十分。
- proof core は `issues/0026-peterfalvi-clifford-core.md` に分割した。残る blocker は
  statement shape ではなく、character-level induction/restriction multiplicity と
  inertia bijection の証明 API。

## 完了条件

- `Clifford.lean` の `clifford_decomposition` から `sorry` が消える、または
  blocking intermediate lemma が独立 issue に分割されている。
- `lake build OddOrder.GroupTheory.RepresentationTheory.Clifford` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0020-peterfalvi-part1-character-stubs.md`
- split: `issues/0026-peterfalvi-clifford-core.md`
- `OddOrder/GroupTheory/RepresentationTheory/Clifford.lean`
- `OddOrder/GroupTheory/RepresentationTheory/Inertia.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `OddOrder/BG/Ch1_Preliminary/S02_Representations.lean`
