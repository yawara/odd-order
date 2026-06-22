---
id: 2015
slug: type-conjugation-5types
title: "HUB: 5型 HasPeterfalviType 共役 infra (II/III/IV/V) — Pf (8.17.a)/exists_second_maximal の unblock"
created: 2026-06-23
---

# HUB: 5型 HasPeterfalviType 共役 infra (II/III/IV/V) — Pf (8.17.a)/exists_second_maximal の unblock

## 背景

lane-h の Pf (12.9) honest assembly (S14_MaximalI, 2026-06-23) で、残る §8 obligation
`exists_second_maximal` ((8.17.a): `∃ L Lt, L maximal ∧ L ≠ M ∧ HasPeterfalviType Lt L ∧
P₀ ⊆ mainSubgroup L Lt`) を discharge しようとしたところ、**一般の 5型 HasPeterfalviType
共役同変性**が必要と判明。

(8.17.a) の証明骨子:
1. `bgTheoremE_cover_data` (BG §16, sorried) で `p ∈ π(G)` を covering する maximal `L₀ = reps i`
   (型 `tau i` = **任意の 5 型**) を取る (p ∣ |mainSubgroup L₀ (tau i)|)。
2. (8.11) Hall + Sylow 共役で `L₀` を共役して `P₀ ⊆ (conj g • L₀)_s` にする。
3. このとき `HasPeterfalviType (tau i) (conj g • L₀)` が要る — `tau i` は任意型ゆえ
   **全 5 型の共役同変性**が必須。

**現状の `OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean` には F/I しか無い**:
- `TypeFData.conj`, `TypeIData.conj`, `isTypeI_pointwise_smul`, `isTypeI_of_conj` ✓
- `isTypeII/III/IV/V_pointwise_smul`, `TypeIIData.conj`/`TypeIIIData.conj`/`TypeIVData.conj`/
  `TypeVData.conj` ✗ (ABSENT)

これは shared/lane-f infra (lane-h owned でない) ゆえ HUB issue として起票。

## やること

- [ ] `MaximalSubgroupTypeConj.lean` に `TypeIIData.conj` / `TypeIIIData.conj` / `TypeIVData.conj` /
  `TypeVData.conj` を追加 (`TypeFData.conj`/`TypeIData.conj` と同パターン、既存の equivariance toolkit
  `card_pointwise_smul`/`isFrobeniusGroup_subgroupOf_pointwise_smul`/`derivedInG` 共役同変 等を使用)。
- [ ] `isTypeII/III/IV/V_pointwise_smul` + 一般 `hasPeterfalviType_pointwise_smul (φ) (tau)
  (h : HasPeterfalviType tau M) : HasPeterfalviType tau (φ • M)` (tau で case split)。
- [ ] (任意) `mainSubgroup_pointwise_smul (φ) (M) (tau) : φ • mainSubgroup M tau =
  mainSubgroup (φ • M) tau` (case split + `maxNilpotentNormalHall_pointwise_smul` [✓] /
  `derivedInG` 共役同変 [S13_PrimeAction の private `smul_derivedInG_conj` を public 化])。

## 完了条件

`hasPeterfalviType_pointwise_smul` (一般) が landing。これで lane-h は (8.17.a)
`exists_second_maximal` を `bgTheoremE_cover_data` (BG §16) + (8.11) Hall + Sylow 共役で
proof 化できる (cover data 自体は BG §16 sorry に bottom-out)。

## 参照

- `OddOrder/Peterfalvi/S14_MaximalI.lean` の `exists_second_maximal` (sorried obligation)
- `OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean` (F/I conj 既存、II–V 欠落)
- `OddOrder/GroupTheory/MaxNilpotentNormalHall.lean` `maxNilpotentNormalHall_pointwise_smul`
- `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean` private `smul_derivedInG_conj`
- notes/peterfalvi/s14_maximalI.md 「(12.9) honest assembly LANDED」
