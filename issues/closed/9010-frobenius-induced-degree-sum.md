---
id: 9010
slug: frobenius-induced-degree-sum
title: "shared: Frobenius 誘導族の次数平方和 e·Σd²=|K|−1 (14.14 Bessel 供給)"
created: 2026-07-05
kind: shared-infra
lanes: [c]
---

# shared: Frobenius 誘導族の次数平方和 e·Σd²=|K|−1 (14.14 Bessel 供給)

## 背景

**CLAIM (lane c, claim-before-build)**: Pf (14.14) `orthogonality_switch_pairing_bounds`
(S16:4783) の Bessel 側で、L/M 両側の誘導族 `{Ind_K^L θᵢ}` の次数平方和
`Σ_{i≠ind1H} θᵢ(1)² = (|K|−1)/e` (教科書 p.90 の `Σaᵢ² = (h−1)/pq`) が要る。
repo 未存在を確認済 (2026-07-05 grep: sum_d_sq / degree_sq_sum 等ヒットなし)。
(7.10) 系 `card_G0_lower_bound` (issue 0044, p.42 line "`Σ_t d_{it}² = (h_i−1)/e_i`") も
同一恒等式を将来 cite する — shared 化が正位置。

**証明 (orbit 機構不要の Mackey 経路、部品は全て既存)**:
fiber(i) = {φ ∈ Irr K : Ind φ = Ind θᵢ} で `Irr K ∖ {1}` を分割 (placed family の inj+cover)。
`|K|·|fiber(i)| = Σ_{φ∈Irr K} |K|·⟨Ind φ, Ind θᵢ⟩ = Σ_{x∈L} Σ_φ ⟨φ, θᵢ^{x⁻¹}⟩ = |L|`
(`card_mul_inner_induce` + `irreducibleCharacter_inner_eq_ite`; ⟨Indφ,Indθᵢ⟩∈{0,1} は
Frobenius 既約性 `isIrreducibleCharacter_induce_of_frobeniusGroup`) ⟹ |fiber| = e。
次数は fiber 上定数 (`induce_apply_one`)。総和 = `sumNontrivialIrreducibleDegreeSq`
(ColumnOrthogonality) = |K|−1。

## やること

- [x] 新 shared leaf `OddOrder/GroupTheory/RepresentationTheory/InducedDegreeSum.lean`:
      `card_index_mul_sum_induced_family_degree_sq` (K ⊴ L, Frobenius (L,K,C), placed family
      θ/ind1H/triv/inj/cover ⟹ `(K.index : ℂ) · Σ_{i≠ind1H} θᵢ(1)² = |K| − 1`)。
      deps 確認済で全て GroupTheory/RepresentationTheory 内 (S08 induce_conj 系には非依存
      = issue 9007 の罠は該当せず)。→ landing `d6328cfe` (sorry-free)。
- [x] consumer = lane c の S16 (14.14) pairing-bounds 組立 (別 leaf、c 所有)。
      → `S16_PairingBessel.lean` の `bessel_bound_of_inner_beta_zeta_ne_zero` が cite
      (`a6c06957`)、S16 の `orthogonality_switch_pairing_bounds` sorry 置換まで完了
      (`60b9b6b6`)。

## 完了条件

leaf が sorry-free で `lake build` green、S16 側が cite。→ **両方達成 (2026-07-05)**。

## 事後 dedup 注記 (hub 宛)

claim 時 grep (sum_d_sq / degree_sq_sum) は名前不一致で見逃したが、
`S09_CertificateDischarge.family_degree_sum` (`Σ ζᵢ(1)²/‖ζᵢ‖² = e(h−1)`, norm-divided、
Frobenius 不要の一般形) が数学的にほぼ同内容で先行存在していた。現状は両形とも使用中
(family_degree_sum → NormEstimates 系 / 本 leaf → Bessel の `Σdᵢ²` 直接形 + fiber count
`card_induce_fiber_of_frobeniusGroup` は独立価値)。統合判断は (7.10) card_G0 (issue 0044)
着手時に。

## 参照

- issue 4001 (lane-c frontier)、issue 0044 (将来の第 2 consumer)、issue 9007 (隣接 hoist、別内容)
- `notes/peterfalvi/s16_w4_char_cascade.md` cont.⁵⁴ (本セッションの (14.14) 部品調査)
- 既存部品: `InducedIrreducible.lean` (`card_mul_inner_induce`:135,
  `isIrreducibleCharacter_induce_of_frobeniusGroup`:465)、`ColumnOrthogonality.lean`
  (`sumNontrivialIrreducibleDegreeSq`:152)、`ZIrrFourier.lean` (`irreducibleCharacter_inner_eq_ite`:41)
