---
id: 2032
slug: sibleytarget-frobi-unsound-nonti-witness
title: "sibleyTarget_frobI は非TI witness で unprovable — frobenius_typeI_coherent を Def8.3 case-split に"
created: 2026-07-01
---

# sibleyTarget_frobI は非TI witness で unprovable — frobenius_typeI_coherent を Def8.3 case-split に

## 背景

`OddOrder/Peterfalvi/S14_MaximalI.lean` の `sibleyTarget_frobI` (sorry) を埋める過程で、
この carrier が (12.16) の witness `L` で**数学的に unprovable** であることが判明
(notes/peterfalvi/s14_maximalI.md loop⁶²)。

Peterfalvi 原文 (三重確認):

- **(6.8)(a)** (references/peterfalvi/04.8_..._Coherence_Theorems.mmd:138):
  「\(H^{\#}\) is a **TI-subset of \(G\)** with normalizer \(L\)」= (6.8) coherence の必須前提。
- **(12.10) proof** (04.14_..._Type_I.mmd:59): witness `L` で「**By (12.9), \(H^{\#}\) is not a
  TI-subset of \(G\)**」。(12.9) の `x ∈ Ω₁(P₀)^# ⊆ H^#` は `C_G(x) ⊄ L` (escaping)、ゆえ
  `hyp.dadeData.dade.H x = supportKernel L L H^# x = maxNilpotentNormalHall L ⊓ C_G(x) = H ⊓ C_G(x) ∋ x ≠ ⊥`
  (S14:1311-1314 の supportKernel def; x∈escapingCentralizerSet)。
- **(12.6) proof** (04.14:45): coherence は **3-case split** — (i) H^# TI ⟹ (6.8); (ii) Def(8.3)
  case(b) [H abelian rank 2] ⟹ 全 S 同次数 ⟹ (5.7); (iii) case(c) [|L/H|∣p-1] ⟹ (6.5.c)。

⟹ `SibleyDadeHypothesis.dade_H_eq_bot` (∀a∈H^#, dade.H a=⊥) = 「H^# TI in G」を hardcode。
`sibleyTarget_frobI` (`cases := Or.inl hfrob`, (6.8)(c1) branch) は dade_H_eq_bot 必須ゆえ
**witness で偽 field を要求** = unprovable。docstring の「Frobenius だから (6.8) SibleyTarget
available」は overclaim ((6.8) は Frobenius に加え (a) H^# TI も要求)。

影響: `frobenius_typeI_coherent` (12.6) が全 Frobenius `L` を sibleyTarget_frobI 経由にするため
**TI case しかカバーせず**、非TI witness (case b/c) を取りこぼす。`witness_L_coherent` →
`exists_witness_dadeNotation` → (12.16) capstone + (5.5) の witness 適用が全てこの carrier に依存。

## やること

- [ ] `frobenius_typeI_coherent` を `hyp.typeI.alternative` (TypeIData の Def-8.3 3-way disjunction,
      `OddOrder/GroupTheory/MaximalSubgroupType.lean:109`) で **case-split** に書き換え:
  - [ ] case(a) H^# TI: `sibleyTarget_frobI` 経由 (6.8)。**要: sibleyTarget_frobI の signature に
        TI 仮説 (`∀a, dade.H a=⊥` 等) を追加**して honest 化 (現状の「全 Frobenius」claim を TI-限定に)。
  - [ ] case(b) abelian rank 2: (5.7) 等次数 coherence (`S07_CoherenceConstantDegree` 在庫) 経由。
  - [ ] case(c) exponent∣p-1: (6.5.c) coherence 経由 (**在庫未確認 = build の可能性あり**)。
- [ ] `witness_L_coherent` は `frobenius_typeI_coherent` を呼ぶだけなので、上記が直れば自動で通る
      (ただし witness が case(b)/(c) のどちらかは (12.10) から特定要)。

## 完了条件

`frobenius_typeI_coherent` が非TI Frobenius (witness) でも honest に coherence を返す
(sibleyTarget_frobI に偽 TI field を要求しない)。`witness_L_coherent` が axiom-clean 化。

## 参照

- notes/peterfalvi/s14_maximalI.md loop⁶²
- 原文: 04.8_..._Coherence_Theorems.mmd (6.8), 04.14_..._Type_I.mmd (12.6/12.9/12.10)
- 既 landing の再利用可能補題 (loop⁶⁰-⁶¹, 一般に正しい): `centralizerSupport_sharp_eq_of_frobenius`,
  `sharpImage_H_subgroupOf_eq_typeIA`, `hconj_transport_ambient`,
  `dadeIntegralCharacterMap_transport_ambient` (S14) — case(a) TI-build や case(b)/(c) で使える。
