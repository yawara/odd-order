---
id: 2011
slug: hconj-supportkernel
title: "Discharge hconj in exists_hypothesis_of_typeIIIorIVorV (supportKernel HConjInvariant)"
created: 2026-06-19
---

# Discharge hconj in exists_hypothesis_of_typeIIIorIVorV (supportKernel HConjInvariant)

## 背景

`exists_hypothesis_of_typeIIIorIVorV` (S12, 2026-06-19 faithful-(10.1) commit `26c1a9f0`) は
type III/IV/V 極大から faithful な (10.1) Hypothesis を構成する producer。唯一の **own residual** が
`hconj : dadeData.dade.HConjInvariant`。これは **gated でない自己完結群論**(char theory 不要)で、
discharge すれば producer は完全 honest(legit な upstream `S10.dadeSupportHypotheses_typeP` のみ cite)。

## やること

`dadeData.dade.HConjInvariant` を証明: `a ∈ A := typePA0 M data`, `l ∈ M` で
`dade.H (l·a·l⁻¹) = MulAut.conj l • dade.H a`。全 plan(~40-50 行):

- [ ] 1. 両 `dade.H` を `dadeData.H_eq_supportKernel` で書換 → `supportKernel M M A (l·a·l⁻¹) = conj l • supportKernel M M A a.1`
- [ ] 2. `supportKernel L M X x = if x ∈ escapingCentralizerSet M X then M_F ⊓ centralizer{x} else ⊥` (`MaximalSubgroupType.lean:64`)
- [ ] 3. **escaping set M-conj 不変**: `l·a·l⁻¹ ∈ escapingCentralizerSet M A ↔ a.1 ∈ ...`
      (`x∈A` は `dade.L_normalizes_A`; `centralizer{x}≤M` は `l∈M` で conj 不変)
- [ ] 4. **singleton centralizer conj**: `conj l • centralizer({a}:Set G) = centralizer({l·a·l⁻¹}:Set G)`。
      `BG.Ch3.S12.centralizer_conj_smul` (`S12_ExceptionalBridge.lean:273`, Subgroup 版) の proof を
      singleton Set 用に local copy(`mem_pointwise_smul_iff_inv_smul_mem` + `mem_centralizer_iff`)。
      その file は Peterfalvi S12 に未 import。
- [ ] 5. **M_F の M-conj 固定**: `conj l • maxNilpotentNormalHall M = maxNilpotentNormalHall M` (l∈M)、
      `maxNilpotentNormalHall_le_normalizer M` (`S15_MF.lean:79`) から。S12 から import 可達か要確認。
- [ ] 6. **組立**: escaping 条件で case 分け。escaping 枝 = `Subgroup.smul_inf`+(4)+(5); 非 escaping 枝 = `Subgroup.smul_bot`。

cleanest = local private helper `supportKernel_conj_invariant`(producer 近傍 or `MaximalSubgroupType.lean`)。

## 完了条件

`exists_hypothesis_of_typeIIIorIVorV` の `hconj` sorry が消える / full build green / real sorry 136→135。

## 参照

- commit `26c1a9f0` (faithful (10.1) + honest (10.10))
- `OddOrder/Peterfalvi/S12_MaximalIII_IV_V.lean` (producer), `MaximalSubgroupType.lean:54,64` (escaping/supportKernel)
- `BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean:273` (centralizer_conj_smul template)
