---
id: 1022
slug: ttypeii-repoint-unconditional-1010
title: "lane c: TTypeII (14.9) の type-V 排除を no_typeV_maximal_unconditional に repoint (任意 hygiene)"
created: 2026-07-11
---

# lane c: TTypeII の type-V 排除を unconditional (10.10) に repoint

**from**: lane a (issue 1020 Phase 3 完遂時の followup)。**owner 提案**: lane c (S16 所有)。
**性質**: 任意の taint hygiene (1 行 + import 1 行)。急ぎではない。

## 背景

issue 1020 Phase 3 で (10.10) の honest heir `S12.no_typeV_maximal_unconditional`
(`OddOrder/Peterfalvi/S12_Noncoherence.lean`、residual = (6.5) gates issue 2022 のみ) が
landed。旧 `S12.no_typeV_maximal` (S12_MaximalIII_IV_V:1669) は legacy bare-sorry
`typeV_forces_coherence` + 旧 `S_not_coherent` (hB sorry) を経由する。

旧版の term consumer のうち、**S16_NonExistenceG/TTypeII.lean:1418 だけが repoint 可能な
DAG 位置にある** (S16 は FeitThompsonSetup 非依存 → `import OddOrder.Peterfalvi.S12_Noncoherence`
を足しても循環しない見込み。他の consumer — S13_SixTwoBridge / S13_Lemmas113To115 /
S14 WitnessSylowCyclic — は Noncoherence の上流で repoint 不能、legacy 残置が正)。

## やること (lane c、~5 分)

- [ ] `TTypeII.lean` に `import OddOrder.Peterfalvi.S12_Noncoherence` (循環チェック)
- [ ] :1418 の `OddOrder.Peterfalvi.S12.no_typeV_maximal hG ⟨…⟩` →
      `OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG ⟨…⟩` (signature 同形)
- [ ] 効果: (14.9) T-side chain の (10.10) 依存が legacy 二重 sorry (typeV_forces_coherence
      bare + hB) から (6.5) gates (2022) に置換 = honest 化
