---
id: 1027
slug: typev-sixfive-gates-handoff
title: "(6.5) type-V gates 実装 handoff: h56-for-type-V (typeV_forces_coherence_v2 の残 3 sorry)"
created: 2026-07-12
---

# (6.5) type-V gates — lane-a 実装 handoff (fresh session 用)

> 2026-07-12 lane-a session の frontier 徹底 census の成果を durable 化。この session は
> discovery のみ (Lean 進捗ゼロ)。**fresh session はここから実装に直行する** (下記 discovery を
> 再実行しないこと)。census は必ず recursive glob (`find OddOrder -name '*.lean'`) + comment-strip
> ([[sorry-census-must-include-subdirs]] [[grep-sorry-docstring-contamination]])。

## ✅ 確定事項 (再導出禁止 — 全て検証済)

- **lane-a 主要 on-path char は body 完成**: (11.8) orthogonality (refuter route) / (11.9)
  type-III determination (`S13_NonGaloisExclusion.lean`, issue 1024) / (9.11) coherence (refuter
  route `coherent_sOf_H0Cprime` + `nineElevenSevenEightRefutation`) / (6.2)/(6.3) (S08 standalone) /
  (11.3)-(11.7) / (5.7) / (5.2.d) `sixTwoDecompositionData` (issue 2022 loop 59)。
- **(9.11.2) の「lane-b」帰属は誤り**: 実体は `S_H0C_not_coherent` (10.8) / `isTypeIIIorIV` (10.10)
  の **optParam DEFAULT 汚染** (issue 1025、[[lean-optparam-default-contaminates-axioms]])。lane-b の
  genuine (9.11.2) sorry は不在。→ AxiomsCheck:7754 訂正済。
- **(7.10) card_G0 は off-path 凍結** (2026-07-04 確定、issue 0044 cont.⁴⁸)。触らない。
- **vestigial (証明しない)**: S13_CoreStructure の orthogonality_setup:1401 / not_orthogonal_mu0_sub_zeta:1420
  / final_typeIII_conclusions:1687 (旧 OrthogonalityData packaging、consumer 0 / free True field) +
  Coherence911 `sibleyTarget_H0C` (unsound do-NOT-fill, 7001 audit)。

## 🎯 genuine 残 frontier = (6.5) type-V gates

`typeV_forces_coherence_v2` (`S12_Noncoherence.lean:274`、type-V 排除、**on-path**) は honest
three-branch assembly で、**唯一の残 sorry = 3 gate**:
- `typeV_sixFiveA_bound` (:203) — (6.5.a) `|Ab(M')| ≤ 4w₁²+1`。
- `typeV_sixFiveB_pGroup` (:224) — (6.5.b) M' non-abelian w₂-group。
- `typeV_sixFiveC_not_dvd` (:244) — (6.5.c) `w₁ ∤ w₂−1`。

six_two/(5.2.d) 完成 (issue 2022) で **newly unblocked** = genuine lane-a char work (bookkeeping でない)。
docstring の「(lane b)」(:223/:243) は stale 誤帰属 → 編集ついでに lane-a へ訂正。

### 依存構造 (確定)

3 gate は全て **(6.5.a) に gated**、(6.5.a) の root = **h56-for-type-V**:
- **(6.5.a)** = `six_three_of_six_two_oracle` (`S08_Theorem62_63_Standalone.lean:382`) の**対偶**
  at type-V (L,K,H,H₁,M)=(M, M', M', M'', 1)。inputs: h56 (型V用) + hcoh (S(M'') coherent) +
  ¬coherent(𝒮) ⟹ ¬hbound = `|M'/M''| ≤ 4·w₁²+1`。K.index=|M:M'|=w₁、|H/H₁|=|M'/M''|=|Ab(M')|。
- **(6.5.b)** = `exists_isPGroup_H_of_c2_of_card_le` (`S08_PGroupReduction.lean:89`, hbound=(6.5.a) 要) +
  `sq_le_card_abelianization_of_isPGroup_of_noncomm` (:209, 一般群論) + 非可換性。
- **(6.5.c)** = `six_five_c_arith` (`S08_PGroupReduction.lean:149`, 純算術 p²≤HH'≤4d²+1→False) +
  (6.5.a) + |M'|=p³ ⟹ |M':M''|=p²。d=w₁, p=w₂。

## 🔑 有力 lead — h56-for-type-V の route (中断直前に判明)

- 既存 `exists_source_of_coherence_dichotomy` (`S13_SixTwoBridge.lean:880`) は **型III/IV 専用**
  (htype/chief/μ-column grid に intrinsic 依存) → 型V に流用不可。
- **だが `exists_source_index_le_two_psi_of_break` (`S08_SixTwoGeneral.lean:986`) は GENERAL な h56
  producer** (抽象 `S04.Hypothesis G A L` + K/A'/B/**anchor**/**hdatum**/hAcoh/hBncoh を取る、型 non-specific)。
  ⟹ **h56-for-type-V はこの general producer に型V の hdatum + anchor を供給すれば作れる**見込み。
- **鍵の問い (fresh session の第一手)**: 型V族 𝒮={Ind_{M'}^M θ} (M'=M_F **nilpotent**, M/M'' Frobenius)
  に **可約 member があるか**。
  - **無ければ** hdatum は既済の irreducible-only discharge (`inducedKernelFamily_breakDa_of_irreducible`
    + `inducedKernelFamily_memberDatum_orthogonal_breakDa_of_irr_irr`, S08_SixTwoGeneral、GENERAL) で足り、
    型III/IV の μ-column 困難を **回避** = tractable。
  - **有れば** 型V用の可約 member 解析が要る (μ-column とは別構造、M' nilpotent)。
  判定 = Coq `PFsection6.v` の (6.5)/`coherent_seqIndD_bound` type-V 適用部 + M/M'' Frobenius の
  Irr(M') への作用 (M-invariant θ の有無) 精読 ([[feedback-ask-chatgpt-for-elided-gaps]] 可)。
- ⚠ **not-(a) 枝は (M')^# 非TI** ゆえ SibleyDadeHypothesis 経由 (H_sharp_ti) は issue 7001 型の
  不健全リスク。general (6.2)/(6.3) 経由 (h56) が正道 (Sibley (6.8) は case-(a) の TI 専用)。
- **(6.4) 型V carrier**: K=M'=M_F nilpotent + L/H₁=M/M'' Frobenius ((8.4.d)+(8.15) から)。
  `S04.Hypothesis` (Dade τ) は `hyp.dadeData` 相当を型V の S12.Hypothesis から取得。

## 進め方 (上流順)

1. **route 決定 (1 手)**: 型V族の可約 member 有無を判定 (Coq 精読)。→ h56-for-type-V の hdatum 供給法確定。
2. **h56-for-type-V 構築** → (6.5.a) 対偶で `typeV_sixFiveA_bound`。
3. **(6.5.b)/(6.5.c)** を (6.5.a) + S08 producer で wire。
4. build-green + commit 単位。`typeV_forces_coherence_v2` の 3 sorry 消滅で type-V 排除が honest 完成。

## 参照

- `S12_Noncoherence.lean` (typeV_forces_coherence_v2 + 3 gate) / `S08_PGroupReduction.lean` (6.5 infra) /
  `S08_Theorem62_63_Standalone.lean` (six_three/six_two) / `S08_SixTwoGeneral.lean:986` (general h56) /
  `S13_SixTwoBridge.lean:880` (型III/IV h56、参考)。
- issue 2022 (six_two/(5.2.d) 完成、loop 1-59)、1025 (optParam 汚染)、0044 (7.10 off-path)、
  7001 (sibleyTarget unsound)、closed/9088 (frontier census)、closed/1026 (11.9 done)。
- Coq `coq/theories/PFsection6.v` (6.5)、`PFsection11.v` (6.5 型V 消費部)。
