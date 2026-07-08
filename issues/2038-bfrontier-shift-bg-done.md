---
id: 2038
slug: bfrontier-shift-bg-done
title: "b-frontier shift: BG §15/§16 done, reachable clean b-sorry 枯渇 → reallocation 要検討 (hub)"
created: 2026-07-08
---

# b-frontier shift: assigned BG §15/§16 done、reachable clean b-sorry 枯渇 (hub 裁定要)

## 契機 (lane-b /loop、2026-07-08)

lane-b /loop で assigned frontier (memory [[ft-four-fronts-w1-w4]] の「真の bottleneck = BG §15/§16
node、4 bare sorry」) を進めようとしたが、**comment-strip 実測で BG §15/§16 は実質 done** と判明
([[grep-sorry-docstring-contamination]] の実害 — 旧 scan は docstring 汚染で ~40 sorry 誤認)。

## 検証結果 (comment-strip、code-level)

- **BG §15/§16 = done**: `S15_MF.lean` 実 sorry **0**、`S16_MainResults.lean` 実 sorry **1**
  (`theoremA_maximal_structure` = faithful 版 `theoremA_maximal_structure_faithful` が proven ゆえ意図的
  scaffold、gap でない)。memory の「BG §15/§16 bottleneck」は完全 stale (memory 訂正済)。
- **真の b-owned 実 sorry** (comment-strip): S14_MaximalI **11** / S15_SAndT_Setup **11** / S15_SAndT **9**
  (S07/S08/S09 = 0)。
- **だが全て gated/off-path/lane-c-coupled** (docstring code-level 確認):
  - **S14 (11)**: 全て「BG §16 residual / hub 9003 に gated、not in reach of S14」明記 —
    `escapingCentralizers_control` (S10:497、(2.3) escaping-centralizer、sorried ungated-most upstream) /
    (8.8.a) dichotomy / (8.3)/(12.8) minimality (=9003)。
  - **S15 char (20)**: W-side (gammaGrid 等) = lane-c-active / S-side cascade
    (`sibleyTarget_S`/`character_degree_analysis`/(13.10) analytic) = **off-path vestigial** (hub 2026-07-02
    ruling: spine は W-side eta grid 経由、tauS=0 placeholder、do-not-complete)。残 (caseB_order_u 等) は
    abstract Prop param (`caseB_for_S : Prop` 中身なし) or coherence 依存で gated。

## lane-b の genuine landed (2026-07-08、参考)

§13 prime-TI residue bridge (`residueS`/`mu2_ne`、S13_PrimeTIResidueBridge.lean) +
`honestTypeP2ASet_subset_typePA` + (13.18) support-set 解決 (9008: typePA0=over-claim、honestTypeP2A0Set
正しい、certainTypeDiffSupported が A parametric ゆえ route clean) + Hypothesis46-for-S feasibility 確定
(subH=M_σ で A_covers 成立)。→ (13.18) pins 2/3 の残 assembly = Hypothesis46-for-S (lane-c file、dadeHypS0 消費、
subH 設計は lane-c 構造知識)。

## hub 裁定要 (reallocation)

assigned b-frontier (BG §15/§16) が done ゆえ **lane-b の次 focus が underdetermined**。選択肢:
1. **char W-side / Hypothesis46-for-S を lane-c と coordinate** (lane-c が active に (13.18) betaGrid_A0_support
   endgame を finishing 中、Hypothesis46-for-S が gate、lane-b の residueS が upstream で citable)。
2. **deep cross-cutting residual を lane-b が engage** (`escapingCentralizers_control` (2.3) 等) — ただし
   BG §16/Ch2 uniqueness 領域で ownership 要確認 (claim-before-build)、hub 9003 と重複可能性。
3. **lane-b reallocation** (frontier 供給に合わせ、過去 4→3 レーン縮約の前例)。

lane-b は本 issue 記録後、/loop 判断で最も policy-compliant な継続 (ungated upstream engage or lane-c 支援)
を選ぶが、reallocation は hub 裁定事項ゆえ surface。
