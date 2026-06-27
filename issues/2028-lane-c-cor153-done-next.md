---
id: 2028
slug: lane-c-cor153-done-next
title: "lane-c W1-b Cor 15.3 COMPLETE — 次配置 hub 相談"
created: 2026-06-27
---

# lane-c W1-b Cor 15.3 COMPLETE — 次配置 hub 相談

## 背景

lane-c の relane #10/#11 割当 = **W1-b = BG §15 Cor 15.3 `mf_hall_centralizer_control`** を完遂
(issue 2025 CLOSED, commit `b9061586`)。

- **Cor 15.3 完全 sorry-free + axiom-clean** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。
  3 input 全 discharge (ha/hconj 既存 + 新 `hfratt_of_hall_not_normal`)。新 reusable helper 3 本。
- **成果伝播確認**: BG Theorem I first assertion (`theoremI_...` S16:3400, lane-f) が axiom-clean
  `mf_hall_centralizer_control` + `nilpotent_hall_embeds_in_msigma` (Cor 15.4, これも axiom-clean) を消費
  = **fusion gate 解消** → Pf (8.8) dichotomy → `theorem88_caseB_holds` (FT endpoint) へ前進。

## やること (hub 判断要)

- [ ] **lane-c の次フロント割当を決定**。lane-c の **§15 (S15_MF) ungated FT-path 群論は枯渇**:
  - 残 real sorry 2 本 = `tau2_transfer_constraint` (15.8) / `centralizer_escape_final_local` (15.9)
    は両方 **off-path frozen** (前者は docstring 参照のみ・不要な回り道と既判定、後者は 0 consumer)。
  - 下流 (Thm I dichotomy = lane-f Prop 16.1 bridges in S16 / Pf 8.8 = lane-h S14_MaximalI) は他レーン所有。

### 候補 (hub 選択)
1. **Cor 15.5(c) 「M'/M_F nilpotent」producer** (S15_MF, §15 群論, lane-c 領域)。現状 statement から省略・
   deferred ("quotient API")。型 P₁ で M_σ=M' ゆえ `msigma_quotient_isNilpotent` インフラ再利用余地あり。
   **FT-path 価値**: lane-f の Prop 16.1 hP1neIIIIV bridge (型 III/IV 構成) の dependency 候補 (issue 8015
   が Cor15.5 を列挙)。ただし現 consumer (hP1neIIIIV) は lane-f deep work で未着手 ⟹ producer 先行の是非を
   hub 判断 (consumer-readiness と lane-f との分担)。
2. **他フロント (W2/W3/W4) への合流** — lane 等価ゆえ value+独立性で再配置 ([[lanes-are-equivalent-no-specialty]])。
3. **lane-f W1-a の非衝突 §15/§16 producer 支援** — Prop 16.1 が要する §15 群論 prerequisite を lane-c が
   別ファイルで生産。

## 完了条件

hub が lane-c の次フロントを指示 (LAUNCH.md 更新 or 本 issue クローズ + 指示)。lane-c 自己復帰モニターで検知。

## 参照

- 完了: issue 2025 (CLOSED), commit `b9061586`。
- 主所有: `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean`。
- 下流: `S16_MainResults.lean:3362` (Thm I, lane-f) / `Peterfalvi/S14_MaximalI.lean:1534`
  (`theorem88_caseB_holds`, lane-h)。
- 関連: 0080 (W1 Prop 16.1, lane-f) / 8015 (Prop 16.1 type classification) / 0081 (W2) / 0082 (W3) / 0083 (W4)。
