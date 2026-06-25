---
id: 2023
slug: hub-lane-h-idle-char-saturated
title: "HUB: lane-h idle — BG spine sorry-free, char frontier saturated, reassign when ungated work opens"
created: 2026-06-24
---

# HUB: lane-h idle — BG spine sorry-free, char frontier saturated, reassign when ungated work opens

## 背景

2026-06-24 lane-h resume。relane #7 (Pf §6 coherence producer, Thm 6.2/6.3) は **producer 側 sorry-free
完成済** (`S08_Theorem62_63_Standalone.lean`, commit `66e6062c`)。残 gate `h56` (solvable kernel の
Pf (5.6) coherence bound) は §10-12 muGrid 領域 = lane-b/c (issue 2022, 別 Explore で再確認: 既存
exported S10/S12 lemma では discharge 不可、新 lemma 要)。

その後 **正確な frontier 調査**を実施。重要な訂正: `grep -c sorry` は本リポで **docstring の "sorry'd
statement" / "scaffold-sorry" / "sorry-free" 等を誤カウント**する (BG §12-13 は "1-3 sorry" に見えるが
全て comment mention)。comment-stripping した**実 sorry タクティク数 = 122 (20 files)**:

| area | 実 sorry | owner |
|---|---|---|
| BG §14-16 (S16_MainResults 14 / S14_TypePCounting 4 / S15_MF 3) | 21 | **lane-f** |
| Pf §10-16 char (S14 14 / S15_Setup 14 / S10 12 / S13 10 / S15 7 / S11 4 / S12 3) | ~64 | **lane-b/c** |
| Pf §16 POLE-2 (S16_NonExistenceG) | 11 | lane-h, char/Dade-gated |
| off-path Appendices (Suzuki/Suzuki2Groups/FeitSibley/NearFields/Huppert/AppD/AppE) | ~22 | off-path |
| FeitThompson 2 POLEs | 2 | 上記に分解 |

**BG 群論 spine (§1-13) は完全 sorry-free** (S01_Solvable 等の旧 "38 sorry" は全て docstring)。よって
lane-h が clean に pivot できる **ungated・uncollided・FT-path タスクは現存しない**: 実 frontier は
char theory (lane-b/c) + BG §14-16 (lane-f) + off-path appendices に飽和。これが lane-h の反復 starve の
構造的真因 (BG group-theory runway 枯渇)。

## やること (HUB judgement)

- [ ] **lane-h を再割当** — ungated work が開いたとき。候補トリガ:
  - lane-b/c が char producer (h56 / Pf §10-16 の一部) を出し、その downstream に lane-h 用の
    ungated wiring/group-theory が生じる。
  - BG §14-16 (lane-f) で lane-h が取れる非衝突 sub-segment を hub が carve (例: BG §16 gated-endpoint
    skeleton, lanes 等価方針)。
  - 新たな上流 group-theory 前提が FT path に出現。
- 再割当は **LAUNCH.md (lane-h) の直接更新** で行う (= 自己復帰モニター trigger (a))、または本 issue を
  `issues/closed/` へ (= trigger (b))。

## 完了条件

- hub が lane-h に新 ungated タスクを割当 (LAUNCH.md 更新 or 本 issue close) → lane-h 自己復帰。

## 参照

- relane #7 producer: `OddOrder/Peterfalvi/S08_Theorem62_63_Standalone.lean` (sorry-free, AxiomsCheck 登録)
- h56 cross-lane gate: issue 2022 (open, lane-b/c)
- 過去の lane-h starve: issue 2019 (Pf S13 exhausted), 2021 (relane #7 origin)
- 自己復帰モニター: `notes/meta/lane_self_resume.md` (本セッションで arm 済, baseline LAUNCH.md=`59bf0db4`)
- ユーザー裁可 (2026-06-24): pivot 先 ungated タスク無 → **idle + 自己復帰モニター** を選択
