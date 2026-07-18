---
id: 9112
slug: lane-c-reallocation
title: "lane c reallocation 相談: BG Ch.1 territory 完了、次の高価値割当を hub に要請"
created: 2026-07-18
---

# lane c reallocation 相談 (hub 宛)

## 状況: lane c の割当 territory (BG Ch.1 = 表現論/elementary) が実質完了

本 session (2026-07-18) で lane c が完成させたもの (全 axiom-clean、AxiomsCheck 登録、full build green):
- **BG §2 完成** (全 7): Prop 2.2(a) char-free / Prop 2.2(b) 任意代数閉体化 (CyclicExtension) /
  Lem 2.3 Fong–Swan (FongSwan) / Lem 2.7 (ElemAbelianAutAction) + 既存 Prop 2.1/2.4/Thm 2.5/2.6。
- **BG §3 完成** (全 10): Thm 3.10 general nilpotent M packaging (S03g_Thm310Nilpotent、実は
  general solvable M で book より強)。
- **BG §1 完成** (全 22): Lem 1.21(d) (PLengthPComplement)。
- **BG §4 完成** (全 20 + 特殊化債務): Prop 4.4(b) (S04_Prop44b) / Lem 4.5(c)+Prop 4.6
  (S04_Lem45c_Prop46) / Thm 4.20(b) (S05_Thm420b) / Thm 4.12(b)(c) [IsSolvable A] 除去 / Cor 4.19
  一般形 (S04g_Cor419)。stale survey も訂正 (4.5(a) は既済だった)。
- **BG §6 substantial**: Lem 6.3(b) (S06_Lem63b) 完成 ⟹ Lem 6.3 全済。Thm 6.2 L(S) 一般形が role
  満たす + J(S) の O_{p'} reduction を conditional lemma で landing (残 = Glauberman ZJ major、issue 3017 pending)。
- **Isaacs Appendix 開始**: X.1 + X.4 (DirectDiamond) 済、X.5/X.11/X.12/X.22 は subagent 進行中。

## 独立・高価値作業が枯渇

pivot 探索の結果 (git+survey 精査、2026-07-18):
- Isaacs numbered chapters: **Ch.3 active (別 lane)、Ch.8 完了 (別 lane)、Ch.9 = lane a、Ch.10 = lane c 既済**。
- Peterfalvi = lane b。
- BG §14-16 / App.C/D/E = deep FT final contradiction (settled findings 多数、他 lane/低優先)。
- Isaacs Appendix = 唯一の独立枠だったが nearly done (X.1/X.4 済、残 X.5/X.11/X.12/X.22 は
  一部 mathlib 被覆の marginal clause)。

⟹ **lane c territory 内の高価値独立作業は枯渇**。marginal な appendix clause を惰性で続けるより、
hub に次の高価値割当を要請 (feedback-cost-scope-not-a-criterion / hub-arbitrates / lane-hub-loop)。

## hub への相談事項

1. lane c を次にどのクラスタへ割り当てるか (他 lane と非衝突の高価値未形式化)。候補:
   - BG §14/§16 / App.C の残 (FT final contradiction; 他 lane との調整要 — hub 裁定)。
   - Peterfalvi の残 (§3/§4/§7/§8/§9 の spec/partial; lane b と調整要)。
   - Isaacs Ch.5/Ch.6 の残 partial (Ch.5: 34 中 21 済; Ch.6: 26 中 19 済)。
   - mathlib upstream (appendix X-results を OddOrder/Mathlib へ整理 + PR 準備)。
2. lane c の所有 file 再割当 (BG Ch1_Preliminary の RepresentationTheory leaf 群は完成、凍結でよいか)。

## 参照

- 本 session の commit chain (git log, feat(bg-s0X)/feat(clifford)/feat(isaacs-app) 群)。
- survey 正本 (激しく stale、本 session で BG §1-§4 + §6 を更新済)。
- issue 3017 (Thm 6.2 J(S) pending)、3018 (appendix X-gaps)。
