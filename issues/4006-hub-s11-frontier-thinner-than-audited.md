---
id: 4006
slug: hub-s11-frontier-thinner-than-audited
title: "HUB: §11 frontier は監査より thin — (9.6) のみ clean、(9.7) Clifford engine は deep multi-session"
created: 2026-06-22
---

# HUB: §11 frontier は監査より thin — (9.6) のみ clean、(9.7) Clifford engine は deep multi-session

> 宛先 = HUB (frontier-cluster 分担設計)。発信 = lane-c (Pf §11)。direction/planning データ点。
> ユーザー方針 (merge_monitor `c886d571`)「方向性判断は issue 起票→hub 解決」に従う報告。
> **direction 自体は決定済** (ユーザーが「Clifford engine 構築」を裁可) — 本 issue は engine の
> scope reality + 監査品質の data point を hub に渡し、frontier-cluster 計画に反映してもらうため。

## 背景

frontier-cluster relane (issue 4005) で lane-c を §16→Pf §11 に再配置。LAUNCH/監査は §11 を
「6 workable leaf (9.6-9.11)、Wielandt(9.1)+§11 内部のみで進む自己完結クラスタ」とした。

## 観測 (lane-c が実地に digging した結果)

- **clean に証明できたのは (9.6) `chiefFactor_basic` のみ** (commit `95dbe3f9`, main 合流済
  `30004a9e`)。しかも旧 statement に **faithfulness バグ** (conjunct 3 `|W₂|=p` が type II で偽) が
  あり修正した = leaf は「workable」どころか「要修正の overstatement」だった。
- **(9.7)-(9.11) は深い未実装エンジンに gated** (監査の「§11 内部のみ」は不正確):
  - (9.7) `clifford_dichotomy` = H̄ の Clifford 分解 (U-既約成分を W₁ が推移置換)。**mathlib に
    Clifford 置換層が無い**。設計ノート `notes/peterfalvi/s11_9_7_clifford_engine.md` に 7-step
    アーキテクチャ済 (de-opacify→bridge→Maschke→Clifford perm→dichotomy→CaseA/B)。**5-10 session 規模**。
  - (9.8)/(9.9) = degree `qu` の induced 指標構成。(9.10) = Frobenius realization。(9.11) = §14-gated。
- これは **issue 4005/4002 と同じパターン**: 監査は「結論が一致」で workable 判定するが、実際は
  absent infrastructure を要する (workability の hypothesis まで合っていない)。

## hub への data point / ask

1. **frontier-cluster 監査の workability 判定を強化**: 「結論の存在」でなく「証明に要る
   infrastructure が在るか」まで確認する (issue 4002 §3 の教訓の再確認)。§11 は「6 workable」でなく
   「(9.6) 1 本 clean + (9.7) deep engine + (9.8-11) 指標論」だった。
2. **lane-c の §11 scope を把握**: (9.7) Clifford engine は 5-10 session の深い build (ユーザー裁可済)。
   完成しても解禁は (9.7) のみで (9.8)-(9.11) は別途指標論を要する。hub は frontier 計画でこの
   「§11 は短期に薄い」現実を織り込む (例: 他に高 ROI な ungated frontier があれば比較検討、あるいは
   engine 投資を是とする — **判断は hub→必要ならユーザー**)。
3. **direction は決定済**: lane-c は次セッション以降 (9.7) engine の step 0 (`exists_chiefFactor_kernel`
   強化で chief factor 既約性を露出 → `ChiefFactorData` de-opacify) から実装に入る予定。hub の再評価が
   あれば反映する。

## 完了条件

hub が (1) §11 の実 workability (1 clean + deep engine) を frontier 計画に反映、(2) lane-c の (9.7)
engine 投資 (5-10 session) を是とするか別配分を検討 (要すればユーザーへ)、を判断。

## 参照

- issue 4005 (frontier-cluster relane) / 4002 (監査 workability 過大の前例) / 4001 (lane-c §16 frontier)
- `notes/peterfalvi/s11_9_7_clifford_engine.md` (9.7 engine 設計) / `s11_wielandt_91_design.md` (9.6 修正)
- commit `95dbe3f9` ((9.6) + faithfulness 修正) / `7b01ed91` (engine 設計ノート)
- `notes/meta/merge_monitor.md` (ownership map + direction→issue policy)
