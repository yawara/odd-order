---
id: 96
slug: s10-section8-dade-support-carveout-lane-b
title: "carve-out: S10 §8 Dade-support 宣言群を lane b 所有 ((8.18.c)/route-B 前提)"
created: 2026-07-02
---

# carve-out: S10 §8 Dade-support 宣言群を lane b 所有 ((8.18.c)/route-B 前提)

## 背景 (2026-07-02 hub 裁定、ユーザー委任レビュー)

lane b (β) の残る最深 body 2 クラスタのうち Cluster B ((8.18.c) `nonconjugate_diffImage_inner_zero`
→ (12.3) → (12.14)/(12.15)/(12.16) 最終矛盾、issue 9003) と route B (issue 8022 の
FamilyHypothesis71 再構成 → `not_all_maximal_typeI` → `theorem88_caseB_holds`) は、いずれも
**Pf §8 Dade-support geometry** を前提とし、その宣言群は物理的に lane a 所有の
`S10_MinimalSimpleStructure.lean` に同居している。

- 9003 の旧指示 (「lane a の S10/S11 は編集しない、S14 に pin」) の下で b は
  `support_mutual_exclusion` を S10 で実証明してしまい自己 flag (65a2be52 / 3bbbde4c)。
  hub 検証の結果この edit は**旧 statement が false as stated (nonconjugacy 仮説欠落) の修正 +
  sorry-free/axiom-clean 実証明**で、9003 裁定にて**受理 (keep in S10)**。
- lane a の active frontier は S12 (11.8 chain) + 次いで S11 σ-tail であり、S10 §8 support 宣言との
  近接衝突リスクは低い。§8 Dade-support は β cluster (type-I Dade tower) の主題そのもの。
- 先例: carve-out 0086/0088/0090 (同型の sub-file 所有例外)。

## 裁定 = scoped carve-out (lane b)

`OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean` のうち、以下の **§8 Dade-support 宣言 +
その直接 helper (新設含む)** を **lane b 所有**として扱う (line は 2026-07-02 main 時点):

- `typeII_A_sets_TI` (:490) / `typeII_A_sets_normalizer` (:500)
- `dadeSupportHypotheses_typeI` (:556, Pf 8.15) / `dadeSupportHypotheses_typeP` (:565)
- `support_mutual_exclusion` (:853, Pf 8.18.c — 65a2be52 で b が実証明済)

加えて `OddOrder/Peterfalvi/S10_BGInterface.lean` への **A₁/σ♯/M̃ bridge 補題の追加**は b 許容
(既存宣言の変更は要 hub flag)。

**対象外 (従来通り lane a、b が編集したら逸脱)**: S10 のそれ以外すべて — bgTheoremE carrier
(`BGTheoremECoverData`/`bgTheoremE_cover_data` 等)、`hall_maxNilpotentNormalHall_and_mainSubgroup`、
`typeI_or_typeII_centralizer_unique`、`escapingCentralizers_control`、type-classification structural
((8.16)/(8.6.a) 系を含む Cluster A 前提 — こちらは 9003 どおり S14 に pin して cite)。

**step 1.5 運用 (merge_monitor)**: lane b の S10/S10_BGInterface 編集は、hunk が上記宣言
(+新 helper) の文脈に収まる場合のみ逸脱としない。曖昧なら `git diff main...b -- …S10…` の
hunk 位置で判定 (carve-out 0086 と同じ運用)。

**lane a への通知**: 上記 5 宣言 (+b の新 helper) は編集しない (要望は notes/issue 経由)。

## やること

- [x] 裁定 + 所有マップ反映 (merge_monitor.md 🔒 マップ直下 carve-out 節)
- [ ] lane b: (8.18.c) の mixed Ã₁∩Ã support theory ((8.13.c)/(8.17)/(8.18)) を本 carve-out 範囲で
      正面から build (9003 loop⁹⁸ への回答 = これが β の最深 body、回避対象ではない)
- [ ] lane b: route B (issue 8022) の per-rep `dadeSupportHypotheses_typeI` (8.15) を同範囲で build
- [ ] 恒久解: §8 support theory が固まったら hub prefix-split で S10 から dedicated leaf
      (例 `S10_DadeSupport.lean`) に分離し、本 carve-out を解消

## 完了条件

(8.18.c)/route-B が要する §8 Dade-support 宣言が sorry-free 化し、恒久解 (dedicated leaf 分離) で
carve-out が不要になること。

## 参照

- issue 9003 (Cluster B gate map + 本裁定の記載先) / issue 8022 (route B) / issue 0091 (受理前例)
- commit 65a2be52 (support_mutual_exclusion 実証明) / 3bbbde4c (b 自己 flag)
- merge_monitor.md 🔒 マップ + carve-out 先例 0086/0088/0090
