---
id: 77
slug: s11-maximaliiiiv-split
title: "S11_MaximalII_III_IV 分割 (1589 行, >1500 — C の (9.7) engine で増加見込み)"
created: 2026-06-22
---

# S11_MaximalII_III_IV 分割 (1589 行, >1500 — C の (9.7) engine で増加見込み)

## 背景

`OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean` が 2026-06-22 tick (merge `057953f5`,
(9.7) Clifford engine step 0 = ChiefFactorData de-opacify) で **1589 行**に到達 (>1500)。
現所有 = lane-c (2026-06-22 relane で H→C 移譲、Wielandt §9 / Clifford 9.6-9.11)。
(9.7) Clifford decomposition engine は 5-10 session 規模 (issue 4006) ゆえ **今後さらに増える**。

## やること

- [ ] (9.7) engine が一段落して凍結境界ができたら、Wielandt §9 chain (9.1-9.6, 完成済) を
      上流 leaf (例 `S11_Wielandt.lean`) に prefix-split し、active な (9.7)-(9.11) を残す
- [ ] 新規 leaf を `OddOrder.lean` の root closure に追加
- [ ] full build green + AxiomsCheck OK 確認
- 実施 owner = hub (lane-c の frontier と衝突しない凍結境界で)。lane-c の default は「新主結果番号=新 leaf」

## 完了条件

S11_MaximalII_III_IV.lean が ~1500 行以下 (または topic-coherent な複数 leaf + hub)、full build green 維持。

## 参照

- merge_monitor.md「各イテレーションの手順」step 4 (サイズ watch)
- issue 4006 ((9.7) Clifford engine = 5-10 session) / 4005 (relane H→C)
- merge `057953f5` (1589 行到達)
- [[feedback-record-deferred-hub-tasks-as-issues]]

## 🧾 注記 (2026-07-02 hub 全体レビュー): owner 更新 + sequencing

- **現 owner = lane a** (3 レーン再編 2026-07-02: Pf S03–S13 は lane a 所有、旧 lane-c
  行は stale。正本 `notes/meta/ft_lane_reallocation_2026_06_28.md`)。
- 行数 refresh: `S11_MaximalII_III_IV.lean` = **8345 行** (2026-07-02)。
- **sequencing**: 分割は **issue 9000 の dedup (S11 dup 3 定理 retire → generic σ-theory
  leaf cite) の後**に実施する。dedup が S11 内の宣言を削る/差し替えるため、先に split
  すると境界が二度動く。

## 完了 (2026-07-09)

dir 化分割を実施 (issue 0103 方式、lean_split.py による機械分割 + 宣言/namespace 文脈/sorry 保存検証 + full build green):
  - CharacterCounts.lean (1148 行)
  - CliffordData.lean (2695 行)
  - Coherence911.lean (970 行)
  - CuS0.lean (3011 行)
  - SummandComplementKernel.lean (4011 行)
  - ThetaCountAssembly.lean (1097 行)
  - WielandtSetup.lean (1474 行)
