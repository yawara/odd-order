---
id: 2027
slug: lane-h-w1-reverse-bridge-carrier
title: "lane-h W1 carrier: reverse-bridge rank-1 carrier (π(W₁)⊆κ(M)) を file-disjoint 生産"
created: 2026-06-26
---

# lane-h W1 carrier: reverse-bridge rank-1 carrier (π(W₁)⊆κ(M)) を file-disjoint 生産

## 背景

**relane #11 (2026-06-26, ユーザー裁可 AskUserQuestion = 「W1 に火力集中」)**: 6 エージェント並列監査
(workflow `wf_1cb6284d-bb2`) で relane #10 を再点検 → 構造は健全だが **4 レーン中 3 つ (b/c/h) が
ungated 作業ほぼ 0 で starve**、唯一 lane-f の W1 群論だけが ungated frontier と判明。特に lane-h の
W2 (S14_MaximalI) は lane-b char に完全従属で独立価値が低かった (W4 char 飽和から逃げて W2 char 飽和に
着地)。ユーザー裁可で **lane-h を lane-f の W1 reverse-bridge carrier 生産に振り替え** (火力集中)。

監査で reverse bridge の crux 構造が確定:
- Prop 16.1 の reverse 3 bridge `hIIP2` / `hIIIIVP1` / `hVP1` (S16_MainResults `proposition_type_classification_of_inputs`)
  は全て **carrier 事実 `π(W₁) ⊆ κ(M)`** に bottom out。
- これは `typePData_kappa_nonempty_of_rank1` (S16_MainResults:~2148/2169) が消費し、その crux は
  **rank-1 条件 `∀ p ∈ π(W₁), pRank_M p = 1`** (issue 8015 §「2026-06-20 kappa bridge 精密分解」条件 3 =
  「carrier-gated・真の残 crux」)。σ-complement 半分 `typePData_W1_prime_not_mem_sigma` は済 (2d59f42d)。

## やること

- [ ] **rank-1 carrier `∀ p ∈ π(W₁), pRank_M p = 1` を生産** (= reverse bridge の真の残 crux)。
      issue 8015 の精密分解 (条件 1 σ-complement[済] / 条件 2 / 条件 3 rank-1) を読み、rank-1 を埋める。
      carrier = `Section16MaximalPair` / `Section16TypePStructure` (FeitThompson.lean、def-unit 共有)
      の type-P データから rank-1 を導く群論。
- [ ] **file-disjoint 厳守**: lane-f は `S16_MainResults.lean` (reverse bridge 本体 + forward pair) を
      active 編集中。lane-h は **carrier 補題を別ファイル** (`S16_PairIntersection.lean` [227 行/0 sorry、
      格好の host] or 新 BG leaf) に隔離生産し、lane-f が cite する。S16_MainResults / FeitThompson carrier
      を直接編集する必要が出たら **def-granularity で lane-f と調整** (notes/issue、co-edit 回避)。
- [ ] 自分のスコーピング survey を先に回し (lane-h が W2 で issue 0081 にやったように)、rank-1 の正確な
      ステートメント・host ファイル・cite 点を確定してから着手。

## 完了条件

`typePData_kappa_nonempty_of_rank1` が要求する rank-1 carrier が sorry-free + axiom-clean で landing し、
lane-f の reverse 3 bridge (hIIP2/hIIIIVP1/hVP1) の cross-lane gate が外れる (= Prop 16.1 の reverse 完成に前進)。

## 参照

- 親 issue: 8015 (Prop 16.1 type-classification, lane-f 所有。本 issue は reverse carrier 半分を lane-h が担当)
- 監査: workflow `wf_1cb6284d-bb2` (relane #10 soundness, verdict=minor-adjust)、merge_monitor 現状メモ (relane #11)
- carrier: `Section16MaximalPair`/`Section16TypePStructure` (FeitThompson.lean)、[[typep-w1-kappa-carrier-not-derivable]]
- consumer: `typePData_kappa_nonempty_of_rank1` (S16_MainResults:~2148)、reverse bridges @2541-2544
- 旧 W2 (theorem88_caseB_holds, S14_MaximalI) は lane-h 離脱で driver/await に降格 (char-gated、issue 0081)
