---
id: 9079
slug: typep-pair-grid-transpose
title: "shared-infra claim: (8.8) typeP-pair grid transpose + (10.7) pair-witness route — S-grid = M-grid swap"
created: 2026-07-10
---

# shared-infra claim: (8.8) typeP-pair grid transpose + (10.7) pair-witness route — S-grid = M-grid swap

## 背景

<!-- なぜこの issue を立てたか. ROADMAP / notes / コミット等への参照. -->

## やること

- [ ]

## 完了条件

<!-- 何をもって closed とするか. 例: 該当 sorry が消える / lake build が通る / ノート x.md を書く -->

## 参照

<!-- 関連 issue / PR / ファイル / コミット. -->

# shared-infra claim (lane a): (8.8) typeP-pair の grid transpose + (10.7) pair-witness route

**claim-before-build (CLAUDE.md (C))**。lane a が (10.7) obligation 2(b) のために claim:

## Scope
1. **(10.7) の pair-witness 再構成** (Coq `Frob_der1_type2` PFsection10:549-560 の忠実 route):
   任意 type-II L に対する直接証明でなく、**M の pair partner S** (`FTtypeP_pair_witness`
   相当) に対して cross-isometry を証明し、`L = S^x` (pair の type-2 分類 clause) の
   **共役転送**で一般 L に拡張。lane-a 既存の T2/dichotomy 機構 (S12_TypeIIColumnPin、
   S-generic) は partner 上でそのまま再利用。
2. **S-grid = M-grid transpose**: partner S は M と W = W₁×W₂ を共有 (役割 swap)。
   S-side certainTypeOmegaSigma (typeIIHypothesis46-S) と M-side alignedOmegaSigmaGrid の
   同定。**鍵候補 = Dade-map 一意性** (`IsDadeMap.unique`): 両 σ は同じ (G, V-TI) の
   Dade isometry ⟹ 同一 map、grid は index の swap 翻訳のみ。
3. repo 既存資産: `Section16MaximalPair` (FeitThompsonSetup:292、W-structure +
   certainTypeS/certainTypeT 済) — coverage 精査から着手。

## 非重複確認
- 9076 (lane c) = §3 rigidity `eq_signed_sub_cTIiso` + `prDade_sub_TIirr` — **別物**
  (norm-2 rigidity; 本 claim は pair-witness + σ-同一視)。9076 成果物は将来 (10.5)-系で
  相互参照の可能性のみ。
- 9014 (primeTI residue API) とも独立。

owner: lane a / 起点 note: notes/peterfalvi/s10_7_derived_frobenius.md 進捗⁸
