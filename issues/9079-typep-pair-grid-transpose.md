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

## 2026-07-10 coverage 調査結果 (Explore agent、実装前提の確定)

**既存資産 (全て確認済)**:
- `Section16MaximalPair` (FeitThompsonSetup:292-334): S/T + `theorem88_caseB`
  (**分類 clause 有**: ∀ M maximal, IsTypeI ∨ conj•M = S ∨ conj•M = T) + `S_typeP2` +
  K/K* (= W₁/W₂)。producer `section16MaximalPair_of_isMinimalSimpleOdd` (726-760、本体 sorry-free;
  推移依存に §11/§13 残 sorry — 本レーンが現在埋めている (5.8)/(10.8) 系そのもの、sorried-cite で可)。
- `certainTypeS`/`certainTypeT` (1132-1153): S06.Hypothesis を **W₁/W₂ swap** で両側構成済。
- `W_structure` (1180-1196): S ⊓ T = K ⊔ K* + cyclic。`Section16TypePStructure.W1_eq_K_and_W2_eq_Kstar` (1203)。
- `typeP_duality` (= pair_witness 相当、∃! partner) + `theoremC_paired_structure` covering。
- `IsDadeMap.unique` (S04_DadeIsometry:651、sorry-free)。

**足りない部品 (優先順、全て exists_typeIICrossIsometryData の単一 sorry に集約)**:
1. **σ-grid pair transpose bridge** (核心新規): certainTypeOmegaSigma (S-side、certainTypeT の
   W-swap 基盤) = alignedOmegaSigmaGrid (M-side) の transpose。材料 = 共有 W + (3.2) σ 一意性
   (IsDadeMap.unique — 両 σ は同一 (G, V-TI) の Dade map)。S05_SignedTripleGrid の
   `IsSignedTripleGrid.transpose` (1489) は grid primitive として再利用可。
2. **pair 対称化** (`typeP_pair_sym` 相当の `.swap`): 現状不在 — S↔T/K↔K*/W₁↔W₂。
3. **type-II L → canonical partner 還元 glue** (組立のみ、新規部品不要):
   theorem88_caseB + typeP_duality + type 排他。
4. **行和 pin 変換**: 1 が入れば dichotomy (typeII_nu_tau2_dichotomy、landed) の
   S-列和 → M-行和変換で nu_tau2_eq が従う。
