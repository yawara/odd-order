---
id: 8022
slug: typeI-cover-reroute-to-mtilde
title: "type-I cover を kernel-cover から M̃-cover へ re-route (gate-2 faithful 化、cross-lane)"
created: 2026-06-30
---

# type-I cover を kernel-cover から M̃-cover へ re-route (gate-2 faithful 化、cross-lane)

## 背景 (ユーザー裁定 2026-06-30, lane d /loop⁴⁸)

gate-2 (`bgTheoremE_cover_data` S10:664 の covering disjunction) を lane-d が 2 iteration 精査し、
従来の **kernel-cover** ルート (`cover_subset_kernels` / consumer `TypeICovering.covers`) が
**M_σ-TI for type-I** を要すること、これが (i) deep (BG D(2) は cyclic 止まり)、(ii) **overstatement の
可能性大** (Coq `mFT_partition`/Peterfalvi 実 Dade support は **thickened M̃-cover** で kernel-cover でない)
と確定 (正本=issue 8020)。**ユーザーは faithful な M̃-cover への re-route を裁可** (/loop⁴⁸ AskUserQuestion)。

## ✅ lane-d 側の数学は完了済 (sorry-free、本 issue の土台)

M̃-cover route が必要とする群論はすべて lane-d が既に proven (S14_TypePCounting、全 sorry-free):
- **`exists_mem_conjClassSet_Mtilde_of_ne_one`** (S14:5421): all-type-F で ∀g≠1, ∃M maximal,
  `g ∈ 𝒞_G(M̃_M)` (BG Lemma 14.6 = `sigma_decomposition_dichotomy` の signalizer branch;
  κ-branch は `IsTypeF`⟹κ=∅ で vacuous)。
- **`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`** (S14:8129): 完全な cover 等式
  `sharpSubgroup ⊤ = ⋃_{M∈maximal} 𝒞_G(M̃_M)` (= `cover_nonidentity` の本体)。
- `one_not_mem_Mtilde` (S14:8102, ⊇)、`conjClassSet_Mtilde_disjoint` (pairwise)。

∴ **gate-2 の TypeICovering branch の `cover_nonidentity` + `pairwise_disjoint_thickened` は供給可能**。

## ✅ 実行体制 (ユーザー裁定 2026-06-30 hub session): lane d に cross-lane carve-out

S10+S09+S14_MaximalI を build-green に一括必要な coupled 改修ゆえ、独立並行不可。**lane d が全体を
1 つの atomic 変更 (専用 branch) として実装** → hub が一括合流。
- **lane d に一時 cross-lane carve-out 付与** (merge_monitor.md 🔀 ブロック): d が S09
  (FrobeniusFamily/FamilyHypothesis71/G0) + S14_MaximalI (`not_all_maximal_typeI`/`covers`) を
  8022 の一環として編集してよい (逸脱としない)。
- **a/b/c への要請**: 8022 land まで S09 FrobeniusFamily/FamilyHypothesis71・S14_MaximalI
  `not_all_maximal_typeI` 周辺の編集を避ける (d の atomic 変更との衝突回避)。各 lane の他フロンティアは継続可。
- hub: d の atomic diff (S09/S14/S10 含む大型) を build-green + sorry/axiom 検証して一括合流。land 後に
  carve-out 解除 + a/b/c へ解除通知。

## やること (cross-lane re-route、coupled = build-green に一括必要)

1. **S10 (`BGTheoremETypeICovering`, lane-d carve-out 8086)**: `cover_subset_kernels` field を
   **削除** (kernel-inclusion は M_σ-TI 依存で faithful でない)。`cover_nonidentity`/`pairwise_disjoint_thickened`
   は残す。`bgTheoremE_cover_data` の type-F branch を `sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`
   (union-over-maximals → union-over-reps に `Mtilde_conj_smul` で変換) で組む。
2. **S09 (`FrobeniusFamily`/`FamilyHypothesis71`, lane-a/c 所有)**: 現 family の `dadeSupport_i =
   𝒞_G((M_i)_F#)` (kernel sharp、H(a)=1) を **M̃ ベース** (`dadeSupport_i = 𝒞_G(M̃_i)`、H(a)=R(a) signalizer)
   に再構成。Peterfalvi 実 Dade support `A~(M)=⋃_{a∈A1}class_support(R(a)·a)` に忠実化。**最も substantial な
   piece** (Dade hypothesis の H(a) を signalizer R(a) で与える)。
3. **S14_MaximalI (`exists_typeICovering`/`TypeICovering`/`not_all_maximal_typeI`, lane-b/c 所有)**:
   `covers` field を M̃-cover (`sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`) から discharge。
   `not_all_maximal_typeI` の `F.G0={1}` 証明を M̃-cover で出す (G0 が M̃-dadeSupport で定義される前提)。

## 完了条件

`bgTheoremE_cover_data` (S10:664) が M̃-cover route で sorry-free 化 (TypeICovering branch; NonTypeICovering
branch は別途) し、`cover_subset_kernels`/M_σ-TI を経由せず consumer chain (→ `not_all_maximal_typeI` →
`theorem88_caseB_holds` → FT spine) が green。

## 参照

- 正本分析 = issue 8020 (gate-2 reduction 訂正、M_σ-TI/τ2-route 無効、M̃-cover が faithful)。
- proven lane-d 補題 = S14:5421 / S14:8129 / S14:8102。
- consumer = `not_all_maximal_typeI` (S14_MaximalI:2787)、`F.G0`/`mem_G0_iff` (S09:660/663)。
- [[scaffold-sorry-free-not-done]] [[gate2-typeF-tau2-reduction-is-false]]
