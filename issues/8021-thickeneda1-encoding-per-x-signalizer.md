---
id: 8021
slug: thickeneda1-encoding-per-x-signalizer
title: "thickenedA1/supportKernel が per-x signalizer (N[x]) でなく M_F — faithfulness 修正要"
created: 2026-06-29
---

# thickenedA1/supportKernel が per-x signalizer (N[x]) でなく M_F — faithfulness 修正要

## 背景 (lane d /loop²⁰ 2026-06-29 finding, issue 8020 派生)

`bgTheoremE_cover_data` (Pf 8.17) の struct 組立 (issue 8020、9/11 field 実証) で、残 deep gate
`thickenedA1_card` を closing しようとして **Lean の `thickenedA1`/`supportKernel` 定義が Peterfalvi
(8.14) に不忠実**と判明。

**定義の比較**:
- Coq Pf (8.14): `FTsignalizer M x = if 'C[x] ⊆ M then 1 else 'R[x]`、`'R[x] = C_{('N[x])_\F}[x]`
  = **per-x signalizer 極大 `N[x]` の Fitting** ⊓ C_G(x)。`N[x]` = C[x] 上の一意極大 (`'N[x]`)。
  `FT_Dade_support M X = ⋃_{x∈X} class_support ('R_M x :* x) G` (PFsection8.v:73-79)。
- Lean: `supportKernel (L M : Subgroup G) (X) (x) = if x ∈ escapingCentralizerSet M X then
  maxNilpotentNormalHall L ⊓ C_G(x) else ⊥` (= **`L_F` ⊓ C_G(x)**)。
  `thickenedA1 L M τ = thickenedSupport L M (A1 M τ)`。
- `BGTheoremECoverData.thickenedA1_card` field は **`thickenedA1 (reps i) (reps i) (tau i)`** を使う
  ⟹ **L = M = reps i** ⟹ `supportKernel` は `(reps i)_F ⊓ C_G(x)` (= **M_F**、元の極大の Fitting)。

**問題**: x∈M_σ# が M を escape する (`C_G(x) ⊄ M`) とき、Coq は `(N[x])_F ⊓ C_G(x) ⊆ N[x]` を使うが
Lean は `M_F ⊓ C_G(x) ⊆ M` を使う。**別の極大 (M vs N[x]) 内の部分群で一般に異なる** (escape ゆえ
C_G(x) の大部分は M 外)。⟹ `thickenedA1 (reps i)(reps i)` は BG の faithful cover `𝒞_G(M̃)` でなく、
`thickenedA1_card = (|M_σ|−1)·[G:M]` は **現定義では一般に成り立たない (likely false)**。

**重要な insight (済)**: signalizer N[x] は type F/P₂ (`signalizer_structure_of_mem_sigmaSharp`) ゆえ
`(N[x])_F = (N[x])_σ` (`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`, S16, /loop²⁰ landed)。
∴ Coq `R(x) = (N[x])_F ⊓ C[x] = (N[x])_σ ⊓ C[x] = BG Rsub(x)`。faithful な R(x) は **Rsub に一致**する。
問題は **Lean の thickenedA1 が M_F を使い per-x N[x] を使わない**点に限る。

## やること (design 決定 + 修正)

- [ ] **design 決定** (hub/cross-lane): `thickenedA1`/`supportKernel` (GroupTheory shared infra) +
      `BGTheoremECoverData.thickenedA1_card` (S10) + consumer `S14_MaximalI:2365` をどう直すか。候補:
  - (A) `supportKernel`/`thickenedA1` を **per-x signalizer** (`FTsignalizer`/`Rsub`、C[x]上の一意極大
        N[x] の σ-core) ベースに再定義。faithful。consumer の covers 証明
        (`thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall`) は L_F に依存ゆえ影響精査要。
  - (B) `thickenedA1_card` field を **`conjClassSet (Mtilde D M)`** (BG faithful cover、`sigmaConjugacySaturation_Mtilde_ncard`
        で proven) に restate。consumer (rw + covers) を BG 記法に追従。
  - (C) `thickenedA1 L M` の L を per-x N[x] にする版を新設 (union over supporting maximals)。
- [ ] 修正後 `thickenedA1_card` を `sigmaConjugacySaturation_Mtilde_ncard` (14.5c, DONE) +
      `mainSubgroup_eq_Msigma` + `maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2` で閉じる。

## 完了条件

`bgTheoremE_cover_data` の `thickenedA1_card` sorry が faithful 定義の下で実証され消える (issue 8020 の
deep gate 1 解消)。consumer S14_MaximalI が green。

## 参照

- 親 issue 8020 (bgTheoremE_cover_data 組立)。`thickenedA1_card` sorry = S10_MinimalSimpleStructure:635。
- Coq `FTsignalizer`/`FT_Dade_support` (PFsection8.v:73-79)、`'R[x]=C_{(N[x])_F}[x]` (:62)。
- Lean defs: `supportKernel`/`thickenedSupport`/`thickenedA1` (GroupTheory/MaximalSubgroupType.lean:64-75/333)。
- consumer: `S14_MaximalI:2365` (`rw [data.thickenedA1_card i₀]`、lane c 系)。
- ingredient (landed): `maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2` (S16)。
- [[scaffold-sorry-free-not-done]] [[verify-port-state-by-number-not-coq-name]]
