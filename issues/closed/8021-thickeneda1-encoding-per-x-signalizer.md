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

## ✅ RESOLVED (lane d, 2026-06-29 /loop²¹, hub/user 承認 Option B): gate 1 cardinality 解消

HUB/ユーザー承認 (Option 1 = lane d が δ struct + lane-b consumer を 1 commit で実施) を受け、faithful
cover への wiring を完遂 (S10 + S14_MaximalI、full build 3889 green、所有例外 = hub 承認)。

- **Option A (共有 `supportKernel` を per-`x` signalizer `Rsub` に再定義) は import 不可で却下確定**:
  `Rsub` は `BG/Ch4/S14_TypePCounting` にあり、それが共有 `GroupTheory/MaximalSubgroupType` (`supportKernel`
  の場所) を import している → 逆向き import は循環。
- **採用 = Option B (抽象 `cover` field)**: `BGTheoremECoverData` に `cover : ι → Set G` field を追加し、
  `thickenedA1_card` を **`cover_card`** (`Nat.card ↥(cover i) = (|(M_i)_s|−1)·[G:M_i]`) に置換。
  `bgTheoremE_cover_data` で `cover i := conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) (reps i))`
  (BG faithful cover) を witness にし、`cover_card` を **`sigmaConjugacySaturation_Mtilde_ncard`** (14.5c,
  DONE) + `mainSubgroup_eq_Msigma` (Pf 8.10) + `Nat.card_coe_set_eq` で**実証 (sorry-free)**。
  ⟹ **deep gate 1 (cardinality) 解消**。`cover` を bare `Set G` に抽象化したので struct は `Mtilde` の
  `SigmaDecompositionData`/`Finite` 依存を carry せず済む。
- **covering struct (`BGTheoremETypeICovering`/`NonTypeICovering`)**: `thickenedA1` → `data.cover` に追従。
  type-I の Frobenius kernel 包含を新 field **`cover_subset_kernels`** (`cover i ⊆ conjClassSet ((M_i)_F#)`)
  として `BGTheoremETypeICovering` に追加 (gate 2 = covering disjunction の sorry に bundle、忠実な未証明
  statement)。
- **consumer `exists_typeICovering` (S14_MaximalI, FT spine)**: `two_le` を `data.cover`/`cover_card` に、
  `covers` を `cover_subset_kernels` cite に追従 (旧 `thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall`
  経由を置換)。FT spine: `theorem88_caseB_holds`→`not_all_maximal_typeI`→`exists_typeICovering`→`cover_card` ✅。

**残 = gate 2 (covering disjunction)**: `bgTheoremE_cover_data` の `BGTheoremETypeICovering ∨ NonTypeICovering`
(S10:664, sorry) = BG Cor 14.9 / (8.8.a) dichotomy。`cover_subset_kernels` (type-I で R(x)=1 ⟹
M̃=(M_i)_σ#=(M_i)_F#) を含む。次の lane-d frontier。

**dead code 注記**: `thickenedSupport_subset_conjClassSet_maxNilpotentNormalHall` / `supportKernel_le_maxNilpotentNormalHall`
(S14_MaximalI:2600/2616, lane-b) は consumer から外れ AxiomsCheck 登録のみの dead lemma に。`thickenedA1`/
`supportKernel`/`thickenedSupport` の def 自体は Dade scaffold (`DadeSupportHypothesisData.H_eq_supportKernel`,
S12 conj-invariant) でまだ使用中ゆえ存続。dead lemma の整理は別タスク (lane-b 所有・AxiomsCheck 登録ゆえ慎重に)。

## 参照

- 親 issue 8020 (bgTheoremE_cover_data 組立)。`thickenedA1_card` sorry = S10_MinimalSimpleStructure:635。
- Coq `FTsignalizer`/`FT_Dade_support` (PFsection8.v:73-79)、`'R[x]=C_{(N[x])_F}[x]` (:62)。
- Lean defs: `supportKernel`/`thickenedSupport`/`thickenedA1` (GroupTheory/MaximalSubgroupType.lean:64-75/333)。
- consumer: `S14_MaximalI:2365` (`rw [data.thickenedA1_card i₀]`、lane c 系)。
- ingredient (landed): `maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2` (S16)。
- [[scaffold-sorry-free-not-done]] [[verify-port-state-by-number-not-coq-name]]

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

in-body ✅ RESOLVED (L54、lane d 2026-06-29、hub/user 承認 Option B) — gate 1 cardinality 解消済
(検証 2026-07-02)。gate 2 は issue 8022/0096 (lane b) で追跡。
