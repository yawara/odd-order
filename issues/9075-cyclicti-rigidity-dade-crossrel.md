---
id: 9075
slug: cyclicti-rigidity-dade-crossrel
title: "shared-infra claim: §3 cyclicTI rigidity (eq_signed_sub_cTIiso) → prDade_sub_TIirr Dade cross-relation — (13.18)/(10.5)/(11.8) 共通 gate"
created: 2026-07-08
---

# shared-infra claim (lane c): §3 cyclicTI rigidity → prDade_sub_TIirr Dade cross-relation

**claim-before-build (CLAUDE.md (C))**. Lane c claims the §3 cyclicTI rigidity lemma
`eq_signed_sub_cTIiso` (Coq PFsection3.v:1681) and the §4 Dade cross-relation `prDade_sub_TIirr`
built on it (Coq PFsection4.v:870). Grep confirms **neither is in repo** as of 2026-07-08
(`PrimeTIResidue.lean` の comment が "missing σ isometry stack (cyclicTIiso, dirr_dIirr, PFsection3.v),
not yet in this file" と明記; grep で `eq_signed_sub`/`dirr_small_norm` は repo hit 0)。

## 背景 (2026-07-08 lane c, issue 3003 (13.18) 精査で判明)

(13.18) の `S`-side βₛ bridge (issue 0098 item 3, 3003) の残 deep obligation 群
(`tauS_mu_row0_cross` cross-relation / `betaGrid_support` (13.18.a) / `gammaGrid_real` / `gammaGrid_Y_norm_bound`)
が**全て同じ §3 cyclicTI rigidity に bottom-out** すると code-level + Coq trace で確定:

- `tauS_mu_row0_cross` (= `τ_S(μ_0j−μ_01)=η_0j−η_01`) は Coq defGamma (PFsection13.v:1908) が
  `prDade_sub_TIirr` で discharge。`prDade_sub_TIirr` (PFsection4.v:880) は `eq_signed_sub_cTIiso` を適用。
- `betaGrid_support` (Coq PVSbeta PFsection13.v:1833) も `cfRes_prTIirr`/`prTIirr_id` (prime-TI 値) を使用。

**`eq_signed_sub_cTIiso` の内容** (PFsection3.v:1681, "(3.8) の帰結、(4.8)/(10.5)/(10.10)/(11.8) で使用"):
> `φ ∈ ℤ[irr G]`, `‖φ‖²=2`, `j1≠j2`, φ が `V` (regular set) 上で `ρ = ±(η_{ij1}−η_{ij2})` と一致
> ⟹ `φ = ρ` (全体で)。

= norm-2 virtual character の **rigidity**: V 上の値 (signed η-difference) で全体が決まる。

## やること (multi-piece §3 port、substantial multi-session)

- [ ] **piece 1 `dirr_small_norm`**: `φ ∈ ZIrr G`, `‖φ‖²=2` ⟹ φ は相異 2 既約の ±和差
  (`φ = ±χ_a ± χ_b`)。**一般 char theory** (Parseval + 整数係数: ∑ coeff² = 2 ⟹ 2 個が ±1)。
  repo に一般 virtual-char Fourier decomposition (φ=∑⟨φ,χ⟩χ, coeff∈ℤ, Parseval) が必要
  (`ZIrrFourier` 断片あり S07_Coherence:1204、`CharacterPsiDecomposition` 用の Parseval は 1434、
  ただし汎用でない)。→ 新 shared leaf `OddOrder/GroupTheory/RepresentationTheory/**` 候補。
- [ ] **piece 2 (3.8) cyclicTI NC bound**: cyclicTI grid に対する class function の "number of components"
  bound。deep §3 cyclicTI (Coq `cycTI_NC`/`small_cycTI_NC`)。σ-isometry (`S05.TICyclicHypothesis.sigma`
  = 既存) の image の rigidity。
- [ ] **piece 3 `eq_signed_sub_cTIiso`**: piece 1+2 の assembly。
- [ ] **piece 4 `prDade_sub_TIirr`**: Dade norm (‖μ2_ij−μ2_ik‖²=2) + V-value + piece 3 ⟹ cross-relation。
  → `tauS_mu_row0_cross` (S15_SAndT.lean, 3003) を discharge。

## consumers (broad — §4/§10/§11/§13)

- **§13**: `tauS_mu_row0_cross` (3003, defGamma) / `betaGrid_support` / `gammaGrid_real` /
  `gammaGrid_Y_norm_bound` → S16 `T_typeIII_ratio_le` (S-side βₛ gap、C-lane W-side frontier)。
- **§10/§11**: Coq comment 明示 = (10.5)/(10.10)/(11.8)。lane-a の §10-13 中央核と重なる可能性 → 要 hub 調整。
- σ-isometry 土台 (`S05.TICyclicHypothesis.sigmaIntegral`) は**既存** (isometry/trivial/ZIrr/V-value 完備、
  旧 lane d 構築)。本 claim = その image の **rigidity** (norm-2 characterization)、9014 (residue API) とは別層
  だが同じ cyclicTIiso provenance。

## interface guard (dup 予防、必須)
- **9014 (prime-TI residue API) と別物だが隣接**: 9014 = residue grid (primeTIred/prTIres_irr_cases) を posit。
  本 claim = Dade/σ rigidity (eq_signed_sub_cTIiso)。両者とも "cyclicTIiso port" の一部。着手前に 9014 の
  scope と重複しないか再確認 + lane-a (§10-13 consumer) と coordination (2026-07-02 dup 事故予防)。
- shared leaf は module-level generic (σ-isometry の任意の image に対する rigidity)、side-specific predicate 禁止。

## 完了条件
- `eq_signed_sub_cTIiso` + `prDade_sub_TIirr` 相当が repo に実装され、`tauS_mu_row0_cross` を discharge。
  → (13.18.c) defGamma が完全 sorry-free (cross-relation cite が実証明に)。build green + AxiomsCheck OK。

## 参照
- Coq: `eq_signed_sub_cTIiso` PFsection3.v:1681 / `prDade_sub_TIirr` PFsection4.v:870 /
  `dirr_small_norm` (mathcomp character) / PVSbeta PFsection13.v:1833。
- 既存 σ-isometry: `OddOrder/Peterfalvi/S05_IntegralSigma.lean` (`TICyclicHypothesis.sigmaIntegral`)。
- 関連 issue: 3003 (13.18 faithful 化 + cross-relation isolate)、9014 (prime-TI residue、隣接)、
  0098 (lane c package item 3)、9000 (σ-theory typeP_Galois、別)。
