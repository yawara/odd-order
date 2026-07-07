---
id: 2037
slug: thm-15-7-d-sigma-compl-e3-eq-bot
title: "BG Thm 15.7(d) nonTI_Fitting_structure part(d): E₃=1 ∧ cyclic(E/E₂) — cyclic-E gate of Cor 15.9"
created: 2026-07-07
---

# BG Thm 15.7(d) — σ-complement structure for `¬FittingIsTI M` (E₃=1, cyclic E/E₂)

> lane b。**issue 9017 の cyclic-E hole の唯一の upstream gate**。BG Cor 15.9
> (`centralizer_escape_final_local`) の残り 1 sorry (`∃ E, IsCyclic E ∧ Frobenius`) が本 node に gated。

## 何が要るか (Coq `nonTI_Fitting_structure` part (d), BGsection15.v:939)

```
(*d*) forall E E1 E2 E3, sigma_complement M E E1 E2 E3 ->
      [/\ E3 :=: 1, E2 <| E, E / E2 \isog E1 & cyclic (E / E2)]
```

hypothesis: `M ∈ 𝓜`, `g ∉ M`, `X := F(M) ⊓ F(M)^g ≠ 1` (= `¬FittingIsTI M`)。
本 escape では `x ∈ M_σ^# ⊆ F(M)`、`C_G(x) ⊄ M` の escape witness `y` (`y ∉ M`, `x^y = x`) が
`X = F(M) ⊓ F(M)^y ∋ x ≠ 1` を与える (Coq `ntX`)。

## cyclic-E への使い方 (Coq `nonFtype_signalizer_base` の `E3_1`/`cycE`)

1. `E := σ(M)'-complement of M` (`Hall_superset`, K ≤ E)、E-setup E₁E₂E₃。
2. **E₂ = 1**: τ₂(M)=∅ (issue 9017 の `tau2_transfer_constraint` = Thm 15.8 を M_lemma=N/H_lemma=M で
   apply、τ₂(N)=∅ と r∈τ₂(N) 矛盾の対偶) ⟹ E₂ (τ₂-Hall) = 1。
3. **E₃ = 1**: 本 issue (part d)。
4. ⟹ `E = E₁` cyclic (`SubgroupESetup.E1_isCyclic`)、Frobenius M = M_σ ⋊ E
   (`typeF_frobenius_of_tau2_prime_free` が Frobenius+complement を供給、E=E₁ で cyclic 化)。

## 既存 repo 資産 (part d の周辺)

- E-setup 構造: `SubgroupESetup.{E1_isCyclic, E3_normal, E23_normal, E2_normal_in_E12}` (S12_ECore)。
- ¬FittingIsTI witness: `exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI` (S15_MF:7888)、
  `exists_inf_conj_fitting_orderP_witness` (8050)、`mem_sigma_of_prime_dvd_card_inf_conj_fitting` (7924)。
- Thm 15.7(e) 断片: `typeF_nonabelian_cyclic_opiCore_compl` (cyclic O_{p'}(M_F))、
  `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`。
- Thm 15.7(a): `piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`、rank-core `M_F=M_σ`。
- ⚠ **part (d) 本体 (E₃=1) は未形式化** (S16:4065-4070 docstring が確認)。W₁-divisibility
  (part e の |W₁|∣p∓1) は不要 — **part (d) のみ**が cyclic-E に要る。

## 進捗 (2026-07-07 lane b, 更新 #2) — 下流半分 (τ₃=∅ → E₃=⊥) を実証明化

Coq part (d) の E₃=1 を精読 → **`E₃=1 ⟸ τ₃(M)=∅ ⟸ M' ≤ F(M)`** に還元 (Coq `sE3F`+`coprime_TIg`:
`E₃ ⊆ E' ⊆ M' ⊆ F(M) = F(M_σ)×Y`、Y=O_σ'(F(M)) は τ₂、τ₃ ⊥ σ∪τ₂ ⟹ τ₃=∅)。**下流 2 補題を landing** (S15_MF、sorry-free):
- `tau3_eq_empty_of_derivedInG_le_fittingInAmbient (hM'F : M' ≤ F(M)) : tau3 M = ∅`
  (`fitting_decomposition` の F=F(M_σ)×Y + `opiCoreInG_sigmaCompl_..._subset_tau2` + τ₂ pRank=2 で prime-set 論法)。
- `E3_eq_bot_of_tau3_eq_empty (hsetup) (htau3 : tau3 M = ∅) : E₃ = ⊥` (τ₃-Hall が空 prime-set)。

⟹ **残る唯一の gate = `M' ≤ F(M)`** (Coq part (c) `sM'F`: `M' nilpotent` ⟸ `M_β=1` (type F、`H=M_σ` + β⊆σ)
+ `derivedQuotientMbeta_isNilpotent` (repo に有) + `Fitting_max`)。`M_β=1` for type-F が唯一の未確認ピース。

## やること (残)

- [ ] **`M' ≤ F(M)` for type-F ¬FittingIsTI M** を形式化 (crux): `M_β = ⊥` (type F) を確立 →
      `derivedQuotientMbeta_isNilpotent` で `M' nilpotent` → `fittingInAmbient` は max nilpotent normal で `M' ≤ F(M)`。
      `M_β=⊥` は Coq `-defH partG_eq1` (H=M_σ、beta_sub_sigma) を repo にマップ。
- [ ] E₂=1: τ₂(M)=∅ (`tau2_transfer_constraint` = Thm 15.8) → E₂ (τ₂-Hall) = ⊥ (E3 と同じ論法の τ₂ 版)。
- [ ] issue 9017 cyclic-E: setup を hFM の上に hoist (matched pair・R・hHmem 共有) → E=E₁ cyclic
      (`E1_isCyclic`、E₂=E₃=⊥) + Frobenius (`typeF_frobenius_of_tau2_prime_free`) → `∃ E cyclic Frobenius` を close。

## 完了条件

`centralizer_escape_final_local` の cyclic-E sorry が消える (Cor 15.9 完全 sorry-free) →
`exists_RData_escape_structure` / `theoremD_msigma_conjugacy_and_centralizers` の escape 構造が honest 化。

## 参照

- issue 9017 (Cor 15.9 escape package、hFM 実証明済・cyclic-E 残)
- `OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF.lean` (Thm 15.7 群、b territory)
- Coq `coq/theories/BGsection15.v:939` (nonTI_Fitting_structure)
