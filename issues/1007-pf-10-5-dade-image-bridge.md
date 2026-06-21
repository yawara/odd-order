---
id: 1007
slug: pf-10-5-dade-image-bridge
title: "Pf (10.5) Dade-image: §10 σ↔τ bridge + §6↔§5 ω reconcile linchpin"
created: 2026-06-21
---

# Pf (10.5) Dade-image: §10 σ↔τ bridge + §6↔§5 ω reconcile linchpin

## 背景

Peterfalvi (10.5) の Dade-image 半分 `α_ij^τ = δ(ω_ij^σ − ω_i0^σ) − n·ζ^{τ₁}`
(`S12_MaximalIII_IV_V.lean` の `alpha_tau_image`, sorry)。support 半分は完了
(`muGrid_alpha_support`, commit a52abf68)。Dade-image 半分の foundation を 2 件 landing 済
(`CoherentHypothesis` de-opaque + `Hypothesis.tau_apply_of_mem_typePV` cornerstone)。
正本設計 = [`notes/peterfalvi/s12_s10_character_bridge.md`](../notes/peterfalvi/s12_s10_character_bridge.md)
「更新⁴」。原文 = `references/peterfalvi/04.12_*.mmd` (10.5)。

`alpha_tau_image` は現状 statement では**証明不能** (arbitrary `params`/`coh`、`omegaSigma`/`mu` free)。
閉じるには下記 carrier 材料化 + 解析が必須 ([[scaffold-sorry-free-not-done]])。

## やること

- [ ] **carrier pinning**: `CharacterParameters.omegaSigma`/`mu` を `Hypothesis.omegaSigmaGrid`/`muGrid`
      に identity field (`omegaSigma_def`/`mu_def`) で pin。producer `exists_charParameters` は既に
      `:= …Grid` ゆえ `rfl` discharge。S13 projection 非破壊の additive 変更 (要 build 確認)。
- [ ] **§10 σ↔τ bridge on V** (本体): `α_ij^τ − δ(ω_ij^σ − ω_i0^σ)` が V=typePV で消える。
  - (a) M-side `muGrid(v) = δ·ω_ij(v)` on V ← (4.3.c) `certainType_apply_eq_of_mem_V`
        (`S06_CertainTypeCharacters:878`、§6 `Hypothesis L`、V=W∖W₂⊇typePV)。
  - (b) σ-side `omegaSigmaGrid(v) = ω_ij(v)` on V ← (3.2.c) `sigma_apply_of_mem_V` (`S05_SigmaIsometry:1203`)。
  - (c) τ-side ← `Hypothesis.tau_apply_of_mem_typePV` (✅ landed, axiom-clean)。
  - **⚠ linchpin**: §6 `chiColumn` ω (4.3.c の RHS) ↔ §5 `omegaGrid` ω (omegaSigmaGrid の素材) を reconcile。
    両者は `TypePData` から**別 bridge** (`toCertainTypeHypothesis` vs `typePData_toTICyclicHypothesis`) 構成で
    現状 citeable な等式が無い = **deep** (この issue の核心)。
- [ ] **norm/numeric `a=0`**: τ isometry (`IsCoherent.inner_eq_on_supported` / `extension_inner_eq`) +
      τ₁ 拡張で `(α_ij^τ, ζ^τ₁) = −n`、Cauchy-Schwarz + 不等式 + (n even,>0 ⟹ n≥2 で n<2 と矛盾)。
      要 μ-grid orthonormality (genuine μ 構造)。
- [ ] **(3.8) trichotomy 配線**: 機構は §5 W-level に既在 (`sigmaCoeff_trichotomy` `S05_SigmaTrichotomy:41`,
      `grid_no_constant_column`/`sigmaNC`)。§10 carrier の σ-coefficient grid に接続。
- [ ] `alpha_tau_image` を close (build-green + axiom 確認)。可能なら (10.6) `tau1_values_and_norm_bound` も。

## 完了条件

`alpha_tau_image` (S12) が sorry-free。axiom footprint は §10 muGrid 系と同じ上流 gate のみ
(自前 sorry 無)。full build + AxiomsCheck green。

## 参照

- 正本設計: `notes/peterfalvi/s12_s10_character_bridge.md` 「更新⁴」「更新³」「6. (10.2)–(10.5) 原文照合」
- §6 (4.8) template (support 違いで直 cite 不可だが部品共有): `S06_CertainTypeIsometry.lean`
  `certainType_diff_dade_eq` (`:794`)・`certainType_diff_dade_apply_eq_of_mem_V` (`:372`)・
  `sigmaNC_dade_le_two` (`:442`)。
- landed foundation: `CoherentHypothesis` (S12, IsCoherent extension)・`Hypothesis.tau_apply_of_mem_typePV`。
- 上位: [[ft-endgame-two-poles]] [[peterfalvi-s10-13-gated-on-bg-spine]]、issue 1004 (section16CharacterData は §10-13 待ち)。
