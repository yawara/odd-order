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
  - **⚠ linchpin (2026-06-21 精査で characterize)**: §6 `chiColumn` ω (4.3.c の RHS) ↔ §5 `omegaGrid` ω
    (omegaSigmaGrid の素材) を reconcile。**両者とも `omega ∘ omegaProdChar` で構成同型だが別 level の
    `TICyclicHypothesis` 上**:
      - §6 = `((hyp.toCertainTypeHypothesis).toHypothesis).sdiffTICyclicHypothesis` = **`TICyclicHypothesis ↥M`**
        (W1/W2 = `subgroupOf M`)、`chiColumn χ₂ i = sdiff.omega (sdiff.omegaProdChar (w1CharEquiv i) χ₂)`
        (`S06_CertainTypeCharacters:222`)。
      - §5 = `typePData_toTICyclicHypothesis hyp.typeP hodd` = **`TICyclicHypothesis G`** (W1/W2 = G の subgroup)、
        `omegaGrid i j = omega (omegaProdChar (charEquiv W1_le_W i) (charEquiv W2_le_W j))` (`S05_OmegaGrid:65`)。
    ⟹ reconcile = **↥M-level ω ↔ G-level ω の cross-level value-transport** (W ≤ M ≤ G, `subtype`/`subgroupOf`)。
    precedent: §5 `mapOfInjective` (`S05_TICyclic:97`) + §6 内部 `omegaProdCharTic`
    (`S06_CertainTypeIsometry:122-142`, ↥L-side chiColumn を G-side に転送し bridge 点で値一致; §6 は自前 ticVdiff
    (W∖W₂) で実装済)。これが **deep gate の核心** (multi-step cross-level transport)。
  - **σ-side note**: `sigmaIntegral_apply_of_mem_V` (3.2.c) の clean 適用だが、`omegaSigmaGrid` の def が
    tactic-mode + 内部 `haveI : NeZero (Nat.card tic.W1)` ゆえ **standalone lemma 化は instance synth が awkward**
    (RHS の `tic.omegaGrid` が NeZero 要求; 2026-06-21 試行→revert)。**→ bridge 本体内で inline 証明**が clean。
  - **(3.8) trichotomy は §5 level** (`sigmaCoeff_trichotomy`/`sigmaNC`) ⟹ omegaSigma の正しい target は §5
    `omegaSigmaGrid` (現状 def) で正解 (§6 `certainTypeOmegaSigma` でなく)。
  - **⚠ 別 obstruction = Dade support gap**: §6 (4.8) `certainType_diff_dade_eq` の `h.tau` は **W∖W₂-based**
    (ticVdiff)、§10 `hyp.tau` は **typePV-based** (typePA0)。W₁# 扱いが違い直 cite 不可 ((10.5) は −nζ で W₁# を消し
    typePV に落とす)。∴ §10 は §6 (4.8) を template に parallel re-derive (部品 4.3.c/3.2.c/3.8/NC 共有)。
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
