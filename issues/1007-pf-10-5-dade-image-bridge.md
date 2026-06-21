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

## ⚠⚠⚠ 最重要 finding (2026-06-21 transport build 中に発覚) — grid index 不整合

**`muGrid` と `omegaSigmaGrid` は独立な index→ω map を使う ⟹ 同一 (i,j) で μ_ij と ω_ij^σ が無関係な
character になり、per-(i,j) の (10.5) identity `alpha_tau_image` は現 grid 定義では SEMANTICALLY FALSE**
(transport だけでは閉じない; これが真の core issue):
- `muGrid i j` (S12:750) = chiColumn 経由、W₁-dual = **`w1CharEquiv i`** (§6, S06:196)、W₂-dual =
  **`finCardEquivCharacterGroup j`** (§10, S12:721)。台 = ↥M。
- `omegaSigmaGrid i j` (S12:782) = §5 tic 経由、両 dual = **`charEquiv i`/`charEquiv j`** (§5, S05:54)。台 = G。
- `w1CharEquiv`/`finCardEquivCharacterGroup`/`charEquiv` は全て「Fin card ≃ duals, 0↦1」だが **独立な
  base equiv** ゆえ対応しない。producer (`exists_charParameters` S12:1659-1660) は両 grid を**独立に**
  `mu := muGrid` / `omegaSigma := omegaSigmaGrid` で詰める ⟹ misaligned。
- **(10.3) (degree/δ 独立性) は index-invariant ゆえ dormant だった**; (10.5) が初めて per-(i,j) 対応を要求し露見。

**∴ 正しい fix = `omegaSigma` を muGrid 自身の ω の §5 σ-image (↥M→G transport) として ALIGN 定義する**
(transport を畳み込み + 整合を構成的に保証)。cross-level transport は不可避だが、それを「与えられた 2 grid の
reconcile」でなく「omegaSigma を muGrid に揃えて定義」する形で使う。⚠ **cross-file 影響**: `omegaSigmaGrid` は
S15.Hypothesis.eta も pin (docstring) ⟹ omegaSigmaGrid 自体を再定義すると S15 に波及。低影響版 = producer 内で
`omegaSigma` だけ aligned grid に差し替え (omegaSigmaGrid は S15 用に温存、docstring の「同一」主張は要更新)。
**要ユーザー判断** (architectural, cross-file)。

## ✅✅ 進捗 (2026-06-21) — cross-level transport + reconciliation DONE

misalignment fix (producer-local) を実装し、**deep gate だった cross-level reconciliation を close**:
- ✅ `Hypothesis.alignedOmegaSigmaGrid` (`3b28cb54`): muGrid 自身の ω (`chiColumn`) を §6 `↥M` から §10 `G` へ
  `e : ↥tic.W ≃* ↥(h.W1⊔h.W2)` (`subgroupOfEquivOfLe.symm` ∘ `subgroupCongr`) で transport し σ_∫。
  infra: `typePData_W2_le_self`/`typePData_W_le_self`/`typePData_sup_subgroupOf_eq` + `ClassFunction.compHom`。
- ✅ `Hypothesis.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` (`dda1134c`): **V 上で
  `μ_ij(v) = δ_j · alignedOmegaSigma_ij(v)`**。M-side (4.3.c) + σ-side (`sigmaIntegral_apply_of_mem_V`+`compHom_apply`)
  + `e` が v を保つ (`he_coe`: `subgroupCongr_apply` rfl + `subgroupOfEquivOfLe.symm` 定義的) → 両 chiColumn 引数一致。
- ⟹ aligned design 検証完了。per-(i,j) (10.5) identity が provable に (raw omegaSigmaGrid では不可能だった)。

## ✅✅✅ 進捗 (2026-06-21 cont.) — value-on-V leg DONE (2 analytic leg のうち 1 本)

下記「残り 2」の **value-on-V leg を grid-level で完全形式化** (`0601b2bb`, build-green 3818 jobs)。
原文「By (3.2.c), (4.3.c) and the definition of τ, α_ij^τ − δ(ω_ij^σ − ω_i0^σ) vanishes on V」を honest 実装:

- ✅ `Hypothesis.tau_muGridAlpha_apply_eq_on_typePV` (leg 本体): **V 上で
  `hyp.tau (μ_ij − δ·μ_i0 − n·ζ) v = δ·(ω_ij^σ − ω_i0^σ)(v)`** (ω^σ = alignedOmegaSigmaGrid)。
  cornerstone `tau_apply_of_mem_typePV` (α は A₀ supported ∵ `muGrid_alpha_support` → τ が V で α 復元)
  + reconciliation `muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` (j と 0 の両方)
  + `muColumnSign_zero` (δ_0=1) + ζ-vanishing (induced from normal M', v∉M')。
- ✅ `typePData_typePV_not_mem_derived` (**完全 axiom-clean** `[propext,Classical.choice,Quot.sound]`):
  v∈V ⟹ v∉M'。↥W (abelian) で v=x·y 分解 (`Subgroup.mem_sup`) → W₂≤M' ∧ W₁⊓M'=⊥ (`M_complement`)
  ⟹ x=1 ⟹ v=y∈W₂ 矛盾。ζ-vanishing on V の構造的核心。
- ✅ `Hypothesis.muColumnSign_zero` (δ_0=1): column-0 dual = trivial (`finCardEquivCharacterGroup_zero`)
  + trivial column sign=1 (`certainType_zero_column_anchor.1`)。
- axiom footprint: leg/muColumnSign_zero = `[propext, sorryAx, Classical.choice, Quot.sound]`
  (sorryAx = §10 muGrid 系と同じ上流 bridge gate Prop16.1/theoremA、**自前 sorry 無**)。

**▶ 残り (full `alpha_tau_image` を閉じるための 2 gate)**:
1. **carrier pinning** (⚠ 要ユーザー判断・cross-file): producer `exists_charParameters` の
   `omegaSigma := hyp.omegaSigmaGrid` を `alignedOmegaSigmaGrid` に差し替え + `CharacterParameters` に
   identity field (`mu_def`/`omegaSigma_def`)。ただし `CharacterParameters` は `hG`/`hodd` を carry せず
   (S13 cascade 回避のため structure param 化は危険、note cont. 参照) ⟹ identity field でなく
   **`alpha_tau_image` を grid-level の `Hypothesis.tau_muGridAlpha_eq` 定理に再構成**し params 版を
   薄い corollary (`hmu`/`hos`/`hzeta` hypothesis で grid に紐付け) にするのが本筋。
2. **a=0 norm 論証** (deep, multi-session): `(α^τ, ζ^{τ₁})=a−n` 定義 → `(α^τ,(ζ−ζ̄)^τ)=−n` (τ isometry)
   → `(α^τ, μ_k^{τ₁})=da` (k≠j,0) → Cauchy-Schwarz `d²a² ≤ ‖α^τ‖²‖μ_k^{τ₁}‖²=(2+n²)w₁` → n<2 矛盾
   ((10.3) n even>0) → `α^τ = X − nζ^{τ₁}`, `‖X‖²=2`, X⊥ζ^{τ₁} → ζ^{τ₁} vanishes on V (5.3.b/5.5/3.2.d)
   → ψ=X−δ(ω^σ diff) vanishes on V (**= leg ✅ + 上記**) → NC(ψ)≤4<2inf(w₁,w₂) → (3.8) → ψ=0。
   要 §3 NC machinery (3.6/3.8) + §5 (5.3.b)/(5.5) + τ-inner-product isometry + μ-grid orthonormality。

## やること (旧)

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
  - **▶ build entry-point (2026-06-21 atomize)**: reconcile は **value-level の character transport を一から build**
    する。`omega`/`omegaProdChar`/`charEquiv` は **W のみ依存** (V/Dade 非依存) ゆえ:
    - atom (1) `omega_apply` (`S05_TICyclic:330`): `omega χ w = χ w`。
    - atom (2) `omegaProdChar χ₁ χ₂ (w) = χ₁ (wFst w) · χ₂ (wSnd w)` (`wFst`/`wSnd` = W₁/W₂ 成分射影,
      `S05_TICyclic:488-501`)。
    - ⟹ `chiColumn_6@↥M(v)` と `omegaGrid_5@G(v)` を両方 dual 値に分解し、`wFst`/`wSnd` の M.subtype 転送 +
      **index 対応** (§6 χ₂ = `finCardEquivCharacterGroup j` ⟦muGrid def⟧ vs §5 `charEquiv W2_le_W j`) を示す。
    - ⚠ `mapOfInjective` (`S05_TICyclic:97`, ↥L→G 転送、docstring が「§6 toTICyclicHypothesis を G に lift」と明記)
      は **定義済だが全くの未使用** (omega/charEquiv transport lemma ゼロ)。∴ transport API は新規 build。
      §5 tic は mapOfInjective 経由でなく G に直接構成ゆえ、tic = `mapOfInjective sdiff M.subtype` の証明も要
      (W は一致するが V が異なる ⟹ 構造 eq でなく omega-grid value 一致を狙う)。
    - 他の bridge 部品: ζ-vanishing on V = `induce_eq_zero_of_not_mem_normal` (ζ∈inducedFamily, v∈V⟹v∉M' ∵
      W₁-成分非自明 + W₁∩M'=1; `muGrid_alpha_support` 内に pattern 既在)。M-side = (4.3.c)。σ-side = inline。
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
