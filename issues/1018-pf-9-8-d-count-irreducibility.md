---
id: 1018
slug: pf-9-8-d-count-irreducibility
title: "Pf (9.8.d): (iv) Ind^M ζ irreducibility + (v) U-orbit/W1 count — close the last (d) sorry"
created: 2026-07-06
---

# Pf (9.8.d): (iv) Ind^M ζ irreducibility + (v) U-orbit/W1 count — close the last (d) sorry

## 背景

`OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean` の `caseA_character_counts` conjunct (d) の
`sorry` (現 ~L11638, 節 `· sorry`)。Peterfalvi (9.8.d): `𝒮(H₀U')` は degree `qa` の既約指標を
少なくとも `((p-1)/a)·(|U|/(a|U'|))` 個含む。

このセッションで **(iii) membership が完全に landed**（下記「済んだ substrate」）。残るは
**(iv) `Ind_{HU}^M ζ` の既約性** と **(v) count** の 2 本で、いずれも genuinely-absent な新 infra を要する。

## 済んだ substrate (このセッション, build-green, sorry/axiom 無)

- **(iii) membership** `Ind_{HU}^M ζ_{θ₁,λ} ∈ 𝒮(H₀U')`:
  - `hcuZetaPair_induceHU_mem_sOf` (最終形) ← `hcuZetaPair_mem_xiOf` ← `hcuZetaPair_mem_xiSet`
    (`H ⊄ Ker`) + `hcuZetaPair_H0supUprime_subset_ker` (`H₀U' ⊆ Ker`)。
  - 支持補題: `hcuPairHom_eq_one_of_mem_realizedH0supUprime` (pointwise kernel),
    `hcuPsiPair_realizedH0supUprime_subgroupOf_subset_characterKernel`,
    `hcuSeedHom_eq_one_of_mem_realizedH0` (θ-ext が H₀=N を kill),
    `hcuThetaHom_inclusion_cuInHu` (θ-ext が complement C_U(S₀) を kill),
    `realizedH0supUprime_le_hcuInHu`, `realizedH0supUprime_eq_realizedH0_sup_uprimeInHu`。
- **(iv) の gated skeleton** `hcuZetaPair_induceHU_irreducible`:
  仮説 `hIM : I(ζ) ≠ ⊤` を取り `Ind_{HU}^M ζ` 既約を返す（`hcZeta_induceHU_irreducible` の
  single-factor mirror、`eq_of_le_of_prime_index` + `isIrreducibleCharacter_induce_of_inertia_eq`）。
  `hIM` = genuinely-hard な W₁-free-orbit fact を honest 仮説として残す（false hyp でも sorry でも無い）。

済んだ degree/source substrate (前セッション): `caseA_exists_irreducible_source_degree_qa`,
`hcuZetaPair_irreducible` (deg a), `hcuZetaPair_induceHU_apply_one` (deg qa), `hcuPsiPair`,
`hcuPairHom`, `index_hcuInHu_eq_caseA_a`, `uprimeSub_le_cuSub`, `realizedH0supUprime_normal_huSub`。

## やること (残り research core)

- [x] **(iv) `hIM` の discharge** = single-summand W₁-free-orbit propagation — **LANDED**
  (2026-07-06, build-green, sorry/axiom 無)。実装は当初想定の「support tracking constructor + `w`-moves」
  ではなく、**既存 `caseA_reducible_theta_regular` の contrapositive** に帰着する clean route:
  - **support witness** `caseA_exists_index_S0_not_le_biSup_compl`: `∃ j₀, ¬ S₀ ≤ ⨆_{j≠j₀} Hpart j`
    (`iSupIndep` + spanning ⟹ `noncommPiCoprod` bijective; nonzero `x∈S₀` は component 射影で
    ある `j₀`-成分が非自明)。
  - **summand-join complement** `caseA_exists_summand_join_complement_S0`: `S₀ ⊕ W = ⊤`,
    `W = ⨆_{j≠j₀} Hpart j` (U-invariant) **かつ `Hpart j₁ ≤ W` (j₁≠j₀, q≥2)**。
    (`W` は order-`p` の `Hpart j₀` を complement ⟹ `[H̄:W]=p`; `S₀⊓W ⊊ S₀` prime ⟹ `⊥`;
    `IsComplement' S₀ W` ⟹ `sup=⊤`。)
  - **non-regular source** `exists_source_char_hom_caseA_nonRegular`: `θ₁` を上記 `W` で作り
    `θ₁.comp (Hpart j₁).subtype = 1` (= 非 regular) を返す。
  - **lies-over descent** `hcuPsiPair_restrict_hInHu_subgroupOf` + `liesOver_of_liesOver_liesOver_subgroupOf`
    (`exists_liesOver_intermediate` の逆向き汎用補題) ⟹ `hcuZetaPair_liesOver_hInHu`
    (`ζ` が `hInHu` で `θ₀` の上に lies over)。
  - **discharge** `hcuZetaPair_inertia_ne_top`: `I_M(ζ)=⊤` を仮定 → `caseA_reducible_theta_regular`
    が `θ₁` regular を強制 → `Hpart j₁` で `θ₁` 非自明のはずが `hnonreg` と矛盾 ⟹ `I_M(ζ)≠⊤`。
  - **unconditional** `hcuZetaPair_induceHU_irreducible_of_nonRegular` /
    `caseA_exists_irreducible_source_degree_qa_induceHU_irreducible`: `hIM` を discharge した
    `Ind_{HU}^M ζ` 既約 (無仮説)。これで (9.8.d) の (iv) member = 既約 ∧ deg `qa` ∧ `HU`-source 既約
    が完成。
- [ ] **(v) count** `((p-1)/a)·|C_U(S₀):U'| = ((p-1)/a)·(|U|/(a|U'|))`:
  - **重要**: `H·C_U(S₀) ◁ HU` (`hcuInHu_normal`) は成立 → U-orbit step は `OrbitOnIrr` の
    `card_image_induce_eq_div` を `H·C_U(S₀)` 上で適用でき `|image|/[HU:H·C_U(S₀)] = |image|/a`。
    (mission note の「C_U(S₀) not normal」は raw C_U(S₀) の話; source subgroup H·C_U(S₀) は normal。)
  - (α) `HU`-conjugation-invariant な pair-family `T = {ψ_{θ₁,λ}}` (各 inertia `= H·C_U(S₀)`):
    **`hcuPsiPair`-conjBy-descent** 補題 (`hcPsi_regular_conjBy` の analog, θ₁ と λ の両方が動く) —
    genuinely absent。`hcuConjDescend`-style の pair 版が要る。
  - (β) domain count `|{(θ₁,λ)}| = (p-1)·|C_U(S₀):U'|` (θ₁: order-p 群の nontrivial char = p-1 個,
    λ: `Irr(C_U(S₀)/U')` = `|C_U(S₀):U'|` 個)。
  - (γ) 第二 induction `ζ ↦ Ind_{HU}^M ζ` の injectivity (= (iv) の W₁-distinctness): distinct `ζ` が
    distinct `𝒮(H₀U')`-member を与える。

## 完了条件

`caseA_character_counts` conjunct (d) の `sorry` が消え (S11 3→2 sorries)、`lake build OddOrder`
が green (sorry/axiom を新規追加しない)。部分的には (iv) 単独 landing でも意味のある前進。

## 参照

- `OddOrder/Peterfalvi/S11_MaximalII_III_IV.lean`: `caseA_character_counts` の docstring
  「**(iii) membership — LANDED** / **Still open** (irreducibility + count)」に (α)(β)(γ) の精密 scope。
- C-side template: `oXtheta_count` (count engine), `hcPsi_regular_conjBy` (T-invariance),
  `card_filter_induce_eq_index_inertia` / `OrbitOnIrr.card_image_induce_eq_div` (orbit count),
  `hcZeta_induceHU_irreducible` (gated irreducibility), `hcZetaPair_mem_xiOf` (membership).
- 原文: `references/peterfalvi/04.11_pp_50_57_...mmd` L79 (statement), L87-90 (proof (d))。

## (v) count 続き (2026-07-06 セッション: route 検証 + prereq landing、build-green)

このセッションで **(v) count の closure route を完全に検証**し、想定より tractable と判明。**`hcuConjDescend`
(pair-conjBy-descent) を新規に建てる必要はない** — (α) は「restriction-characterization + HU-normal 部分群
の kernel-containment 保存」で足りる。以下 route と、その prereq として landed した補題群。

### landed prereq (build-green, sorry/axiom 無, +75 行, full build 3932 jobs exit 0)

- **算術恒等 (goal RHS)**: `card_U_eq_a_mul_card_cuSub` (`|U| = a·|C_U(S₀)|`),
  `card_U_div_a_mul_card_Uprime_eq_relIndex` (`|U|/(a·|U'|) = [C_U(S₀):U'] = (uprimeSub).relIndex (cuSub)`)。
  goal RHS `((p-1)/a)·(|U|/(a·|U'|))` を genuine な `((p-1)/a)·[C_U(S₀):U']` に落とす橋。
- **U'-normality (α の λ-half)**: `uprimeSub_subgroupOf_M_normal` (`U' ◁ M`),
  `uprimeInHu_normal_huSub` (`U' ◁ HU` realized)。`chiefFactor_H0supUprime_subgroupOf_normal` を
  U' 単独に写した版 (`uprimeSub_normalized_by_uW1` + `typeP_H_le_normalizer_uprimeSub`)。

### 検証済み closure route (次セッションで実装, 推定 ~400 行)

- **鍵の単純化 1 (α)**: 族 `T = {ψ_{θ₁,λ}}` を **intrinsic な restriction 条件**で特徴づける:
  χ linear ∧ (H₀-realized ⊆ ker χ) ∧ (**W-lifted ⊆ ker χ**) ∧ (χ|_H ≠ 1) ∧ (**U'-realized ⊆ ker χ**)。
  各条件は「N ◁ HU ⟹ (N ⊆ ker χ) は conjBy 不変」で **HU-conjugation-stable**。必要な normality:
  H₀-realized ◁ HU, W-lifted ◁ HU (W は Ū-invariant, H は H̄ 中心化), U'-realized ◁ HU (今回 landed),
  H-realized ◁ HU (既存)。**`hcuConjDescend` 不要**。`inertia_eq_hcuInHu` で各 member inertia = H·C_U(S₀)
  ((θ trivial-on-W ∧ ≠1) ⟹ nontrivial-on-S₀; H̄/W は order p ゆえ ≠1 ⟺ S₀ 上非自明)。
  → `card_image_induce_eq_div` (`OrbitOnIrr`, `hcuInHu_normal`) で `|image₁| = |T|/a`。
- **鍵の単純化 2 (γ)**: 第二 induction `Ind_{HU}^M` の injectivity は **W₁-part のみ**で足りる:
  ζ ∈ Irr(HU) は自群 HU-conjugation で不変 (`ClassFunction.conjBy_eq_self_of_mem`) ゆえ、
  `induce_eq_induce_iff_conj` の `∃ w∈M` は `∃ w₁∈W₁` に collapse。distinct ζ₁,ζ₂ が W₁-conjugate
  でないことは: 族 member は H₂…H_q ⊆ ker (W-lifted trivial) ゆえ H₁ 上非自明、ζ^{w₁} (w₁≠1) は
  summand permutation で H₁ ⊆ ker → 族外。`caseA_reducible_theta_regular` の summand-permutation
  機構 (landed) を流用。
- **β domain count**: `|T| = (p-1)·[C_U(S₀):U']`。restriction bijection `T ≃ (Irr(H̄/W)\{1}) ×
  Irr(C_U(S₀)/U')`。`card_monoidHom_of_hasEnoughRootsOfUnity` (H̄/W ≅ Z/p で p-1、C_U(S₀)/U' abelian
  ∵ U/U' abelian ⊇ C_U(S₀)/U')。
- **assembly**: `|image₁| = |T|/a = ((p-1)·[C_U(S₀):U'])/a`、γ で `ncard(target) ≥ |image₁|`、
  各 member は irreducible ∧ deg qa ∧ ∈𝒮(H₀U') (全て landed:
  `caseA_exists_irreducible_source_degree_qa_induceHU_irreducible` 系)。
  RHS 算術は今回 landed の恒等で bridge。`≤` の向きは `Nat.div` monotonicity に注意。

## (v) count セッション 2 (2026-07-06 続き): conjBy-closure 基盤 landed + γ が真の blocker と確定

`caseA_character_counts` conjunct (d) の `sorry` は **未 close** (S11 は依然 3 sorries: 8074/12432/12517 系)。
Coq `typeP_nonGalois_characters` (9.8.d) 原証明 (`PFsection9.v` L844-1254) を精読し、count = 3 ピース
((α) conjBy-closed inertia-=-source family, (β) domain count, (γ) W₁-injectivity) と確定。**(γ) は
repo に完全欠落の hard infra** で、これが真の gating item。

### このセッションで landed (build-green, sorry/axiom 無, full build 3932 jobs exit 0, AxiomsCheck OK)

intrinsic-kernel route ((α) を `hcuPsiPair`-conjBy-descent 無しで閉じる) の linchpin 2 本を S11 に追加:

- **`subsetCharacterKernel_conjBy_of_invariant`** (S11:11695): `A ⊆ ↥K` が `conjByMulEquiv g`-不変 かつ
  `A ⊆ characterKernel χ` ⟹ `A ⊆ characterKernel (conjBy g χ)`。汎用 (K ◁ G 任意)。
- **`conjByMulEquiv_invariant_of_normal`** (S11:11726): `N ◁ K` (実は G-conj-stable) ⟹ `(N:Set ↥K)` は
  全 `g:G` で `conjByMulEquiv g`-不変。上の `hAinv` を供給。
- これで T の intrinsic 特徴づけ `{χ ∈ Irr(H·C_U(S₀)) linear | H₀-realized ⊆ Ker ∧ W-lifted ⊆ Ker ∧
  χ|_H ≠1 ∧ U'-realized ⊆ Ker}` の **conjBy-closure が機械化可能** (各 realized kernel 条件が HU-normal
  ゆえ HU-conj-stable)。**`hcuConjDescend` の pair 版は不要**と再確認。

### 残り (次セッションが直行すべき precise gap; 詳細は `caseA_character_counts` docstring "Still open (v)")

- **(α)-surjectivity**: 上記 characterized χ が全て `ψ_{θ₁,λ}` である (Coq `def_Itheta` = `cfDprodl`/`cfSdprod`
  で χ|_H, χ|_{C_U(S₀)} から θ₁/λ を復元)。各 member inertia = H·C_U(S₀) は `hcuPsiPair_inertia_eq_hcu` (既存)。
- **(β) domain count `|T| = (p-1)·[C_U(S₀):U']`**: restriction bijection `T ≃ (Irr(H̄/W)\{1}) ×
  Irr(C_U(S₀)/U')`。θ-count `p-1` は `card_ne_one_chiefFactorHom` の mirror (order-p `H̄/W≅S₀`;
  本セッションで scratch 検証済 6 行, `card_monoidHom_of_hasEnoughRootsOfUnity` + `exists_ne_one_hom_of_prime_card`)。
  λ-count `[C_U(S₀):U']` は abelian `C_U(S₀)/U'`。RHS 橋は既存 `card_U_div_a_mul_card_Uprime_eq_relIndex`。
- **(γ) W₁-injectivity (真の hard blocker, 完全欠落)**: Coq `injXtheta` (L1233-1253) + `kerH1c` (L1226)。
  `w∈M`, `ζ₁=ζ₂^w` (ζ_i∈Xtheta) ⟹ `w∈HU`: `w=y·w₁` 分解 → `ζ₁=ζ₂^{w₁}` → `W=H₂…H_q ⊆ Ker ζ_i` かつ
  `S₀=H₁ ⊆ Ker(ζ₂^{w₁})` (w₁≠1; `cfker_conjg` が W を S₀ を含む W₁-conjugate へ動かす, (9.7) の
  Clifford 置換 `H̄=⊕S₀^w` 利用) → `H₀U'` 構造 + Frobenius `Ū⋊W₁` が w₁=1 強制。**新 `cfker`-conjugation
  infra 必須** (既存 `caseA_reducible_theta_regular` は別命題; `induce_injective_of_inertia_stable` は
  M-invariant source 用で (9.8.d) の non-invariant source に不適用)。
- **assembly**: `card_image_induce_eq_div` ((α)+`hcuInHu_normal`) ⟹ `|𝒵|=|T|/a`; (γ) ⟹ `induceHU` inj on 𝒵
  ⟹ `ncard ≥ |𝒵| = |T|/a` (`Set.ncard_image_of_injOn`+`Set.ncard_le_ncard`); (β)+橋 ⟹ RHS。

## (v) count セッション 3 (2026-07-06 続き): cfker-conjugation infra + γ reduction frame + β θ-count landed

`caseA_character_counts` conjunct (d) の `sorry` は **依然 open** (S11 comment-stripped sorry = 3)。
本セッションは (γ) の真の linchpin (genuinely-absent `cfker_conjg`) と (γ) の honest reduction frame、
および (β) の θ-numerator を landing。**full build 3932 jobs exit 0, AxiomsCheck OK, sorry/axiom 新規 0**。

### landed (build-green, sorry/axiom 無)

**(γ) infra — cfker-conjugation transport (完全欠落だった brick)**:
- `mem_characterKernel_conjBy` (S11): `n ∈ Ker(χ^w) ↔ conjByMulEquiv w n ∈ Ker χ` (汎用 K◁G)。
  pointwise。`subsetCharacterKernel_conjBy_of_invariant` の non-invariant 版で、conjugation が kernel を
  どこへ動かすかを正確に追う = Coq `cfker_conjg` 相当。
- `subsetCharacterKernel_conjBy_iff` (S11): 上の subgroup subset 版
  (`(N:Set) ⊆ Ker(χ^w) ↔ ∀ n∈N, w·n·w⁻¹ ∈ Ker χ`)。γ で `S₀ ⊆ Ker(ζ₂^{w₁})` を
  `w₁·S₀·w₁⁻¹ ⊆ Ker ζ₂` に落とす形。

**(γ) frame — injectivity の honest reduction**:
- `induceHU_eq_induce` (S11): wrapper unfold (`induceHU χ = Ind_{HU} χ`, Invertible instance subsingleton)。
- `induceHU_eq_imp_exists_conj` (S11): `Ind_{HU}^M χ = Ind_{HU}^M ψ ⟹ ∃w∈M, ψ^w = χ`
  (`induce_eq_induce_iff_conj` を wrapper level で)。
- `induceHU_inj_of_conj_mem_huSub` (S11): **(γ) を純群論命題 `hcrit` に還元** — 「family member を
  互いに写す M-conjugation w は必ず w∈HU」を仮定すれば `induceHU` は {χ,ψ} で injective
  (HU-conj は inner ゆえ `conjBy_eq_self_of_mem`)。これで (γ) の残りが `hcrit` 一点に集約。

**(β) θ-numerator (完全)**:
- `card_hom_triv_W_eq_card_quotient` (S11): `#{θ:H̄→*ℂˣ | W ≤ ker θ} = |H̄/W →* ℂˣ|`
  (QuotientGroup.lift 双射)。
- `card_theta_triv_W_nontriv_S0` (S11): `#{θ | W ≤ ker θ ∧ θ|_{S₀} ≠ 1} = p-1`
  (`IsComplement'.QuotientMulEquiv` で `|H̄/W| = |S₀| = p`、Pontryagin、W-trivial∧S₀-trivial ⟹ trivial
  で trivial hom 1 個除去)。= domain count の `(p-1)` factor。

### 残り (次セッションの precise gap — docstring "Still open (v)" 更新済)

- **(γ) `hcrit`** (frame で集約済、残る hard core 2 本):
  1. `W = H₂…H_q ⊆ Ker ζ_i` — source hom の `θ|_W = 1` を `Ind_{H·C_U(S₀)}^{HU}` 経由で ζ に伝播
     (`hcuZetaPair_H0supUprime_subset_ker` の W-summand-complement 版; W-lifted を HU に realize + kernel induce)。
  2. `w₁·S₀·w₁⁻¹ ⊆ W` (w₁≠1) — (9.7) Clifford orbit `H̄=⊕_{w∈W₁} S₀^w` を **HU realized level** で。
  + `M = HU⋊W₁` 分解 (`data.M_complement`) + `conjBy y` inner + 上の cfker-transport で組む。
- **(α)-surjectivity** — 前セッションと同じ (Coq `def_Itheta` cfDprod/cfSdprod)。
- **(β) 残り** — θ-count×λ-count を product bijection で組む (α 必要)。
- **assembly** — `induceHU_inj_of_conj_mem_huSub` + `card_image_induce_eq_div` で組む (frame 準備済)。

### issue 1018 訂正
- 前セッション note の「θ-count は `card_ne_one_chiefFactorHom` の mirror」→ 実際は
  `card_theta_triv_W_nontriv_S0` として **W-trivial 制約付きで独立に landed** (chiefFactorHom は全 H̄ 対象で
  W-summand 版ではない)。今 build-green。
- 「`cfker`-conjugation infra 必須」→ **本セッションで landed** (`mem_characterKernel_conjBy` /
  `subsetCharacterKernel_conjBy_iff`)。γ は now `hcrit` の 2 本 (W⊆Ker propagation + S₀ orbit) に絞り込み済。

## (v) count セッション 4 (2026-07-06 続き): γ core (1) 完全 landed + hcrit assembly 完成 — 残る唯一の gap = (9.7.a) W₁-free-orbit

`caseA_character_counts` conjunct (d) の `sorry` は **依然 open** (S11 comment-stripped sorry = 3;
full build 3932 jobs exit 0)。本セッションで **γ の 2 core のうち core (1) を完全に discharge** し、
**`hcrit` assembly を完成** (M=HU⋊W₁ 分解 + conjBy 還元 + cfker-conjg + core(1) を全て実証明)。
残る唯一の gap は **core (2) = Peterfalvi (9.7.a) の W₁-free-orbit 構造** で、これは
`CliffordCaseAData` の abstraction が deliberately elide している genuine prerequisite と**確定**。

### landed (build-green, sorry/axiom 無, full build 3932 jobs exit 0)

**γ core (1) — `W = H₂…H_q ⊆ Ker ζ` 完全実装** (前 note の想定通り `hcuZetaPair_H0supUprime_subset_ker`
の mirror):
- `caseA_realizedComplement` (def): chief-factor subgroup `W ⊆ H̄` を G に realize (`(W.comap (mk' N)).map H.subtype`)。
- realized W の基本補題: `caseA_realizedComplement_le_H` / `H0_le_caseA_realizedComplement` /
  `caseA_realizedComplement_subgroupOf_le_hInHu` / `caseA_realizedComplement_subgroupOf_hInHu_eq_comap`
  (realized W in hInHu = `W.comap (mk'∘hInHuEquivH)`, `realizedH0_subgroupOf_hInHu_eq_comap` の一般版)。
- seed/pair 上の消滅: `hcuSeedHom_eq_one_of_mem_realizedComplement` (θ|_W=1 ⟹ seed=1 on realized W),
  `hcuPairHom_eq_one_of_mem_realizedComplement`, `hcuPsiPair_realizedComplement_subset_characterKernel`。
- **HU-normality** `caseA_realizedComplement_uW_le_normalizer` (`H⊔U ≤ N(WG)`; H̄ abelian ⟹ WH ◁ H, U-inv ⟹ U 正規化) +
  `caseA_realizedComplement_subgroupOf_huSub_normal` (`le_normalizer_comap` で huSub-realize)。W₁ は不要 (HU で十分)。
- **capstone** `hcuZetaPair_summandComplement_subset_ker`: realized W ⊆ Ker ζ (`subsetCharacterKernel_induce_of_subgroupOf`)。
  = Coq injXtheta の `H₂…H_q ⊆ Ker χ` (`kerH1c`)。
- 補助 `caseA_hInHu_le_realizedS0_sup_realizedComplement`: `S₀⊔W=⊤` ⟹ `hInHu ≤ realizedS₀ ⊔ realizedW`
  (`comap_sup_eq` surjective + preimage-of-⊤; H̄ abelian で mem_sup_of_normal)。

**γ `hcrit` assembly — 完成 (core (2) = horbit を honest 仮説として集約)**:
- `hcrit_of_summand_orbit`: 3 仮説 (`hS0notker`: realized S₀ ⊄ Ker ζ₁ [member は θ₁≠1 on S₀ ゆえ真];
  `hkerW₂`: realized W ⊆ Ker ζ₂ [core (1) で discharge 可]; `horbit`: **w₁∈W₁# が realized S₀ を realized W へ動かす**)
  ⟹ `hcrit`。証明は Coq injXtheta を逐語再現: w=a·w₁ (M=HU⋊W₁, `M_complement`) → conjBy a inner →
  conjBy w₁ ζ₂ = ζ₁ → w₁≠1 なら realized S₀ ⊆ Ker ζ₁ (cfker-conjg `mem_characterKernel_conjBy` で
  w₁·s·w₁⁻¹∈W⊆Ker ζ₂) が `hS0notker` と矛盾 → w₁=1 → w∈HU。**kernel-subgroup 不要な clean route**
  (H̄⊆Ker でなく S₀⊄Ker で矛盾)。

### 残る唯一の gap = core (2) `horbit` = Peterfalvi (9.7.a) W₁-free-orbit (`CliffordCaseAData` に欠落)

**確定した構造 gap**: `CliffordCaseAData` は summands を `Hpart : Fin q → Subgroup H̄` +
`orbitRep : Fin q → ↥(U⊔W₁)` (choice function 由来, `clifford_caseA_data` の
`exists_supIndep_aInvariant_family_of_iSup`) で持つが、**Peterfalvi (9.7.a) の `{Hᵢ}={H₁^w|w∈W₁}`
(= summands が S₀ の W₁-共役軌道、W₁ で自由に添字づけ) を持たない**。よって「w₁∈W₁# が S₀ を別の
summand (⊆W) へ動かす」(`horbit`) は現構造から**導出不可**。導出には (9.7.a) の再構成が要る:
W₁ が U-invariant summands を置換 (W₁ が U を正規化 ∵ Frobenius UW₁, U が各 summand を保存) →
UW₁-irreducibility で transitive → |W₁|=q=#summands prime ゆえ free。これは数百行の独立 prerequisite。

**次セッションの選択肢** (どちらも genuine): (A) `CliffordCaseAData` に W₁-orbit field を追加 +
producer `clifford_caseA_data` で (9.7.a) 再構成を供給 (signature 変更; 全 S11/S12 consumer に影響)。
(B) 既存 field + Frobenius UW₁ から `horbit` を派生する standalone 補題を建てる (prime-transitive⟹free)。
どちらも `horbit` を埋めれば `hcrit_of_summand_orbit` で (γ) が unconditional になり、(α)(β) + assembly
で (9.8.d) sorry が閉じる。

### 訂正
- mission note「core (2) は orbit API (`Hpart`/`orbitRep`/`S0`) で足りる」→ **誤り**。orbitRep は
  W₁-valued/free でなく choice-derived U⊔W₁ 元。core (2) は (9.7.a) 構造 (現状欠落) を要する。
- assembly は当初「H̄⊆Ker ζ₁ で xiSet と矛盾」想定 → **kernel-is-subgroup (|χ|≤χ(1) equality, repo 未整備)
  を要するため回避**。代わりに「realized S₀ ⊄ Ker (member は θ₁≠1 on S₀)」で矛盾させ clean 化。

## (v) count セッション 5 (2026-07-06 続き): (9.7.a) W₁-free-orbit を再構成 → γ の `horbit` を DISCHARGE (option B 実現)

`caseA_character_counts` conjunct (d) の `sorry` は **依然 open** (S11 comment-stripped sorry = 3:
8283 SibleyTarget / 13347 (9.8.d) / 13421 (11.7); α surjectivity + β + assembly が残るため予定通り)。
本セッションで **γ の唯一の残 gap だった `horbit` (= Peterfalvi (9.7.a)) を完全に discharge**。
**選択肢 (B) を実現** — `CliffordCaseAData` の signature 変更 (option A) は**不要**と確定し、既存 field
(`S0`/`S0_aInvariant`) + `chief.quotient_chiefFactor` (U W₁-irreducibility) + Frobenius から
standalone に (9.7.a) を再構成した。**full build 3849 jobs 相当 exit 0, AxiomsCheck OK, sorry/axiom 新規 0**。

### 前セッション note の訂正 (重要)
- 「(9.7.a) の再構成は数百行の独立 prerequisite」「W₁-orbit field 追加 (option A) で全 consumer に影響」
  → **実際は ~200 行の standalone 補題群で足り、structure 変更ゼロ**。鍵は既存 infra の再利用:
  - `iSup_smul_eq_top_of_irreducible` (U W₁-orbit spanning ← `chief.quotient_chiefFactor`)
  - `iSup_phi_smul_eq_iSup_W_of_normal` (U W₁-orbit を W₁-orbit に collapse; U-invariance)
  - `noncommPiCoprod_bijective_of_card` (spanning + `∏|S₀^w| = p^q = |H̄|` ⟹ 直積 bijective)
  - **S₀ の U-irreducibility は不要** (|S₀|=p ゆえ自動; orbit の spanning だけ irreducibility を使う)。
- 「core (2) は (9.7.a) 構造 (欠落) を要する」は正しかったが、その構造は **carrier に足すのでなく
  re-derive できる** (choice-derived `Hpart`/`orbitRep` は使わず、`S0` から orbit を作り直す)。

### landed (build-green, sorry/axiom 無)

**汎用 brick** (S11, `noncommPiCoprod_bijective_of_card` の直後):
- `iSupIndep_of_noncommPiCoprod_injective_comm`: CommGroup で noncommPiCoprod injective ⟹ iSupIndep
  (mathlib は逆向き `injective_noncommPiCoprod_of_iSupIndep` のみ)。`Finset.prod_subtype` + `mulSingle`。

**(9.7.a) H̄-level free orbit** (S11, `caseA_S0_card` の直後):
- `caseA_wOrbit` (def): W₁-orbit 族 `w ↦ φ(w)•S₀` (index = `W1.subgroupOf (U⊔W1)`)。
- `caseA_wOrbit_one`: `caseA_wOrbit 1 = S₀`。
- `caseA_wOrbit_iSup`: W₁-orbit が H̄ を張る (U W₁-orbit spanning を W₁ に collapse)。
- `caseA_wOrbit_iSupIndep`: W₁-orbit が iSupIndep (bijective-of-card + 上の brick)。= (9.7.a) の free 添字。
- `caseA_wComplement` (def): `W = ⨆_{w∈W₁#} S₀^w` (Peterfalvi の `H₂…H_q`)。
- `caseA_wComplement_aInvariant` / `caseA_S0_sup_wComplement` (`S₀⊔W=⊤`) /
  `caseA_S0_inf_wComplement` (`S₀⊓W=⊥`, iSupIndep から)。= `H̄ = S₀ ⊕ W`, `[H̄:W]=p`。

**(9.7.a) realized `horbit`** (S11, `caseA_realizedComplement_subgroupOf_huSub_normal` の直後):
- `caseA_wOrbit_horbit`: `hcrit_of_summand_orbit` の `horbit` 仮説そのものを証明。
  descent: `s∈realized S₀` → `x_s:↥H` (`mk'(N)x_s∈S₀`) → conjBy w₁ の H̄-像 =
  `φ(⟨w₁⟩)•(mk' x_s) ∈ φ(⟨w₁⟩)•S₀ = S₀^{w₁}` (`quotientMulAutHom_apply_mk'`) → w₁≠1 ゆえ
  `S₀^{w₁} = caseA_wOrbit ⟨w₁⟩ ≤ caseA_wComplement = W`。= Coq injXtheta の `H₁^w ⊆ H₂…H_q` (w∈W₁#)。

**γ unconditional 化** (S11, `hcrit_of_summand_orbit` の直後):
- `caseA_hcrit_of_member`: `W := caseA_wComplement caseA` に固定し `horbit := caseA_wOrbit_horbit` を供給した
  **無 `horbit`-仮説版 hcrit**。member の 2 事実 (`realized S₀ ⊄ Ker ζ₁`, `realized W ⊆ Ker ζ₂`) だけで hcrit。
  → `induceHU_inj_of_conj_mem_huSub` と合わせて **(γ) は `horbit` について unconditional**。

### 残り (次セッションが直行すべき precise gap; (9.8.d) sorry を閉じるのに必要)

γ の `horbit` は closed。(9.8.d) sorry を閉じる残りは **(α) surjectivity + (β) domain count + assembly** の 3 本:
- **(α)-surjectivity**: characterized χ が全て `ψ_{θ₁,λ}` (Coq `def_Itheta` = `cfDprodl`/`cfSdprod` で
  χ|_H, χ|_{C_U(S₀)} から θ₁/λ 復元)。member inertia = H·C_U(S₀) は `hcuPsiPair_inertia_eq_hcu` (既存)。
- **(β) domain count** `|T| = (p-1)·[C_U(S₀):U']`: θ-count `p-1` は landed (`card_theta_triv_W_nontriv_S0`,
  ただし **W = caseA_wComplement を使う版に instantiate 要**; `caseA_S0_sup/inf_wComplement` が入力)。
  λ-count は abelian `C_U(S₀)/U'`。product bijection で組む (α 必要)。
- **assembly**: `caseA_hcrit_of_member` + `hcuZetaPair_summandComplement_subset_ker`
  (W = caseA_wComplement で `hkerW₂` 供給) + `induceHU_inj_of_conj_mem_huSub` (γ inj) +
  `card_image_induce_eq_div` ⟹ `ncard ≥ |T|/a`; (β) + 既存算術橋で RHS。

## (v) count セッション 6 (2026-07-06 続き): def_Itheta 完全実装 + 両 numerator (θ-count/λ-count) landed — count の数学的コアが全て在庫

`caseA_character_counts` conjunct (d) の `sorry` は **依然 open** (S11 comment-stripped sorry = 3)。
だが本セッションで **(9.8.d) count の数学的コア全体を landing**: **def_Itheta 復元 (mission が
"the last genuinely-substantial piece" と呼んだ (α) surjectivity) を完全実装**し、さらに **(β) の
両 numerator (θ-count は既存 landed、λ-count を新規 landing)** と **family-inertia helper** を追加。
**full build 3932 jobs exit 0, AxiomsCheck OK, sorry/axiom 新規 0**。残るは assembly wiring のみ。

### 重要な発見 (Coq 精読で確定): count は IMAGE-family + injectivity 方式 (surjectivity 不要な Route も可)

`PFsection9.v` L1149-1254 (`typeP_nonGalois_characters` 第2ブロック = (9.8.d)) を精読:
- `Mtheta := [set mod_Iirr (cfIirr (theta i j)) | i in [set~ 0], j in setT]` = **pair-param の IMAGE**
  (`theta i j := cfSdprod defHCH1 (cfDprod defH1CH1 'chi_i (lam j))`)。
- `|Mtheta| = (p-1)·|Clam|` は **injectivity** で (cfSdprodK/dprod_IirrK)。**intrinsic 特徴づけ (def_Itheta
  surjectivity) は Coq では不使用** — conjBy-closure は explicit pair-conjBy-descent (`conjg_Iirr i yb`,
  L1210-1224) で示す。
- `card_imset_Ind_irr` (= Lean `card_image_induce_eq_div`/`_mul_index_eq`) で `|Mtheta|=|Xtheta|·a`。
- 最終 bound は `≤ count` (uniq_leq_size) — image ⊆ target の inclusion + injXtheta。
- **arithmetic に floor 問題なし**: `lb_d | lb_n` を先に証明、`a | (p-1)·|Clam|` は `|Mtheta|=|Xtheta|·a` から自動。

Lean では conjBy-closure を **def_Itheta (intrinsic) 経由**で得る方が pair-conjBy-descent より易しい
(kernel-stability は landed 済) と判断し Route I (intrinsic-T + def_Itheta) を採用。

### landed (build-green, sorry/axiom 無, full build 3932 jobs exit 0)

**def_Itheta 復元 (α surjectivity — mission の "last genuinely-substantial piece" 完了)**:
- `hom_eq_of_eqOn_hInHu_cuInHu`: join 上の hom は H-制限と C-制限で一意 (`MonoidHom.eq_of_eqOn_denseM`,
  `H ⋊ C_U(S₀)` complement)。復元の linchpin。
- `exists_hcuSeedHom_eq_of_realizedH0_ker`: `f_H : hInHu→*ℂˣ` (realizedH0 ⊆ ker) → `θ:H̄→*ℂˣ` で
  `hcuSeedHom θ = f_H` (H̄=H/N へ factor)。
- `hcuSeedHom_hinv_of_comp`: hinv 互換は **abelian ℂˣ への任意の hom で成立** (conjugation inner)。
- `exists_pairHom_eq_of_realizedH0_ker`: hom-form def_Itheta core — `f` (realizedH0 ⊆ ker(f|_H)) =
  `hcuPairHom θ λ` (θ from f|_H, λ := f|_C)。
- `mem_characterKernel_linearIrreducibleCharacter`: linear char の characterKernel = hom の ker。
- `exists_hcuPsiPair_eq_of_linear_realizedH0_ker`: **char-level def_Itheta (surjectivity)** — linear
  `χ` (realizedH0 ⊆ Ker) = `hcuPsiPair θ (hinv) λ`。
- `hcuPsiPair_injective_pair`: pair-param injectivity (restriction で θ,λ 復元; `hcuSeedHom_injective`)。
- `hcuPsiPair_apply_inclusion_cuInHu`: pair char の C-制限 = λ。

**(β) numerator 両方**:
- `card_theta_triv_W_nontriv_S0` (既存): θ-count = p-1。
- `card_hom_triv_N_eq_card_quotient_general` (新, 汎用): `#{f:K→*ℂˣ | N ≤ ker f} = |K/N →*ℂˣ|`。
- `commutator_cuInHu_le_uprimeRealized` (新): `⁅cuInHu,cuInHu⁆ ≤ U'-realized` (cuInHu≤U ⟹ [.,.]≤[U,U]=U')。
- `card_lambda_triv_uprime` (新): **λ-count = [C_U(S₀):U']** (`= (uprimeSub).relIndex(cuSub)`;
  cuInHu/U' abelian → Pontryagin → relIndex_subgroupOf 2 回)。

**family-inertia helper**:
- `hcuPsiPair_family_inertia_eq` (新): θ (W-triv on `caseA_wComplement` + S₀-nontriv) の pair char
  inertia = `H·C_U(S₀)` (`inertia_eq_hcuInHu` + `hcuPsiPair_inertia_eq_hcu`)。fold の入力。

### 残り (次セッションが直行すべき precise gap = assembly wiring のみ)

数学的コアは全て在庫。残るは **mechanical な assembly** (推定 ~150-200 行):
1. **family Finset `Mtheta`**: `(Dθ ×ˢ Dλ)` の `.attach` 上で `(θ,hθ,λ) ↦ hcuPsiPair θ (hinv from hθ) λ`
   の image。`|Mtheta| = |Dθ|·|Dλ| = (p-1)·[C:U']` (`hcuPsiPair_injective_pair` + 上の 2 count)。
2. **conjBy-closure** (`card_image_induce_mul_index_eq` の `hT`): `conjBy g ψ ∈ Mtheta`。
   `conjBy g ψ` は linear ∧ 4 kernel 条件 (realizedH0/W/U'⊆Ker, |_H≠1; **全て conjBy-stable** ←
   `subsetCharacterKernel_conjBy_of_invariant`+`conjByMulEquiv_invariant_of_normal` landed) →
   `exists_hcuPsiPair_eq_of_linear_realizedH0_ker` で pair char → kernel 条件を domain 条件 (θ' W-triv,
   S₀-nontriv, λ' U'-triv) に翻訳して `(θ',λ')∈Dθ×Dλ`。**翻訳の逆補題** (realizedW⊆Ker ⟺ θ W-triv 等)
   が要 (一部 landed: `hcuPsiPair_realizedComplement_subset_characterKernel`)。
3. **fold**: `card_image_induce_mul_index_eq` (H:=hInHu⊔cuInHu ◁ huSub; conjBy-closure + inertia
   `hcuPsiPair_family_inertia_eq`) ⟹ `|𝒴|·a = |Mtheta|`。
4. **target-membership**: `𝒴` の各 `Ind_{HCH1}^{HU} ψ` を `Ind^M` した member が irreducible ∧ deg qa ∧
   ∈𝒮(H₀U') (`hcuZetaPair_induceHU_mem_sOf` + `caseA_exists_irreducible_source_degree_qa_induceHU_irreducible`)。
5. **γ inj**: `induceHU` inj on 𝒴 (`caseA_hcrit_of_member` + `induceHU_inj_of_conj_mem_huSub`)。
6. **ncard bound**: `Set.ncard_le_ncard` (subset) + `InjOn.ncard_image` ⟹ `ncard ≥ |𝒴| = |Mtheta|/a`。
7. **arithmetic**: `((p-1)/a)·(|U|/(a|U'|)) ≤ (p-1)·[C:U']/a = |𝒴|` via `Nat.le_div_iff_mul_le` +
   `Nat.div_mul_le_self` + `card_U_div_a_mul_card_Uprime_eq_relIndex`。
