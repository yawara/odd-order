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
