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

- [ ] **(iv) `hIM` の discharge** = single-summand W₁-free-orbit propagation:
  `θ₁` が `S₀ = H₁` supported (`H₂…H_q` trivial) なら `w ∈ W₁#` で support が別の Clifford 因子
  `H_j` (j≠1) に移る (`{Hpart j}` の W₁-transitivity, `Hpart_orbit`/`orbitRep`)。よって `χ^w ≠ χ`,
  `I(ζ)∩W₁ = 1`, `I(ζ) ≠ ⊤`。**full-regular の `clifford_caseA_exists_char_inertia_hc_not_fixed`
  より clean** (全因子 nontrivial 不要) だが、single-summand の support を追跡する新補題が要る。
  - 前提: `θ₁` を `Irr(H̄/(H₂…H_q))#` から作る新 constructor (support = S₀ を保証)。
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
