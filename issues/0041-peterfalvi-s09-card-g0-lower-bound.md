---
id: 41
slug: peterfalvi-s09-card-g0-lower-bound
title: "Peterfalvi (7.10) card_G0_lower_bound を証明する"
created: 2026-05-28
---

# Peterfalvi (7.10) card_G0_lower_bound を証明する

## 背景

`OddOrder/Peterfalvi/S09_NonexistenceCertain.lean` の `card_G0_lower_bound`
(Peterfalvi (7.10), pp. 42-43) は §9 の **数値定理** で, (7.11) 主非存在定理を
(7.10) の系として導く出発点になる。statement は既に書かれており (`72a9864`),
(7.11) も (7.10) modulo で sorry-free にできている。残るは (7.10) 本体の証明。

`isometry_difference_pair_structure` (issue 0025) が sorry-free になったので,
§3 (1.4) 経由の §5 (3.2) / §6 (4.5) / §7 (5.6) の使用前提は整っている。

## 全体構造 (Peterfalvi §9 mmd `04.9_pp_38_43_*.mmd` より)

(7.10) は次の構成ブロックの **合成定理**:

| # | 役割 | 状態 |
|---|------|------|
| (7.1) Hypothesis | (2.2) + `ρ : CF(G) → CF(L,A)` (`χ^ρ(a) = |H(a)|⁻¹ Σ_{x∈H(a)} χ(ax)`), `A^τ = ⋃_{a∈A} (aH(a))^G` | ✅ `Hypothesis71` (issue 0042) |
| (7.2) Lemma | (a) `α ∈ CF(L,A) ⇒ α^{τρ} = α`. (b) `‖χ^ρ‖² ≤ ‖χ‖²`, 等号 ⟺ `χ ∈ im τ`. | ✅ `chiRho_dadeImage_eq`, `chiRho_norm_sq_le` (issue 0042, 等号条件は後回し) |
| (7.3) Lemma | `|G|⁻¹ Σ_{A^τ} \|χ\|² ≥ ‖χ^ρ‖²`, 等号 ⟺ `χ` が `aH(a)` 上定数 | ✅ `chiRho_integral_inequality` (issue 0042, 等号条件は後回し) |
| (7.4) Hypothesis | 部分群族 `(L_i)`, 各 (7.1), `A_i^{τ_i}` pairwise disjoint, `G_0 = G - ⋃ A_i^{τ_i}` | ✅ `FamilyHypothesis71` |
| (7.5) Theorem | `|G|⁻¹(Σ_{G_0}\|χ\|² - |G_0|) + Σ_i (‖χ^{ρ_i}‖² - |A_i|/|L_i|) ≤ 0` | ✅ `family_inequality` (sorry-free) |
| (7.6) Hypothesis | normal `H ⊴ L`, `A = H^#`, `|H|=h`, `|L:H|=e`, `T = {Ind_H^L θ}` | ✅ `Hypothesis76` |
| (7.7) Lemma | `χ^ρ(x) = Σ c̄_i/‖ζ_i‖² · ζ_i(x)` の explicit formula, `‖χ^ρ‖²` 二重和 | ✅ (7.7.a) `chiRho_explicit_formula` (certificate field `chiRho_decomp`) + (7.7.b) `chiRho_norm_sq_double_sum` (proved) |
| (7.8) Lemma | (a) `β = 1_G - ζ^ν + a·Σ + Γ` の形, `a ∈ ℤ`. (b) `‖ζ^{νρ}‖² ≥ 1 - e/h`, `‖Γ‖² ≤ e-1`. (c) `χ ⊥ S^ν ⇒ ‖χ^ρ‖² = |A|/|L|·(β,χ)²`. | 🟡 (7.8.c) `Hypothesis78` + `chiRho_eq_inner_beta_on_A` (certificate field) + `chiRho_norm_sq_eq_card_ratio_mul` (proved); (7.8.a)/(7.8.b) 未 stmt |
| (7.9) Key Lemma | `I={1,2}`, `G` 奇位数, coherent ⟹ `(β_1, ζ_2^{ν_2}) ≠ 0` または `(β_2, ζ_1^{ν_1}) ≠ 0` | ⬜ 未 stmt |
| (6.8) Theorem | 直交族分解 `Ind_{L_i}^G (ζ_{it} - d_{it}ζ_{i1}) = χ_{it} - d_{it}χ_{i1}` | 🟡 `sibleySetup_is_coherent` stmt + `IndChainDecomposition` (issue 0043, 本体 proof 別途) |
| Thompson kernel-nilpotent | Frobenius kernel 冪零 | ✅ Isaacs Ch.6 |
| (7.10) | 上記の合成 + 算術操作 | ⬜ sorry (S09:1589) |

各内部依存: (7.2)←(2.7),(2.6); (7.3)←(7.2); (7.5)←(7.3); (7.7)←(7.6);
(7.8)←(7.7),(1.5),(2.7); (7.9)←(7.8),(5.9),(1.1),(4.1); (7.10)←(7.5),(7.8),(7.9),(6.8) + Thompson; (7.11)←(7.10).

## やること (粒度別)

サブ issue 0042+ で分割予定。本 issue は roof tracker。

- [x] sub-issue 0042: (7.1) `Hypothesis71` + (7.2.a/b) + (7.3) integral inequality (sorry-free)
- [x] sub-issue 0043: (6.8) `sibleySetup_is_coherent` statement + `IndChainDecomposition` consumer interface (proof 本体は別 issue)
- [x] sub-issue: (7.4) family hypothesis + (7.5) main inequality (sorry-free, 2026-05-29)
- [x] sub-issue: (7.6) `Hypothesis76` + (7.7.a/b) `χ^ρ` explicit formula + norm-square double sum (2026-05-29; (7.7.a) は `chiRho_decomp` 証明書フィールド, (7.7.b) は proved)
- [ ] sub-issue: (7.8.a/b/c) norm estimates — (7.8.c) `Hypothesis78` + `chiRho_eq_inner_beta_on_A` (証明書) + `chiRho_norm_sq_eq_card_ratio_mul` (proved) done 2026-05-29; **(7.8.a)/(7.8.b) 未** (`β = 1_G - ζ^ν + aΣ + Γ` 分解と `‖ζ^{νρ}‖² ≥ 1-e/h`, `‖Γ‖² ≤ e-1`)
- [ ] sub-issue: (7.9) 2-family non-orthogonality
- [ ] sub-issue: (6.8) 本体 proof ((6.1)-(6.7), (5.2), (4.6) の積み上げ)
- [ ] (7.10) 最終 assembly: (7.5)(7.8)(7.9)(6.8)+Thompson の連立 + 算術

## 完了条件

- `OddOrder.Peterfalvi.S09.card_G0_lower_bound` の `sorry` が消える。
- `lake build OddOrder.Peterfalvi.S09_NonexistenceCertain` が通る。
- (7.11) 主定理が依然 sorry-free。

## 参照

- depends on: `issues/closed/0025-peterfalvi-isometry-difference-core.md` (済)
- file: `OddOrder/Peterfalvi/S09_NonexistenceCertain.lean`
- file: `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean` (SibleySetup)
- file: `OddOrder/Peterfalvi/S07_Coherence.lean`
- note: `notes/peterfalvi/s09_nonexistence_certain.md`
- mmd: `references/peterfalvi/04.9_pp_38_43_Non-existence_of_a_Certain_Type_of_Group_of_Odd_Order.mmd`
