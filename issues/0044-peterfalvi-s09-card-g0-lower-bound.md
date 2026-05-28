---
id: 44
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
| (7.1) Hypothesis | (2.2) + `ρ : CF(G) → CF(L,A)` (`χ^ρ(a) = |H(a)|⁻¹ Σ_{x∈H(a)} χ(ax)`), `A^τ = ⋃_{a∈A} (aH(a))^G` | ⬜ 未 stmt |
| (7.2) Lemma | (a) `α ∈ CF(L,A) ⇒ α^{τρ} = α`. (b) `‖χ^ρ‖² ≤ ‖χ‖²`, 等号 ⟺ `χ ∈ im τ`. | ⬜ 未 stmt |
| (7.3) Lemma | `|G|⁻¹ Σ_{A^τ} \|χ\|² ≥ ‖χ^ρ‖²`, 等号 ⟺ `χ` が `aH(a)` 上定数 | ⬜ 未 stmt |
| (7.4) Hypothesis | 部分群族 `(L_i)`, 各 (7.1), `A_i^{τ_i}` pairwise disjoint, `G_0 = G - ⋃ A_i^{τ_i}` | ⬜ 未 stmt |
| (7.5) Theorem | `|G|⁻¹(Σ_{G_0}\|χ\|² - |G_0|) + Σ_i (‖χ^{ρ_i}‖² - |A_i|/|L_i|) ≤ 0` | ⬜ 未 stmt |
| (7.6) Hypothesis | normal `H ⊴ L`, `A = H^#`, `|H|=h`, `|L:H|=e`, `T = {Ind_H^L θ}` | ⬜ 未 stmt |
| (7.7) Lemma | `χ^ρ(x) = Σ c̄_i/‖ζ_i‖² · ζ_i(x)` の explicit formula, `‖χ^ρ‖²` 二重和 | ⬜ 未 stmt |
| (7.8) Lemma | (a) `β = 1_G - ζ^ν + a·Σ + Γ` の形, `a ∈ ℤ`. (b) `‖ζ^{νρ}‖² ≥ 1 - e/h`, `‖Γ‖² ≤ e-1`. (c) `χ ⊥ S^ν ⇒ ‖χ^ρ‖² = |A|/|L|·(β,χ)²`. | ⬜ 未 stmt |
| (7.9) Key Lemma | `I={1,2}`, `G` 奇位数, coherent ⟹ `(β_1, ζ_2^{ν_2}) ≠ 0` または `(β_2, ζ_1^{ν_1}) ≠ 0` | ⬜ 未 stmt |
| (6.8) Theorem | 直交族分解 `Ind_{L_i}^G (ζ_{it} - d_{it}ζ_{i1}) = χ_{it} - d_{it}χ_{i1}` | ⬜ 未 stmt (S08 SibleySetup あり) |
| Thompson kernel-nilpotent | Frobenius kernel 冪零 | ✅ Isaacs Ch.6 |
| (7.10) | 上記の合成 + 算術操作 | ⬜ sorry (S09:217) |

各内部依存: (7.2)←(2.7),(2.6); (7.3)←(7.2); (7.5)←(7.3); (7.7)←(7.6);
(7.8)←(7.7),(1.5),(2.7); (7.9)←(7.8),(5.9),(1.1),(4.1); (7.10)←(7.5),(7.8),(7.9),(6.8) + Thompson; (7.11)←(7.10).

## やること (粒度別)

サブ issue 0045+ で分割予定。本 issue は roof tracker。

- [ ] sub-issue: `ρ` map + `A^τ` infrastructure + `CF(L,A)` 用 API (新規 module の可能性)
- [ ] sub-issue: (7.1) `Hypothesis71` structure + (7.2) lemmas
- [ ] sub-issue: (7.3) integral inequality
- [ ] sub-issue: (7.4) family hypothesis + (7.5) main inequality
- [ ] sub-issue: (7.6) hypothesis + (7.7) `χ^ρ` explicit formula
- [ ] sub-issue: (7.8.a/b/c) norm estimates
- [ ] sub-issue: (7.9) 2-family non-orthogonality
- [ ] sub-issue: (6.8) `IndChainDecomposition` (S08 既存 `SibleySetup` を強化)
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
