---
id: 1009
slug: pf-10-6-summed-isometry-norm-bound
title: "Pf (10.6): summed isometry μ_j^τ₁=δ∑ω_ij^σ + ζ^τ₁ norm bound (gated on §5 (5.8))"
created: 2026-06-22
---

# Pf (10.6): summed isometry + ζ^τ₁ norm bound

## 背景

(10.5) Dade-image identity 締結 (issue 1007/1008 CLOSED) に続く文書順次ターゲット。
`tau1_values_and_norm_bound` (`S12_MaximalIII_IV_V.lean:3521`, sorry) が (10.6) の Lean 化で、
2 つの conjunct を持つ:
1. **(10.6.a) summed isometry**: `∀ j ≠ 0, coh.tau1 (∑_i μ_ij) = δ • ∑_i ω_ij^σ`。
2. **(10.6.b) norm bound** (= opaque `CharacterParameters.zeta_tau1_norm_bound : Prop`, 現 `True`):
   `g ∈ G − Ã(M)` で位数 prime to w₁ ⟹ `|ζ^τ₁(g)| ≥ 1`。

原文 = `references/peterfalvi/04.12_*.mmd` (10.6) (pp. 58-63)。

## ⚠ gate: Peterfalvi (5.8) が未形式化

**(10.6.a) は Peterfalvi (5.8) [§5 Coherence, `references/peterfalvi/04.7_pp_25_29_Coherence.mmd:119`]
に gated**。原文証明:
```
1 = (α_ij, μ_j − dζ̄) = (α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = (δ(ω_ij^σ − ω_i0^σ), μ_j^τ₁)   [by (10.5)]
→ by (5.8), μ_j^τ₁ = δ ∑_i ω_ij^σ.
```
(5.8) は coherence isometry τ₁ の下で column-character μ_k の像を決定する §5 結果 (2 ケース、複雑な
statement)。**S07_Coherence.lean に未形式化** — 本 issue の真の prerequisite。

**(10.6.b)** は (10.6.a) の第2関係式 `(μ_0 − ζ)^τ = ∑_i ω_i0^σ − ζ^τ₁` + parity 論証:
- τ の定義より `(μ_0 − ζ)^τ` は G − Ã(M) で消える ⟹ `ζ^τ₁(g) = ∑_i ω_i0^σ(g)`。
- (3.9.c): `ω_i0^σ(g) ∈ ℤ`。i≠0 で `ω̄_i0 ≠ ω_i0` + (3.9.a) `ω̄_i0^σ = conj(ω_i0^σ)` ⟹ `∑_{i>0} ω_i0^σ(g) ∈ 2ℤ`。
- (3.2.b) `ω_00^σ = 1_G` ⟹ `ζ^τ₁(g) ≡ 1 (mod 2)` ⟹ `|ζ^τ₁(g)| ≥ 1`。
(10.6.b) も (10.6.a) 経由ゆえ (5.8) に gated。(3.9.a)/(3.9.c)/(3.2.b) は §5 (repo S05) に在庫見込み。

## やること

- [ ] **Peterfalvi (5.8) combinatorial core** = 真の linchpin (下記スコープ参照; multi-piece)。
- [x] **(10.6.a) M→G→τ₁ reduction chain DONE** (2026-06-22, commits `88a95a70`/`3d9eb887`/`a2ff9e18`):
  - M-side diagonal IP `(α_ij, μ_j − dζ̄) = 1` (`muGridAlpha_inner_muColumn_self_sub_conj`)
  - G-side diagonal IP `(α_ij^τ, (μ_j − dζ̄)^τ) = 1` (`muGridAlpha_tau_inner_muColumn_self_sub_conj`)
  - τ/τ₁ split `(α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = 1` (`muGridAlpha_tau1_inner_muColumn_self_sub_conj`)
  ⟹ (10.6.a) reduction opening 確立。残 = (1) ⊥Imσ 項落とし `(δ(ω_ij^σ−ω_i0^σ), μ_j^τ₁)=1`
  (ζ^τ₁/ζ̄^τ₁⊥Imσ [tau1_zeta_vanishes 経由] + ζ^τ₁⊥μ_j^τ₁ [isometry+次数] + (10.5))、(2) (5.8) core。
- [ ] (10.6.a): diagonal IP + τ/τ₁ transfer (既存 `muGridAlpha_tau_inner_muColumn_sub_conj` 類比) +
      (5.8) → `μ_j^τ₁ = δ∑ω_ij^σ`。
- [ ] `zeta_tau1_norm_bound` Prop を (10.6.b) の genuine 主張に materialize + 証明。
- [ ] `tau1_values_and_norm_bound` を sorry-free に。

## 📋 (5.8) 詳細スコープ (2026-06-22 lane-b 精読) — multi-session piece

(5.8) [`04.7:119`] = coherence isometry τ₁ 下での certain-type column-char μ_k の像決定。原文証明の依存:
1. **(5.5)** `χ^τ₁ = ∑_{α∈E} α (E⊆R(χ))` ← (5.4) with ψ=0。**(5.4) は repo S07 在庫**。R(μ_j)=
   `{δ_j ω_ij^σ, −δ_j ω_ik^σ}` (2-column σ-構造, k=conj(j) 列) ← (5.3.b)/(4.9)。⟹ μ_k^τ₁ = ∑_i a_ik ω_ik^σ
   + ∑_i a_ij ω_ij^σ, a_ik∈{0,δ_k}, a_ij∈{0,−δ_k}。
2. **μ_k^τ₁ vanishes on V** (crux) ← χ∈S∩Irr(L)(=ζ deg w₁) + **(4.7)** `χ(1)μ_k−μ_k(1)χ ∈ ℤ[S,A]`
   + **ζ^τ₁ vanishes on V (✅ `tau1_zeta_vanishes_on_typePV`)** + A∩V=∅ + τ 定義。
3. **(3.7) separability** ⟹ a_ik=a_0k, a_ij=a_0j (row-constant)。repo S05 `sigmaCoeff_add_eq` 在庫。
4. **‖μ_k^τ₁‖²=w₁** + coeffs∈{0,±1} ⟹ a_0k²+a_0j²=1 ⟹ 一方のみ ±1 ⟹ **full column** δ∑ω_ik^σ or −δ∑ω_ij^σ。
5. uniqueness ("j,k のみ") ← Theorem (4.9) summed isometry (repo S06 `certainType_diff_dade_sum_eq` 在庫)。

**在庫**: (5.4) [S07]、(4.9) summed isometry [S06]、(3.7)/(3.8) [S05]、ζ^τ₁/ζ̄^τ₁ vanish on V [S12]、
diagonal IP `(α_ij,μ_j−dζ̄)=1` [✅本 issue]。**要新規**: (5.5) を certain-type column R(μ_j) で適用する形 +
**(4.7) A-support of `w₁μ_j−dζ`** + **(5.8) combinatorial core** (2-column separable + norm-w₁ → full column,
= 私の (10.5) `eq_smul_chiFam_diff_of_vanishOnV` の full-column 類比、grid 機構流用可) + assembly。

**(10.6.a) §10-specialized route** (full (5.8) より tractable な可能性): reduction
`(α_ij^τ, μ_j^τ₁−dζ̄^τ₁) = (δ(ω_ij^σ−ω_i0^σ), μ_j^τ₁)` は my infra (diagonal IP + ζ^τ₁⊥σ + isometry) で provable
だが、最終 `= δ∑ω_ij^σ` は (5.8) core 必須。⟹ (5.8) combinatorial core (full-column trichotomy) が真の linchpin。

**評価: (5.8) は §5-§8 coherence 機構に深く絡む multi-session piece** (上記 4 新規部品 + assembly、~数百行)。
単発でなく focused 複数セッションで攻めるべき。次着手の clean entry = **(5.8) combinatorial core を S05 一般補題化**
(my (10.5) trichotomy の full-column 類比、§5 σ-machinery のみ依存、reusable)。

## 完了条件

`tau1_values_and_norm_bound` (S12) が sorry-free。axiom footprint = §10 muGrid 系上流 gate のみ。
full build + AxiomsCheck green。

## 参照

- issue 1007/1008 (closed): (10.5) Dade-image identity + (10.3) n-even。
- `tau1_values_and_norm_bound` (S12:3521)、`CharacterParameters.zeta_tau1_norm_bound`。
- (5.8) = `references/peterfalvi/04.7_pp_25_29_Coherence.mmd:119`。
- 上位: [[ft-endgame-two-poles]] / `notes/peterfalvi/s12_s10_character_bridge.md`。
