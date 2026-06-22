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

- [ ] **Peterfalvi (5.8) を S07_Coherence に形式化** (本 issue の prerequisite; 別 issue 化も可)。
- [ ] **M-side diagonal inner product** `(α_ij, μ_j − dζ̄) = 1` (= `muGridAlpha_inner_muColumn_sub_conj`
      の diagonal 版; within-column 正規直交 `muGrid_inner_within_column` で provable NOW, (5.8) 不要)。
- [ ] (10.6.a): diagonal IP + τ/τ₁ transfer (既存 `muGridAlpha_tau_inner_muColumn_sub_conj` 類比) +
      (5.8) → `μ_j^τ₁ = δ∑ω_ij^σ`。
- [ ] `zeta_tau1_norm_bound` Prop を (10.6.b) の genuine 主張に materialize + 証明。
- [ ] `tau1_values_and_norm_bound` を sorry-free に。

## 完了条件

`tau1_values_and_norm_bound` (S12) が sorry-free。axiom footprint = §10 muGrid 系上流 gate のみ。
full build + AxiomsCheck green。

## 参照

- issue 1007/1008 (closed): (10.5) Dade-image identity + (10.3) n-even。
- `tau1_values_and_norm_bound` (S12:3521)、`CharacterParameters.zeta_tau1_norm_bound`。
- (5.8) = `references/peterfalvi/04.7_pp_25_29_Coherence.mmd:119`。
- 上位: [[ft-endgame-two-poles]] / `notes/peterfalvi/s12_s10_character_bridge.md`。
