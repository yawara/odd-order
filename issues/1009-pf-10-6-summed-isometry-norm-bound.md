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

- [x] **(5.8) abstract combinatorial core DONE** (2026-06-22, `grid_eq_const_column_of_two_col`,
  `S05_GridTrichotomy.lean`, **axiom-clean** `[propext, Classical.choice, Quot.sound]`)。
  norm-w₁ full-column endgame の純代数核: separable grid `a:ι×κ→ℂ` + 2-column support {j,k} +
  係数 {0,δ}/{0,−δ} (δ=±1) + `∑(a)²=|ι|` ⟹ **単一 full column** (column k=δ / column j=−δ)。
  既存 norm-2 `eq_smul_chiFam_diff_of_vanishOnV` は constant-column を**排除**するが、これは逆に
  **採用** (separability+零列 q₀ で column-constant → Parseval mass → `a(i₀,j)²+a(i₀,k)²=1` →
  {0,±1} で片方のみ ±1)。= (5.8) proof step 4 を忠実に capture、reusable。
- [ ] **(5.8) σ-level wrapper** (残 linchpin、下記スコープ参照; multi-piece): 上記 abstract core を
  `TICyclicHypothesis`-level に wrap。要 (a) **Parseval** `‖X‖²=∑|sigmaCoeff X|²` (X∈chiFam span)、
  (b) **(5.5)** で `μ_k^τ₁` を 2-column σ-combination に分解 (係数 {0,δ}/{0,−δ})、(c) (4.7) A-support、
  (d) sigmaCoeff↔core の hsupp/hnorm 配線 (`sigmaCoeff_add_eq` で separability、(5.5) で係数 bound)。
  - **🔎 resource (次セッション起点、2026-06-22 調査; 要 workability 検証 — 結論の存在≠infra 在庫)**:
    S07 に (5.5) decomposition + Parseval 機構が既存。`S07_RetargetScaled.lean:451` の docstring
    「(5.5) gives `X=∑_{α∈E}α` with `|E|=‖χ‖²` so `‖X‖²=‖χ‖²`」(= core の hnorm 供給源候補) +
    `CharacterDifferenceImage` (`S07_Coherence.lean:395`、`imageSet`/`muClassFunction`/`difference`
    = R(χ) 構造)。⚠ **真の gate は §6 certain-type μ ↔ §5 sigmaCoeff grid の reconcile**
    (notes s12_s10 §更新⁴「deep gate (multi-session)」)。abstract core が hsupp/hnorm/係数 bound を
    どう sigmaCoeff から受け取るかの interface を先に設計せよ。
- [x] **(10.6.a) M→G→τ₁ reduction chain DONE** (2026-06-22, commits `88a95a70`/`3d9eb887`/`a2ff9e18`):
  - M-side diagonal IP `(α_ij, μ_j − dζ̄) = 1` (`muGridAlpha_inner_muColumn_self_sub_conj`)
  - G-side diagonal IP `(α_ij^τ, (μ_j − dζ̄)^τ) = 1` (`muGridAlpha_tau_inner_muColumn_self_sub_conj`)
  - τ/τ₁ split `(α_ij^τ, μ_j^τ₁ − dζ̄^τ₁) = 1` (`muGridAlpha_tau1_inner_muColumn_self_sub_conj`)
  ⟹ (10.6.a) reduction opening 確立。
- **⊥落とし isometry orthogonality 2/3 DONE** (2026-06-22, S12, isometry pattern of `zeta_tau1_inner_self`):
  - `zeta_tau1_inner_conj`: `(ζ^τ₁, ζ̄^τ₁)=0` (**完全 axiom-clean**; isometry + (ζ,ζ̄)=0, ζ̄≠ζ irr)。
  - `zeta_tau1_inner_muColumn`: `(ζ^τ₁, μ_k^τ₁)=0` (sorryAx=upstream muGrid gate のみ=§10 全 muGrid lemma と同一、自前 sorry 0; isometry + ∑_i (ζ,μ_ik)=0 degree mismatch)。
- ⚠ **訂正 (audit over-optimism)**: ⊥落とし の残 3 番目 orthogonality `ζ̄^τ₁⊥Imσ` は **in-stock でない**。
  旧記述「tau1_zeta_vanishes 経由」は誤り — Pf (5.8) 原文では `χ^τ₁⊥Imσ ⟹ vanish on V (by 3.2.d)`
  であって**逆ではない**。vanish-on-V から ⊥Imσ は出ず、これは **§5 (5.3.b)/(5.5) gated** (5.8 σ-wrapper
  と同じゲート)。∴ ⊥落とし全体 = §5 gated; in-stock な 2 orthogonality のみ先行着地。
  残 (10.6.a) = `ζ̄^τ₁⊥Imσ` (§5) + (5.8) σ-wrapper。
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
