---
id: 2006
slug: s13-12-13-statements
title: "Lemma 13.12/13.13 statement draft (§14 funnel unblock)"
created: 2026-06-15
---

# Lemma 13.12/13.13 statement draft (§14 funnel unblock)

## 背景

BG §14 funnel の keystone **Prop 14.2** は **Lemma 13.12 / 13.13** に直接依存するが、両者は
`S13_PrimeActionTransition.lean` に **statement すら未記述**で、§14 全体（14.2→14.13）の long pole
になっている（解析: `notes/bg/s14_typeP_counting.md`「🟢 Thm 13.9 landed → … funnel prep」）。

Lane H が両 statement を BG 原文（mmd L3745 / L3765）逐条照合で draft し、**S13 context で elaborate
することを検証済み**（S13_PrimeActionTransition に一時挿入 → leaf build green 3092 jobs → revert）。
**proof は F（S13 owner）が記入**。下の Lean を `S13_PrimeActionTransition.lean` の `end
OddOrder.BG.Ch3.S13` 直前にそのまま貼れる（名前は F の S13 convention に合わせて改名可）。

## やること（F = S13 owner）

- [ ] 下の 2 statement を `S13_PrimeActionTransition.lean` に追加（proof は `sorry` のまま着地でも可）。
- [ ] proof を記入（依存は各 docstring に明記、すべて landed 済 = 13.4/13.6/13.9/12.x）。
- [ ] AxiomsCheck 登録（proof 完了時）。

## 検証済 draft（S13 context で build green）

```lean
/-- **BG Lemma 13.12** (mmd L3745): if `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `q ∈ τ₂(M)`, `A ∈ ℰ_q²(E)`,
and `C_A(P) ≠ 1`, then `C_{M_σ}(P) = 1`.

Proof (BG L3747): suppose `C_{M_σ}(P) ≠ 1`.  By Corollary 12.6(a),(e), `A ◁ E` and
`P ⊄ C_E(A)`, so `Y = C_A(P)` has order `q`.  By Theorem 13.4, `1 ⊂ C_{M_σ}(P) ⊆ C_{M_σ}(Y)`,
hence `𝓜(C_G(Y)) = {M}` by Corollary 12.6(c).  For `M* ∈ 𝓜(N_G(A))` we have `q ∈ σ(M*)` and
`p ∈ τ₁(M*) ∪ τ₂(M*)` by Lemma 12.11.  The case `p ∈ τ₂(M*)` gives `1 ⊂ C_G(P) ∩ M_σ ⊆ M* ∩ M_σ`,
contrary to Theorem 12.5(e); the case `p ∈ τ₁(M*)` gives `𝓜(C_G(Y)) = {M*}` by Lemma 13.6 for
`M*`, contradicting `𝓜(C_G(Y)) = {M}`. -/
theorem Msigma_centralizer_eq_bot_of_tau1_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p q : ℕ} (hp : p ∈ tau1 M) (hq : q ∈ tau2 M)
    {P A : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hA : A ∈ elemAbelianOfRank G q 2) (hAE : A ≤ E)
    (hCAP : A ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  sorry

/-- **BG Lemma 13.13** (mmd L3765): if `p ∈ τ₁(M) ∪ τ₃(M)`, `P ∈ ℰ_p¹(E)`, and `C_{M_σ}(P) ≠ 1`,
then `p ∈ σ(M*)` for every `M* ∈ 𝓜(N_G(P))`.

Proof (BG L3767): by Lemma 12.2, `p ∈ σ(M*) ∪ τ₂(M*)`; suppose `p ∈ τ₂(M*)`.  Pick
`q ∈ π(C_{M_σ}(P))`, `Q ∈ ℰ_q¹(C_{M_σ}(P))`; by Theorem 13.9, `q ∉ σ(M*)`.  Let `E*` be a
complement of `M*_σ` in `M*` containing `PQ`, and `A ∈ ℰ_p²(E*)`; by Corollary 12.6(a), `A ◁ E*`
and `P ⊆ A`.  WLOG `P ≤ E₁` or `P ≤ E₃` (using Corollary 13.11 when `P ⊆ E₃`); Lemma 13.6 gives
`C_G(Q) ⊆ M`, so `A ⊄ C_{E*}(Q)` (as `r_p(M) = 1`), whence `q ∈ τ₁(M*)` by Corollary 12.10(c) and
`P = C_A(Q)`.  Lemma 13.12 for `M*` gives `C_{M*_σ}(Q) = 1`, and Corollary 12.9(c) then yields
`N_G(P) ⊄ M*`, contradicting `M* ∈ 𝓜(N_G(P))`. -/
theorem mem_sigma_of_tau1_tau3_centralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p ∈ tau1 M ∪ tau3 M)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hCP : S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G))) :
    p ∈ S10.sigma Mstar := by
  sorry
```

## 設計メモ（H → F）

- **convention**: `SubgroupESetup M E E₁ E₂ E₃` + `elemAbelianOfRank G p k` + `S10.Msigma`/`S10.sigma`
  + `maximalSubgroupsContaining (Subgroup.normalizer (P : Set G))` — 13.10/13.11 と完全に揃えた。
- **`C_A(P) ≠ 1`** は `A ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥`、**`C_{M_σ}(P)`** は
  `S10.Msigma M ⊓ Subgroup.centralizer (P : Set G)` で表現（13.10 conclusion と同じ idiom）。
- **`P ∈ ℰ_p¹(E)`** は `hP : P ∈ elemAbelianOfRank G p 1` + `hPE : P ≤ E` の 2 仮説に分解。
- proof 依存はすべて landed 済（13.4✅ / 13.6✅ / 13.9✅ / Cor 12.6 / Lem 12.11 / Thm 12.5(e) /
  Lem 12.2 / Cor 13.11[stated, ⏳proof] / Cor 12.10(c) / Cor 12.9(c)）。**13.13 は 13.12 を使う**（順序注意）。
- 名前は仮（descriptive・番号なし規約準拠）。F の S13 convention に合わせて改名可。

## 完了条件

- 両 statement が S13 に landed（最低限 statement、proof は段階的でも可）。
- landed 後、Lane H が Prop 14.2 を assemble して §14 funnel を駆動できる。

## 参照

- mmd `references/bg/local-analysis.mmd` L3745 (13.12) / L3765 (13.13)
- `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeActionTransition.lean`（13.10/13.11 の隣に追加）
- `notes/bg/s14_typeP_counting.md`「ブロッカーの正体」「🟢 Thm 13.9 landed → … funnel prep」
- 依存先 Prop 14.2 = `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean` `typeP_structure`
