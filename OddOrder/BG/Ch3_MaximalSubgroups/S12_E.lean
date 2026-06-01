/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch2_Uniqueness.Setup
import OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma
import OddOrder.GroupTheory.MaximalSubgroup
import OddOrder.GroupTheory.ElementaryAbelianFamily
import OddOrder.GroupTheory.NarrowPGroup
import OddOrder.GroupTheory.PRank
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# BG §12: The Subgroup `E`

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §12 (pp. 79-90), mmd `references/bg/local-analysis.mmd`
L3023-3483, **19 結果** (Lem 12.1/12.2/12.11/12.17/12.18/12.19 + Prop 12.4/12.15 +
Thm 12.5/12.7/12.13 + Cor 12.6/12.8/12.9/12.10/12.14/12.16 + Lem 12.3)。

§12 は maximal subgroup `M` の **複合体 `E`** (= `M_σ` の補群、`E ≅ M/M_σ`) の構造を解析する大規模節。
`r(E) ≤ 2`, `E'` nilpotent, 各 Sylow abelian 等。本ファイルは §12 の **定義層 + Lemma 12.1**。

## 定義 (BG → repo, mmd L3029)

- `tau1/tau2/tau3 M` (`Set ℕ`): `σ(M)'` を rank と `π(M')` で 3 分割 (mmd L3029)。
- `SubgroupESetup M E E₁ E₂ E₃`: `E` は `M_σ` の `M` 内補群、`Eᵢ` は `E` の Hall `τᵢ(M)`-部分群。
- `M'` = `Ch2.S07.derivedInG M`; `M_σ` = `S10.Msigma M`; `r_p` = `pRank ↥· p`。
- 固定 G `(hG : IsMinimalSimpleOdd G)` を明示 thread。残り 18 結果 (12.2–12.19) は後続。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §12 prime 分割 τ₁/τ₂/τ₃ (mmd L3029) -/

/-- **BG `τ₁(M)`** (mmd L3029): `{p ∈ σ(M)' | p ∉ π(M') ∧ r_p(M)=1}`。 -/
def tau1 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ p ∉ (Nat.card ↥(Ch2.S07.derivedInG M)).primeFactors ∧ pRank ↥M p = 1}

/-- **BG `τ₂(M)`** (mmd L3029): `{p ∈ σ(M)' | r_p(M)=2}`。 -/
def tau2 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ pRank ↥M p = 2}

/-- **BG `τ₃(M)`** (mmd L3029): `{p ∈ σ(M)' | p ∈ π(M') ∧ r_p(M)=1}`。 -/
def tau3 (M : Subgroup G) : Set ℕ :=
  {p | p ∉ S10.sigma M ∧ p ∈ (Nat.card ↥(Ch2.S07.derivedInG M)).primeFactors ∧ pRank ↥M p = 1}

/-- **BG §12 setup**: `E` は `M_σ` の `M` 内補群 (`M_σ ⊓ E = 1`, `M_σ ⊔ E = M`)、`E₁/E₂/E₃` は
`E` の Hall `τ₁/τ₂/τ₃(M)`-部分群。`E₁₂ = E₁E₂` (= `E₁ ⊔ E₂`)。 -/
structure SubgroupESetup (M E E₁ E₂ E₃ : Subgroup G) : Prop where
  mem_maximal : M ∈ maximalSubgroups G
  E_le : E ≤ M
  E_compl_inf : S10.Msigma M ⊓ E = ⊥
  E_compl_sup : S10.Msigma M ⊔ E = M
  E₁_le : E₁ ≤ E
  E₂_le : E₂ ≤ E
  E₃_le : E₃ ≤ E
  E₁_hall : Ch03.IsHallSubgroup (tau1 M) (E₁.subgroupOf E)
  E₂_hall : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf E)
  E₃_hall : Ch03.IsHallSubgroup (tau3 M) (E₃.subgroupOf E)

/-! ## Lemma 12.1 — `E` の構造の易しい帰結 (mmd L3035) -/

/-- **BG Lemma 12.1** (mmd L3035): §12 setup のもと、
(a) `E'` nilpotent; (b) `E₃ ⊆ E'` かつ `E₃ ⊴ E`; (c) `E₂=1 → E₁≠1`; (d) `E₁`,`E₃` cyclic;
(e) `E=E₁E₂E₃`, `E₂E₃⊴E`, `E₂⊴E₁₂`; (f) `C_{E₃}(E)=1`;
(g) `p∈τ₂(M)`, `A∈ℰ_p²(M)` ⇒ `A∈ℰ_p*(G)` かつ `p` は ideal でない (⇒ `p∉β(G)`)。 -/
theorem subgroupE_basic [Finite G] (hG : IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) :
    Group.IsNilpotent ↥(Ch2.S07.derivedInG E) ∧
    (E₃ ≤ Ch2.S07.derivedInG E ∧ E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G)) ∧
    (E₂ = ⊥ → E₁ ≠ ⊥) ∧
    (IsCyclic ↥E₁ ∧ IsCyclic ↥E₃) ∧
    (E = E₁ ⊔ E₂ ⊔ E₃ ∧
      E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) ∧
      (E₁ ⊔ E₂ : Subgroup G) ≤ Subgroup.normalizer ((E₂ : Subgroup G) : Set G)) ∧
    Subgroup.centralizer (E : Set G) ⊓ E₃ = ⊥ ∧
    (∀ p : ℕ, p ∈ tau2 M → ∀ A : Subgroup G, A ≤ M → A ∈ elemAbelianOfRank G p 2 →
      IsMaximalElementaryAbelian p A ∧ ¬ S10.idealPrime p G) := by
  sorry

/-! ## §12 追加結果 (clean core; 多部分の一部は後続) -/

/-- **BG Lemma 12.2(a)** (mmd L3062): `X` を `M` の非自明 `p`-部分群、`M* ∈ ℳ(N_G(X))` とすると
`p ∈ σ(M*) ∪ τ₂(M*)`。(原典 (b) の τ₁∪τ₃ 非共役は後続。) -/
theorem prime_mem_sigma_or_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥) (hXp : IsPGroup p ↥X)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    p ∈ S10.sigma Mstar ∨ p ∈ tau2 Mstar := by
  sorry

/-- **BG Proposition 12.4(a)** (mmd L3023-): `A ∈ ℰ_p²(M)` なら `C_G(A) ⊆ M`。
(原典 (b): `N_G(A₀)` の uniqueness ⇒ `p∈σ(M), M_α=1, M_σ` nilpotent は後続。) -/
theorem centralizer_le_of_elemAb_rank_two [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  sorry

/-- **BG Theorem 12.13** (mmd L3023-): `G` のすべての非可換 `p`-部分群は `𝒰` に属す。 -/
theorem nonabelian_pgroup_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative P) :
    IsUniquelyMaximal P := by
  sorry

/-- **BG Corollary 12.14** (mmd L3023-): `p ∈ σ(M)`, `X ∈ ℰ_p¹(M)`、`p ∈ β(M)` または
`X ⊆ M_σ'` なら `ℳ(C_G(X)) = {M}`。 -/
theorem maximalContaining_centralizer_eq_singleton [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ S10.sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXM : X ≤ M)
    (hcase : p ∈ S10.beta M ∨ X ≤ Ch2.S07.derivedInG (S10.Msigma M)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  sorry

/-- **BG Corollary 12.16(a)** (mmd L3023-): `M` の `σ(M)`-部分群 `Y` は `M_σ` に共役で写せる
(`∃ g ∈ M, Y^g ⊆ M_σ`)。(原典 (b) の rank/derived 評価は後続。) -/
theorem sigma_subgroup_conj_into_Msigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Y : Subgroup G} (hYM : Y ≤ M)
    (hYpi : Subgroup.IsPiSubgroup (S10.sigma M) Y) :
    ∃ g ∈ M, MulAut.conj g • Y ≤ S10.Msigma M := by
  sorry

/-- **BG Lemma 12.17** (mmd L3023-): `C_{M_σ}(E) ⊆ M_σ'` かつ `[M_σ, E] = M_σ`。
(原典の `M_σ ∩ M^g` cyclic 評価は後続。) -/
theorem Msigma_E_relations [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) :
    Subgroup.centralizer (E : Set G) ⊓ S10.Msigma M ≤ Ch2.S07.derivedInG (S10.Msigma M) ∧
    ⁅S10.Msigma M, E⁆ = S10.Msigma M := by
  sorry

end OddOrder.BG.Ch3.S12
