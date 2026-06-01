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
import OddOrder.GroupTheory.OmegaSubgroup
import OddOrder.GroupTheory.PRank

/-!
# BG §11: Exceptional Maximal Subgroups

**スコープ**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §11 (pp. 76-79), mmd `references/bg/local-analysis.mmd`
L2913-3022, **7 結果** (Lem 11.1 + Thm 11.3/11.5/11.7 + Cor 11.2/11.4/11.6)。

§11 は **Hypothesis 11.1** (`M ∈ ℳ`, `p ∈ σ(M)'`, `A₀ ∈ ℰ_p¹(M)`, `N_G(A₀) ⊆ M`) のもとで、
*exceptional* maximal subgroup `M` (= `r(H/H_σ)=1` が破れる) の構造を示す: `M_σ` nilpotent (11.3)、
`M` の Sylow `p` abelian (11.5)、`M_σ A ⊴ M` (11.7)。Thompson Transitivity (§7 Thm 7.6) に依存。

## 記法

- 固定 `M, p, A₀` + 導出 `A ∈ ℰ_p²(M)` (`A₀⊆A`, Lem 10.5), `A ⊆ P ∈ Syl_p(M)`, `N_G(P)⊄M`,
  `A∈ℰ_p*(G)` を `Hypothesis111 M p A₀ A P` に束ねる。`M_σ` = `S10.Msigma M`。
- 「`A`-不変 Sylow `q`-部分群」= `IsAInvSylowIn` (M_σ 内の `A`-不変・`q`-極大 部分群)。
- 固定 G `(hG : IsMinimalSimpleOdd G)` を明示 thread。proof は §7/§10 + Thm 3.7 等に依存 (全 sorry)。
-/

namespace OddOrder.BG.Ch3.S11

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Hypothesis 11.1** (mmd L2917) + 導出データ: `M ∈ ℳ`, `p ∈ σ(M)'`, `A₀ ∈ ℰ_p¹(M)`,
`N_G(A₀) ⊆ M`; さらに Lem 10.5 から `A ∈ ℰ_p²(M)` (`A₀⊆A`), `A ⊆ P ∈ Syl_p(M)`, `N_G(P)⊄M`,
`A ∈ ℰ_p*(G)`。§11 全体の standing assumption。 -/
structure Hypothesis111 (M : Subgroup G) (p : ℕ) (A₀ A P : Subgroup G) : Prop where
  mem_maximal : M ∈ maximalSubgroups G
  prime : p.Prime
  notMem_sigma : p ∉ S10.sigma M
  A₀_mem : A₀ ∈ elemAbelianOfRank G p 1
  A₀_le : A₀ ≤ M
  normalizer_A₀_le : Subgroup.normalizer (A₀ : Set G) ≤ M
  A_mem : A ∈ elemAbelianOfRank G p 2
  A_le : A ≤ M
  A₀_le_A : A₀ ≤ A
  P_pgroup : IsPGroup p ↥P
  A_le_P : A ≤ P
  P_le : P ≤ M
  normalizer_P_not_le : ¬ Subgroup.normalizer (P : Set G) ≤ M
  A_maximal : IsMaximalElementaryAbelian p A

/-- `Q` は `H` の `A`-不変 Sylow `q`-部分群 (= `Q ≤ H`, `q`-群, `A`-不変, `H` 内で `q`-極大)。 -/
def IsAInvSylowIn (q : ℕ) (A Q H : Subgroup G) : Prop :=
  Q ≤ H ∧ IsPGroup q ↥Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
    ∀ R : Subgroup G, Q ≤ R → R ≤ H → IsPGroup q ↥R → R = Q

/-- **BG Lemma 11.1** (mmd L2939): Hyp 11.1 のもと、`g ∈ G−M`, `A ⊆ M^g`, `q ∈ σ(M)`、`Q₁`/`Q₂`
を `M_σ`/`M_σ^g` の `A`-不変 Sylow `q`-部分群とする。すると (a) `Q₁ ⊓ Q₂ = 1`、(b) 各 `X ∈ ℰ¹(A)`
で `C_{Q₁}(X) = 1` または `C_{Q₂}(X) = 1`。 -/
theorem invariant_sylow_disjoint [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {g : G} (hg : g ∉ M) (hAg : A ≤ MulAut.conj g • M) {q : ℕ} [Fact q.Prime]
    (hq : q ∈ S10.sigma M) {Q₁ Q₂ : Subgroup G}
    (hQ₁ : IsAInvSylowIn q A Q₁ (S10.Msigma M))
    (hQ₂ : IsAInvSylowIn q A Q₂ (MulAut.conj g • S10.Msigma M)) :
    Q₁ ⊓ Q₂ = ⊥ ∧
    ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ A →
      Subgroup.centralizer (X : Set G) ⊓ Q₁ = ⊥ ∨
      Subgroup.centralizer (X : Set G) ⊓ Q₂ = ⊥ := by
  sorry

/-- **BG Corollary 11.2** (mmd L2946): `g ∈ G−M`, `A ⊆ M^g` ⇒ (a) `M_σ ⊓ M^g = 1`、
(b) `M_σ ⊓ C_G(A₀^g) = 1`。 -/
theorem Msigma_meet_conjugate [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {g : G} (hg : g ∉ M) (hAg : A ≤ MulAut.conj g • M) :
    S10.Msigma M ⊓ MulAut.conj g • M = ⊥ ∧
    S10.Msigma M ⊓ Subgroup.centralizer ((MulAut.conj g • A₀ : Subgroup G) : Set G) = ⊥ := by
  sorry

/-- **BG Theorem 11.3** (mmd L2955): `M_σ` は nilpotent。 -/
theorem Msigma_isNilpotent [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    Group.IsNilpotent ↥(S10.Msigma M) := by
  sorry

/-- **BG Corollary 11.4** (mmd L2959): `H ∈ ℳ(A)` で `M_σ ⊓ H_σ ≠ 1` なら `M = H`。 -/
theorem eq_of_Msigma_meet_Hsigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    {H : Subgroup G} (hH : H ∈ maximalSubgroupsContaining A)
    (hne : S10.Msigma M ⊓ S10.Msigma H ≠ ⊥) :
    M = H := by
  sorry

/-- **BG Theorem 11.5** (mmd L2963): `M` の Sylow `p`-部分群は abelian。 -/
theorem sylow_p_isCommutative [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P)
    (S : Sylow p ↥M) :
    IsMulCommutative (S : Subgroup ↥M) := by
  sorry

/-- **BG Corollary 11.6 (a)(b)** (mmd L2974 付近): (a) `A = Ω₁(P)`、(b) `C_{M_σ}(A) = 1`。
(原典 (c): `g₁,g₂∈N_G(P)−N_M(P)` で `C_{M_σ}(A₀^{gᵢ})=1` ∧ `A=A₁×A₂` — 後続。) -/
theorem omega1_eq_and_centralizer_trivial [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    A = (Omega ↥P p 1).map P.subtype ∧
    Subgroup.centralizer (A : Set G) ⊓ S10.Msigma M = ⊥ := by
  sorry

/-- **BG Theorem 11.7** (mmd L2997): `M_σ A ⊴ M`。§11 の主結果。 -/
theorem MsigmaA_normal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} {p : ℕ} {A₀ A P : Subgroup G} (h : Hypothesis111 M p A₀ A P) :
    M ≤ Subgroup.normalizer ((S10.Msigma M ⊔ A : Subgroup G) : Set G) := by
  sorry

end OddOrder.BG.Ch3.S11
