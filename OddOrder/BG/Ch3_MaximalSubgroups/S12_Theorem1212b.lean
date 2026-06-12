/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212

/-!
# BG §12: Theorem 12.12 — Case 3 (abelian Sylow `p`), building blocks

**スコープ**: BG Theorem 12.12 (mmd L3344-3373) の Case 3。`G` の Sylow `p`-部分群が可換で
`τ₂(M) ≠ ∅` のとき、Lemma 12.8 の設定下で `A₀ = E₂` が (a) を満たす。(b) のためには各
`p ∈ τ₂(M)` に対し、`exp(Z) = exp(S)` をもつ cyclic な `N_G(S)`-不変部分群 `Z ≤ S` で
`C_{M_σ}(Ω₁(Z)) = 1` なるものを構成すればよい (`E₀ = E₁E₃·∏Z_p`)。

本ファイルは Case 3 の部品を下から積む。最初の foundational lemma:
**`inf_centralizer_line_eq_bot_of_invariant`** — `N_G(S)`-不変な line `L ≤ S` (`L ∈ ℰ_p¹`) は
自動的に `C_{M_σ}(L) = 1` を満たす (BG L3345-3347 の「key fact」)。`L ≤ Ω₁(S) = A` ゆえ
Cor 12.6(c) が `N_G(L) ⊆ M` を与え、`N_G(S) ≤ N_G(L) ⊆ M` が `N_G(S) ⊄ M` に矛盾。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The maximality predicate making `S` a Sylow `p`-subgroup *of `M`* as well: any `p`-subgroup
`R` of `M` containing `S` equals `S`. Holds because `S` is already a Sylow `p`-subgroup of `G`. -/
theorem sylow_maximal_in_M_of_le {p : ℕ} [Fact p.Prime] {M : Subgroup G} [Finite G]
    {S : Sylow p G} (hSM : (S : Subgroup G) ≤ M) :
    ∀ R : Subgroup G, (S : Subgroup G) ≤ R → R ≤ M → IsPGroup p ↥R → R = (S : Subgroup G) := by
  intro R hSR _ hRpg
  refine (Subgroup.eq_of_le_of_card_ge hSR ?_).symm
  obtain ⟨k, hk⟩ := hRpg.exists_card_eq
  rw [S.card_eq_multiplicity, hk]
  refine Nat.pow_le_pow_right (Fact.out : p.Prime).pos ?_
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne', ← hk]
  exact Subgroup.card_subgroup_dvd_card R

/-- **Theorem 12.12, Case 3 key fact** (BG L3345-3347): since `p ∉ σ(M)` gives `N_G(S) ⊄ M`,
every `N_G(S)`-invariant line `L ≤ S` automatically satisfies `C_{M_σ}(L) = 1`. Indeed `L ≤ A`
(`= Ω₁(S)`, all order-`p` elements), so if `M_σ ⊓ C_G(L) ≠ 1` then Corollary 12.6(c) makes `M`
the unique maximal over `C_G(L)`, forcing `N_G(L) ⊆ M` and hence `N_G(S) ≤ N_G(L) ⊆ M`,
contradicting `N_G(S) ⊄ M`. -/
theorem inf_centralizer_line_eq_bot_of_invariant [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {S : Sylow p G} (hAS : A ≤ (S : Subgroup G)) (hSM : (S : Subgroup G) ≤ M)
    {L : Subgroup G} (hL : L ∈ elemAbelianOfRank G p 1) (hLS : L ≤ (S : Subgroup G))
    (hLinv : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `Ω₁(S) = A` and `N_G(S) ⊄ M` (Theorem 12.5(b) packaging).
  obtain ⟨hΩ, hNS_not_le⟩ := omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM
    S.isPGroup' hAS hSM (sylow_maximal_in_M_of_le hSM)
  -- the line `L ≤ A`: its order-`p` elements lie in `Ω₁(S) = A`.
  have hLA : L ≤ A := by
    rw [hΩ]
    intro g hg
    rw [Subgroup.mem_map]
    have hgS : (g : G) ∈ (S : Subgroup G) := hLS hg
    refine ⟨⟨g, hgS⟩, ?_, rfl⟩
    apply Omega.mem_of_pow_eq_one
    have hgp : (g : G) ^ p = 1 := by
      have h1 := congrArg (Subtype.val : ↥L → G) (hL.1.pow_eq_one ⟨g, hg⟩)
      simpa using h1
    exact Subtype.ext (by simpa using hgp)
  by_contra hne
  -- Corollary 12.6(c): `M` is the unique maximal subgroup over `C_G(L)`.
  have hsingle : maximalSubgroupsContaining (Subgroup.centralizer (L : Set G)) = {M} :=
    maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE hL hLA hne
  -- hence `N_G(L) ⊆ M`.
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hL
  have hNL_lt : Subgroup.normalizer (L : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal (hLA.trans hAM) hLne
  have hNL_le_M : Subgroup.normalizer (L : Set G) ≤ M := by
    obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNL_lt.ne
    have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (L : Set G)) :=
      mem_maximalSubgroupsContaining.mpr
        ⟨hco, (Subgroup.centralizer_le_normalizer _).trans hle⟩
    rw [hsingle, Set.mem_singleton_iff] at hmem
    exact hmem ▸ hle
  exact hNS_not_le (hLinv.trans hNL_le_M)

end OddOrder.BG.Ch3.S12
