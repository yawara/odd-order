/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Corollary1214

/-!
# BG §12: Lemma 12.17 (third clause — `M_σ ∩ M^g` is a `β(M)′`-group)

**スコープ**: BG Chapter III §12, Lemma 12.17, third clause (mmd L3478).

`Msigma_E_relations` (`S12_E.lean`) already supplies the first two clauses of Lemma 12.17,
`C_{M_σ}(E) ⊆ M_σ'` and `[M_σ, E] = M_σ`.  This downstream leaf adds the third clause's
`β(M)′`-group part: for `g ∈ G − M`, every prime dividing `|M_σ ∩ M^g|` avoids `β(M)`.

This is the clause consumed by **Proposition 14.2(g)** (`S14_TypePCounting.lean`): together with
the type-`P₂` identity `β(M) = σ(M)` it forces `M_σ ∩ M_σ^g = 1` for `g ∉ M`, i.e. `M_σ` is a
TI-set.  It must live downstream of Corollary 12.14 (which transitively imports `S12_E` via
`S12_Theorem1213`), so it cannot be added to `S12_E` itself (circular import).

**Proof** (BG): for `p ∈ π(M_σ ∩ M^g)` take a rank-one `X ≤ M_σ ∩ M^g` of order `p`.  Then
`X ≤ M` and `X ≤ M^g` with `g ∉ M`; Theorem 10.1(b) (`C_G(X)` is transitive on the conjugates
of `M` containing `X`) produces a `c ∈ C_G(X)` mapping `M` to `M^g`.  If `c ∈ M` then `g ∈ M`,
so `c ∉ M`, i.e. `C_G(X) ⊄ M`, whence `ℳ(C_G(X)) ≠ {M}`.  The contrapositive of Corollary 12.14
then gives `p ∉ β(M)`.

(The full BG clause also asserts `M_σ ∩ M^g` is cyclic and meets `M_σ'` trivially; those parts —
used in §15/§16 — are deferred, mirroring the existing `Msigma_E_relations` docstring.) -/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Lemma 12.17, third clause** (mmd L3478, `β(M)′`-group part): for every `g ∈ G − M`,
the intersection `M_σ ∩ M^g` is a `β(M)′`-group (every prime dividing its order avoids `β(M)`).

Consumed by Proposition 14.2(g): with `β(M) = σ(M)` it yields `M_σ ∩ M_σ^g = 1` for `g ∉ M`. -/
theorem Msigma_inf_conj_isBetaCompl [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∉ M) :
    Subgroup.IsPiSubgroup (S10.beta M)ᶜ (S10.Msigma M ⊓ MulAut.conj g • M) := by
  classical
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hpdvd : p ∣ Nat.card ↥(S10.Msigma M ⊓ MulAut.conj g • M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  -- Cauchy: an element `w` of order `p` in `M_σ ∩ M^g`; `X := ⟨w⟩` is rank-one of order `p`.
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (S10.Msigma M ⊓ MulAut.conj g • M).subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXle : Subgroup.zpowers (w : G) ≤ S10.Msigma M ⊓ MulAut.conj g • M :=
    Subgroup.zpowers_le.mpr w.2
  have hXMσ : Subgroup.zpowers (w : G) ≤ S10.Msigma M := hXle.trans inf_le_left
  have hXM : Subgroup.zpowers (w : G) ≤ M := hXMσ.trans (S10.Msigma_le M)
  have hXgM : Subgroup.zpowers (w : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
  have hXne : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXp : IsPGroup p ↥(Subgroup.zpowers (w : G)) := hXelem.1.isPGroup
  -- `p ∈ σ(M)` since `X ≤ M_σ`.
  have hpσ : p ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨hp_prime, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  -- `N_G(M) = M` (maximal ⟹ self-normalizing).
  have hMne : M ≠ ⊥ := fun hbot => hXne (le_bot_iff.mp (hbot ▸ hXM))
  have hNM_eq : Subgroup.normalizer (M : Set G) = M := by
    have hlt := normalizer_lt_top_of_le_of_ne_bot hG hM le_rfl hMne
    by_contra hne
    exact hlt.ne ((mem_maximalSubgroups.mp hM).2 _
      (lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)))
  -- **Theorem 10.1(b)** ⟹ `C_G(X) ⊄ M`.
  have hCnotM : ¬ Subgroup.centralizer (↑(Subgroup.zpowers (w : G)) : Set G) ≤ M := by
    intro hCM
    obtain ⟨c, hcC, hc⟩ :=
      (S10.fusion_control_of_mem_sigma hG hM hpσ hXne hXp).2.1 1 g
        (by rw [map_one, one_smul]; exact hXM) hXgM
    rw [map_one, one_smul] at hc
    -- `conj c • M = conj g • M` ⟹ `c⁻¹g ∈ N_G(M) = M` ⟹ `g ∈ M`, contradicting `g ∉ M`.
    have hcg : MulAut.conj (c⁻¹ * g) • M = M := by
      rw [map_mul, mul_smul, ← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hcgM : c⁻¹ * g ∈ M := hNM_eq ▸ mem_normalizer_of_conj_smul_eq_self hcg
    have hgM' : g ∈ M := by
      have hmem : c * (c⁻¹ * g) ∈ M := M.mul_mem (hCM hcC) hcgM
      simpa using hmem
    exact hg hgM'
  -- `ℳ(C_G(X)) ≠ {M}` (else `C_G(X) ≤ M`).
  have hℳ : maximalSubgroupsContaining
      (Subgroup.centralizer (↑(Subgroup.zpowers (w : G)) : Set G)) ≠ {M} := by
    intro hsing
    exact hCnotM (mem_maximalSubgroupsContaining.mp
      (by rw [hsing]; exact Set.mem_singleton M)).2
  -- **Corollary 12.14** contrapositive: `ℳ(C_G(X)) ≠ {M}` ⟹ `p ∉ β(M)`.
  rw [Set.mem_compl_iff]
  intro hpβ
  exact hℳ (Cor1214.maximalContaining_centralizer_and_someSylow_eq_singleton hG hM hpσ hXelem hXM
    (Or.inl hpβ)).1

end OddOrder.BG.Ch3.S12
