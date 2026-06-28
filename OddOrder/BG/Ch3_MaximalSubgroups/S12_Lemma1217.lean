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

/-! ## Lemma 12.17 third clause — the `cyclic` / `TI` building blocks

The cyclicity of `M_σ ∩ M^g` (BG Theorem D(2)) is established from two facts proved here and a
rank-one ⇒ cyclic step deferred to §15 (`isCyclic_of_isMulCommutative_of_rank_le_one`, which lives
downstream of §12): a shared σ-uniqueness core (`C_G(X) ⊄ M` for any nontrivial `p`-subgroup
`X ≤ M_σ ∩ M^g`) and the TI part (`M_σ ∩ M^g ⊓ M_σ' = 1`).  The final assembly
`Msigma_inf_conj_isCyclic` is supplied near BG Theorem D in `S16_MainResults`. -/

/-- **Core σ-uniqueness fact for `M_σ ∩ M^g`** (`g ∉ M`), the engine of BG Lemma 12.17's third
clause (Coq `not_sCX_M` inside `sigma_compl_embedding`, BGsection12 L2476): for a nontrivial
`p`-subgroup `X ≤ M_σ ∩ M^g` with `p ∈ σ(M)`, the centralizer `C_G(X)` is **not** contained in `M`.

Theorem 10.1(b) (`fusion_control_of_mem_sigma`, σ-fusion transitivity) yields `c ∈ C_G(X)` with
`M^c = M^g`; were `C_G(X) ≤ M`, then `c⁻¹g ∈ N_G(M) = M`, hence `g ∈ M`, contradicting `g ∉ M`. -/
theorem centralizer_not_le_of_isPGroup_le_Msigma_inf_conj [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∉ M)
    {p : ℕ} [Fact p.Prime] (hpσ : p ∈ S10.sigma M) {X : Subgroup G}
    (hXp : IsPGroup p ↥X) (hXne : X ≠ ⊥)
    (hXle : X ≤ S10.Msigma M ⊓ MulAut.conj g • M) :
    ¬ Subgroup.centralizer (X : Set G) ≤ M := by
  intro hCM
  have hXM : X ≤ M := (hXle.trans inf_le_left).trans (S10.Msigma_le M)
  have hXgM : X ≤ MulAut.conj g • M := hXle.trans inf_le_right
  -- Theorem 10.1(b): some `c ∈ C_G(X)` conjugates `M` to `M^g`.
  obtain ⟨c, hcC, hc⟩ :=
    (S10.fusion_control_of_mem_sigma hG hM hpσ hXne hXp).2.1 1 g
      (by rw [map_one, one_smul]; exact hXM) hXgM
  rw [map_one, one_smul] at hc
  -- `N_G(M) = M` (maximal ⟹ self-normalizing).
  have hMne : M ≠ ⊥ := fun hbot => hXne (le_bot_iff.mp (hbot ▸ hXM))
  have hNM_eq : Subgroup.normalizer (M : Set G) = M := by
    have hlt := normalizer_lt_top_of_le_of_ne_bot hG hM le_rfl hMne
    by_contra hne
    exact hlt.ne ((mem_maximalSubgroups.mp hM).2 _
      (lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)))
  have hcg : MulAut.conj (c⁻¹ * g) • M = M := by
    rw [map_mul, mul_smul, ← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hcgM : c⁻¹ * g ∈ M := hNM_eq ▸ mem_normalizer_of_conj_smul_eq_self hcg
  exact hg (by have := M.mul_mem (hCM hcC) hcgM; simpa using this)

/-- **BG Lemma 12.17, third clause (TI part)** (mmd L3478, Coq `tiMsMg_Ms'`, BGsection12 L2492): for
`g ∉ M` the intersection `M_σ ∩ M^g` meets the derived subgroup `M_σ'` trivially.

A nontrivial element of the meet provides a rank-one `X ≤ M_σ ∩ M^g` with `X ≤ M_σ'`; Corollary
12.14 (`Or.inr` disjunct) then forces `C_G(X) ≤ M`, contradicting
`centralizer_not_le_of_isPGroup_le_Msigma_inf_conj`. -/
theorem Msigma_inf_conj_inf_derived_eq_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∉ M) :
    S10.Msigma M ⊓ MulAut.conj g • M ⊓ derivedInG (S10.Msigma M) = ⊥ := by
  classical
  by_contra hne
  set K : Subgroup G := S10.Msigma M ⊓ MulAut.conj g • M ⊓ derivedInG (S10.Msigma M) with hKdef
  -- The meet is nontrivial: pick a prime `p` dividing its order and an order-`p` element `w`.
  have hKnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  obtain ⟨p, hp_prime, hpdvd⟩ :=
    (Nat.card ↥K).exists_prime_and_dvd (by
      have := Finite.one_lt_card_iff_nontrivial.mpr hKnt; omega)
  haveI : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ K.subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXp : IsPGroup p ↥(Subgroup.zpowers (w : G)) := hXelem.1.isPGroup
  have hXne : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXK : Subgroup.zpowers (w : G) ≤ K := Subgroup.zpowers_le.mpr w.2
  have hXmeet : Subgroup.zpowers (w : G) ≤ S10.Msigma M ⊓ MulAut.conj g • M :=
    hXK.trans inf_le_left
  have hXMσ' : Subgroup.zpowers (w : G) ≤ derivedInG (S10.Msigma M) := hXK.trans inf_le_right
  have hXMσ : Subgroup.zpowers (w : G) ≤ S10.Msigma M := hXmeet.trans inf_le_left
  have hXM : Subgroup.zpowers (w : G) ≤ M := hXMσ.trans (S10.Msigma_le M)
  -- `p ∈ σ(M)` from `X ≤ M_σ`.
  have hpσ : p ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨hp_prime, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  -- Corollary 12.14 (`Or.inr`): `ℳ(C_G(X)) = {M}` ⟹ `C_G(X) ≤ M`, contradicting the core.
  have hℳ := (Cor1214.maximalContaining_centralizer_and_someSylow_eq_singleton
    hG hM hpσ hXelem hXM (Or.inr hXMσ')).1
  have hCM : Subgroup.centralizer (↑(Subgroup.zpowers (w : G)) : Set G) ≤ M :=
    (mem_maximalSubgroupsContaining.mp (by rw [hℳ]; exact Set.mem_singleton M)).2
  exact centralizer_not_le_of_isPGroup_le_Msigma_inf_conj hG hM hg hpσ hXp hXne hXmeet hCM

end OddOrder.BG.Ch3.S12
