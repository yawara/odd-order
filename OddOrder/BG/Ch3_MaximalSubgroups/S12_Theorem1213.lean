/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212c
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch3_MaximalSubgroups.S10_BetaRadicalCore
import OddOrder.BG.Ch1_Preliminary.S01b_Prop116

/-!
# BG §12: Theorem 12.13 — every nonabelian `p`-subgroup of `G` lies in `𝒰`

**スコープ**: BG Theorem 12.13 (mmd L3347). The first uniqueness result of the `σ(M)`-side,
derived from Proposition 12.4.

**証明** (背理法): 非可換 `p`-部分群 `P` が相異なる極大 `M`, `M*` に含まれると仮定する。
Corollary 12.10(a)(d) で `p ∈ σ(M) ∩ σ(M*)` かつ `N_G(P) ⊆ M ∩ M*`。`P` を `M ∩ M*` の Sylow
`p`-部分群と仮定でき(よって `G` の Sylow `p`-部分群)、Uniqueness Theorem で `r(P) = 2`。
Corollary 10.7(b) で order `p³`・exponent `p` の非可換 `Q ⊆ P`(extraspecial)、`Z = Z(Q) = Q'`
order `p`。`Q/Z` の `K = C_{M_α}(Z)` 上の作用 + Proposition 1.16 + Proposition 12.4(a) で `K ⊆ M*`、
`N_M(Z) ⊆ M*`、`ℳ(N_G(Z)) ≠ {M}`、`M_α ≠ 1`。最後に Proposition 12.4(b) で `A₀, A₀* ∈ ℰ¹(A)−{Z}`
が `M ∩ M*`(⊇ `Q`)内で非共役となり、`Q` の構造に矛盾。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- A nonabelian `p`-subgroup `P` contained in two distinct maximal subgroups `M`, `M*` of `G`
satisfies `p ∈ σ(M) ∩ σ(M*)` and `N_G(P) ⊆ M ∩ M*` (Corollary 12.10(a),(d)). The membership
`p ∈ σ(M)` is the contrapositive of 12.10(a): a `σ(M)'`-`p`-subgroup is nilpotent, hence abelian.
The normalizer containment is 12.10(d) (nonabelian `⟹` noncyclic). -/
theorem mem_sigma_normalizer_le_of_two_maximals [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P M : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) (hM : M ∈ maximalSubgroups G) (hPM : P ≤ M) :
    p ∈ S10.sigma M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  haveI : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hcor := nilpotent_sigmaComplement_abelian hG hsetup
  -- `P` is a `σ(M)'`-`p`-subgroup only if `p ∉ σ(M)`; its primes are all `p`.
  have hPpi : p ∉ S10.sigma M → Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) P := by
    intro hpσ q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    rw [hn] at hqd
    have : q = p := (Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp (hqp.dvd_of_dvd_pow hqd)
    rwa [this]
  have hpσM : p ∈ S10.sigma M := by
    by_contra hpσ
    exact hPnab (hcor.1 P hPM (hPpi hpσ) ‹_›)
  refine ⟨hpσM, ?_⟩
  -- `N_G(P) ⊆ M`: 12.10(d), `P` noncyclic.
  refine hcor.2.2.2.1 p hpσM P hPM hPp ?_
  intro hcyc
  haveI := hcyc
  exact hPnab (IsMulCommutative.of_comm (IsCyclic.commGroup (α := ↥P)).mul_comm)

/-- **Conjugates of a noncentral element cover its central coset** in an exponent-`p` extraspecial
group: for `a₀ ∉ Z(Q)` and any `z ∈ Z(Q)`, there is `q` with `q a₀ q⁻¹ = z · a₀`.

The map `φ : Q → Z(Q)`, `q ↦ ⁅q, a₀⁆`, is a homomorphism (commutators lie in `[Q,Q] = Z(Q)`,
which is central), nontrivial since `a₀ ∉ Z(Q)`, hence surjective onto the order-`p` group `Z(Q)`.
So every `z ∈ Z(Q)` is realized as `⁅q,a₀⁆`, i.e. `q a₀ q⁻¹ = z · a₀`. This is the conjugacy half of
the BG 12.13 Heisenberg line-conjugacy argument. -/
theorem exists_conj_eq_center_mul_of_expPExtraspecial {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsExpPExtraspecial p Q) {a₀ : Q} (ha₀ : a₀ ∉ Subgroup.center Q)
    {z : Q} (hz : z ∈ Subgroup.center Q) :
    ∃ q : Q, q * a₀ * q⁻¹ = z * a₀ := by
  classical
  have hes := hQ.isExtraspecial
  have hZcard : Nat.card (Subgroup.center Q) = p := hes.center_card
  have hZcomm : commutator Q = Subgroup.center Q := hes.commutator_eq_center
  -- (1) `⁅q, a₀⁆ ∈ Z(Q)` for all `q`.
  have hmemZ : ∀ q : Q, ⁅q, a₀⁆ ∈ Subgroup.center Q := fun q => by
    rw [← hZcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top q) (Subgroup.mem_top a₀)
  -- (2) `φ : Q →* Z(Q)`, `q ↦ ⁅q, a₀⁆` (homomorphism by centrality of commutators).
  have hcentral : ∀ z : Q, z ∈ Subgroup.center Q → ∀ w : Q, Commute z w :=
    fun z hz w => (Subgroup.mem_center_iff.mp hz w).symm
  let φ : Q →* Subgroup.center Q := MonoidHom.mk'
    (fun q => ⟨⁅q, a₀⁆, hmemZ q⟩) (fun x y => by
      apply Subtype.ext
      show ⁅x * y, a₀⁆ = ⁅x, a₀⁆ * ⁅y, a₀⁆
      have hc := hcentral ⁅y, a₀⁆ (hmemZ y)
      have e1 : ⁅x * y, a₀⁆ = x * ⁅y, a₀⁆ * x⁻¹ * ⁅x, a₀⁆ := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅y, a₀⁆ * x⁻¹ = ⁅y, a₀⁆ := by rw [(hc x).symm.eq]; group
      rw [e1, e2, (hc ⁅x, a₀⁆).eq])
  -- (3) `φ` is surjective: its range is a nontrivial subgroup of the order-`p` group `Z(Q)`.
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    have hdvd : Nat.card ↥φ.range ∣ p := hZcard ▸ Subgroup.card_subgroup_dvd_card φ.range
    have hne1 : Nat.card ↥φ.range ≠ 1 := by
      rw [ne_eq, Subgroup.card_eq_one]
      intro hbot
      refine ha₀ (Subgroup.mem_center_iff.mpr fun g => ?_)
      have hg1 : φ g = 1 := by rw [← Subgroup.mem_bot, ← hbot]; exact ⟨g, rfl⟩
      have h2 : ⁅g, a₀⁆ = 1 := Subtype.ext_iff.mp hg1
      exact commutatorElement_eq_one_iff_commute.mp h2
    have hcardr : Nat.card ↥φ.range = p :=
      (Nat.dvd_prime Fact.out).mp hdvd |>.resolve_left hne1
    exact Subgroup.eq_top_of_card_eq _ (by rw [hcardr, hZcard])
  -- (4) realize `z` as `⁅q, a₀⁆`, so `q a₀ q⁻¹ = z · a₀`.
  obtain ⟨q, hq⟩ := hφsurj ⟨z, hz⟩
  refine ⟨q, ?_⟩
  have hqz : ⁅q, a₀⁆ = z := Subtype.ext_iff.mp hq
  rw [commutatorElement_def] at hqz
  exact mul_inv_eq_iff_eq_mul.mp hqz

/-- **`ℳ(N_G(·))`-uniqueness blocks `M`-conjugacy**: if `A₀⋆ = g • A₀` (conjugation by some
`g ∈ M`), `ℳ(N_G(A₀)) = {M}`, and `ℳ(N_G(A₀⋆)) = {M⋆}`, then `M = M⋆`.

Conjugation by `g` commutes with `N_G(·)` (`normalizer_conj_smul`) and preserves coatomicity
(`isCoatom_conj_smul`), so `g • M` is a maximal subgroup containing `N_G(A₀⋆)`, hence the unique
such, namely `M⋆`; but `g ∈ M` fixes `M` (`conj_smul_eq_self_of_mem_normalizer`), whence `M = M⋆`.
This is the engine of the final contradiction in BG 12.13: `A₀` and `A₀⋆` are `Q`-conjugate, yet
their `ℳ(N_G(·))` are the distinct singletons `{M}` and `{M⋆}`. -/
theorem eq_of_conj_of_maximalContaining_normalizer_eq_singleton
    {A₀ A₀star M Mstar : Subgroup G} {g : G} (hgM : g ∈ M)
    (hconj : MulAut.conj g • A₀ = A₀star)
    (hM : maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) = {M})
    (hMstar : maximalSubgroupsContaining (Subgroup.normalizer (A₀star : Set G)) = {Mstar}) :
    M = Mstar := by
  -- `M ∈ ℳ(N_G(A₀))`, so `IsCoatom M` and `N_G(A₀) ≤ M`.
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
    rw [hM]; exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨hMcoat, hMle⟩ := mem_maximalSubgroupsContaining.mp hMmem
  -- `g • M` is a coatom containing `N_G(A₀⋆)`, hence lies in `ℳ(N_G(A₀⋆)) = {M⋆}`.
  have hle' : Subgroup.normalizer (A₀star : Set G) ≤ MulAut.conj g • M := by
    rw [← hconj, ← normalizer_conj_smul]
    exact conj_smul_mono _ hMle
  have hmem' : MulAut.conj g • M
      ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀star : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨isCoatom_conj_smul hMcoat, hle'⟩
  rw [hMstar, Set.mem_singleton_iff] at hmem'
  -- `g ∈ M` fixes `M` under conjugation, so `M = M⋆`.
  rwa [conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)] at hmem'

/-- **BG Theorem 12.13** (mmd L3347): every nonabelian `p`-subgroup of `G` (for every prime `p`)
lies in `𝒰`. -/
theorem nonabelian_pgroup_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) :
    IsUniquelyMaximal P := by
  classical
  -- `P < ⊤` (else `G` is a `p`-group, hence solvable).
  have hPlt : P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hPtop
    have hGp : IsPGroup p G :=
      (hPtop ▸ hPp : IsPGroup p ↥(⊤ : Subgroup G)).of_equiv Subgroup.topEquiv
    haveI := hGp.isNilpotent
    exact hG.notSolvable IsNilpotent.to_isSolvable
  obtain ⟨M, hMcoatom, hPM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom P).resolve_left hPlt.ne
  refine IsUniquelyMaximal.of_unique_maximal hPlt (mem_maximalSubgroups.mpr hMcoatom) hPM ?_
  intro Mstar hMstar hPMstar
  by_contra hne
  -- `p ∈ σ(M) ∩ σ(M*)` and `N_G(P) ⊆ M ∩ M*`.
  obtain ⟨hpσM, hNM⟩ := mem_sigma_normalizer_le_of_two_maximals hG hPp hPnab
    (mem_maximalSubgroups.mpr hMcoatom) hPM
  obtain ⟨hpσMstar, hNMstar⟩ := mem_sigma_normalizer_le_of_two_maximals hG hPp hPnab hMstar hPMstar
  -- **Hard core** (Z-action via Prop 1.16 + Prop 12.4, non-conjugacy contradiction).
  sorry

end OddOrder.BG.Ch3.S12
