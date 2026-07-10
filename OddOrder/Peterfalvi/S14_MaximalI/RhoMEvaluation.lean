/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI.MinimalCounterexample
import OddOrder.Peterfalvi.S14_MaximalI.PairCoherence
import OddOrder.Peterfalvi.S14_MaximalI.DadeContradiction

/-!
# Peterfalvi (12.15), first claim — the `ρ_M`-evaluation `ψ^{ρ_M}(g) = ψ(g)` on `K^#`

For the counterexample maximal `M` of (12.8) and the witness Dade character `ψ = χ^{τ₁}` of
(12.13), the `ρ_M`-average of `ψ` at any `g ∈ K^#` is just the value `ψ(g)`
(`counterexample_chiRho_eval_of_mem_K_sharp`).  Peterfalvi's proof, faithfully:

* if `C_G(g) ⊆ M` (non-escaping), the local Dade kernel is `H(g) = ⊥` and the average is
  trivial;
* otherwise `g` is a `σ`-sharp element of `M` escaping `M`, so BG Theorem D(4)
  (`exists_RData_escape_structure`) attaches the unique maximal `N = N[g] ⊇ C_G(g)` with
  `H(g) = N_σ ∩ C_G(g)`, of type `F` or `P₂`; the `P₂` branch would make `M` a Frobenius group
  over `M_σ` with cyclic complement ((8.13.c4) "furthermore"), refuted by
  `counterexample_not_frobenius_MF`.  So `N` is of type I (`isTypeI_of_isTypeF`) with
  `N_F = N_σ`, and `g ∈ N − N_F` with `C_{N_F}(g) ≠ 1` — whence `N` is not conjugate to the
  Frobenius witness `L` (`witness_L_not_conj_of_kernel_centralizer_ne_bot`).  The (12.3)/(5.5)
  cross-orthogonality then gives `ψ ⊥ R_N(χ)` for every `χ ∈ S_N`, and (12.4)
  (`orthogonal_character_constant_on_coset`) makes `ψ` constant on `g·N_F ⊇ g·H(g)`, collapsing
  the `ρ_M`-average (`chiRho_apply_eq_of_forall_coset`).
-/

namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), first claim**: `ψ^{ρ_M}(g) = ψ(g)` for `g ∈ K^#`, where
`ψ = coh.extension χ₀` is the witness Dade character of (12.13) and `ρ_M` is the (7.1)
`ρ`-machinery of the counterexample `M` (`hypM.toHypothesis71`). -/
theorem counterexample_chiRho_eval_of_mem_K_sharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hypM : Hypothesis ctr.M)
    {g : G} (hgK : g ∈ ctr.K) (hg1 : g ≠ 1) (hgM : g ∈ ctr.M) :
    hypM.toHypothesis71.chiRho ψ ⟨g, hgM⟩ = ψ g := by
  classical
  have hHK : hypM.typeI.typeF.H = ctr.K :=
    hypM.typeI.typeF.H_eq.trans ctr.K_eq_MF.symm
  -- `g ∈ A(M)` (it lies in `K^# = H_M^# ⊆ A(M)`).
  have hgA : ((⟨g, hgM⟩ : ↥ctr.M) : G) ∈
      OddOrder.GroupTheory.typeIA ctr.M hypM.typeI := by
    refine sharpSubgroup_H_subset_typeIA hypM.typeI ⟨?_, ?_⟩
    · exact SetLike.mem_coe.mpr (hHK ▸ hgK)
    · simpa using hg1
  refine OddOrder.Peterfalvi.S09.Hypothesis71.chiRho_apply_eq_of_forall_coset
    hypM.toHypothesis71 ψ hgA ?_
  intro y hy
  -- Identify the local kernel with the faithful (8.14) signalizer.
  have hyKer : y ∈ OddOrder.Peterfalvi.S10.ftSupportKernel ctr.M
      (OddOrder.GroupTheory.typeIA ctr.M hypM.typeI) g := by
    rw [← hypM.dadeData.H_eq_ftSupportKernel ⟨g, hgA⟩]
    exact hy
  by_cases hesc : g ∈ OddOrder.GroupTheory.escapingCentralizerSet ctr.M
      (OddOrder.GroupTheory.typeIA ctr.M hypM.typeI)
  · -- Escaping branch.
    have hgKσ : g ∈ OddOrder.BG.Ch3.S10.Msigma ctr.M := MF_eq_Msigma hG ctr ▸ hgK
    have hgσs : g ∈ OddOrder.BG.Ch4.S14.sigmaSharp ctr.M := ⟨hgKσ, hg1⟩
    have hescC : ¬ Subgroup.centralizer ({g} : Set G) ≤ ctr.M := hesc.2
    -- the unique maximal `N₀ ⊇ C_G(g)` and the `FT_signalizerBase` pin
    obtain ⟨N₀, hN₀⟩ :=
      OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG ctr.M_maximal hgσs hescC
    have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement g).ncard := by
      by_contra h
      push Not at h
      exact hescC
        (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG ctr.M_maximal hgKσ hg1 h)
    have hne : (OddOrder.GroupTheory.maximalSubgroupsContaining
        (Subgroup.centralizer ({g} : Set G))).Nonempty := by
      rw [hN₀]
      exact ⟨N₀, rfl⟩
    have hcond : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement g).ncard ∧
        (OddOrder.GroupTheory.maximalSubgroupsContaining
          (Subgroup.centralizer ({g} : Set G))).Nonempty := ⟨hgt, hne⟩
    have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase g = N₀ := by
      have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase g = hcond.2.choose := dif_pos hcond
      have hch : hcond.2.choose ∈ ({N₀} : Set (Subgroup G)) :=
        (Set.ext_iff.mp hN₀ _).mp hcond.2.choose_spec
      exact hb.trans (Set.mem_singleton_iff.mp hch)
    -- the kernel is `N₀_σ ⊓ C_G(g)`
    have hker_eq : OddOrder.BG.Ch4.S16.FT_signalizer g
        = OddOrder.BG.Ch3.S10.Msigma N₀ ⊓ Subgroup.centralizer ({g} : Set G) := by
      rw [show OddOrder.BG.Ch4.S16.FT_signalizer g
          = OddOrder.BG.Ch3.S10.Msigma (OddOrder.BG.Ch4.S16.FT_signalizerBase g) ⊓
            Subgroup.centralizer ({g} : Set G) from rfl, hbase]
    rw [OddOrder.Peterfalvi.S10.ftSupportKernel_eq_of_escaping hesc, hker_eq] at hyKer
    -- Theorem D(4): the escape structure at `N`, pinned to `N₀`
    obtain ⟨R, -, N, ⟨hNmem, -, -, hASet, hNtype, -, hP2pkg⟩, -⟩ :=
      OddOrder.BG.Ch4.S16.exists_RData_escape_structure hG ctr.M_maximal hgσs hescC
    have hNN₀ : N = N₀ := by
      rw [hN₀] at hNmem
      exact hNmem
    subst hNN₀
    have hNmax : N ∈ maximalSubgroups G := by
      have := hN₀ ▸ (Set.mem_singleton N)
      exact (OddOrder.GroupTheory.mem_maximalSubgroupsContaining.mp this).1
    have hCgN : Subgroup.centralizer ({g} : Set G) ≤ N := by
      have := hN₀ ▸ (Set.mem_singleton N)
      exact (OddOrder.GroupTheory.mem_maximalSubgroupsContaining.mp this).2
    -- kill the `P₂` branch: it would make `M` Frobenius over `M_σ` with cyclic complement
    have hNF : OddOrder.BG.Ch4.S14.IsTypeF N := by
      rcases hNtype with h | h
      · exact h
      · exfalso
        obtain ⟨-, -, E, hEM, hEcyc, hEcompl, hEfrob⟩ := hP2pkg h
        exact counterexample_not_frobenius_MF hG ctr ⟨E, hEM, hEcyc, hEcompl, hEfrob⟩
    have hNtypeI : IsTypeI N := OddOrder.BG.Ch4.S16.isTypeI_of_isTypeF hG hNmax hNF
    have hNFeq : maxNilpotentNormalHall N = OddOrder.BG.Ch3.S10.Msigma N :=
      OddOrder.BG.Ch4.S16.maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2
        hG hNmax hNtype
    -- `g ∈ N ∖ N_F` and `C_{N_F}(g) ≠ 1`
    have hgN : g ∈ N := hCgN (Subgroup.mem_centralizer_iff.mpr
      (fun z hz => by rw [Set.mem_singleton_iff.mp hz]))
    have hgNF : g ∉ maxNilpotentNormalHall N := by
      rw [hNFeq]
      exact fun hmem => hASet.2 (SetLike.mem_coe.mpr hmem)
    have hRne : maxNilpotentNormalHall N ⊓ Subgroup.centralizer ({g} : Set G) ≠ ⊥ := by
      obtain ⟨N₁, ⟨hN₁max, hCN₁, hR₁ne, -, -, -, -⟩, -⟩ :=
        OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG ctr.M_maximal hgσs hgt
      have hN₁mem : N₁ ∈ OddOrder.GroupTheory.maximalSubgroupsContaining
          (Subgroup.centralizer ({g} : Set G)) := ⟨hN₁max, hCN₁⟩
      rw [hN₀] at hN₁mem
      rw [hNFeq]
      rw [Set.mem_singleton_iff] at hN₁mem
      rwa [hN₁mem] at hR₁ne
    -- `N` is not conjugate to the Frobenius witness `L`
    have hLN : ¬ ∃ c : G, MulAut.conj c • data.L = N :=
      witness_L_not_conj_of_kernel_centralizer_ne_bot hG data hgN hgNF hRne
    -- the N-side (12.4) supply
    obtain ⟨hypN⟩ := exists_typeI_hypothesis hG hNmax hNtypeI
    have data_N : ∀ χ ∈ hypN.Sset, CharacterDecompositionData hypN χ :=
      fun χ hχ => (character_decomposition_and_dade_domain hG hypN hχ).choose
    have horth : ∀ χ (hχ : χ ∈ hypN.Sset), ∀ α ∈ Rset (data_N χ hχ),
        ClassFunction.inner ψ α = 0 := by
      intro χ hχ α hα
      rw [hpsi]
      exact coherent_extension_constituent_orthogonal_Rset_of_nonconjugate hG hyp coh data0
        hchi0 hchi0_mem hypN hLN (data_N χ hχ) α hα
    have hgNhyp : g ∉ hypN.H := by
      intro hmem
      exact hgNF (hypN.typeI.typeF.H_eq ▸ hmem)
    -- (12.4): `ψ` is constant on `g·N_F ⊇ g·H(g)`
    have hconstN := orthogonal_character_constant_on_coset hG hypN data_N horth hgN hgNhyp
    have hyNF : y ∈ hypN.H := by
      have hyMσ : y ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hyKer).1
      have hyNF' : y ∈ maxNilpotentNormalHall N := hNFeq ▸ hyMσ
      show y ∈ hypN.typeI.typeF.H
      rw [hypN.typeI.typeF.H_eq]
      exact hyNF'
    exact hconstN y hyNF
  · -- Non-escaping branch: `H(g) = ⊥`, the coset is trivial.
    rw [OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping hesc,
      Subgroup.mem_bot] at hyKer
    rw [hyKer, mul_one]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), second claim**: the witness Dade character `ψ` is **constant on
`K − K′`** — the (12.5)-M constancy of `ψ^{ρ_M}` (`psi_constant_on_kernel_sub_derived_ofData`,
coherence-free, with the `(12.3)+(5.5)` cross-orthogonality supply from `L ≁ M`) transported to
`ψ` by the first claim (`counterexample_chiRho_eval_of_mem_K_sharp`). -/
theorem counterexample_psi_constant_on_K_sub_Kprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hypM : Hypothesis ctr.M)
    {g₁ g₂ : G} (hg₁K : g₁ ∈ ctr.K) (hg₁K' : g₁ ∉ ctr.Kprime)
    (hg₂K : g₂ ∈ ctr.K) (hg₂K' : g₂ ∉ ctr.Kprime) :
    ψ g₁ = ψ g₂ := by
  classical
  have hHK : hypM.typeI.typeF.H = ctr.K :=
    hypM.typeI.typeF.H_eq.trans ctr.K_eq_MF.symm
  have hLM : ¬ ∃ c : G, MulAut.conj c • data.L = ctr.M := witness_L_not_conj_M hG data
  have data_M : ∀ χ ∈ hypM.Sset, CharacterDecompositionData hypM χ :=
    fun χ hχ => (character_decomposition_and_dade_domain hG hypM hχ).choose
  have horth : ∀ χ (hχ : χ ∈ hypM.Sset), ∀ α ∈ Rset (data_M χ hχ),
      ClassFunction.inner ψ α = 0 := by
    intro χ hχ α hα
    rw [hpsi]
    exact coherent_extension_constituent_orthogonal_Rset_of_nonconjugate hG hyp coh data0
      hchi0 hchi0_mem hypM hLM (data_M χ hχ) α hα
  have heval : ∀ z : G, ∀ hz : z ∈ hypM.typeI.typeF.H, z ≠ 1 →
      hypM.toHypothesis71.chiRhoCF ψ
        (⟨z, hypM.typeI.typeF.H_le hz⟩ : ↥ctr.M) = ψ z := by
    intro z hz hz1
    rw [OddOrder.Peterfalvi.S09.Hypothesis71.chiRhoCF_apply]
    exact counterexample_chiRho_eval_of_mem_K_sharp hG data hyp coh data0 hchi0 hchi0_mem
      hpsi hypM (by rw [← hHK]; exact hz) hz1 (hypM.typeI.typeF.H_le hz)
  have hK' : derivedInG hypM.typeI.typeF.H = ctr.Kprime := by
    rw [hHK, ctr.Kprime_eq]
  exact psi_constant_on_kernel_sub_derived_ofData hypM data_M
    (sharpSubgroup_H_subset_typeIA hypM.typeI) (one_notMem_typeIA hypM.typeI) horth heval
    (by rw [hHK]; exact hg₁K) (by rw [hK']; exact hg₁K')
    (by rw [hHK]; exact hg₂K) (by rw [hK']; exact hg₂K')

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.15), third claim**: `ψ(g) ∈ ℤ` for `g ∈ K − K′` — the constancy of the
second claim fed into the rationality/integrality argument `rhoM_integer_values`. -/
theorem counterexample_psi_int_on_K_sub_Kprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (hyp : Hypothesis data.L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi0 : IrreducibleCharacter ↥data.L}
    (data0 : CharacterDecompositionData hyp (chi0 : ClassFunction ↥data.L ℂ))
    (hchi0 : chi0 ∈ data0.constituents)
    (hchi0_mem : (chi0 : ClassFunction ↥data.L ℂ) ∈ hyp.Sset)
    {ψ : ClassFunction G ℂ}
    (hpsi : ψ = coh.extension (chi0 : ClassFunction ↥data.L ℂ))
    (hψZ : ψ ∈ ZIrr G)
    (hypM : Hypothesis ctr.M)
    {g : G} (hgK : g ∈ ctr.K) (hgK' : g ∉ ctr.Kprime) :
    ∃ z : ℤ, ψ g = (z : ℂ) :=
  rhoM_integer_values hψZ
    (fun g₁ g₂ h1 h2 h3 h4 =>
      counterexample_psi_constant_on_K_sub_Kprime hG data hyp coh data0 hchi0 hchi0_mem
        hpsi hypM h1 h2 h3 h4)
    g hgK hgK'

end OddOrder.Peterfalvi.S14
