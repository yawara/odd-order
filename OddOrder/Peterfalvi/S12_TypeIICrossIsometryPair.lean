/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S12_TypeIIGridTranspose

/-!
# Peterfalvi (10.7): the cross-isometry package at the canonical pair

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), §10
(10.7); Coq mirror `PFsection10.v` (`Frob_der1_type2`).

The pair-witness production of the (10.7) cross-isometry package
(`TypeIICrossIsometryData`): at the `M`-seeded canonical pair (`T = M`,
`Kstar = hyp.typeP.W1`, `exists_section16MaximalPair_around`), with the §9 setup of the
type-II member `mp.S` wired to the pair (`exists_typesIIIIIIVSetup_Sdata`), the
character-theoretic fields are **produced**, not posited:

* `tau2` — the (5.7) coherent extension, `typeII_T2_coherent`'s `IsCoherent.extension`;
* `r'`, `delta'`, `nu_tau2_eq` — the (5.8) row pin
  `Hypothesis.exists_nu_extension_eq_alignedRow_at_pair` (the assembled grid transpose of
  issue 9079: (9.8) classification → (5.8) dichotomy → pair transpose → fiber sweep).

The remaining four fields (`lam_ortho_grid`, `zeta_ortho_grid`, `zeta_lam_ortho`,
`cross_zero`) are the **(5.3.b) / (8.18.b) support-geometry obligations** (obligation 3 of
the (10.7) frontier note `notes/peterfalvi/s10_7_derived_frobenius.md`) — they are `sorry`d
here as the explicit remaining work, so this file is the single discharge point for the
gate's residual.
-/

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory
open OddOrder.GroupTheory

variable {G : Type*} [Group G]

open scoped Classical FiniteInduce in
/-- **The (5.3.b) base-orthogonality kernel, `S`-side** (the honest content of Coq
`FTtypeP_base_ortho` at an irreducible family member): the `τ_S`-image of the conjugate
difference `λ − λ̄` is orthogonal to every (3.5) grid vector `χ_P`.

`λ − λ̄` is supported on `A(S)` (member supports lie in `A(S) ∪ {1}` and the degrees at `1`
agree), so its Dade image **vanishes on the exceptional set `V`**
(`typeII_tau_apply_eq_zero_of_mem_ticVdiffV` — `V ⊆ A₀(S)` consists of Dade base points
whose value is `(λ − λ̄)(v) = 0` off `S'`).  It is a norm-`2` virtual character (Dade
isometry on the supported pair of distinct orthonormal irreducibles), so the (3.7)/(3.8)
counting kills every σ-coefficient (`sigmaCoeff_eq_zero_of_vanishOnV`) — and the
σ-coefficients **are** the inner products with the grid. -/
theorem typeII_tau_diff_inner_chiFam_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (P : ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W1.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ) ×
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W2.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ)) :
    ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 0 := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  -- family memberships of `λ` and `λ̄` (through the world bridge)
  have hlamIKF := typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  have hlamBarIKF := OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate
    _ hlamIKF
  -- `λ ≠ λ̄` (no real characters in the family, `|S|` odd)
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (Y.subgroupOf S) hlamIKF
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  -- support of the difference: in `A(S)` (degrees at `1` agree)
  have hsupp : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
        (derivedInG S)) S := by
    have hmem := typeII_T2_member_support hG hSmax hSII data hlam_mem hlam_mem
    refine diff_support_subset_of_support_subset_union_one
      (hmem lam (by simp)) (hmem lam.conj (by simp)) ?_
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [ClassFunction.conj_apply, hn, star_natCast]
  -- the `A₀`-supported form (the Dade hypothesis' set is `A(S) ∪ V^S`)
  have hsuppA0 : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data.typeP)) S :=
    hsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- `ψ ∈ ZIrr G`
  have hψZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
      (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
      (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP)
      hsuppA0
      (Submodule.sub_mem _
        (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hlamIKF)
        (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hlamBarIKF))
  -- `‖ψ‖² = 2` (Dade isometry + distinct orthonormal irreducible pair)
  have hcross : ClassFunction.inner lam lam.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam.conj, hlam_irr.conj⟩
    rwa [if_neg (fun heq => hlamne (congrArg Subtype.val heq))] at h
  have hcross' : ClassFunction.inner lam.conj lam = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcross, star_zero]
  have hiso : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      = ClassFunction.inner (lam - lam.conj) (lam - lam.conj) :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
      (typeIIHypothesis46_dade0_hConjInvariant hG hSmax hSII data.typeP) hsuppA0 hsuppA0
  have hψ2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj)) = 2 := by
    rw [hiso, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hlam_irr.inner_self_eq_one,
      hlam_irr.conj.inner_self_eq_one, hcross, hcross']
    norm_num
  -- `ψ` vanishes on `V` (the anchor)
  have hψV : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj) v = 0 :=
    fun v hv => typeII_tau_apply_eq_zero_of_mem_ticVdiffV hG hSmax hSII data.typeP hsupp hv
  -- the (3.7)/(3.8) counting kills every σ-coefficient
  have hall := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).sigmaCoeff_eq_zero_of_vanishOnV rfl
    (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
      (typeIIHypothesis46 hG hSmax hSII data.typeP)) hψZ hψ2 hψV
  exact hall P

set_option linter.unusedVariables false in
open scoped Classical FiniteInduce in
/-- **The (10.7) cross-isometry package at the canonical pair** (Coq `Frob_der1_type2`,
production step): for the `M`-seeded pair (`T = M`, `Kstar = hyp.typeP.W1`) and a
`(K, K*)`-reconciled §9 setup on the type-II member `mp.S`, the package exists with the
grid fields **honestly produced**: `tau2` is the (5.7) `T2`-coherent extension
(`typeII_T2_coherent`), and `nu_tau2_eq` is the (5.8) row pin
(`exists_nu_extension_eq_alignedRow_at_pair`).

The four support-geometry fields ((5.3.b) grid orthogonality and the (8.18.b)
cross-support vanishing) are the remaining obligation-3 content — `sorry`d here as the
explicit frontier (see the module docstring). -/
theorem exists_typeIICrossIsometryData_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {mp : Section16MaximalPair G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_red : ¬ IsIrreducibleCharacter nu)
    (hdeg : lam 1 = nu 1) :
    Nonempty (TypeIICrossIsometryData hG coh lam nu) := by
  classical
  -- the (5.7) `T2`-coherence on `mp.S`
  obtain ⟨c⟩ := typeII_T2_coherent hG mp.S_maximal (section16_S_isTypeII hG mp) data
    hlam_mem hlam_irr hnu_mem hnu_red hdeg
  -- the (5.8) row pin (the assembled grid transpose)
  obtain ⟨r', delta', hpm, hrow⟩ := hyp.exists_nu_extension_eq_alignedRow_at_pair hG
    hT hKstar hSW1 hSW2 hlam_mem hlam_irr hnu_mem hnu_red hdeg c
  exact ⟨{ tau2 := c.extension
           r' := r'
           delta' := delta'
           delta'_pm := hpm
           nu_tau2_eq := hrow
           lam_ortho_grid := sorry
           zeta_ortho_grid := sorry
           zeta_lam_ortho := sorry
           cross_zero := sorry }⟩

end OddOrder.Peterfalvi.S12
