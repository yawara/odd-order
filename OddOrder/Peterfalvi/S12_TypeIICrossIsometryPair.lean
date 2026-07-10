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

open scoped Classical FiniteInduce in
/-- **The (5.3.b) base orthogonality, per `R`-element** (Coq `FTtypeP_base_ortho`): every
member of the dispatched `R(λ)`-family is orthogonal to every (3.5) grid vector `χ_P`.

The constituent trick over the kernel `typeII_tau_diff_inner_chiFam_eq_zero`: an
`R`-element `α` with `⟨α, χ_P⟩ ≠ 0` would satisfy `χ_P = ±α` (both are norm-one virtual
characters, so the integer inner product is `±1` and the difference/sum has norm `0`);
but then the flat expansion `τ_S(λ − λ̄) = ∑_{β ∈ R(λ)} β` (`image_eq`) pairs with `χ_P`
to `⟨α, χ_P⟩ = ±1 ≠ 0` (all other terms die by orthonormality of `R(λ)`), contradicting
the kernel. -/
theorem typeII_R_mem_inner_chiFam_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    {α : ClassFunction G ℂ}
    (hα : α ∈ (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).imageSet)
    (P : ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W1.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ) ×
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W2.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ)) :
    ClassFunction.inner α
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 0 := by
  classical
  by_contra hne
  -- both sides are norm-one virtual characters
  have hαZ : α ∈ ZIrr G :=
    (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).mem_ZIrr α hα
  have hα1 : ClassFunction.inner α α = 1 :=
    (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).inner_self_of_mem hα
  have hPZ : (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P ∈ ZIrr G :=
    ((OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam_spec rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP))).2.1 P
  have hP1 : ClassFunction.inner
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 1 := by
    rw [((OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam_spec rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP))).2.2.1, if_pos rfl]
  -- the integer inner product is `±1`
  obtain ⟨c, hc⟩ := inner_intCast_of_mem_ZIrr hαZ hPZ
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    exact hne (by rw [hc]; norm_num)
  have hcstar : ClassFunction.inner
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) α = (c : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc, star_intCast]
  have hsub : ClassFunction.inner
      (α - (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      (α - (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = ((2 - 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hα1, hP1, hc, hcstar]
    push_cast; ring
  have hadd : ClassFunction.inner
      (α + (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      (α + (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = ((2 + 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hα1, hP1, hc, hcstar]
    push_cast; ring
  have hle : c ≤ 1 := by
    have h0 := inner_self_re_nonneg (α - (OddOrder.Peterfalvi.S06.ticVdiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
    rw [hsub, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 - 2 * c := by exact_mod_cast h0
    omega
  have hge : -1 ≤ c := by
    have h0 := inner_self_re_nonneg (α + (OddOrder.Peterfalvi.S06.ticVdiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
    rw [hadd, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 + 2 * c := by exact_mod_cast h0
    omega
  -- `χ_P = ±α`
  have hPeq : (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P = (c : ℂ) • α := by
    interval_cases c
    · -- `c = −1`: `χ_P = −α`
      have hzero : α + (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P = 0 := by
        refine eq_zero_of_inner_self_re_eq_zero ?_
        rw [hadd]
        norm_num
      rw [show (((-1 : ℤ) : ℂ)) = -1 from by norm_num, neg_one_smul]
      exact eq_neg_of_add_eq_zero_right hzero
    · exact absurd rfl hcne
    · -- `c = 1`: `χ_P = α`
      have hzero : α - (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P = 0 := by
        refine eq_zero_of_inner_self_re_eq_zero ?_
        rw [hsub]
        norm_num
      rw [show (((1 : ℤ) : ℂ)) = 1 from by norm_num, one_smul]
      exact (sub_eq_zero.mp hzero).symm
  -- the flat `R`-expansion pairs to `±1 ≠ 0`, contradicting the kernel
  have hk1 := typeII_tau_diff_inner_chiFam_eq_zero hG hSmax hSII data hlam_mem hlam_irr P
  rw [(typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).image_eq,
    OddOrder.RepresentationTheory.inner_sum_left] at hk1
  have hsingle : ∀ β ∈ (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).imageSet, β ≠ α →
      ClassFunction.inner β
        ((OddOrder.Peterfalvi.S06.ticVdiff
            (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 0 := by
    intro β hβ hβne
    rw [hPeq, OddOrder.RepresentationTheory.inner_smul_right,
      (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
        (Set.mem_insert _ _)).orthonormal β hβ α hα, if_neg hβne]
    simp
  rw [Finset.sum_eq_single α hsingle (fun h => absurd hα h)] at hk1
  rw [hPeq, OddOrder.RepresentationTheory.inner_smul_right, hα1, mul_one] at hk1
  have : (c : ℂ) = 0 := star_eq_zero.mp hk1
  exact hcne (by exact_mod_cast this)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.5) for the `T2`-coherence** (the lane-b template
`coherent_extension_mem_span_Rset_of_mem` re-enacted at the type-II member family): the
coherent image of the irreducible member `λ` lies in `ℤ[R(λ)]`.

The `ofProjection (ψ := 0)` engine against the dispatched `R(λ)`-family
(`typeII_T2_memberRFamily`): the (5.4) decomposition `λ^{τ₂} = X − Y` has `‖Y‖² ≥ 0 = ‖ψ‖²`
automatically, so (5.4.b) forces `Y = 0` and `λ^{τ₂} = X ∈ ℤ[R(λ)]`
(`eq_sum_of_psi_eq_zero`).  The isometry/agreement inputs are the coherence's own fields on
the sponsoring lattice `ℤ[λ, λ̄]  ⊆ ℤ[T2]`; the support input is the `A₀(S)`-support of
`λ − λ̄` (as in the kernel `typeII_tau_diff_inner_chiFam_eq_zero`). -/
theorem typeII_T2_extension_lam_mem_span_RFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
            (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S)) :
    c.extension lam ∈ Submodule.span ℤ
      ((typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
        (Set.mem_insert _ _)).imageSet : Set (ClassFunction G ℂ)) := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  -- `λ ≠ λ̄`, and the `A₀(S)`-support of the difference (as in the kernel)
  have hlamIKF := typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (Y.subgroupOf S) hlamIKF
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  have hsupp : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
        (derivedInG S)) S := by
    have hmem := typeII_T2_member_support hG hSmax hSII data hlam_mem hlam_mem
    refine diff_support_subset_of_support_subset_union_one
      (hmem lam (by simp)) (hmem lam.conj (by simp)) ?_
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [ClassFunction.conj_apply, hn, star_natCast]
  have hsuppA0 : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data.typeP)) S :=
    hsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- `⟨λ, λ̄⟩ = 0`
  have hcross : ClassFunction.inner lam lam.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam.conj, hlam_irr.conj⟩
    rwa [if_neg (fun heq => hlamne (congrArg Subtype.val heq))] at h
  -- lattice memberships
  have hchi_zSpan : lam ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hchibar_zSpan : lam.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hdiff_zSpan : lam - lam.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Submodule.sub_mem _ hchi_zSpan hchibar_zSpan
  have hsub : OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam - lam.conj, lam - 0} : Set (ClassFunction ↥S ℂ)) ≤
      OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
        ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) := by
    change Submodule.span ℤ _ ≤ Submodule.span ℤ _
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hdiff_zSpan
    · rw [sub_zero]; exact hchi_zSpan
  -- the (5.4)/(5.5) engine at `ψ = 0`
  obtain ⟨-, hτ1χ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection (ψ := 0)
        (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
          (Set.mem_insert _ _)) c.extension
        (fun φ ζ hφ hζ => c.extension_inner_eq φ ζ (hsub hφ) (hsub hζ))
        (c.extends_on_supported (lam - lam.conj) ⟨hdiff_zSpan, hsuppA0⟩)
        (by rw [sub_zero]; exact c.extension_mem_ZIrr _ hchi_zSpan)
        (ClassFunction.inner_zero_right _)
        (ClassFunction.inner_zero_right _)
        hcross)
  have hgoal : c.extension lam = ∑ α ∈ E, α := hτ1χ.trans hXsum
  rw [hgoal]
  exact Submodule.sum_mem _ fun α hα =>
    Submodule.subset_span (Finset.mem_coe.mpr (hEsub hα))

open scoped Classical FiniteInduce in
/-- **The (5.3.b) `S`-side grid orthogonality of the coherent image** (Coq
`coherent_ortho_cycTIiso` at the irreducible member): `⟨χ_P, λ^{τ₂}⟩ = 0` for every (3.5)
grid vector.  `λ^{τ₂} ∈ ℤ[R(λ)]` by (5.5) (`typeII_T2_extension_lam_mem_span_RFamily`) and
every `R(λ)`-element is orthogonal to `χ_P` (`typeII_R_mem_inner_chiFam_eq_zero`), so the
inner product dies by ℤ-linearity of the right slot. -/
theorem typeII_T2_extension_lam_inner_chiFam_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
            (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S))
    (P : ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W1.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ) ×
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W2.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ)) :
    ClassFunction.inner
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      (c.extension lam) = 0 := by
  classical
  have key : ∀ x ∈ Submodule.span ℤ
      ((typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
        (Set.mem_insert _ _)).imageSet : Set (ClassFunction G ℂ)),
      ClassFunction.inner
        ((OddOrder.Peterfalvi.S06.ticVdiff
            (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        have h0 := typeII_R_mem_inner_chiFam_eq_zero hG hSmax hSII data
          hlam_mem hlam_irr hnu_mem hdeg (Finset.mem_coe.mp hy) P
        rw [OddOrder.RepresentationTheory.inner_conj_symm, h0, star_zero]
    | zero => exact ClassFunction.inner_zero_right _
    | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ih =>
        rw [← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]
  exact key _ (typeII_T2_extension_lam_mem_span_RFamily hG hSmax hSII data
    hlam_mem hlam_irr hnu_mem hdeg c)

open scoped Classical FiniteInduce in
/-- **The (5.3.b) `λ`-orthogonality against the aligned `M`-grid at the canonical pair**
(the `lam_ortho_grid` production; Coq `coherent_ortho_cycTIiso` consumed at `etaC`): the
`T2`-coherent image of the irreducible member `λ` is orthogonal to every `M`-side aligned
σ-grid vector.

Chain: the aligned grid vector is an `M`-side `χ`-family member
(`exists_alignedOmegaSigmaGrid_chiFam_family`); the per-index pair transpose reads it as an
`S`-side grid vector (`section16_pair_chiFam_transpose_T`); and the `S`-side grid is
orthogonal to `λ^{τ₂}` by (5.5) + the constituent trick
(`typeII_T2_extension_lam_inner_chiFam_eq_zero`). -/
theorem Hypothesis.extension_lam_inner_alignedGrid_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPair G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
            (derivedInG mp.S)
          ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S))
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j) (c.extension lam) = 0 := by
  classical
  subst hT
  -- the aligned vector is an `M`-side `χ`-family member
  obtain ⟨P, -, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hG.odd i
  rw [hP j]
  -- transpose to an `S`-side grid vector, then apply the `S`-side orthogonality
  rw [section16_pair_chiFam_transpose_T hG hG.odd hSW1 hSW2 hyp.typeP hKstar.symm
    (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
      (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP))
    (hyp.canonicalFullDadeApp hG hG.odd) (P j)]
  exact typeII_T2_extension_lam_inner_chiFam_eq_zero hG mp.S_maximal
    (section16_S_isTypeII hG mp) data hlam_mem hlam_irr hnu_mem hdeg c _

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
           lam_ortho_grid := fun i j =>
             hyp.extension_lam_inner_alignedGrid_eq_zero_at_pair hG hT hKstar hSW1 hSW2
               hlam_mem hlam_irr hnu_mem hdeg c i j
           zeta_ortho_grid := sorry
           zeta_lam_ortho := sorry
           cross_zero := sorry }⟩

end OddOrder.Peterfalvi.S12
