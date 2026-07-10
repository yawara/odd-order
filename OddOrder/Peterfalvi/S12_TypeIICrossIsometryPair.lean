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

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.3.b), `M`-side: `ζ^{τ₁}` is orthogonal to the aligned σ-grid** (the
`zeta_ortho_grid` production — the full-`𝒮`-coherence form of the grid-orthogonality
intermediate of `tau1_zeta_vanishes_on_typePV`; cf. its `S(HC)`-port
`SHC_extension_inner_alignedOmegaSigma_eq_zero`).

`(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` (`tau_zeta_sub_conj_eq_tau1`) vanishes on `V`
(`tau_zeta_sub_conj_vanishes_on_typePV`) and has at most `2 < min(w₁, w₂)` nonzero
σ-coefficients (each `τ₁`-image is norm-`1` with at most one,
`ncard_inner_chiFam_ne_zero_le_one`), so every σ-coefficient dies
(`sigmaCoeff_eq_zero_of_sigmaNC_lt`); the norm-`1` projection
(`inner_left_eq_zero_of_inner_sub_eq_zero`) upgrades the difference orthogonality to
`⟨ζ^{τ₁}, χ_P⟩ = 0`, and the aligned grid vector **is** a `χ_P`
(`exists_alignedOmegaSigmaGrid_chiFam_family`). -/
theorem Hypothesis.tau1_zeta_inner_alignedGrid_eq_zero [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (coh.tau1 ζ) (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0 := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hζne : ζ.conj ≠ ζ := inducedFamily_hasNoRealCharacters hModd hζS
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  obtain ⟨P, -, hPeq⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  rw [hPeq j]
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have haZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 ζ.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζcS)
  have ha1 : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have hb1 : ClassFunction.inner (coh.tau1 ζ.conj) (coh.tau1 ζ.conj) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζcS hζcirr
  have hab : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζcirr, if_neg (fun h => hζne h.symm)]
  -- `(ζ − ζ̄)^τ` vanishes on `V`, with `NC ≤ 2 < min(w₁, w₂)`
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.tau1 ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.tau1 ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  -- σ-coefficient of the difference at `P j` dies; project to the `ζ^{τ₁}`-slot
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (P j) = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (P j)
  have hdiff : ClassFunction.inner (coh.tau1 ζ - coh.tau1 ζ.conj)
      (tic.chiFam hVeq app (P j)) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr]; exact hL3
  have hsZ : tic.chiFam hVeq app (P j) ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (P j)
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (P j))
      (tic.chiFam hVeq app (P j)) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **`ℤ[𝒮]`-combinations vanishing at `1` are supported in `(M′)^#`** (the `zchar_on`/`defA1`
step of Coq `Frob_der1_type2`): every member of `inducedFamily M` is induced from the normal
`M′`, hence vanishes off `M′` (a ℤ-linear property, so every lattice element does); vanishing
at `1` then pins the support inside the sharp set.  This is the `M`-side support refinement
`supp ⊆ A₁(M) = (M′)^#` feeding the (8.18.b) disjointness (`A₀`-support alone would not do:
the pair's `A₀`-sets share the conjugates of `V`). -/
theorem Hypothesis.mem_zSpan_inducedFamily_support_sharp_derived [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) (inducedFamily M))
    (hφ1 : φ 1 = 0) :
    φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (sharpSubgroup (derivedInG M)) M := by
  haveI := hyp.finiteG
  classical
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  haveI hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  -- every lattice element vanishes off `M′` (span induction, the property is ℤ-linear)
  have hvanish : ∀ χ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) (inducedFamily M),
      ∀ w : ↥M, w ∉ (derivedInG M).subgroupOf M → χ w = 0 := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem x hx =>
        intro w hw
        obtain ⟨θ, -, hxeq⟩ := hx
        rw [hxeq]
        exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
    | zero => intro w _; rfl
    | add x y _ _ ihx ihy =>
        intro w hw
        rw [ClassFunction.add_apply, ihx w hw, ihy w hw, add_zero]
    | smul a x _ ih =>
        intro w hw
        rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.smul_apply, ih w hw, mul_zero]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    exact hz (hvanish φ hφ z hzK)
  have hz1 : z ≠ 1 := by rintro rfl; exact hz hφ1
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact ⟨Subgroup.mem_subgroupOf.mp hzK,
    fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩

open scoped FiniteInduce in
/-- **`(M′)^# ⊆ A₀(M)`**: every nonidentity element of the derived subgroup centralizes
itself (a nonidentity element of `M`), so it lies in the `A(M)`-disjunct of `typePA0` —
the same witness as `inducedFamily_sub_support`'s tail.  Composes the sharp-support
refinement back into the `A₀`-supported lattice (`extends_on_supported`). -/
theorem Hypothesis.supportInSubgroup_sharp_derived_subset_A0 [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S04.supportInSubgroup (sharpSubgroup (derivedInG M)) M
      ⊆ hyp.A0 := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hz
  obtain ⟨hzM', hz1⟩ := hz
  show (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', hz1, (z : G), ⟨z.2, hz1⟩, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

set_option linter.unusedVariables false in
open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.18.b), base-point disjointness at the canonical pair** (the
support-geometry core of Coq `oST`): no `H(a)`-thickened `A₁(M)`-point of the type-`P₁`
`M = mp.T` is conjugate to an `A(S)`-point of the type-II member `mp.S`.

This is the set-level content of `[disjoint 'A1~(M) & 'A~(S)]` (Coq
`FT_Dade_support_disjoint` part (b) + `FTsupport_facts`): a conjugacy `a·h ~ b` would
produce a supporting configuration `FTsupports M (S^x)`; the (8.13.b) unique supporting
maximal of the escaping point is of type I or II ((8.13.c4)), and the type-II case forces
`M` to be a Frobenius group with kernel `M_F` — impossible for the type-`P₁` `M`
(Coq `typePF_exclusion`).  **`sorry`d as the single remaining (8.18.b) obligation** (issue
9079 obligation 3; the (8.13) control `escapingCentralizers_control` upstream is itself an
open §8 obligation). -/
theorem typeP_pair_base_not_isConj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPair G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    {a : G} (haM' : a ∈ sharpSubgroup (derivedInG M)) (ha0 : a ∈ typePA0 M hyp.typeP)
    {h : G} (hh : h ∈ hyp.dadeData.dade.H ⟨a, ha0⟩)
    {b : G} (hbS : b ∈ centralizerSupport
      (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S)) (derivedInG mp.S)) :
    ¬ IsConj (a * h) b := by
  sorry

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.18.b), cross-Dade orthogonality at the canonical pair** (Coq `oST` of
`Frob_der1_type2`, `PFsection10.v:577-590`): for `φ` a `(M′)^#`-supported class function of
the type-`P₁` `M = mp.T` and `ψ` an `A(S)`-supported class function of the type-II member
`mp.S`, the two Dade images are orthogonal, `⟨φ^{τ_M}, ψ^{τ_S}⟩ = 0`.

The image supports are the **restricted** thickenings
(`IsDadeMap.exists_base_of_map_apply_ne_zero`): a nonvanishing point of `φ^{τ_M}` is
conjugate to `a·h` with `a ∈ Supp(φ) ⊆ A₁(M) = (M′)^#` and `h ∈ H(a)`, and a nonvanishing
point of `ψ^{τ_S}` is conjugate to a bare `b ∈ Supp(ψ) ⊆ A(S)` (the (8.16) TI-route has
trivial signalizers).  A common point would make `a·h ~ b` — impossible by the (8.18.b)
base-point disjointness (`typeP_pair_base_not_isConj`), so the supports are disjoint and
the inner product vanishes (`inner_eq_zero_of_disjoint_support`). -/
theorem Hypothesis.cross_dade_inner_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPair G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {φ : ClassFunction ↥M ℂ} {ψ : ClassFunction ↥mp.S ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (sharpSubgroup (derivedInG M)) M)
    (hψsupp : ψ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
        (derivedInG mp.S)) mp.S) :
    ClassFunction.inner (hyp.tau φ)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau ψ)
      = 0 := by
  classical
  have hφA0 : φ.support ⊆ hyp.A0 :=
    hφsupp.trans hyp.supportInSubgroup_sharp_derived_subset_A0
  have hψA0 : ψ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
          (derivedInG mp.S)
        ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S :=
    hψsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  refine ClassFunction.inner_eq_zero_of_disjoint_support ?_
  rw [Set.disjoint_left]
  intro g hg1 hg2
  rw [ClassFunction.mem_support] at hg1 hg2
  -- `M`-side base point: `g ~ a·h`, `a ∈ Supp(φ) ⊆ (M′)^#`, `h ∈ H(a)`
  have hg1' : (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData hyp.hconj) φ) g ≠ 0 := hg1
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    hyp.dadeData.dade _ hφA0] at hg1'
  obtain ⟨a, h, hh, hconja, hvala⟩ :=
    OddOrder.Peterfalvi.S04.IsDadeMap.exists_base_of_map_apply_ne_zero
      (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)) _ hg1'
  have haM' : a.1 ∈ sharpSubgroup (derivedInG M) := by
    have := hφsupp (ClassFunction.mem_support.mpr hvala)
    rwa [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at this
  -- `S`-side base point: `g ~ b·k` with `k ∈ ⊥`, so `g ~ b`, `b ∈ Supp(ψ) ⊆ A(S)`
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
    _ hψA0] at hg2
  obtain ⟨b, k, hk, hconjb, hvalb⟩ :=
    OddOrder.Peterfalvi.S04.IsDadeMap.exists_base_of_map_apply_ne_zero
      ((typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
        data.typeP).dade0.isDadeMap_dadeMap (k := ℂ)) _ hg2
  have hbS : b.1 ∈ centralizerSupport
      (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S)) (derivedInG mp.S) := by
    have := hψsupp (ClassFunction.mem_support.mpr hvalb)
    rwa [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at this
  -- the TI-route has trivial signalizers: `k = 1`
  have hk1 : k = 1 := by
    have hbot : (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
        data.typeP).dade0.H b = ⊥ := rfl
    rw [hbot, Subgroup.mem_bot] at hk
    exact hk
  -- combine the conjugacies: `a·h ~ g ~ b`
  exact typeP_pair_base_not_isConj hG hyp hT hKstar hSW1 hSW2 haM' a.2 hh hbS
    (hconja.trans (by rw [hk1, mul_one] at hconjb; exact hconjb.symm))

open scoped Classical FiniteInduce in
/-- **The (10.7) cross-side orthogonality `⟨ζ^{τ₁}, λ^{τ₂}⟩ = 0`** (the `zeta_lam_ortho`
production; Coq `Frob_der1_type2`'s `orthonormal_vchar_diff_ortho` step): the `M`-side
coherent image of `ζ` is orthogonal to the `S`-side coherent image of `λ`.

The conjugate-pair difference trick: `{ζ^{τ₁}, ζ̄^{τ₁}}` and `{λ^{τ₂}, λ̄^{τ₂}}` are
orthonormal pairs of virtual characters (the coherence isometries on distinct
irreducibles), the differences are the Dade images `(ζ − ζ̄)^{τ_M}` and `(λ − λ̄)^{τ_S}`
(coherence agreement on the supported lattice) — orthogonal by the (8.18.b) support
disjointness (`cross_dade_inner_eq_zero_at_pair`) and both vanishing at `1`
(`dadeIntegralCharacterMap_apply_one_eq_zero`), so the cross-orthogonality primitive
`orthonormal_vchar_diff_ortho` applies. -/
theorem Hypothesis.tau1_zeta_inner_extension_lam_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPair G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (_hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (_hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
            (derivedInG mp.S)
          ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S)) :
    ClassFunction.inner (coh.tau1 params.zeta) (c.extension lam) = 0 := by
  classical
  subst hT
  -- `M`-side pieces: `ζ`, `ζ̄`, their coherent images
  have hζS : params.zeta ∈ inducedFamily mp.T := params.zeta_mem_S
  have hζirr := params.zeta_irreducible
  have hModd : Odd (Nat.card ↥mp.T) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card mp.T)
  have hζne : params.zeta.conj ≠ params.zeta := inducedFamily_hasNoRealCharacters hModd hζS
  have hζcS : params.zeta.conj ∈ inducedFamily mp.T :=
    inducedFamily_closedUnderConjugate mp.T hζS
  have haZ : coh.tau1 params.zeta ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr _ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 params.zeta.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr _ (Submodule.subset_span hζcS)
  have ha1 := hyp.zeta_tau1_inner_self hG hG.odd coh hζS hζirr
  have hb1 := hyp.zeta_tau1_inner_self hG hG.odd coh hζcS hζirr.conj
  have hab : ClassFunction.inner (coh.tau1 params.zeta) (coh.tau1 params.zeta.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension _) (coh.coherent.extension _) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj,
      if_neg (fun h => hζne h.symm)]
  -- `S`-side pieces: `λ`, `λ̄`, their coherent images (as in the (5.5) span lemma)
  have hSmodd : Odd (Nat.card ↥mp.S) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card mp.S)
  have hlamIKF := typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hSmodd
      (Y.subgroupOf mp.S) hlamIKF
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  have hlam_zspan : lam ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hlamc_zspan : lam.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hcZ : c.extension lam ∈ ZIrr G := c.extension_mem_ZIrr _ hlam_zspan
  have hdZ : c.extension lam.conj ∈ ZIrr G := c.extension_mem_ZIrr _ hlamc_zspan
  have hc1 : ClassFunction.inner (c.extension lam) (c.extension lam) = 1 := by
    rw [c.extension_inner_eq _ _ hlam_zspan hlam_zspan]
    exact hlam_irr.inner_self_eq_one
  have hd1 : ClassFunction.inner (c.extension lam.conj) (c.extension lam.conj) = 1 := by
    rw [c.extension_inner_eq _ _ hlamc_zspan hlamc_zspan]
    exact hlam_irr.conj.inner_self_eq_one
  have hcd : ClassFunction.inner (c.extension lam) (c.extension lam.conj) = 0 := by
    rw [c.extension_inner_eq _ _ hlam_zspan hlamc_zspan,
      OddOrder.RepresentationTheory.irr_cf_inner hlam_irr hlam_irr.conj,
      if_neg (fun h => hlamne h)]
  -- supports of the two differences
  have hsupp : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
        (derivedInG mp.S)) mp.S := by
    have hmem := typeII_T2_member_support hG mp.S_maximal (section16_S_isTypeII hG mp) data
      hlam_mem hlam_mem
    refine diff_support_subset_of_support_subset_union_one
      (hmem lam (by simp)) (hmem lam.conj (by simp)) ?_
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [ClassFunction.conj_apply, hn, star_natCast]
  have hsuppA0 : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
          (derivedInG mp.S)
        ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S :=
    hsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  have hζ1conj : params.zeta.conj 1 = params.zeta 1 := by
    obtain ⟨nn, -, hn, -⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  have hφsupp : (params.zeta - params.zeta.conj).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (sharpSubgroup (derivedInG mp.T)) mp.T :=
    hyp.mem_zSpan_inducedFamily_support_sharp_derived
      (Submodule.sub_mem _ (Submodule.subset_span hζS) (Submodule.subset_span hζcS))
      (by rw [ClassFunction.sub_apply, hζ1conj, sub_self])
  -- the two difference identities: coherent images = Dade images
  have hMdiff : coh.tau1 params.zeta - coh.tau1 params.zeta.conj
      = hyp.tau (params.zeta - params.zeta.conj) :=
    (hyp.tau_zeta_sub_conj_eq_tau1 hG hG.odd coh hζS hζirr).symm
  have hSdiff : c.extension lam - c.extension lam.conj
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau
        (lam - lam.conj) := by
    rw [← c.extends_on_supported _
      ⟨Submodule.sub_mem _ hlam_zspan hlamc_zspan, hsuppA0⟩, map_sub]
  -- (8.18.b): the differences are orthogonal
  have hdiff : ClassFunction.inner
      (coh.tau1 params.zeta - coh.tau1 params.zeta.conj)
      (c.extension lam - c.extension lam.conj) = 0 := by
    rw [hMdiff, hSdiff]
    exact hyp.cross_dade_inner_eq_zero_at_pair hG rfl hKstar hSW1 hSW2 hφsupp hsupp
  -- both differences vanish at `1`
  have hab1 : (coh.tau1 params.zeta) 1 = (coh.tau1 params.zeta.conj) 1 := by
    have hz : (coh.tau1 params.zeta - coh.tau1 params.zeta.conj) (1 : G) = 0 := by
      rw [hMdiff]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        hyp.dadeData.dade hyp.hconj (hyp.zeta_sub_conj_support hG hG.odd hζS hζirr)
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  have hcd1 : (c.extension lam) 1 = (c.extension lam.conj) 1 := by
    have hz : (c.extension lam - c.extension lam.conj) (1 : G) = 0 := by
      rw [hSdiff]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46_dade0_hConjInvariant hG mp.S_maximal
          (section16_S_isTypeII hG mp) data.typeP) hsuppA0
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  exact orthonormal_vchar_diff_ortho haZ hbZ hcZ hdZ ha1 hb1 hc1 hd1 hab hcd hdiff hab1 hcd1

open scoped Classical FiniteInduce in
/-- **The (10.7) `cross_zero` production** (Coq `Frob_der1_type2`'s
`'[alpha^\tau, beta^{tau2}] = 0` step): for a nontrivial column `s`, the `τ₁`-image of
`α = μ_s − d·ζ` is orthogonal to `ν^{τ₂} − λ^{τ₂}`.

Both sides are Dade images of supported lattice elements: `μ_s = ∑_i μ_{is} ∈ 𝒮`
(`muGrid_column_sum_mem_inducedFamily`) and `ζ ∈ 𝒮` with `α(1) = w₁·d − d·w₁ = 0`
((10.3) degree independence and `ζ(1) = w₁`), so `α` is `(M′)^#`-supported
(`mem_zSpan_inducedFamily_support_sharp_derived`) and `τ₁α = α^{τ_M}`
(`extends_on_supported` through `(M′)^# ⊆ A₀`); `ν − λ` is `A(S)`-supported with
`τ₂(ν − λ) = (ν − λ)^{τ_S}`.  The (8.18.b) support disjointness
(`cross_dade_inner_eq_zero_at_pair`) kills the cross inner product. -/
theorem Hypothesis.tau1_muColumn_sub_zeta_inner_extension_diff_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPair G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hζ1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hμd : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hG.odd i j 1 = (params.d : ℂ))
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (_hlam_irr : IsIrreducibleCharacter lam)
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
    (s : Fin hyp.w2) (hs : s ≠ 0) :
    ClassFunction.inner
      (coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
        - (params.d : ℂ) • params.zeta))
      (c.extension nu - c.extension lam) = 0 := by
  classical
  subst hT
  -- `M`-side: `α = μ_s − d·ζ` is a `1`-vanishing lattice element, `(M′)^#`-supported
  have hd01 : hyp.muGrid hG hG.odd 0 s 1 ≠ 1 := by
    rw [hμd 0 s hs]
    intro h
    have hd : params.d = 1 := by exact_mod_cast h
    have := params.d_gt_one
    omega
  have hμS : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s) ∈ inducedFamily mp.T :=
    hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd s hd01
  have hdsmul : (params.d : ℂ) • params.zeta = (params.d : ℤ) • params.zeta := by
    rw [← Int.cast_smul_eq_zsmul ℂ (params.d : ℤ) params.zeta]
    norm_num
  have hαspan : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta
      ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.T) (inducedFamily mp.T) := by
    refine Submodule.sub_mem _ (Submodule.subset_span hμS) ?_
    rw [hdsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span params.zeta_mem_S)
  have hα1 : ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta) 1 = 0 := by
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, hζ1,
      ClassFunction.finset_sum_apply,
      Finset.sum_congr rfl (fun i _ => hμd i s hs),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hαsharp := hyp.mem_zSpan_inducedFamily_support_sharp_derived hαspan hα1
  have hM : coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta)
      = hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
        - (params.d : ℂ) • params.zeta) :=
    coh.coherent.extends_on_supported _
      ⟨hαspan, hαsharp.trans hyp.supportInSubgroup_sharp_derived_subset_A0⟩
  -- `S`-side: `ν − λ` is `A(S)`-supported
  have hψsupp : (nu - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
        (derivedInG mp.S)) mp.S := by
    have hmem := typeII_T2_member_support hG mp.S_maximal (section16_S_isTypeII hG mp) data
      hlam_mem hnu_mem
    exact diff_support_subset_of_support_subset_union_one
      (hmem nu (by simp)) (hmem lam (by simp)) hdeg.symm
  have hψA0 : (nu - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
          (derivedInG mp.S)
        ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S :=
    hψsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  have hnu_zspan : nu ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hlam_zspan : lam ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hS : c.extension nu - c.extension lam
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau
        (nu - lam) := by
    rw [← c.extends_on_supported _ ⟨Submodule.sub_mem _ hnu_zspan hlam_zspan, hψA0⟩, map_sub]
  rw [hM, hS]
  exact hyp.cross_dade_inner_eq_zero_at_pair hG rfl hKstar hSW1 hSW2 hαsharp hψsupp

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
    (hζ1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hμd : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hG.odd i j 1 = (params.d : ℂ))
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
           zeta_ortho_grid := fun i j =>
             hyp.tau1_zeta_inner_alignedGrid_eq_zero hG hG.odd coh params.zeta_mem_S
               params.zeta_irreducible i j
           zeta_lam_ortho :=
             hyp.tau1_zeta_inner_extension_lam_eq_zero_at_pair hG hT hKstar hSW1 hSW2
               coh hlam_mem hlam_irr hnu_mem hdeg c
           cross_zero := fun s hs =>
             hyp.tau1_muColumn_sub_zeta_inner_extension_diff_eq_zero_at_pair hG hT hKstar
               hSW1 hSW2 coh hζ1 hμd hlam_mem hlam_irr hnu_mem hdeg c s hs }⟩

end OddOrder.Peterfalvi.S12
