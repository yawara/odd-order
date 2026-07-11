import OddOrder.Peterfalvi.S12_MaximalIII_IV_V_Core.CharacterParameters
import OddOrder.Peterfalvi.S13_MaximalIII_IVBasic
import OddOrder.Peterfalvi.S13_Orthogonality
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapCross

/-!
# Peterfalvi (11.8): T-side non-orthogonality inputs

Producer-level bridges needed to apply the Section 11 non-orthogonality
calculation to each member of the T-side coherent family, rather than to a
freshly reselected distinguished character.
-/

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **Peterfalvi (10.1), the Section 12 carrier with a specified type-`P`
decomposition.**  The standard existence theorem chooses an unspecified
`TypePData`.  For cross-construction comparisons we must retain the already
reconciled `W₁,W₂` factors; the faithful type-`P₁` Dade producer works for that
specified datum verbatim. -/
noncomputable def s12HypothesisOfTypePData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (htype : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    OddOrder.Peterfalvi.S12.Hypothesis M := by
  let dadeData :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
      hG hM data hP1).some
  exact
    { maximal := hM
      typeP := data
      type_alt := htype
      dadeData := dadeData
      hconj := dadeData.hconj }

open scoped Classical in
/-- **Peterfalvi (4.4)--(4.5), the Section 12 zero column is the prime-TI
anchor.**  The column-`0` dual is trivial, so its distinguished constituent
restricts to `1_{M'}`.  Summing the whole column and applying (4.5.a) therefore
gives exactly `Ind_{M'}^M 1`, independently of every enumeration choice.

This is the source-side identification needed to compare the Section 11
residual with `primeTIred 0` in the T-side (11.9.a) projection. -/
theorem s12_muGrid_zeroColumn_sum_eq_induce_trivial [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) =
      ClassFunction.induce ((derivedInG M).subgroupOf M)
        (trivialClassFunction ↥((derivedInG M).subgroupOf M)) := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  haveI hNeZ1 : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  haveI hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    OddOrder.Peterfalvi.S12.typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let chi2 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup _
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2))
  have hchi2 : chi2 = 1 := by
    dsimp only [chi2]
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by
      apply Fin.ext
      simp, OddOrder.Peterfalvi.S12.finCardEquivCharacterGroup_zero]
  have hsum : ClassFunction.induce h.K
        (ClassFunction.restrict h.K
          ((h.columnFamily chi2).mu 0 : ClassFunction ↥M ℂ)) =
      ∑ i : Fin (Nat.card h.W1),
        ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ) :=
    h.induce_restrict_certainType_eq chi2
  have hsource : ClassFunction.restrict h.K
        ((h.columnFamily chi2).mu 0 : ClassFunction ↥M ℂ) =
      trivialClassFunction ↥h.K := by
    rw [hchi2, h.certainType_zero_column_anchor.2]
    ext x
    simp
  rw [hsource] at hsum
  calc
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) =
        ∑ i : Fin (Nat.card h.W1),
          ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ) := by
      rw [← Equiv.sum_comp (finCongr hcardW1.symm)
        (fun i : Fin (Nat.card h.W1) =>
          ((h.columnFamily chi2).mu i : ClassFunction ↥M ℂ))]
      exact Finset.sum_congr rfl (fun i _ => by
        unfold OddOrder.Peterfalvi.S12.Hypothesis.muGrid
        rfl)
    _ = ClassFunction.induce h.K (trivialClassFunction ↥h.K) := hsum.symm
    _ = ClassFunction.induce ((derivedInG M).subgroupOf M)
          (trivialClassFunction ↥((derivedInG M).subgroupOf M)) := rfl

open scoped Classical in
/-- **Peterfalvi (2.11)/(11.8), the Section 12 residual uses the T-side
Dade map.**  For the specified type-`P₁` datum, the Section 12 full `A₀(T)`
map restricts to the canonical `A₁(T)` map.  Together with the zero-column
anchor above, this identifies the complete source term used by (11.8) with
the `τ_T(ν₀-ζ)` term of (11.9.a). -/
theorem s12Tau_zeroColumn_sub_eq_tSideDadeMap [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (side : Hypothesis (G := G))
    (dataT : TypePData side.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 side.base.T)
    (hIII : IsTypeIII side.base.T)
    (zeta nu0 : ClassFunction ↥side.base.T ℂ)
    (hnu0 : nu0 = ClassFunction.induce
      ((derivedInG side.base.T).subgroupOf side.base.T)
      (trivialClassFunction
        ↥((derivedInG side.base.T).subgroupOf side.base.T)))
    (hsupp : (nu0 - zeta).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp side.base.T) side.base.T) :
    let hyp12 := s12HypothesisOfTypePData hG side.base.T_maximal dataT
      (Or.inl hIII) hP1
    hyp12.tau
        ((∑ i : Fin hyp12.w1, hyp12.muGrid hG hG.odd i 0) - zeta) =
      tSideDadeMap side hG (nu0 - zeta) := by
  let hyp12 := s12HypothesisOfTypePData hG side.base.T_maximal dataT
    (Or.inl hIII) hP1
  have hanchor := s12_muGrid_zeroColumn_sum_eq_induce_trivial hG hyp12
  have hmap := tSideDadeMap_eq_full_typeP1DadeMap_of_support
    hG side dataT hP1 hsupp
  change hyp12.tau
      ((∑ i : Fin hyp12.w1, hyp12.muGrid hG hG.odd i 0) - zeta) =
    tSideDadeMap side hG (nu0 - zeta)
  rw [hanchor, ← hnu0]
  simpa only [hyp12, s12HypothesisOfTypePData,
    OddOrder.Peterfalvi.S12.Hypothesis.tau] using hmap.symm

/-- **Peterfalvi (10.2)--(10.3), character parameters based at a specified
family member.**  The arithmetic data `d`, `delta`, and `n` depend only on the
maximal subgroup.  Hence the standard parameter construction can retain any
specified degree-`w₁` irreducible member `zeta` instead of discarding it and
choosing a new distinguished character.

This is the producer needed by the arbitrary-member form of the (11.8)
non-orthogonality calculation used in (11.9.a). -/
theorem exists_charParameters_full_for_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ)) :
    ∃ params : OddOrder.Peterfalvi.S12.CharacterParameters hyp,
      params.zeta = zeta ∧
      params.mu = hyp.muGrid hG hG.odd ∧
      params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd ∧
      params.zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧
      params.zeta 1 = (hyp.w1 : ℂ) ∧
      params.zeta.conj ≠ params.zeta ∧
      (params.delta = 1 ∨ params.delta = -1) ∧
      ∀ j : Fin hyp.w2, j ≠ 0 →
        hyp.muColumnSign hG hG.odd j = params.delta := by
  haveI := hyp.finiteG
  classical
  obtain ⟨d, delta, n, hd1, hnf, hn2, hdi, hdelta⟩ :=
    hyp.exists_charParamArith hG hG.odd
  let params : OddOrder.Peterfalvi.S12.CharacterParameters hyp :=
    { zeta := zeta
      zeta_mem_S := hzetaS
      zeta_irreducible := hzetairr
      d := d
      delta := delta
      n := n
      w2_prime := hyp.w2_prime hG
      d_gt_one := hd1
      mu := hyp.muGrid hG hG.odd
      omegaSigma := hyp.alignedOmegaSigmaGrid hG hG.odd
      degree_independent := hdi
      n_formula := hnf
      two_le_n := hn2
      alpha_support := fun i j hj =>
        hyp.muGrid_alpha_support hG hG.odd hj hzetaS (hdi i j hj)
          (hyp.muGrid_zero_column_apply_one hG hG.odd i) hzeta1 hnf (hdelta j hj)
      typeV_parameter_formula := True
      typeV_coherence_formula := True }
  refine ⟨params, rfl, rfl, rfl, hzetaS, hzeta1, ?_, ?_, hdelta⟩
  · exact hyp.inducedFamily_degree_w1_conj_ne hG hzetairr hzeta1
  · have hw2 : 2 ≤ hyp.w2 := (hyp.w2_prime hG).two_le
    have hj : (⟨1, by omega⟩ : Fin hyp.w2) ≠ 0 := by simp [Fin.ext_iff]
    have hde := hdelta ⟨1, by omega⟩ hj
    have hs := hyp.muColumnSign_eq_one_or_neg_one hG hG.odd ⟨1, by omega⟩
    rw [hde] at hs
    exact hs

/-- **Peterfalvi (11.1)--(11.7), the Section 13 carrier based at a specified
family member.**  This is the member-preserving form of
`S13.exists_hypothesis_of_isTypeIIIorIV`; it uses the same concrete subgroup
and chief-factor data, but retains the supplied `zeta` through the character
parameter field. -/
theorem exists_s13Hypothesis_for_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ)) :
    ∃ s13 : OddOrder.Peterfalvi.S13.Hypothesis M,
      s13.base = hyp ∧ s13.params.zeta = zeta := by
  haveI := hyp.finiteG
  classical
  have hnt : OddOrder.GroupTheory.TypePNontrivialCore M hyp.typeP :=
    OddOrder.GroupTheory.typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨params, hparams, hmu, _, hzmem, hzdeg, _, hdeltaPm, hdeltaSign⟩ :=
    exists_charParameters_full_for_member hG hyp zeta hzetaS hzetairr hzeta1
  refine ⟨{
    base := hyp
    params := params
    params_mu_eq := fun _ _ => hmu
    params_delta_sign := fun _ _ j hj => hdeltaSign j hj
    params_delta_pm := hdeltaPm
    params_zeta_mem := hzmem
    params_zeta_degree := hzdeg
    type_alt := htype
    s11Setup := hyp.toTypesIIIIIIVSetup htype hnt
    chief := (OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
      (hyp.toTypesIIIIIIVSetup htype hnt)).choose
    setup_typeP_eq := rfl
    C := hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)
    C_le_U := inf_le_left
    C_eq_centralizer := rfl
    C_normalized_by_M :=
      OddOrder.Peterfalvi.S12.typePData_C_normalized_by_M hyp.typeP hnt.1
    Hprime := derivedInG hyp.typeP.H
    Hprime_eq := rfl
    Uprime := derivedInG hyp.typeP.U
    Uprime_eq := rfl
    SOf := fun X => OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (X.subgroupOf M)
    SOf_eq := fun _ => rfl
    notOrthogonalFormula := fun _ => True
    finalOrthogonalityFormula := fun _ => True
    caseB_of_97 := True }, rfl, hparams⟩

/-- **Peterfalvi (11.8), residual non-orthogonality for a specified family
member.**  This is the arbitrary-member strengthening of
`S13.exists_zeta_residual_not_orthogonal_H0C_of_refuter`.  Its proof is the
same (11.8.1)--(11.8.6) chain, with the member-preserving parameter and
Section 13 producers above preventing the distinguished character from being
reselected. -/
theorem member_residual_not_orthogonal_H0C_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M =
      hyp.typeP.H ⊔
        (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1)
    (hrefute : ∀ s13hyp : OddOrder.Peterfalvi.S13.Hypothesis M,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ)) :
    ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - zeta)) -
          ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  obtain ⟨s13hyp, hbase, hparams⟩ :=
    exists_s13Hypothesis_for_member hG hyp htype zeta hzetaS hzetairr hzeta1
  rw [← hbase] at hM2 hHcard ⊢
  rw [← hparams]
  intro horth
  let params := s13hyp.params
  have hmu : params.mu = s13hyp.base.muGrid hG hG.odd :=
    s13hyp.params_mu_eq hG hG.odd
  have hzS : params.zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M :=
    s13hyp.params_zeta_mem
  have hz1 : params.zeta 1 = (s13hyp.base.w1 : ℂ) :=
    s13hyp.params_zeta_degree
  have hdeltaPm : params.delta = 1 ∨ params.delta = -1 :=
    s13hyp.params_delta_pm
  have hdeltaSign : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      s13hyp.base.muColumnSign hG hG.odd j = params.delta :=
    s13hyp.params_delta_sign hG hG.odd
  have hdelta1 : params.delta = 1 :=
    s13hyp.base.charParam_delta_eq_one hG htype params hmu hdeltaPm
  obtain ⟨nu, hnuConj, h114⟩ :=
    s13hyp.base.exists_coherent_extension_h114_of_orthogonal hG hG.odd hzS
      params.zeta_irreducible hz1 horth
  obtain ⟨R, hZ, hRorth, hRmem, hRrev, hRcard⟩ :=
    s13hyp.base.exists_coherentImage_SHC nu
  have hRn : R.card = params.n :=
    hRcard.trans
      (s13hyp.base.card_SHCSet_filter_eq_charParam_n
        hG htype params hmu hdeltaPm hM2 hHcard)
  have hnf : (params.n : ℤ) * (s13hyp.base.w1 : ℤ) =
      (params.d : ℤ) - 1 := by
    rw [← hdelta1]
    exact params.n_formula
  have hd : (params.d : ℂ) =
      (s13hyp.base.w1 : ℂ) * (params.n : ℂ) + 1 := by
    have h : (params.n : ℂ) * (s13hyp.base.w1 : ℂ) =
        (params.d : ℂ) - 1 := by
      exact_mod_cast hnf
    linear_combination -h
  have hmu0 : ∀ i : Fin s13hyp.base.w1,
      s13hyp.base.muGrid hG hG.odd i 0 1 = 1 :=
    fun i => s13hyp.base.muGrid_zero_column_apply_one hG hG.odd i
  have hcol : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      s13hyp.base.tau
          ((∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j) -
            (params.d : ℂ) • params.zeta) =
        (∑ i : Fin s13hyp.base.w1,
            s13hyp.base.alignedOmegaSigmaGrid hG hG.odd i j) -
          (params.d : ℂ) • nu.extension params.zeta := by
    intro j hj
    have hdeg : ∀ i : Fin s13hyp.base.w1,
        s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    have hsign : s13hyp.base.muColumnSign hG hG.odd j = 1 :=
      (hdeltaSign j hj).trans hdelta1
    exact s13hyp.base.tau_muColumnSum_sub_dzeta_eq_of_residualData
      hG nu hnuConj hG.odd hj hzS params.zeta_irreducible hz1 params.w2_prime
      hd hnf hdeg hmu0 hsign params.two_le_n hRn hZ hRorth hRmem hRrev h114
  have hzHC : params.zeta ∈ s13hyp.SOf s13hyp.HC := by
    rw [← OddOrder.Peterfalvi.S13.secondDerived_eq_HC hG s13hyp,
      s13hyp.SOf_secondDerived_eq hG]
    exact ⟨hzS, params.zeta_irreducible, hz1⟩
  have hzdeg : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      (∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j) 1 =
        (params.d : ℂ) * params.zeta 1 := by
    intro j hj
    have hall : ∀ i : Fin s13hyp.base.w1,
        s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    rw [ClassFunction.finset_sum_apply]
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hz1]
    ring
  haveI : NeZero
      (Nat.card ↥(s13hyp.base.toHypothesis46 hG hG.odd).W1) :=
    ⟨by
      have hw := (s13hyp.base.toHypothesis46 hG hG.odd).one_lt_card_W1
      omega⟩
  exact hrefute s13hyp
    (OddOrder.Peterfalvi.S13.coherent_SOf_H0C_of_column_identities hG s13hyp
      (OddOrder.Peterfalvi.S13.isCoherent_of_subset nu
        (OddOrder.Peterfalvi.S13.SOf_HC_subset_SHCSet hG s13hyp)
        (OddOrder.Peterfalvi.S13.coherent_SOf_HC hG s13hyp).some.nonzero)
      hzS hzHC hzdeg hcol)

/-- **Peterfalvi (11.8), transport to a transposed T-side grid.**
The Section 12 calculation is indexed by `W₁ × W₂`, whereas the shared
Section 16 grid writes the T-side factors in the transposed order `q × p`.
Once the two cardinal identifications, the Dade image, and each grid entry
are identified, non-orthogonality transports without any further character
theory.  The hypotheses below are equalities of the concrete producers, not
new mathematical assumptions hidden in a carrier. -/
theorem member_residual_not_orthogonal_of_transposed_alignment [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M =
      hyp.typeP.H ⊔
        (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1)
    (hrefute : ∀ s13hyp : OddOrder.Peterfalvi.S13.Hypothesis M,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    (zeta : ClassFunction ↥M ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (hyp.w1 : ℂ))
    {p q : ℕ} [NeZero p] [NeZero q]
    (hp : hyp.w1 = p) (hq : hyp.w2 = q)
    (tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G)
    (nu0 : ClassFunction ↥M ℂ)
    (eta : Fin q → Fin p → ClassFunction G ℂ)
    (himage : hyp.tau
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - zeta) =
      tauT (nu0 - zeta))
    (hgrid : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      hyp.alignedOmegaSigmaGrid hG hG.odd i j =
        eta (finCongr hq j) (finCongr hp i)) :
    ¬ ∀ (i : Fin q) (j : Fin p),
      ClassFunction.inner
        (tauT (nu0 - zeta) - ∑ j' : Fin p, eta 0 j')
        (eta i j) = 0 := by
  have hnot := member_residual_not_orthogonal_H0C_of_refuter
    hG hyp htype hM2 hHcard hrefute zeta hzetaS hzetairr hzeta1
  intro horth
  apply hnot
  intro i j
  have hsum :
      (∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0) =
        ∑ j' : Fin p, eta 0 j' := by
    calc
      (∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0) =
          ∑ i' : Fin hyp.w1, eta 0 (finCongr hp i') := by
        apply Finset.sum_congr rfl
        intro i' _
        simpa using hgrid i' 0
      _ = ∑ j' : Fin p, eta 0 j' := by
        simpa using Equiv.sum_comp (finCongr hp) (fun j' : Fin p => eta 0 j')
  rw [himage, hsum, hgrid]
  exact horth (finCongr hq j) (finCongr hp i)

/-- Reindex a non-orthogonal rectangular residual after transposing its two
axes.  Unlike `finCongr`, the equivalences may encode the independent
enumeration choices made by two concrete character-grid producers; preserving
the distinguished column-zero index is exactly what identifies the subtracted
base row. -/
theorem residual_not_orthogonal_of_transposed_reindexing
    [Fintype G] {w1 w2 p q : ℕ}
    [NeZero w1] [NeZero w2] [NeZero p] [NeZero q]
    (source : ClassFunction G ℂ)
    (grid : Fin w1 → Fin w2 → ClassFunction G ℂ)
    (eta : Fin q → Fin p → ClassFunction G ℂ)
    (rowEquiv : Fin w1 ≃ Fin p) (colEquiv : Fin w2 ≃ Fin q)
    (hcol0 : colEquiv 0 = 0)
    (hgrid : ∀ i j, grid i j = eta (colEquiv j) (rowEquiv i))
    (hnot : ¬ ∀ (i : Fin w1) (j : Fin w2),
      ClassFunction.inner
        (source - ∑ i' : Fin w1, grid i' 0) (grid i j) = 0) :
    ¬ ∀ (i : Fin q) (j : Fin p),
      ClassFunction.inner
        (source - ∑ j' : Fin p, eta 0 j') (eta i j) = 0 := by
  intro horth
  apply hnot
  intro i j
  have hsum : (∑ i' : Fin w1, grid i' 0) = ∑ j' : Fin p, eta 0 j' := by
    calc
      (∑ i' : Fin w1, grid i' 0) =
          ∑ i' : Fin w1, eta 0 (rowEquiv i') := by
        apply Finset.sum_congr rfl
        intro i' _
        rw [hgrid, hcol0]
      _ = ∑ j' : Fin p, eta 0 j' := by
        simpa using Equiv.sum_comp rowEquiv (fun j' : Fin p => eta 0 j')
  rw [hsum, hgrid]
  exact horth (colEquiv j) (rowEquiv i)

end OddOrder.Peterfalvi.S16
